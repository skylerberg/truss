let bug format = Compiler_bug.bug ~stage:"Intrinsics" format

type argument = Place of Lowered.place | Value of Lowered.operand
type types = { uint64 : Ground.ty; string_slice : Ground.ty }

let operand = function Place place -> Lowered.Copy place | Value operand -> operand
let place = function Place place -> place | Value _ -> bug "an operation on storage given a value"

let read = function
  | Place place | Value (Copy place) -> place
  | Value _ -> bug "a value to read that is in no place"

let scalar env (ty : Ground.ty) =
  match (Memory_layout.of_type env ty).form with
  | Scalar scalar -> scalar
  | _ -> bug "%s is not a number" (Ground.to_string ty)

let consumed_places : Intrinsic.operation -> int list = function
  | Array_from_storage -> [ 0 ]
  | _ -> []

let lower ?(checks = false) ?(value_arguments = []) ?reported env builder types operation
    ~type_arguments arguments ~destination ~site =
  let set rvalue =
    Option.iter
      (fun destination_place -> Emit_c.Builder.emit builder (Assign (destination_place, rvalue)))
      destination
  in
  let argument position = List.nth arguments position in
  let value position = operand (argument position) in
  let type_argument position =
    match List.nth_opt type_arguments position with
    | Some ty -> ty
    | None -> bug "a missing type argument"
  in
  let binary op = set (Binary (op, value 0, value 1)) in
  let unary op = set (Unary (op, value 0)) in
  let call ?result intrinsic arguments =
    let result = match result with Some place -> Lowered.Returned place | None -> Discarded in
    Emit_c.Builder.emit builder (Call { target = Intrinsic intrinsic; arguments; result })
  in
  let into intrinsic = call ?result:destination intrinsic (List.map operand arguments) in
  let uint64_local name = Emit_c.Builder.local builder ~name (Value types.uint64) in
  let element () = type_argument 0 in
  let element_layout () = Memory_layout.of_type env (element ()) in
  let length storage = Lowered.Copy (Storage.project_length storage) in
  let view_length view = Lowered.Copy (Storage.project_view_length view) in
  let element_at = Storage.index_element in
  let panic_when failed message =
    let fail = Emit_c.Builder.block builder and go_on = Emit_c.Builder.block builder in
    Emit_c.Builder.branch builder failed ~yes:fail ~no:go_on;
    Emit_c.Builder.start builder fail;
    Emit_c.Builder.finish builder
      (Fail
         {
           failure = Panic;
           message = Constant (Bytes message);
           length = Lowered.make_uint64_constant (String.length message);
           site;
           reported;
         });
    Emit_c.Builder.start builder go_on
  in
  let set_capacity storage capacity =
    let layout = element_layout () in
    let bytes = uint64_local "bytes" and too_many = Emit_c.Builder.local builder (Raw Bool) in
    call
      ~result:(Lowered.make_local_place too_many)
      Multiply_overflow
      [
        capacity;
        Lowered.make_uint64_constant layout.size;
        Address { place = Lowered.make_local_place bytes; writable = true };
      ];
    panic_when (Copy (Lowered.make_local_place too_many)) "out of memory";
    let buffer = Emit_c.Builder.local builder (Raw (Pointer Opaque)) in
    let is_allocated = Emit_c.Builder.local builder (Raw Bool)
    and is_unallocated = Emit_c.Builder.local builder (Raw Bool) in
    Emit_c.Builder.emit builder
      (Assign (Lowered.make_local_place is_allocated, Storage.build_is_allocated storage));
    Emit_c.Builder.emit builder
      (Assign
         ( Lowered.make_local_place is_unallocated,
           Unary (Not, Copy (Lowered.make_local_place is_allocated)) ));
    Emit_c.Builder.when_ builder
      (Copy (Lowered.make_local_place is_allocated))
      (fun () ->
        let held = uint64_local "held" in
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place held,
               Binary
                 ( Multiply,
                   Copy (Storage.project_capacity storage),
                   Lowered.make_uint64_constant layout.size ) ));
        call ~result:(Lowered.make_local_place buffer) Reallocate
          [
            Copy (Storage.project_buffer storage);
            Copy (Lowered.make_local_place held);
            Copy (Lowered.make_local_place bytes);
            Lowered.make_uint64_constant layout.alignment;
          ]);
    Emit_c.Builder.when_ builder
      (Copy (Lowered.make_local_place is_unallocated))
      (fun () ->
        call ~result:(Lowered.make_local_place buffer) Allocate
          [ Copy (Lowered.make_local_place bytes); Lowered.make_uint64_constant layout.alignment ]);
    Emit_c.Builder.emit builder
      (Assign (Storage.project_buffer storage, Use (Copy (Lowered.make_local_place buffer))));
    Emit_c.Builder.emit builder (Assign (Storage.project_capacity storage, Use capacity))
  in
  let add_to_length storage amount =
    Emit_c.Builder.emit builder
      (Assign (Storage.project_length storage, Binary (Add, length storage, amount)))
  in
  let lent place = Some place in
  let panic_if (failed : Lowered.rvalue) message =
    let decided =
      let unsigned_zero : Lowered.operand -> bool = function
        | Constant (Integer ((UInt8 | UInt16 | UInt32 | UInt64), zero)) -> Z.sign zero = 0
        | _ -> false
      in
      match failed with
      | Binary (op, Constant (Integer (_, left)), Constant (Integer (_, right))) -> (
          match op with
          | Greater -> Some (Z.gt left right)
          | Greater_equal -> Some (Z.geq left right)
          | Less -> Some (Z.lt left right)
          | Less_equal -> Some (Z.leq left right)
          | Equal -> Some (Z.equal left right)
          | Not_equal -> Some (not (Z.equal left right))
          | _ -> None)
      | Binary (Greater, zero, _) when unsigned_zero zero -> Some false
      | Binary (Less, _, zero) when unsigned_zero zero -> Some false
      | Binary (Greater_equal, _, zero) when unsigned_zero zero -> Some true
      | Binary (Less_equal, zero, _) when unsigned_zero zero -> Some true
      | _ -> None
    in
    if checks then
      match decided with
      | Some false -> ()
      | Some true ->
          Emit_c.Builder.finish builder
            (Fail
               {
                 failure = Panic;
                 message = Constant (Bytes message);
                 length = Lowered.make_uint64_constant (String.length message);
                 site;
                 reported;
               });
          Emit_c.Builder.start builder (Emit_c.Builder.block builder)
      | None ->
          let holds = Emit_c.Builder.local builder (Raw Bool) in
          Emit_c.Builder.emit builder (Assign (Lowered.make_local_place holds, failed));
          panic_when (Copy (Lowered.make_local_place holds)) message
  in
  let check_index index count =
    panic_if (Binary (Greater_equal, index, count)) "index out of bounds"
  in
  let room storage : Lowered.operand =
    let room = Emit_c.Builder.local builder ~name:"room" (Value types.uint64) in
    Emit_c.Builder.emit builder
      (Assign
         ( Lowered.make_local_place room,
           Binary (Subtract, Copy (Storage.project_capacity storage), length storage) ));
    Copy (Lowered.make_local_place room)
  in
  match (operation : Intrinsic.operation) with
  | Storage_at ->
      let storage = place (argument 0) in
      check_index (value 1) (length storage);
      lent (element_at storage (value 1))
  | Storage_at_mut ->
      check_index (value 1) (length (place (argument 0)));
      lent (element_at (place (argument 0)) (value 1))
  | View_at | View_at_mut ->
      let view = place (argument 0) in
      check_index (value 1) (view_length view);
      lent (Storage.index_view_element view (value 1))
  | Array_at_mut ->
      (match value_arguments with
      | [ count ] -> check_index (value 1) (Constant (Integer (UInt64, count)))
      | _ -> bug "array_at_mut without the array's length");
      lent (Lowered.project (place (argument 0)) (Index (value 1)))
  | _ ->
      let integer_argument () =
        match (Memory_layout.of_type env (type_argument 0)).form with
        | Scalar (Integer integer) -> Some integer
        | _ -> None
      in
      let checked_arithmetic op overflow =
        match integer_argument () with
        | Some _ when checks ->
            let result = Emit_c.Builder.local builder (Value (type_argument 0)) in
            let over = Emit_c.Builder.local builder (Raw Bool) in
            call ~result:(Lowered.make_local_place over) overflow
              [
                value 0;
                value 1;
                Address { place = Lowered.make_local_place result; writable = true };
              ];
            panic_when (Copy (Lowered.make_local_place over)) "arithmetic overflow";
            set (Use (Copy (Lowered.make_local_place result)))
        | _ -> binary op
      in
      let checked_division op =
        match integer_argument () with
        | Some integer when checks ->
            let zero = Emit_c.Builder.local builder (Raw Bool) in
            Emit_c.Builder.emit builder
              (Assign
                 ( Lowered.make_local_place zero,
                   Binary (Equal, value 1, Constant (Integer (integer, Z.zero))) ));
            panic_when (Copy (Lowered.make_local_place zero)) "division by zero";
            (match integer with
            | Int8 | Int16 | Int32 | Int64 ->
                let bits = 8 * Memory_layout.integer_size integer in
                let least = Z.neg (Z.shift_left Z.one (bits - 1)) in
                let by_minus_one = Emit_c.Builder.local builder (Raw Bool)
                and of_least = Emit_c.Builder.local builder (Raw Bool) in
                let both = Emit_c.Builder.local builder (Raw Bool) in
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place by_minus_one,
                       Binary (Equal, value 1, Constant (Integer (integer, Z.minus_one))) ));
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place of_least,
                       Binary (Equal, value 0, Constant (Integer (integer, least))) ));
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place both,
                       Binary
                         ( Bit_and,
                           Copy (Lowered.make_local_place by_minus_one),
                           Copy (Lowered.make_local_place of_least) ) ));
                panic_when (Copy (Lowered.make_local_place both)) "arithmetic overflow"
            | _ -> ());
            binary op
        | _ -> binary op
      in
      let byte = Ground.builtin UInt8 in
      let number_constant number : Lowered.operand =
        let integer =
          match scalar env (Ground.builtin (Intrinsic.libc_builtin (Libc.number_type number))) with
          | Integer integer -> integer
          | _ -> bug "a number of the C library that is not an integer"
        in
        Constant (Integer (integer, Z.of_int (Libc.value (Memory_layout.system env) number)))
      in
      let text_at address ~is_present =
        Emit_c.Builder.emit builder
          (Assign
             (is_present, Binary (Not_equal, Copy (Lowered.make_local_place address), Constant Null)));
        let elements = Emit_c.Builder.local builder (Raw (Pointer (Data byte))) in
        let count = uint64_local "length" in
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place elements, Use (Constant (Bytes ""))));
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place count, Use (Lowered.make_uint64_constant 0)));
        Emit_c.Builder.when_ builder (Copy is_present) (fun () ->
            Emit_c.Builder.emit builder
              (Assign
                 (Lowered.make_local_place elements, Use (Copy (Lowered.make_local_place address))));
            call ~result:(Lowered.make_local_place count) Terminated_length
              [ Copy (Lowered.make_local_place address) ]);
        set
          (Storage.build_view (Storage.make_view_type byte)
             ~elements:(Copy (Lowered.make_local_place elements))
             ~length:(Copy (Lowered.make_local_place count)))
      in
      (match (operation : Intrinsic.operation) with
      | Storage_at | Storage_at_mut | View_at | View_at_mut | Array_at_mut -> ()
      | Add -> checked_arithmetic Add Add_overflow
      | Subtract -> checked_arithmetic Subtract Subtract_overflow
      | Multiply -> checked_arithmetic Multiply Multiply_overflow
      | Divide -> checked_division Divide
      | Remainder -> checked_division Remainder
      | Negate -> (
          match integer_argument () with
          | Some ((Int8 | Int16 | Int32 | Int64) as integer) when checks ->
              let bits = 8 * Memory_layout.integer_size integer in
              let least = Z.neg (Z.shift_left Z.one (bits - 1)) in
              let of_least = Emit_c.Builder.local builder (Raw Bool) in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place of_least,
                     Binary (Equal, value 0, Constant (Integer (integer, least))) ));
              panic_when (Copy (Lowered.make_local_place of_least)) "arithmetic overflow";
              unary Negate
          | _ -> unary Negate)
      | Wrapping_add -> binary Add
      | Wrapping_subtract -> binary Subtract
      | Wrapping_multiply -> binary Multiply
      | Add_overflows | Subtract_overflows | Multiply_overflows ->
          let ignored = Emit_c.Builder.local builder (Value (type_argument 0)) in
          call ?result:destination
            (match operation with
            | Add_overflows -> Add_overflow
            | Subtract_overflows -> Subtract_overflow
            | _ -> Multiply_overflow)
            [
              value 0;
              value 1;
              Address { place = Lowered.make_local_place ignored; writable = true };
            ]
      | Equal -> binary Equal
      | Less -> binary Less
      | Ieee_equal -> binary Ieee_equal
      | Ieee_less -> binary Ieee_less
      | Leading_zeros -> into Leading_zeros
      | Trailing_zeros -> into Trailing_zeros
      | Count_ones -> into Count_ones
      | Swap_bytes -> into Swap_bytes
      | Rotate_left -> into Rotate_left
      | Rotate_right -> into Rotate_right
      | Multiply_high -> into Multiply_high
      | Compare_bytes ->
          let left = place (argument 0) and right = place (argument 1) in
          let shorter = Emit_c.Builder.local builder (Raw Bool) in
          let count = uint64_local "count" in
          Emit_c.Builder.emit builder
            (Assign
               (Lowered.make_local_place shorter, Binary (Less, view_length left, view_length right)));
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place count, Use (view_length right)));
          Emit_c.Builder.when_ builder
            (Copy (Lowered.make_local_place shorter))
            (fun () ->
              Emit_c.Builder.emit builder
                (Assign (Lowered.make_local_place count, Use (view_length left))));
          let order = Emit_c.Builder.local builder (Raw (Integer Int32)) in
          call ~result:(Lowered.make_local_place order) Compare_bytes
            [
              Copy (Storage.project_view_elements left);
              Copy (Storage.project_view_elements right);
              Copy (Lowered.make_local_place count);
            ];
          let same = Emit_c.Builder.local builder (Raw Bool) in
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place same,
                 Binary
                   (Equal, Copy (Lowered.make_local_place order), Constant (Integer (Int32, Z.zero)))
               ));
          Emit_c.Builder.when_ builder
            (Copy (Lowered.make_local_place same))
            (fun () ->
              let longer = Emit_c.Builder.local builder (Raw Bool)
              and shorter = Emit_c.Builder.local builder (Raw Bool) in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place longer,
                     Binary (Greater, view_length left, view_length right) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place shorter,
                     Binary (Less, view_length left, view_length right) ));
              let first = Emit_c.Builder.local builder (Raw (Integer Int32))
              and second = Emit_c.Builder.local builder (Raw (Integer Int32)) in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place first,
                     Convert (Copy (Lowered.make_local_place longer), Integer Int32) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place second,
                     Convert (Copy (Lowered.make_local_place shorter), Integer Int32) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place order,
                     Binary
                       ( Subtract,
                         Copy (Lowered.make_local_place first),
                         Copy (Lowered.make_local_place second) ) )));
          set (Convert (Copy (Lowered.make_local_place order), Integer Int8))
      | Bit_and -> binary Bit_and
      | Bit_or -> binary Bit_or
      | Bit_xor -> binary Bit_xor
      | Complement -> unary Complement
      | Shift_left | Shift_right ->
          (match (integer_argument (), scalar env (type_argument 1)) with
          | Some integer, Integer amount ->
              let bits = 8 * Memory_layout.integer_size integer in
              let constant number : Lowered.operand =
                Constant (Integer (amount, Z.of_int number))
              in
              (match amount with
              | Int8 | Int16 | Int32 | Int64 ->
                  panic_if (Binary (Less, value 1, constant 0)) "shift amount out of range"
              | _ -> ());
              panic_if (Binary (Greater_equal, value 1, constant bits)) "shift amount out of range"
          | _ -> ());
          binary (if operation = Shift_left then Shift_left else Shift_right)
      | Convert | Fits -> (
          let fits () : Lowered.rvalue =
            match (scalar env (type_argument 0), scalar env (type_argument 1)) with
            | Integer source, Integer target_integer -> (
                let source_low, source_high = Memory_layout.integer_range source in
                let low, high = Memory_layout.integer_range target_integer in
                let constant value = Lowered.Constant (Integer (source, value)) in
                let tests =
                  (if Z.lt source_low low then [ (Lowered.Greater_equal, low) ] else [])
                  @ if Z.gt source_high high then [ (Lowered.Less_equal, high) ] else []
                in
                let results =
                  List.map
                    (fun (op, bound) ->
                      let result = Emit_c.Builder.local builder (Raw Bool) in
                      Emit_c.Builder.emit builder
                        (Assign
                           (Lowered.make_local_place result, Binary (op, value 0, constant bound)));
                      Lowered.Copy (Lowered.make_local_place result))
                    tests
                in
                match results with
                | [] -> Use (Constant (Bool true))
                | [ only ] -> Use only
                | [ first; second ] -> Binary (Bit_and, first, second)
                | _ -> bug "more than two bounds")
            | ((Float32 | Float64) as source), Integer target_integer ->
                let low, high = Memory_layout.integer_range target_integer in
                let held bound =
                  match source with
                  | Float32 ->
                      Int32.float_of_bits (Int32.bits_of_float (Z.to_float bound))
                      = Z.to_float bound
                      && Z.equal (Z.of_float (Z.to_float bound)) bound
                  | _ -> Z.equal (Z.of_float (Z.to_float bound)) bound
                in
                let constant bound : Lowered.operand =
                  match source with
                  | Float32 -> Constant (Float32 (Int32.bits_of_float (Z.to_float bound)))
                  | _ -> Constant (Float64 (Int64.bits_of_float (Z.to_float bound)))
                in
                let above = Emit_c.Builder.local builder (Raw Bool)
                and below = Emit_c.Builder.local builder (Raw Bool) in
                let under = Z.pred low in
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place above,
                       if held under then Binary (Ieee_less, constant under, value 0)
                       else Binary (Ieee_less_equal, constant low, value 0) ));
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place below,
                       Binary (Ieee_less, value 0, constant (Z.succ high)) ));
                Binary
                  ( Bit_and,
                    Copy (Lowered.make_local_place above),
                    Copy (Lowered.make_local_place below) )
            | _ -> bug "fits between these types"
          in
          match (operation, scalar env (type_argument 0), scalar env (type_argument 1)) with
          | Fits, _, _ -> set (fits ())
          | _, (Float32 | Float64), Integer _ ->
              if checks then begin
                let in_range = Emit_c.Builder.local builder (Raw Bool) in
                Emit_c.Builder.emit builder (Assign (Lowered.make_local_place in_range, fits ()));
                panic_if
                  (Unary (Not, Copy (Lowered.make_local_place in_range)))
                  "conversion out of range"
              end;
              set (Convert (value 0, scalar env (type_argument 1)))
          | _ -> set (Convert (value 0, scalar env (type_argument 1))))
      | Square_root -> into Square_root
      | Fused_multiply_add -> into Fused_multiply_add
      | Floor -> into Floor
      | Ceiling -> into Ceiling
      | Truncate -> into Truncate
      | Round_to_even -> into Round_even
      | To_bits -> into Float_bits
      | From_bits -> into Float_from_bits
      | Is_nan ->
          let same = Emit_c.Builder.local builder (Raw Bool) in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place same, Binary (Ieee_equal, value 0, value 0)));
          set (Unary (Not, Copy (Lowered.make_local_place same)))
      | Storage_empty -> set (Storage.build_empty (Storage.make_storage_type (element ())))
      | Storage_with_capacity ->
          let ty = Storage.make_storage_type (element ()) in
          let result = Emit_c.Builder.local builder (Value ty) in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place result, Storage.build_empty ty));
          let any = Emit_c.Builder.local builder (Raw Bool) in
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place any,
                 Binary (Greater, value 0, Lowered.make_uint64_constant 0) ));
          Emit_c.Builder.when_ builder
            (Copy (Lowered.make_local_place any))
            (fun () -> set_capacity (Lowered.make_local_place result) (value 0));
          set (Use (Move (Lowered.make_local_place result)))
      | Storage_length -> set (Use (length (place (argument 0))))
      | Storage_capacity -> set (Use (Copy (Storage.project_capacity (place (argument 0)))))
      | Storage_set_capacity ->
          let storage = place (argument 0) in
          panic_if
            (Binary (Less, value 1, length storage))
            "a storage's capacity set to less than its length";
          set_capacity storage (value 1)
      | Storage_lengthen ->
          let storage = place (argument 0) in
          if checks then
            panic_if
              (Binary (Greater, value 1, room storage))
              "a storage lengthened to more than its capacity";
          add_to_length storage (value 1)
      | Storage_shorten ->
          let storage = place (argument 0) in
          panic_if
            (Binary (Greater, value 1, length storage))
            "a storage shortened to more than its length";
          Emit_c.Builder.emit builder (Assign (Storage.project_length storage, Use (value 1)))
      | Storage_push ->
          let storage = place (argument 0) in
          panic_if
            (Binary (Greater_equal, length storage, Copy (Storage.project_capacity storage)))
            "an element pushed to a storage that has no room";
          Emit_c.Builder.emit builder (Assign (element_at storage (length storage), Use (value 1)));
          add_to_length storage (Lowered.make_uint64_constant 1)
      | Storage_pop ->
          let storage = place (argument 0) in
          panic_if
            (Binary (Equal, length storage, Lowered.make_uint64_constant 0))
            "an element popped from an empty storage";
          Emit_c.Builder.emit builder
            (Assign
               ( Storage.project_length storage,
                 Binary (Subtract, length storage, Lowered.make_uint64_constant 1) ));
          set (Use (Move (element_at storage (length storage))))
      | Storage_insert ->
          let storage = place (argument 0) in
          let index = value 1 in
          panic_if (Binary (Greater, index, length storage)) "index out of bounds";
          panic_if
            (Binary (Greater_equal, length storage, Copy (Storage.project_capacity storage)))
            "an element inserted into a storage that has no room";
          let after = uint64_local "after" in
          let bytes = uint64_local "bytes" in
          Emit_c.Builder.emit builder
            (Assign
               (Lowered.make_local_place after, Binary (Add, index, Lowered.make_uint64_constant 1)));
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place bytes, Binary (Subtract, length storage, index)));
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place bytes,
                 Binary
                   ( Multiply,
                     Copy (Lowered.make_local_place bytes),
                     Lowered.make_uint64_constant (element_layout ()).size ) ));
          call Move_bytes
            [
              Address
                {
                  place = element_at storage (Copy (Lowered.make_local_place after));
                  writable = true;
                };
              Address { place = element_at storage index; writable = true };
              Copy (Lowered.make_local_place bytes);
            ];
          Emit_c.Builder.emit builder (Assign (element_at storage index, Use (value 2)));
          add_to_length storage (Lowered.make_uint64_constant 1)
      | Storage_remove ->
          check_index (value 1) (length (place (argument 0)));
          let storage = place (argument 0) in
          let index = value 1 in
          set (Use (Move (element_at storage index)));
          let after = uint64_local "after" in
          let bytes = uint64_local "bytes" in
          Emit_c.Builder.emit builder
            (Assign
               (Lowered.make_local_place after, Binary (Add, index, Lowered.make_uint64_constant 1)));
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place bytes,
                 Binary (Subtract, length storage, Copy (Lowered.make_local_place after)) ));
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place bytes,
                 Binary
                   ( Multiply,
                     Copy (Lowered.make_local_place bytes),
                     Lowered.make_uint64_constant (element_layout ()).size ) ));
          call Move_bytes
            [
              Address { place = element_at storage index; writable = true };
              Address
                {
                  place = element_at storage (Copy (Lowered.make_local_place after));
                  writable = true;
                };
              Copy (Lowered.make_local_place bytes);
            ];
          Emit_c.Builder.emit builder
            (Assign
               ( Storage.project_length storage,
                 Binary (Subtract, length storage, Lowered.make_uint64_constant 1) ))
      | Storage_swap ->
          check_index (value 1) (length (place (argument 0)));
          check_index (value 2) (length (place (argument 0)));
          let storage = place (argument 0) in
          let held = Emit_c.Builder.local builder (Value (element ())) in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place held, Use (Move (element_at storage (value 1)))));
          Emit_c.Builder.emit builder
            (Assign (element_at storage (value 1), Use (Move (element_at storage (value 2)))));
          Emit_c.Builder.emit builder
            (Assign (element_at storage (value 2), Use (Move (Lowered.make_local_place held))))
      | Storage_from_array ->
          let count =
            match value_arguments with
            | [ count ] -> count
            | _ -> bug "storage_from_array without the array's length"
          in
          let array_ty : Ground.ty =
            Named
              {
                path = Intrinsic.builtin_path Array;
                arguments = [ Type (element ()); Value count ];
              }
          in
          let ty = Storage.make_storage_type (element ()) in
          let result = Emit_c.Builder.local builder (Value ty) in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place result, Storage.build_empty ty));
          if Z.sign count > 0 then
            set_capacity (Lowered.make_local_place result) (Constant (Integer (UInt64, count)));
          if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
            let untyped = Emit_c.Builder.local builder (Raw (Pointer Opaque)) in
            Emit_c.Builder.emit builder
              (Assign
                 ( Lowered.make_local_place untyped,
                   Use (Copy (Storage.project_buffer (Lowered.make_local_place result))) ));
            let typed =
              Emit_c.Builder.local builder (Pointer { target = Value array_ty; writable = true })
            in
            Emit_c.Builder.emit builder
              (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place untyped))));
            Emit_c.Builder.emit builder
              (Assign ({ root = Local typed; projections = [ Deref ] }, Use (value 0)))
          end;
          add_to_length (Lowered.make_local_place result) (Constant (Integer (UInt64, count)));
          set (Use (Move (Lowered.make_local_place result)))
      | Array_from_storage ->
          let count =
            match value_arguments with
            | [ count ] -> count
            | _ -> bug "array_from_storage without the array's length"
          in
          let array_ty : Ground.ty =
            Named
              {
                path = Intrinsic.builtin_path Array;
                arguments = [ Type (element ()); Value count ];
              }
          in
          let moved_storage =
            Lowered.make_local_place
              (Emit_c.Builder.local builder (Value (Storage.make_storage_type (element ()))))
          in
          Emit_c.Builder.emit builder (Assign (moved_storage, Use (Move (place (argument 0)))));
          if checks then begin
            let other = Emit_c.Builder.local builder (Raw Bool) in
            Emit_c.Builder.emit builder
              (Assign
                 ( Lowered.make_local_place other,
                   Binary (Not_equal, length moved_storage, Constant (Integer (UInt64, count))) ));
            panic_when
              (Copy (Lowered.make_local_place other))
              "a storage made into an array of another length"
          end;
          if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
            let untyped = Emit_c.Builder.local builder (Raw (Pointer Opaque)) in
            Emit_c.Builder.emit builder
              (Assign
                 ( Lowered.make_local_place untyped,
                   Use (Copy (Storage.project_buffer moved_storage)) ));
            let typed =
              Emit_c.Builder.local builder (Pointer { target = Value array_ty; writable = true })
            in
            Emit_c.Builder.emit builder
              (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place untyped))));
            set (Use (Move { root = Local typed; projections = [ Deref ] }))
          end;
          let is_allocated = Emit_c.Builder.local builder (Raw Bool) in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place is_allocated, Storage.build_is_allocated moved_storage));
          Emit_c.Builder.when_ builder
            (Copy (Lowered.make_local_place is_allocated))
            (fun () -> call Free [ Copy (Storage.project_buffer moved_storage) ])
      | Array_view ->
          let count =
            match value_arguments with
            | [ count ] -> count
            | _ -> bug "array_view without the array's length"
          in
          let array_ty : Ground.ty =
            Named
              {
                path = Intrinsic.builtin_path Array;
                arguments = [ Type (element ()); Value count ];
              }
          in
          let elements : Lowered.operand =
            if Memory_layout.has_zero_size env array_ty then Constant (Bytes "")
            else
              Address
                {
                  place =
                    Lowered.project (read (argument 0)) (Index (Lowered.make_uint64_constant 0));
                  writable = false;
                }
          in
          set
            (Storage.build_view
               (Storage.make_view_type (element ()))
               ~elements
               ~length:(Constant (Integer (UInt64, count))))
      | View_swap ->
          check_index (value 1) (view_length (place (argument 0)));
          check_index (value 2) (view_length (place (argument 0)));
          let element_at index = Storage.index_view_element (place (argument 0)) index in
          let held = Emit_c.Builder.local builder (Value (element ())) in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place held, Use (Move (element_at (value 1)))));
          Emit_c.Builder.emit builder
            (Assign (element_at (value 1), Use (Move (element_at (value 2)))));
          Emit_c.Builder.emit builder
            (Assign (element_at (value 2), Use (Move (Lowered.make_local_place held))))
      | Storage_view ->
          let storage = place (argument 0) in
          set
            (Storage.build_view
               (Storage.make_view_type (element ()))
               ~elements:(Copy (Storage.project_buffer storage))
               ~length:(length storage))
      | View_length -> set (Use (view_length (place (argument 0))))
      | View_address ->
          set (Convert (Copy (Storage.project_view_elements (place (argument 0))), Integer UInt64))
      | View_slice ->
          let view = place (argument 0) in
          panic_if (Binary (Greater, value 1, value 2)) "slice out of bounds";
          panic_if (Binary (Greater, value 2, view_length view)) "slice out of bounds";
          let count = uint64_local "count" in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place count, Binary (Subtract, value 2, value 1)));
          set
            (Storage.build_view
               (Storage.make_view_type (element ()))
               ~elements:
                 (Address { place = Storage.index_view_element view (value 1); writable = false })
               ~length:(Copy (Lowered.make_local_place count)))
      | Storage_model | View_model | Array_model ->
          bug "a model, which exists only in specifications"
      | Crash ->
          let message = read (argument 0) in
          let bytes =
            match (Memory_layout.of_type env types.string_slice).form with
            | Struct [ only ] -> Lowered.project message (Field only.name)
            | _ -> bug "a StringSlice that is not a record of one field"
          in
          Emit_c.Builder.finish builder
            (Fail
               {
                 failure = Panic;
                 message = Copy (Storage.project_view_elements bytes);
                 length = Copy (Storage.project_view_length bytes);
                 site;
                 reported;
               });
          Emit_c.Builder.start builder (Emit_c.Builder.block builder)
      | Handle_from ->
          set
            (Build
               { ty = Ground.builtin Handle; variant = None; fields = [ ("descriptor", value 0) ] })
      | Handle_descriptor ->
          set (Use (Copy (Lowered.project (read (argument 0)) (Field "descriptor"))))
      | Shared_new ->
          let ty = type_argument 0 in
          let block = Emit_c.Builder.local builder (Raw (Pointer Opaque)) in
          call ~result:(Lowered.make_local_place block) Shared_allocate
            [ Constant (Size_of ty); Constant (Alignment_of ty) ];
          if (Memory_layout.of_type env ty).size > 0 then begin
            let typed =
              Emit_c.Builder.local builder (Pointer { target = Value ty; writable = true })
            in
            Emit_c.Builder.emit builder
              (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place block))));
            Emit_c.Builder.emit builder
              (Assign ({ root = Local typed; projections = [ Deref ] }, Use (value 0)))
          end;
          set
            (Build
               {
                 ty = Named { path = Intrinsic.builtin_path Shared; arguments = [ Type ty ] };
                 variant = None;
                 fields = [ ("value", Copy (Lowered.make_local_place block)) ];
               })
      | Shared_key ->
          set (Convert (Copy (Lowered.project (read (argument 0)) (Field "value")), Integer UInt64))
      | Shared_update -> bug "shared_update is lowered with the call of its function value"
      | Holds_invariant -> bug "holds_invariant is lowered with its type's invariant"
      | Handle_release ->
          let released =
            Emit_c.Builder.local builder
              (Value (Named { path = Intrinsic.builtin_path Handle; arguments = [] }))
          in
          Emit_c.Builder.emit builder (Assign (Lowered.make_local_place released, Use (value 0)));
          set
            (Use (Copy (Lowered.project (Lowered.make_local_place released) (Field "descriptor"))))
      | Run_test -> call Run_test [ value 0 ]
      | Coroutine_start ->
          call ?result:destination Coroutine_start [ Copy (read (argument 0)); value 1 ]
      | Coroutine_resume -> call ?result:destination Coroutine_resume [ value 0 ]
      | Coroutine_suspend -> call Coroutine_suspend []
      | Tasks_spawn ->
          call ?result:destination Tasks_spawn [ value 0; Copy (read (argument 1)); value 2 ]
      | Report_tests_to -> call Report_tests_to [ value 0 ]
      | Live_blocks -> call ?result:destination Live_blocks []
      | System_is_os os -> set (Use (Constant (Bool ((Memory_layout.system env).os = os))))
      | System_is_architecture architecture ->
          set (Use (Constant (Bool ((Memory_layout.system env).architecture = architecture))))
      | Environment_entry ->
          let environment = Emit_c.Builder.local builder (Raw (Pointer Opaque)) in
          call ~result:(Lowered.make_local_place environment) Environment [];
          let position = uint64_local "position" in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place position, Use (Lowered.make_uint64_constant 0)));
          let entry = Emit_c.Builder.local builder (Raw (Nullable_pointer (Data byte))) in
          let test = Emit_c.Builder.block builder
          and next = Emit_c.Builder.block builder
          and after = Emit_c.Builder.block builder in
          Emit_c.Builder.finish builder (Goto test);
          Emit_c.Builder.start builder test;
          call ~result:(Lowered.make_local_place entry) Program_argument
            [
              Copy (Lowered.make_local_place environment); Copy (Lowered.make_local_place position);
            ];
          let last = Emit_c.Builder.local builder (Raw Bool)
          and reached = Emit_c.Builder.local builder (Raw Bool) in
          let stop = Emit_c.Builder.local builder (Raw Bool) in
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place last,
                 Binary (Equal, Copy (Lowered.make_local_place entry), Constant Null) ));
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place reached,
                 Binary (Equal, Copy (Lowered.make_local_place position), value 0) ));
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place stop,
                 Binary
                   ( Bit_or,
                     Copy (Lowered.make_local_place last),
                     Copy (Lowered.make_local_place reached) ) ));
          Emit_c.Builder.branch builder (Copy (Lowered.make_local_place stop)) ~yes:after ~no:next;
          Emit_c.Builder.start builder next;
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place position,
                 Binary
                   (Add, Copy (Lowered.make_local_place position), Lowered.make_uint64_constant 1)
               ));
          Emit_c.Builder.finish builder (Goto test);
          Emit_c.Builder.start builder after;
          text_at entry ~is_present:(place (argument 1))
      | Libc function_ when not (Libc.available (Memory_layout.system env) function_) ->
          let message =
            Printf.sprintf "this system's C library has no %s" (Libc.function_name function_)
          in
          Emit_c.Builder.finish builder
            (Fail
               {
                 failure = Panic;
                 message = Constant (Bytes message);
                 length = Lowered.make_uint64_constant (String.length message);
                 site;
                 reported;
               });
          Emit_c.Builder.start builder (Emit_c.Builder.block builder)
      | Libc function_ -> (
          let ground scalar =
            Ground.Named
              { path = Intrinsic.builtin_path (Intrinsic.libc_builtin scalar); arguments = [] }
          in
          let { Libc.parameters; result; _ } = Libc.signature function_ in
          let after = ref [] in
          let next = ref 0 in
          let next_argument () =
            let index = !next in
            incr next;
            index
          in
          let call_arguments =
            List.map
              (fun (_, (passes : Libc.passes)) : Lowered.operand ->
                match passes with
                | Value _ -> value (next_argument ())
                | Elements _ ->
                    Copy (Storage.project_view_elements (place (argument (next_argument ()))))
                | Room _ ->
                    let storage = place (argument (next_argument ())) in
                    Address { place = element_at storage (length storage); writable = true }
                | Elements_to_change _ ->
                    Copy (Storage.project_buffer (place (argument (next_argument ()))))
                | Written (scalar, names) ->
                    let structure =
                      Emit_c.Builder.local builder
                        (Value
                           (Named
                              {
                                path = Intrinsic.builtin_path Array;
                                arguments =
                                  [ Type (ground scalar); Value (Z.of_int (List.length names)) ];
                              }))
                    in
                    List.iteri
                      (fun index _ ->
                        let written = place (argument (next_argument ())) in
                        Emit_c.Builder.emit builder
                          (Assign
                             ( Lowered.project
                                 (Lowered.make_local_place structure)
                                 (Index (Lowered.make_uint64_constant index)),
                               Use (Copy written) ));
                        after :=
                          (fun () ->
                            Emit_c.Builder.emit builder
                              (Assign
                                 ( written,
                                   Use
                                     (Copy
                                        (Lowered.project
                                           (Lowered.make_local_place structure)
                                           (Index (Lowered.make_uint64_constant index)))) )))
                          :: !after)
                      names;
                    Address { place = Lowered.make_local_place structure; writable = true }
                | Always number -> Lowered.make_uint64_constant number
                | Fixed number -> number_constant number)
              parameters
          in
          if checks then begin
            let position = ref 0 in
            let passed =
              List.concat_map
                (fun (name, (passes : Libc.passes)) ->
                  match passes with
                  | Value _ | Elements _ | Room _ | Elements_to_change _ ->
                      let index = !position in
                      incr position;
                      [ (name, Some passes, index) ]
                  | Written (_, names) ->
                      List.map
                        (fun name ->
                          let index = !position in
                          incr position;
                          (name, None, index))
                        names
                  | Always _ | Fixed _ -> [])
                parameters
            in
            let as_uint64 operand : Lowered.operand =
              let count = uint64_local "count" in
              Emit_c.Builder.emit builder
                (Assign (Lowered.make_local_place count, Convert (operand, Integer UInt64)));
              Copy (Lowered.make_local_place count)
            in
            let counted (extent : Libc.extent) : Lowered.operand option =
              match extent with
              | Counted { by; each } -> (
                  match List.find_opt (fun (name, _, _) -> name = by) passed with
                  | Some (_, _, index) ->
                      let count = as_uint64 (value index) in
                      if each = 1 then Some count
                      else begin
                        let scaled = uint64_local "count" in
                        Emit_c.Builder.emit builder
                          (Assign
                             ( Lowered.make_local_place scaled,
                               Binary (Multiply, count, Lowered.make_uint64_constant each) ));
                        Some (Copy (Lowered.make_local_place scaled))
                      end
                  | None -> bug "a C library row counts by %s, which it does not take" by)
              | Exactly elements -> Some (Lowered.make_uint64_constant elements)
              | Number number -> Some (as_uint64 (number_constant number))
              | Through_zero -> None
            in
            List.iter
              (fun (_, (passes : Libc.passes option), index) ->
                match passes with
                | Some (Room (_, extent)) ->
                    Option.iter
                      (fun count ->
                        panic_if
                          (Binary (Greater, count, room (place (argument index))))
                          "a call of the C library with less room than it writes")
                      (counted extent)
                | Some (Elements_to_change (_, extent)) ->
                    Option.iter
                      (fun count ->
                        panic_if
                          (Binary (Greater, count, length (place (argument index))))
                          "a call of the C library with fewer elements than it mutates")
                      (counted extent)
                | Some (Elements (element, extent)) -> (
                    let view = place (argument index) in
                    match counted extent with
                    | Some count ->
                        panic_if
                          (Binary (Greater, count, view_length view))
                          "a call of the C library with fewer elements than it reads"
                    | None ->
                        let message =
                          "a call of the C library with text that does not end with a zero"
                        in
                        let zero : Lowered.operand =
                          match scalar env (ground element) with
                          | Integer integer -> Constant (Integer (integer, Z.zero))
                          | _ -> bug "a C library row reads up to a zero that is not an integer"
                        in
                        panic_if
                          (Binary (Equal, view_length view, Lowered.make_uint64_constant 0))
                          message;
                        let last = uint64_local "last" in
                        Emit_c.Builder.emit builder
                          (Assign
                             ( Lowered.make_local_place last,
                               Binary (Subtract, view_length view, Lowered.make_uint64_constant 1)
                             ));
                        panic_if
                          (Binary
                             ( Not_equal,
                               Copy
                                 (Storage.index_view_element view
                                    (Copy (Lowered.make_local_place last))),
                               zero ))
                          message)
                | Some (Value _ | Written _ | Always _ | Fixed _) | None -> ())
              passed
          end;
          let target = Lowered.Foreign (Libc.declaration (Memory_layout.system env) function_) in
          let bracket intrinsic =
            if Libc.blocks function_ then
              Emit_c.Builder.emit builder
                (Call { target = Intrinsic intrinsic; arguments = []; result = Discarded })
          in
          let call result =
            bracket Blocking_begin;
            Emit_c.Builder.emit builder (Call { target; arguments = call_arguments; result });
            bracket Blocking_end;
            List.iter (fun write -> write ()) (List.rev !after)
          in
          match result with
          | Returns _ ->
              call (match destination with Some place -> Returned place | None -> Discarded)
          | Never ->
              call Discarded;
              Emit_c.Builder.finish builder Unreachable;
              Emit_c.Builder.start builder (Emit_c.Builder.block builder)
          | Points_at scalar ->
              let address = Emit_c.Builder.local builder (Raw (Pointer (Data (ground scalar)))) in
              call (Returned (Lowered.make_local_place address));
              set (Use (Copy (Lowered.project (Lowered.make_local_place address) Deref)))
          | Text ->
              let address = Emit_c.Builder.local builder (Raw (Nullable_pointer (Data byte))) in
              call (Returned (Lowered.make_local_place address));
              text_at address ~is_present:(place (argument (next_argument ()))))
      | Libc_number number -> set (Use (number_constant number)));
      None
