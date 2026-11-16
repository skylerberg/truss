module Builder = Emit_c.Builder

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
      (fun destination_place -> Builder.emit builder (Assign (destination_place, rvalue)))
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
    Builder.emit builder (Call { target = Intrinsic intrinsic; arguments; result })
  in
  let into intrinsic = call ?result:destination intrinsic (List.map operand arguments) in
  let uint64_local name = Builder.local builder ~name (Value types.uint64) in
  let element () = type_argument 0 in
  let element_layout () = Memory_layout.of_type env (element ()) in
  let length storage = Lowered.Copy (Storage.project_length storage) in
  let view_length view = Lowered.Copy (Storage.project_view_length view) in
  let element_at = Storage.index_element in
  let panic_when failed message =
    let fail = Builder.block builder and go_on = Builder.block builder in
    Builder.branch builder failed ~yes:fail ~no:go_on;
    Builder.start builder fail;
    Builder.finish builder
      (Fail
         {
           failure = Panic;
           message = Constant (Bytes message);
           length = Builder.constant_uint64 (String.length message);
           site;
           reported;
         });
    Builder.start builder go_on
  in
  let set_capacity storage capacity =
    let layout = element_layout () in
    let bytes = uint64_local "bytes" and too_many = Builder.local builder (Raw Bool) in
    call ~result:(Builder.at too_many) Multiply_overflow
      [
        capacity;
        Builder.constant_uint64 layout.size;
        Address { place = Builder.at bytes; writable = true };
      ];
    panic_when (Copy (Builder.at too_many)) "out of memory";
    let buffer = Builder.local builder (Raw (Pointer Opaque)) in
    let is_allocated = Builder.local builder (Raw Bool)
    and is_unallocated = Builder.local builder (Raw Bool) in
    Builder.emit builder (Assign (Builder.at is_allocated, Storage.build_is_allocated storage));
    Builder.emit builder
      (Assign (Builder.at is_unallocated, Unary (Not, Copy (Builder.at is_allocated))));
    Builder.when_ builder
      (Copy (Builder.at is_allocated))
      (fun () ->
        let held = uint64_local "held" in
        Builder.emit builder
          (Assign
             ( Builder.at held,
               Binary
                 ( Multiply,
                   Copy (Storage.project_capacity storage),
                   Builder.constant_uint64 layout.size ) ));
        call ~result:(Builder.at buffer) Reallocate
          [
            Copy (Storage.project_buffer storage);
            Copy (Builder.at held);
            Copy (Builder.at bytes);
            Builder.constant_uint64 layout.alignment;
          ]);
    Builder.when_ builder
      (Copy (Builder.at is_unallocated))
      (fun () ->
        call ~result:(Builder.at buffer) Allocate
          [ Copy (Builder.at bytes); Builder.constant_uint64 layout.alignment ]);
    Builder.emit builder (Assign (Storage.project_buffer storage, Use (Copy (Builder.at buffer))));
    Builder.emit builder (Assign (Storage.project_capacity storage, Use capacity))
  in
  let add_to_length storage amount =
    Builder.emit builder
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
          Builder.finish builder
            (Fail
               {
                 failure = Panic;
                 message = Constant (Bytes message);
                 length = Builder.constant_uint64 (String.length message);
                 site;
                 reported;
               });
          Builder.start builder (Builder.block builder)
      | None ->
          let holds = Builder.local builder (Raw Bool) in
          Builder.emit builder (Assign (Builder.at holds, failed));
          panic_when (Copy (Builder.at holds)) message
  in
  let check_index index count =
    panic_if (Binary (Greater_equal, index, count)) "index out of bounds"
  in
  let room storage : Lowered.operand =
    let room = Builder.local builder ~name:"room" (Value types.uint64) in
    Builder.emit builder
      (Assign
         ( Builder.at room,
           Binary (Subtract, Copy (Storage.project_capacity storage), length storage) ));
    Copy (Builder.at room)
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
            let result = Builder.local builder (Value (type_argument 0)) in
            let over = Builder.local builder (Raw Bool) in
            call ~result:(Builder.at over) overflow
              [ value 0; value 1; Address { place = Builder.at result; writable = true } ];
            panic_when (Copy (Builder.at over)) "arithmetic overflow";
            set (Use (Copy (Builder.at result)))
        | _ -> binary op
      in
      let checked_division op =
        match integer_argument () with
        | Some integer when checks ->
            let zero = Builder.local builder (Raw Bool) in
            Builder.emit builder
              (Assign
                 (Builder.at zero, Binary (Equal, value 1, Constant (Integer (integer, Z.zero)))));
            panic_when (Copy (Builder.at zero)) "division by zero";
            (match integer with
            | Int8 | Int16 | Int32 | Int64 ->
                let bits = 8 * Memory_layout.integer_size integer in
                let least = Z.neg (Z.shift_left Z.one (bits - 1)) in
                let by_minus_one = Builder.local builder (Raw Bool)
                and of_least = Builder.local builder (Raw Bool) in
                let both = Builder.local builder (Raw Bool) in
                Builder.emit builder
                  (Assign
                     ( Builder.at by_minus_one,
                       Binary (Equal, value 1, Constant (Integer (integer, Z.minus_one))) ));
                Builder.emit builder
                  (Assign
                     ( Builder.at of_least,
                       Binary (Equal, value 0, Constant (Integer (integer, least))) ));
                Builder.emit builder
                  (Assign
                     ( Builder.at both,
                       Binary (Bit_and, Copy (Builder.at by_minus_one), Copy (Builder.at of_least))
                     ));
                panic_when (Copy (Builder.at both)) "arithmetic overflow"
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
        Builder.emit builder
          (Assign (is_present, Binary (Not_equal, Copy (Builder.at address), Constant Null)));
        let elements = Builder.local builder (Raw (Pointer (Data byte))) in
        let count = uint64_local "length" in
        Builder.emit builder (Assign (Builder.at elements, Use (Constant (Bytes ""))));
        Builder.emit builder (Assign (Builder.at count, Use (Builder.constant_uint64 0)));
        Builder.when_ builder (Copy is_present) (fun () ->
            Builder.emit builder (Assign (Builder.at elements, Use (Copy (Builder.at address))));
            call ~result:(Builder.at count) Terminated_length [ Copy (Builder.at address) ]);
        set
          (Storage.build_view (Storage.make_view_type byte)
             ~elements:(Copy (Builder.at elements))
             ~length:(Copy (Builder.at count)))
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
              let of_least = Builder.local builder (Raw Bool) in
              Builder.emit builder
                (Assign
                   ( Builder.at of_least,
                     Binary (Equal, value 0, Constant (Integer (integer, least))) ));
              panic_when (Copy (Builder.at of_least)) "arithmetic overflow";
              unary Negate
          | _ -> unary Negate)
      | Wrapping_add -> binary Add
      | Wrapping_subtract -> binary Subtract
      | Wrapping_multiply -> binary Multiply
      | Add_overflows | Subtract_overflows | Multiply_overflows ->
          let ignored = Builder.local builder (Value (type_argument 0)) in
          call ?result:destination
            (match operation with
            | Add_overflows -> Add_overflow
            | Subtract_overflows -> Subtract_overflow
            | _ -> Multiply_overflow)
            [ value 0; value 1; Address { place = Builder.at ignored; writable = true } ]
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
          let shorter = Builder.local builder (Raw Bool) in
          let count = uint64_local "count" in
          Builder.emit builder
            (Assign (Builder.at shorter, Binary (Less, view_length left, view_length right)));
          Builder.emit builder (Assign (Builder.at count, Use (view_length right)));
          Builder.when_ builder
            (Copy (Builder.at shorter))
            (fun () -> Builder.emit builder (Assign (Builder.at count, Use (view_length left))));
          let order = Builder.local builder (Raw (Integer Int32)) in
          call ~result:(Builder.at order) Compare_bytes
            [
              Copy (Storage.project_view_elements left);
              Copy (Storage.project_view_elements right);
              Copy (Builder.at count);
            ];
          let same = Builder.local builder (Raw Bool) in
          Builder.emit builder
            (Assign
               ( Builder.at same,
                 Binary (Equal, Copy (Builder.at order), Constant (Integer (Int32, Z.zero))) ));
          Builder.when_ builder
            (Copy (Builder.at same))
            (fun () ->
              let longer = Builder.local builder (Raw Bool)
              and shorter = Builder.local builder (Raw Bool) in
              Builder.emit builder
                (Assign (Builder.at longer, Binary (Greater, view_length left, view_length right)));
              Builder.emit builder
                (Assign (Builder.at shorter, Binary (Less, view_length left, view_length right)));
              let first = Builder.local builder (Raw (Integer Int32))
              and second = Builder.local builder (Raw (Integer Int32)) in
              Builder.emit builder
                (Assign (Builder.at first, Convert (Copy (Builder.at longer), Integer Int32)));
              Builder.emit builder
                (Assign (Builder.at second, Convert (Copy (Builder.at shorter), Integer Int32)));
              Builder.emit builder
                (Assign
                   ( Builder.at order,
                     Binary (Subtract, Copy (Builder.at first), Copy (Builder.at second)) )));
          set (Convert (Copy (Builder.at order), Integer Int8))
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
                      let result = Builder.local builder (Raw Bool) in
                      Builder.emit builder
                        (Assign (Builder.at result, Binary (op, value 0, constant bound)));
                      Lowered.Copy (Builder.at result))
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
                let above = Builder.local builder (Raw Bool)
                and below = Builder.local builder (Raw Bool) in
                let under = Z.pred low in
                Builder.emit builder
                  (Assign
                     ( Builder.at above,
                       if held under then Binary (Ieee_less, constant under, value 0)
                       else Binary (Ieee_less_equal, constant low, value 0) ));
                Builder.emit builder
                  (Assign (Builder.at below, Binary (Ieee_less, value 0, constant (Z.succ high))));
                Binary (Bit_and, Copy (Builder.at above), Copy (Builder.at below))
            | _ -> bug "fits between these types"
          in
          match (operation, scalar env (type_argument 0), scalar env (type_argument 1)) with
          | Fits, _, _ -> set (fits ())
          | _, (Float32 | Float64), Integer _ ->
              if checks then begin
                let in_range = Builder.local builder (Raw Bool) in
                Builder.emit builder (Assign (Builder.at in_range, fits ()));
                panic_if (Unary (Not, Copy (Builder.at in_range))) "conversion out of range"
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
          let same = Builder.local builder (Raw Bool) in
          Builder.emit builder (Assign (Builder.at same, Binary (Ieee_equal, value 0, value 0)));
          set (Unary (Not, Copy (Builder.at same)))
      | Storage_empty -> set (Storage.build_empty (Storage.make_storage_type (element ())))
      | Storage_with_capacity ->
          let ty = Storage.make_storage_type (element ()) in
          let result = Builder.local builder (Value ty) in
          Builder.emit builder (Assign (Builder.at result, Storage.build_empty ty));
          let any = Builder.local builder (Raw Bool) in
          Builder.emit builder
            (Assign (Builder.at any, Binary (Greater, value 0, Builder.constant_uint64 0)));
          Builder.when_ builder
            (Copy (Builder.at any))
            (fun () -> set_capacity (Builder.at result) (value 0));
          set (Use (Move (Builder.at result)))
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
          Builder.emit builder (Assign (Storage.project_length storage, Use (value 1)))
      | Storage_push ->
          let storage = place (argument 0) in
          panic_if
            (Binary (Greater_equal, length storage, Copy (Storage.project_capacity storage)))
            "an element pushed to a storage that has no room";
          Builder.emit builder (Assign (element_at storage (length storage), Use (value 1)));
          add_to_length storage (Builder.constant_uint64 1)
      | Storage_pop ->
          let storage = place (argument 0) in
          panic_if
            (Binary (Equal, length storage, Builder.constant_uint64 0))
            "an element popped from an empty storage";
          Builder.emit builder
            (Assign
               ( Storage.project_length storage,
                 Binary (Subtract, length storage, Builder.constant_uint64 1) ));
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
          Builder.emit builder
            (Assign (Builder.at after, Binary (Add, index, Builder.constant_uint64 1)));
          Builder.emit builder (Assign (Builder.at bytes, Binary (Subtract, length storage, index)));
          Builder.emit builder
            (Assign
               ( Builder.at bytes,
                 Binary
                   ( Multiply,
                     Copy (Builder.at bytes),
                     Builder.constant_uint64 (element_layout ()).size ) ));
          call Move_bytes
            [
              Address { place = element_at storage (Copy (Builder.at after)); writable = true };
              Address { place = element_at storage index; writable = true };
              Copy (Builder.at bytes);
            ];
          Builder.emit builder (Assign (element_at storage index, Use (value 2)));
          add_to_length storage (Builder.constant_uint64 1)
      | Storage_remove ->
          check_index (value 1) (length (place (argument 0)));
          let storage = place (argument 0) in
          let index = value 1 in
          set (Use (Move (element_at storage index)));
          let after = uint64_local "after" in
          let bytes = uint64_local "bytes" in
          Builder.emit builder
            (Assign (Builder.at after, Binary (Add, index, Builder.constant_uint64 1)));
          Builder.emit builder
            (Assign (Builder.at bytes, Binary (Subtract, length storage, Copy (Builder.at after))));
          Builder.emit builder
            (Assign
               ( Builder.at bytes,
                 Binary
                   ( Multiply,
                     Copy (Builder.at bytes),
                     Builder.constant_uint64 (element_layout ()).size ) ));
          call Move_bytes
            [
              Address { place = element_at storage index; writable = true };
              Address { place = element_at storage (Copy (Builder.at after)); writable = true };
              Copy (Builder.at bytes);
            ];
          Builder.emit builder
            (Assign
               ( Storage.project_length storage,
                 Binary (Subtract, length storage, Builder.constant_uint64 1) ))
      | Storage_swap ->
          check_index (value 1) (length (place (argument 0)));
          check_index (value 2) (length (place (argument 0)));
          let storage = place (argument 0) in
          let held = Builder.local builder (Value (element ())) in
          Builder.emit builder (Assign (Builder.at held, Use (Move (element_at storage (value 1)))));
          Builder.emit builder
            (Assign (element_at storage (value 1), Use (Move (element_at storage (value 2)))));
          Builder.emit builder (Assign (element_at storage (value 2), Use (Move (Builder.at held))))
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
          let result = Builder.local builder (Value ty) in
          Builder.emit builder (Assign (Builder.at result, Storage.build_empty ty));
          if Z.sign count > 0 then
            set_capacity (Builder.at result) (Constant (Integer (UInt64, count)));
          if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
            let untyped = Builder.local builder (Raw (Pointer Opaque)) in
            Builder.emit builder
              (Assign (Builder.at untyped, Use (Copy (Storage.project_buffer (Builder.at result)))));
            let typed =
              Builder.local builder (Pointer { target = Value array_ty; writable = true })
            in
            Builder.emit builder (Assign (Builder.at typed, Use (Copy (Builder.at untyped))));
            Builder.emit builder
              (Assign ({ root = Local typed; projections = [ Deref ] }, Use (value 0)))
          end;
          add_to_length (Builder.at result) (Constant (Integer (UInt64, count)));
          set (Use (Move (Builder.at result)))
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
            Builder.at (Builder.local builder (Value (Storage.make_storage_type (element ()))))
          in
          Builder.emit builder (Assign (moved_storage, Use (Move (place (argument 0)))));
          if checks then begin
            let other = Builder.local builder (Raw Bool) in
            Builder.emit builder
              (Assign
                 ( Builder.at other,
                   Binary (Not_equal, length moved_storage, Constant (Integer (UInt64, count))) ));
            panic_when (Copy (Builder.at other)) "a storage made into an array of another length"
          end;
          if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
            let untyped = Builder.local builder (Raw (Pointer Opaque)) in
            Builder.emit builder
              (Assign (Builder.at untyped, Use (Copy (Storage.project_buffer moved_storage))));
            let typed =
              Builder.local builder (Pointer { target = Value array_ty; writable = true })
            in
            Builder.emit builder (Assign (Builder.at typed, Use (Copy (Builder.at untyped))));
            set (Use (Move { root = Local typed; projections = [ Deref ] }))
          end;
          let is_allocated = Builder.local builder (Raw Bool) in
          Builder.emit builder
            (Assign (Builder.at is_allocated, Storage.build_is_allocated moved_storage));
          Builder.when_ builder
            (Copy (Builder.at is_allocated))
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
                  place = Lowered.project (read (argument 0)) (Index (Builder.constant_uint64 0));
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
          let held = Builder.local builder (Value (element ())) in
          Builder.emit builder (Assign (Builder.at held, Use (Move (element_at (value 1)))));
          Builder.emit builder (Assign (element_at (value 1), Use (Move (element_at (value 2)))));
          Builder.emit builder (Assign (element_at (value 2), Use (Move (Builder.at held))))
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
          Builder.emit builder (Assign (Builder.at count, Binary (Subtract, value 2, value 1)));
          set
            (Storage.build_view
               (Storage.make_view_type (element ()))
               ~elements:
                 (Address { place = Storage.index_view_element view (value 1); writable = false })
               ~length:(Copy (Builder.at count)))
      | Storage_model | View_model | Array_model ->
          bug "a model, which exists only in specifications"
      | Crash ->
          let message = read (argument 0) in
          let bytes =
            match (Memory_layout.of_type env types.string_slice).form with
            | Struct [ only ] -> Lowered.project message (Field only.name)
            | _ -> bug "a StringSlice that is not a record of one field"
          in
          Builder.finish builder
            (Fail
               {
                 failure = Panic;
                 message = Copy (Storage.project_view_elements bytes);
                 length = Copy (Storage.project_view_length bytes);
                 site;
                 reported;
               });
          Builder.start builder (Builder.block builder)
      | Handle_from ->
          set
            (Build
               { ty = Ground.builtin Handle; variant = None; fields = [ ("descriptor", value 0) ] })
      | Handle_descriptor ->
          set (Use (Copy (Lowered.project (read (argument 0)) (Field "descriptor"))))
      | Shared_new ->
          let ty = type_argument 0 in
          let block = Builder.local builder (Raw (Pointer Opaque)) in
          call ~result:(Builder.at block) Shared_allocate
            [ Constant (Size_of ty); Constant (Alignment_of ty) ];
          if (Memory_layout.of_type env ty).size > 0 then begin
            let typed = Builder.local builder (Pointer { target = Value ty; writable = true }) in
            Builder.emit builder (Assign (Builder.at typed, Use (Copy (Builder.at block))));
            Builder.emit builder
              (Assign ({ root = Local typed; projections = [ Deref ] }, Use (value 0)))
          end;
          set
            (Build
               {
                 ty = Named { path = Intrinsic.builtin_path Shared; arguments = [ Type ty ] };
                 variant = None;
                 fields = [ ("value", Copy (Builder.at block)) ];
               })
      | Shared_key ->
          set (Convert (Copy (Lowered.project (read (argument 0)) (Field "value")), Integer UInt64))
      | Shared_update -> bug "shared_update is lowered with the call of its function value"
      | Holds_invariant -> bug "holds_invariant is lowered with its type's invariant"
      | Handle_release ->
          let released =
            Builder.local builder
              (Value (Named { path = Intrinsic.builtin_path Handle; arguments = [] }))
          in
          Builder.emit builder (Assign (Builder.at released, Use (value 0)));
          set (Use (Copy (Lowered.project (Builder.at released) (Field "descriptor"))))
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
          let environment = Builder.local builder (Raw (Pointer Opaque)) in
          call ~result:(Builder.at environment) Environment [];
          let position = uint64_local "position" in
          Builder.emit builder (Assign (Builder.at position, Use (Builder.constant_uint64 0)));
          let entry = Builder.local builder (Raw (Nullable_pointer (Data byte))) in
          let test = Builder.block builder
          and next = Builder.block builder
          and after = Builder.block builder in
          Builder.finish builder (Goto test);
          Builder.start builder test;
          call ~result:(Builder.at entry) Program_argument
            [ Copy (Builder.at environment); Copy (Builder.at position) ];
          let last = Builder.local builder (Raw Bool)
          and reached = Builder.local builder (Raw Bool) in
          let stop = Builder.local builder (Raw Bool) in
          Builder.emit builder
            (Assign (Builder.at last, Binary (Equal, Copy (Builder.at entry), Constant Null)));
          Builder.emit builder
            (Assign (Builder.at reached, Binary (Equal, Copy (Builder.at position), value 0)));
          Builder.emit builder
            (Assign
               (Builder.at stop, Binary (Bit_or, Copy (Builder.at last), Copy (Builder.at reached))));
          Builder.branch builder (Copy (Builder.at stop)) ~yes:after ~no:next;
          Builder.start builder next;
          Builder.emit builder
            (Assign
               ( Builder.at position,
                 Binary (Add, Copy (Builder.at position), Builder.constant_uint64 1) ));
          Builder.finish builder (Goto test);
          Builder.start builder after;
          text_at entry ~is_present:(place (argument 1))
      | Libc function_ when not (Libc.available (Memory_layout.system env) function_) ->
          let message =
            Printf.sprintf "this system's C library has no %s" (Libc.function_name function_)
          in
          Builder.finish builder
            (Fail
               {
                 failure = Panic;
                 message = Constant (Bytes message);
                 length = Builder.constant_uint64 (String.length message);
                 site;
                 reported;
               });
          Builder.start builder (Builder.block builder)
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
                      Builder.local builder
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
                        Builder.emit builder
                          (Assign
                             ( Lowered.project (Builder.at structure)
                                 (Index (Builder.constant_uint64 index)),
                               Use (Copy written) ));
                        after :=
                          (fun () ->
                            Builder.emit builder
                              (Assign
                                 ( written,
                                   Use
                                     (Copy
                                        (Lowered.project (Builder.at structure)
                                           (Index (Builder.constant_uint64 index)))) )))
                          :: !after)
                      names;
                    Address { place = Builder.at structure; writable = true }
                | Always number -> Builder.constant_uint64 number
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
              Builder.emit builder (Assign (Builder.at count, Convert (operand, Integer UInt64)));
              Copy (Builder.at count)
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
                        Builder.emit builder
                          (Assign
                             ( Builder.at scaled,
                               Binary (Multiply, count, Builder.constant_uint64 each) ));
                        Some (Copy (Builder.at scaled))
                      end
                  | None -> bug "a C library row counts by %s, which it does not take" by)
              | Exactly elements -> Some (Builder.constant_uint64 elements)
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
                          (Binary (Equal, view_length view, Builder.constant_uint64 0))
                          message;
                        let last = uint64_local "last" in
                        Builder.emit builder
                          (Assign
                             ( Builder.at last,
                               Binary (Subtract, view_length view, Builder.constant_uint64 1) ));
                        panic_if
                          (Binary
                             ( Not_equal,
                               Copy (Storage.index_view_element view (Copy (Builder.at last))),
                               zero ))
                          message)
                | Some (Value _ | Written _ | Always _ | Fixed _) | None -> ())
              passed
          end;
          let target = Lowered.Foreign (Libc.declaration (Memory_layout.system env) function_) in
          let bracket intrinsic =
            if Libc.blocks function_ then
              Builder.emit builder
                (Call { target = Intrinsic intrinsic; arguments = []; result = Discarded })
          in
          let call result =
            bracket Blocking_begin;
            Builder.emit builder (Call { target; arguments = call_arguments; result });
            bracket Blocking_end;
            List.iter (fun write -> write ()) (List.rev !after)
          in
          match result with
          | Returns _ ->
              call (match destination with Some place -> Returned place | None -> Discarded)
          | Never ->
              call Discarded;
              Builder.finish builder Unreachable;
              Builder.start builder (Builder.block builder)
          | Points_at scalar ->
              let address = Builder.local builder (Raw (Pointer (Data (ground scalar)))) in
              call (Returned (Builder.at address));
              set (Use (Copy (Lowered.project (Builder.at address) Deref)))
          | Text ->
              let address = Builder.local builder (Raw (Nullable_pointer (Data byte))) in
              call (Returned (Builder.at address));
              text_at address ~is_present:(place (argument (next_argument ()))))
      | Libc_number number -> set (Use (number_constant number)));
      None
