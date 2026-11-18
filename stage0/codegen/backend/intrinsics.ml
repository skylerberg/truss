let raise_bug format = Compiler_bug.raise_bug ~stage:"Intrinsics" format

type argument = Place of Lowered.place | Value of Lowered.operand
type types = { uint64 : Ground.ty; string_slice : Ground.ty }

let make_operand = function Place place -> Lowered.Copy place | Value operand -> operand

let extract_place = function
  | Place place -> place
  | Value _ -> raise_bug "an operation on storage given a value"

let read = function
  | Place place | Value (Copy place) -> place
  | Value _ -> raise_bug "a value to read that is in no place"

let classify_scalar env (ty : Ground.ty) =
  match (Memory_layout.of_type env ty).form with
  | Scalar scalar -> scalar
  | _ -> raise_bug "%s is not a number" (Ground.to_string ty)

let list_consumed_places : Intrinsic.operation -> int list = function
  | Buffer Array_from_storage -> [ 0 ]
  | _ -> []

let lower ?(value_arguments = []) ?reported env builder types operation ~type_arguments arguments
    ~destination ~site ~trace =
  let set rvalue =
    Option.iter
      (fun destination_place -> Emit_c.Builder.emit builder (Assign (destination_place, rvalue)))
      destination
  in
  let read_argument position = List.nth arguments position in
  let read_operand position = make_operand (read_argument position) in
  let read_type_argument position =
    match List.nth_opt type_arguments position with
    | Some ty -> ty
    | None -> raise_bug "a missing type argument"
  in
  let call ?result intrinsic arguments =
    let result = match result with Some place -> Lowered.Returned place | None -> Discarded in
    Emit_c.Builder.emit builder (Call { target = Intrinsic intrinsic; arguments; result })
  in
  let allocate_uint64_local () = Emit_c.Builder.allocate_local builder (Value types.uint64) in
  let copy_length storage = Lowered.Copy (Storage.project_length storage) in
  let copy_view_length view = Lowered.Copy (Storage.project_view_length view) in
  let index_element = Storage.index_element in
  let fail failure message =
    Emit_c.Builder.finish builder
      (Fail
         {
           failure;
           message = Constant (Bytes message);
           length = Lowered.make_uint64_constant (String.length message);
           site;
           reported;
           trace;
         })
  in
  let fail_when failure condition message =
    let failed = Emit_c.Builder.allocate_block builder
    and after = Emit_c.Builder.allocate_block builder in
    Emit_c.Builder.branch builder condition ~yes:failed ~no:after;
    Emit_c.Builder.start builder failed;
    fail failure message;
    Emit_c.Builder.start builder after
  in
  let check_when condition message = fail_when Obligation condition message in
  let check_if (condition : Lowered.rvalue) message =
    let decided =
      let is_unsigned_zero : Lowered.operand -> bool = function
        | Constant (Integer ((UInt8 | UInt16 | UInt32 | UInt64), zero)) -> Z.sign zero = 0
        | _ -> false
      in
      match condition with
      | Binary (op, Constant (Integer (_, left)), Constant (Integer (_, right))) -> (
          match op with
          | Greater -> Some (Z.gt left right)
          | Greater_equal -> Some (Z.geq left right)
          | Less -> Some (Z.lt left right)
          | Less_equal -> Some (Z.leq left right)
          | Equal -> Some (Z.equal left right)
          | Not_equal -> Some (not (Z.equal left right))
          | _ -> None)
      | Binary (Greater, zero, _) when is_unsigned_zero zero -> Some false
      | Binary (Less, _, zero) when is_unsigned_zero zero -> Some false
      | Binary (Greater_equal, _, zero) when is_unsigned_zero zero -> Some true
      | Binary (Less_equal, zero, _) when is_unsigned_zero zero -> Some true
      | _ -> None
    in
    match decided with
    | Some false -> ()
    | Some true ->
        fail Obligation message;
        Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder)
    | None ->
        let is_failed = Emit_c.Builder.allocate_local builder (Raw Bool) in
        Emit_c.Builder.emit builder (Assign (Lowered.make_local_place is_failed, condition));
        check_when (Copy (Lowered.make_local_place is_failed)) message
  in
  let check_index index count =
    check_if (Binary (Greater_equal, index, count)) "index out of bounds"
  in
  let compute_room storage : Lowered.operand =
    let room = Emit_c.Builder.allocate_local builder (Value types.uint64) in
    Emit_c.Builder.emit builder
      (Assign
         ( Lowered.make_local_place room,
           Binary (Subtract, Copy (Storage.project_capacity storage), copy_length storage) ));
    Copy (Lowered.make_local_place room)
  in
  let read_array_length () =
    match value_arguments with
    | [ count ] -> count
    | _ -> raise_bug "%s without the array's length" (Intrinsic.show_operation operation)
  in
  let lower_lend : Intrinsic.lend -> Lowered.place = function
    | Storage_at | Storage_at_mut ->
        let storage = extract_place (read_argument 0) in
        check_index (read_operand 1) (copy_length storage);
        index_element storage (read_operand 1)
    | View_at | View_at_mut ->
        let view = extract_place (read_argument 0) in
        check_index (read_operand 1) (copy_view_length view);
        Storage.index_view_element view (read_operand 1)
    | Array_at_mut ->
        check_index (read_operand 1) (Constant (Integer (UInt64, read_array_length ())));
        Lowered.project (extract_place (read_argument 0)) (Index (read_operand 1))
  in
  let lower_scalar (scalar : Intrinsic.scalar) =
    let set_binary op = set (Binary (op, read_operand 0, read_operand 1)) in
    let set_unary op = set (Unary (op, read_operand 0)) in
    let call_into intrinsic =
      call ?result:destination intrinsic (List.map make_operand arguments)
    in
    let find_integer_argument () =
      match (Memory_layout.of_type env (read_type_argument 0)).form with
      | Scalar (Integer integer) -> Some integer
      | _ -> None
    in
    let lower_checked_arithmetic op overflow =
      match find_integer_argument () with
      | Some _ ->
          let result = Emit_c.Builder.allocate_local builder (Value (read_type_argument 0)) in
          let over = Emit_c.Builder.allocate_local builder (Raw Bool) in
          call ~result:(Lowered.make_local_place over) overflow
            [
              read_operand 0;
              read_operand 1;
              Address { place = Lowered.make_local_place result; writable = true };
            ];
          check_when (Copy (Lowered.make_local_place over)) "arithmetic overflow";
          set (Use (Copy (Lowered.make_local_place result)))
      | _ -> set_binary op
    in
    let lower_checked_division op =
      match find_integer_argument () with
      | Some integer ->
          let zero = Emit_c.Builder.allocate_local builder (Raw Bool) in
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place zero,
                 Binary (Equal, read_operand 1, Constant (Integer (integer, Z.zero))) ));
          check_when (Copy (Lowered.make_local_place zero)) "division by zero";
          (match integer with
          | Int8 | Int16 | Int32 | Int64 ->
              let bits = 8 * Memory_layout.compute_integer_size integer in
              let least = Z.neg (Z.shift_left Z.one (bits - 1)) in
              let by_minus_one = Emit_c.Builder.allocate_local builder (Raw Bool)
              and of_least = Emit_c.Builder.allocate_local builder (Raw Bool) in
              let both = Emit_c.Builder.allocate_local builder (Raw Bool) in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place by_minus_one,
                     Binary (Equal, read_operand 1, Constant (Integer (integer, Z.minus_one))) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place of_least,
                     Binary (Equal, read_operand 0, Constant (Integer (integer, least))) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place both,
                     Binary
                       ( Bit_and,
                         Copy (Lowered.make_local_place by_minus_one),
                         Copy (Lowered.make_local_place of_least) ) ));
              check_when (Copy (Lowered.make_local_place both)) "arithmetic overflow"
          | _ -> ());
          set_binary op
      | _ -> set_binary op
    in
    let lower_overflow_test overflow =
      let ignored = Emit_c.Builder.allocate_local builder (Value (read_type_argument 0)) in
      call ?result:destination overflow
        [
          read_operand 0;
          read_operand 1;
          Address { place = Lowered.make_local_place ignored; writable = true };
        ]
    in
    let lower_checked_shift op =
      (match (find_integer_argument (), classify_scalar env (read_type_argument 1)) with
      | Some integer, Integer amount ->
          let bits = 8 * Memory_layout.compute_integer_size integer in
          let make_constant number : Lowered.operand =
            Constant (Integer (amount, Z.of_int number))
          in
          (match amount with
          | Int8 | Int16 | Int32 | Int64 ->
              check_if (Binary (Less, read_operand 1, make_constant 0)) "shift amount out of range"
          | _ -> ());
          check_if
            (Binary (Greater_equal, read_operand 1, make_constant bits))
            "shift amount out of range"
      | _ -> ());
      set_binary op
    in
    let make_fits_test () : Lowered.rvalue =
      match
        (classify_scalar env (read_type_argument 0), classify_scalar env (read_type_argument 1))
      with
      | Integer source, Integer target_integer -> (
          let source_low, source_high = Memory_layout.compute_integer_range source in
          let low, high = Memory_layout.compute_integer_range target_integer in
          let make_constant value = Lowered.Constant (Integer (source, value)) in
          let tests =
            (if Z.lt source_low low then [ (Lowered.Greater_equal, low) ] else [])
            @ if Z.gt source_high high then [ (Lowered.Less_equal, high) ] else []
          in
          let results =
            List.map
              (fun (op, bound) ->
                let result = Emit_c.Builder.allocate_local builder (Raw Bool) in
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place result,
                       Binary (op, read_operand 0, make_constant bound) ));
                Lowered.Copy (Lowered.make_local_place result))
              tests
          in
          match results with
          | [] -> Use (Constant (Bool true))
          | [ only ] -> Use only
          | [ first; second ] -> Binary (Bit_and, first, second)
          | _ -> raise_bug "more than two bounds")
      | ((Float32 | Float64) as source), Integer target_integer ->
          let low, high = Memory_layout.compute_integer_range target_integer in
          let is_held bound =
            match source with
            | Float32 ->
                Int32.float_of_bits (Int32.bits_of_float (Z.to_float bound)) = Z.to_float bound
                && Z.equal (Z.of_float (Z.to_float bound)) bound
            | _ -> Z.equal (Z.of_float (Z.to_float bound)) bound
          in
          let make_constant bound : Lowered.operand =
            match source with
            | Float32 -> Constant (Float32 (Int32.bits_of_float (Z.to_float bound)))
            | _ -> Constant (Float64 (Int64.bits_of_float (Z.to_float bound)))
          in
          let above = Emit_c.Builder.allocate_local builder (Raw Bool)
          and below = Emit_c.Builder.allocate_local builder (Raw Bool) in
          let under = Z.pred low in
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place above,
                 if is_held under then Binary (Ieee_less, make_constant under, read_operand 0)
                 else Binary (Ieee_less_equal, make_constant low, read_operand 0) ));
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place below,
                 Binary (Ieee_less, read_operand 0, make_constant (Z.succ high)) ));
          Binary
            (Bit_and, Copy (Lowered.make_local_place above), Copy (Lowered.make_local_place below))
      | _ -> raise_bug "fits between these types"
    in
    match scalar with
    | Add -> lower_checked_arithmetic Add Add_overflow
    | Subtract -> lower_checked_arithmetic Subtract Subtract_overflow
    | Multiply -> lower_checked_arithmetic Multiply Multiply_overflow
    | Divide -> lower_checked_division Divide
    | Remainder -> lower_checked_division Remainder
    | Negate -> (
        match find_integer_argument () with
        | Some ((Int8 | Int16 | Int32 | Int64) as integer) ->
            let bits = 8 * Memory_layout.compute_integer_size integer in
            let least = Z.neg (Z.shift_left Z.one (bits - 1)) in
            let of_least = Emit_c.Builder.allocate_local builder (Raw Bool) in
            Emit_c.Builder.emit builder
              (Assign
                 ( Lowered.make_local_place of_least,
                   Binary (Equal, read_operand 0, Constant (Integer (integer, least))) ));
            check_when (Copy (Lowered.make_local_place of_least)) "arithmetic overflow";
            set_unary Negate
        | _ -> set_unary Negate)
    | Wrapping_add -> set_binary Add
    | Wrapping_subtract -> set_binary Subtract
    | Wrapping_multiply -> set_binary Multiply
    | Add_overflows -> lower_overflow_test Add_overflow
    | Subtract_overflows -> lower_overflow_test Subtract_overflow
    | Multiply_overflows -> lower_overflow_test Multiply_overflow
    | Equal -> set_binary Equal
    | Less -> set_binary Less
    | Ieee_equal -> set_binary Ieee_equal
    | Ieee_less -> set_binary Ieee_less
    | Leading_zeros -> call_into Leading_zeros
    | Trailing_zeros -> call_into Trailing_zeros
    | Count_ones -> call_into Count_ones
    | Swap_bytes -> call_into Swap_bytes
    | Rotate_left -> call_into Rotate_left
    | Rotate_right -> call_into Rotate_right
    | Multiply_high -> call_into Multiply_high
    | Bit_and -> set_binary Bit_and
    | Bit_or -> set_binary Bit_or
    | Bit_xor -> set_binary Bit_xor
    | Complement -> set_unary Complement
    | Shift_left -> lower_checked_shift Shift_left
    | Shift_right -> lower_checked_shift Shift_right
    | Fits -> set (make_fits_test ())
    | Convert ->
        (match
           (classify_scalar env (read_type_argument 0), classify_scalar env (read_type_argument 1))
         with
        | (Float32 | Float64), Integer _ ->
            let in_range = Emit_c.Builder.allocate_local builder (Raw Bool) in
            Emit_c.Builder.emit builder
              (Assign (Lowered.make_local_place in_range, make_fits_test ()));
            check_if
              (Unary (Not, Copy (Lowered.make_local_place in_range)))
              "conversion out of range"
        | _ -> ());
        set (Convert (read_operand 0, classify_scalar env (read_type_argument 1)))
    | Square_root -> call_into Square_root
    | Fused_multiply_add -> call_into Fused_multiply_add
    | Floor -> call_into Floor
    | Ceiling -> call_into Ceiling
    | Truncate -> call_into Truncate
    | Round_to_even -> call_into Round_even
    | To_bits -> call_into Float_bits
    | From_bits -> call_into Float_from_bits
    | Is_nan ->
        let same = Emit_c.Builder.allocate_local builder (Raw Bool) in
        Emit_c.Builder.emit builder
          (Assign
             (Lowered.make_local_place same, Binary (Ieee_equal, read_operand 0, read_operand 0)));
        set (Unary (Not, Copy (Lowered.make_local_place same)))
  in
  let lower_buffer (buffer : Intrinsic.buffer) =
    let read_element_type () = read_type_argument 0 in
    let make_array_type count : Ground.ty =
      Named
        {
          path = Intrinsic.make_builtin_path Array;
          arguments = [ Type (read_element_type ()); Value count ];
        }
    in
    let compute_element_layout () = Memory_layout.of_type env (read_element_type ()) in
    let set_capacity storage capacity =
      let layout = compute_element_layout () in
      let bytes = allocate_uint64_local ()
      and too_many = Emit_c.Builder.allocate_local builder (Raw Bool) in
      call
        ~result:(Lowered.make_local_place too_many)
        Multiply_overflow
        [
          capacity;
          Lowered.make_uint64_constant layout.size;
          Address { place = Lowered.make_local_place bytes; writable = true };
        ];
      fail_when Panic (Copy (Lowered.make_local_place too_many)) "out of memory";
      let buffer = Emit_c.Builder.allocate_local builder (Raw (Pointer Opaque)) in
      let is_allocated = Emit_c.Builder.allocate_local builder (Raw Bool)
      and is_unallocated = Emit_c.Builder.allocate_local builder (Raw Bool) in
      Emit_c.Builder.emit builder
        (Assign (Lowered.make_local_place is_allocated, Storage.build_is_allocated storage));
      Emit_c.Builder.emit builder
        (Assign
           ( Lowered.make_local_place is_unallocated,
             Unary (Not, Copy (Lowered.make_local_place is_allocated)) ));
      Emit_c.Builder.emit_when builder
        (Copy (Lowered.make_local_place is_allocated))
        (fun () ->
          let held = allocate_uint64_local () in
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
      Emit_c.Builder.emit_when builder
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
        (Assign (Storage.project_length storage, Binary (Add, copy_length storage, amount)))
    in
    match buffer with
    | Compare_bytes ->
        let left = extract_place (read_argument 0) and right = extract_place (read_argument 1) in
        let shorter = Emit_c.Builder.allocate_local builder (Raw Bool) in
        let count = allocate_uint64_local () in
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place shorter,
               Binary (Less, copy_view_length left, copy_view_length right) ));
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place count, Use (copy_view_length right)));
        Emit_c.Builder.emit_when builder
          (Copy (Lowered.make_local_place shorter))
          (fun () ->
            Emit_c.Builder.emit builder
              (Assign (Lowered.make_local_place count, Use (copy_view_length left))));
        let order = Emit_c.Builder.allocate_local builder (Raw (Integer Int32)) in
        call ~result:(Lowered.make_local_place order) Compare_bytes
          [
            Copy (Storage.project_view_elements left);
            Copy (Storage.project_view_elements right);
            Copy (Lowered.make_local_place count);
          ];
        let same = Emit_c.Builder.allocate_local builder (Raw Bool) in
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place same,
               Binary
                 (Equal, Copy (Lowered.make_local_place order), Constant (Integer (Int32, Z.zero)))
             ));
        Emit_c.Builder.emit_when builder
          (Copy (Lowered.make_local_place same))
          (fun () ->
            let longer = Emit_c.Builder.allocate_local builder (Raw Bool)
            and shorter = Emit_c.Builder.allocate_local builder (Raw Bool) in
            Emit_c.Builder.emit builder
              (Assign
                 ( Lowered.make_local_place longer,
                   Binary (Greater, copy_view_length left, copy_view_length right) ));
            Emit_c.Builder.emit builder
              (Assign
                 ( Lowered.make_local_place shorter,
                   Binary (Less, copy_view_length left, copy_view_length right) ));
            let first = Emit_c.Builder.allocate_local builder (Raw (Integer Int32))
            and second = Emit_c.Builder.allocate_local builder (Raw (Integer Int32)) in
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
    | Storage_empty -> set (Storage.build_empty (Storage.make_storage_type (read_element_type ())))
    | Storage_with_capacity ->
        let ty = Storage.make_storage_type (read_element_type ()) in
        let result = Emit_c.Builder.allocate_local builder (Value ty) in
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place result, Storage.build_empty ty));
        let any = Emit_c.Builder.allocate_local builder (Raw Bool) in
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place any,
               Binary (Greater, read_operand 0, Lowered.make_uint64_constant 0) ));
        Emit_c.Builder.emit_when builder
          (Copy (Lowered.make_local_place any))
          (fun () -> set_capacity (Lowered.make_local_place result) (read_operand 0));
        set (Use (Move (Lowered.make_local_place result)))
    | Storage_length -> set (Use (copy_length (extract_place (read_argument 0))))
    | Storage_capacity ->
        set (Use (Copy (Storage.project_capacity (extract_place (read_argument 0)))))
    | Storage_set_capacity ->
        let storage = extract_place (read_argument 0) in
        check_if
          (Binary (Less, read_operand 1, copy_length storage))
          "a storage's capacity set to less than its length";
        set_capacity storage (read_operand 1)
    | Storage_lengthen ->
        let storage = extract_place (read_argument 0) in
        check_if
          (Binary (Greater, read_operand 1, compute_room storage))
          "a storage lengthened to more than its capacity";
        add_to_length storage (read_operand 1)
    | Storage_shorten ->
        let storage = extract_place (read_argument 0) in
        check_if
          (Binary (Greater, read_operand 1, copy_length storage))
          "a storage shortened to more than its length";
        Emit_c.Builder.emit builder (Assign (Storage.project_length storage, Use (read_operand 1)))
    | Storage_push ->
        let storage = extract_place (read_argument 0) in
        check_if
          (Binary (Greater_equal, copy_length storage, Copy (Storage.project_capacity storage)))
          "an element pushed to a storage that has no room";
        Emit_c.Builder.emit builder
          (Assign (index_element storage (copy_length storage), Use (read_operand 1)));
        add_to_length storage (Lowered.make_uint64_constant 1)
    | Storage_pop ->
        let storage = extract_place (read_argument 0) in
        check_if
          (Binary (Equal, copy_length storage, Lowered.make_uint64_constant 0))
          "an element popped from an empty storage";
        Emit_c.Builder.emit builder
          (Assign
             ( Storage.project_length storage,
               Binary (Subtract, copy_length storage, Lowered.make_uint64_constant 1) ));
        set (Use (Move (index_element storage (copy_length storage))))
    | Storage_insert ->
        let storage = extract_place (read_argument 0) in
        let index = read_operand 1 in
        check_if (Binary (Greater, index, copy_length storage)) "index out of bounds";
        check_if
          (Binary (Greater_equal, copy_length storage, Copy (Storage.project_capacity storage)))
          "an element inserted into a storage that has no room";
        let after = allocate_uint64_local () in
        let bytes = allocate_uint64_local () in
        Emit_c.Builder.emit builder
          (Assign
             (Lowered.make_local_place after, Binary (Add, index, Lowered.make_uint64_constant 1)));
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place bytes, Binary (Subtract, copy_length storage, index)));
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place bytes,
               Binary
                 ( Multiply,
                   Copy (Lowered.make_local_place bytes),
                   Lowered.make_uint64_constant (compute_element_layout ()).size ) ));
        call Move_bytes
          [
            Address
              {
                place = index_element storage (Copy (Lowered.make_local_place after));
                writable = true;
              };
            Address { place = index_element storage index; writable = true };
            Copy (Lowered.make_local_place bytes);
          ];
        Emit_c.Builder.emit builder (Assign (index_element storage index, Use (read_operand 2)));
        add_to_length storage (Lowered.make_uint64_constant 1)
    | Storage_remove ->
        check_index (read_operand 1) (copy_length (extract_place (read_argument 0)));
        let storage = extract_place (read_argument 0) in
        let index = read_operand 1 in
        set (Use (Move (index_element storage index)));
        let after = allocate_uint64_local () in
        let bytes = allocate_uint64_local () in
        Emit_c.Builder.emit builder
          (Assign
             (Lowered.make_local_place after, Binary (Add, index, Lowered.make_uint64_constant 1)));
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place bytes,
               Binary (Subtract, copy_length storage, Copy (Lowered.make_local_place after)) ));
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place bytes,
               Binary
                 ( Multiply,
                   Copy (Lowered.make_local_place bytes),
                   Lowered.make_uint64_constant (compute_element_layout ()).size ) ));
        call Move_bytes
          [
            Address { place = index_element storage index; writable = true };
            Address
              {
                place = index_element storage (Copy (Lowered.make_local_place after));
                writable = true;
              };
            Copy (Lowered.make_local_place bytes);
          ];
        Emit_c.Builder.emit builder
          (Assign
             ( Storage.project_length storage,
               Binary (Subtract, copy_length storage, Lowered.make_uint64_constant 1) ))
    | Storage_swap ->
        check_index (read_operand 1) (copy_length (extract_place (read_argument 0)));
        check_index (read_operand 2) (copy_length (extract_place (read_argument 0)));
        let storage = extract_place (read_argument 0) in
        let held = Emit_c.Builder.allocate_local builder (Value (read_element_type ())) in
        Emit_c.Builder.emit builder
          (Assign
             (Lowered.make_local_place held, Use (Move (index_element storage (read_operand 1)))));
        Emit_c.Builder.emit builder
          (Assign
             ( index_element storage (read_operand 1),
               Use (Move (index_element storage (read_operand 2))) ));
        Emit_c.Builder.emit builder
          (Assign
             (index_element storage (read_operand 2), Use (Move (Lowered.make_local_place held))))
    | Storage_from_array ->
        let count = read_array_length () in
        let array_ty = make_array_type count in
        let ty = Storage.make_storage_type (read_element_type ()) in
        let result = Emit_c.Builder.allocate_local builder (Value ty) in
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place result, Storage.build_empty ty));
        if Z.sign count > 0 then
          set_capacity (Lowered.make_local_place result) (Constant (Integer (UInt64, count)));
        if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
          let untyped = Emit_c.Builder.allocate_local builder (Raw (Pointer Opaque)) in
          Emit_c.Builder.emit builder
            (Assign
               ( Lowered.make_local_place untyped,
                 Use (Copy (Storage.project_buffer (Lowered.make_local_place result))) ));
          let typed =
            Emit_c.Builder.allocate_local builder
              (Pointer { target = Value array_ty; writable = true })
          in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place untyped))));
          Emit_c.Builder.emit builder
            (Assign ({ root = Local typed; projections = [ Deref ] }, Use (read_operand 0)))
        end;
        add_to_length (Lowered.make_local_place result) (Constant (Integer (UInt64, count)));
        set (Use (Move (Lowered.make_local_place result)))
    | Array_from_storage ->
        let count = read_array_length () in
        let array_ty = make_array_type count in
        let moved_storage =
          Lowered.make_local_place
            (Emit_c.Builder.allocate_local builder
               (Value (Storage.make_storage_type (read_element_type ()))))
        in
        Emit_c.Builder.emit builder
          (Assign (moved_storage, Use (Move (extract_place (read_argument 0)))));
        check_if
          (Binary (Not_equal, copy_length moved_storage, Constant (Integer (UInt64, count))))
          "a storage made into an array of another length";
        if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
          let untyped = Emit_c.Builder.allocate_local builder (Raw (Pointer Opaque)) in
          Emit_c.Builder.emit builder
            (Assign
               (Lowered.make_local_place untyped, Use (Copy (Storage.project_buffer moved_storage))));
          let typed =
            Emit_c.Builder.allocate_local builder
              (Pointer { target = Value array_ty; writable = true })
          in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place untyped))));
          set (Use (Move { root = Local typed; projections = [ Deref ] }))
        end;
        let is_allocated = Emit_c.Builder.allocate_local builder (Raw Bool) in
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place is_allocated, Storage.build_is_allocated moved_storage));
        Emit_c.Builder.emit_when builder
          (Copy (Lowered.make_local_place is_allocated))
          (fun () -> call Free [ Copy (Storage.project_buffer moved_storage) ])
    | Array_view ->
        let count = read_array_length () in
        let array_ty = make_array_type count in
        let elements : Lowered.operand =
          if Memory_layout.has_zero_size env array_ty then Constant (Bytes "")
          else
            Address
              {
                place =
                  Lowered.project (read (read_argument 0)) (Index (Lowered.make_uint64_constant 0));
                writable = false;
              }
        in
        set
          (Storage.build_view
             (Storage.make_view_type (read_element_type ()))
             ~elements
             ~length:(Constant (Integer (UInt64, count))))
    | View_swap ->
        check_index (read_operand 1) (copy_view_length (extract_place (read_argument 0)));
        check_index (read_operand 2) (copy_view_length (extract_place (read_argument 0)));
        let index_element index =
          Storage.index_view_element (extract_place (read_argument 0)) index
        in
        let held = Emit_c.Builder.allocate_local builder (Value (read_element_type ())) in
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place held, Use (Move (index_element (read_operand 1)))));
        Emit_c.Builder.emit builder
          (Assign (index_element (read_operand 1), Use (Move (index_element (read_operand 2)))));
        Emit_c.Builder.emit builder
          (Assign (index_element (read_operand 2), Use (Move (Lowered.make_local_place held))))
    | Storage_view ->
        let storage = extract_place (read_argument 0) in
        set
          (Storage.build_view
             (Storage.make_view_type (read_element_type ()))
             ~elements:(Copy (Storage.project_buffer storage))
             ~length:(copy_length storage))
    | View_length -> set (Use (copy_view_length (extract_place (read_argument 0))))
    | View_address ->
        set
          (Convert
             (Copy (Storage.project_view_elements (extract_place (read_argument 0))), Integer UInt64))
    | View_slice ->
        let view = extract_place (read_argument 0) in
        check_if (Binary (Greater, read_operand 1, read_operand 2)) "slice out of bounds";
        check_if (Binary (Greater, read_operand 2, copy_view_length view)) "slice out of bounds";
        let count = allocate_uint64_local () in
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place count, Binary (Subtract, read_operand 2, read_operand 1)));
        set
          (Storage.build_view
             (Storage.make_view_type (read_element_type ()))
             ~elements:
               (Address
                  { place = Storage.index_view_element view (read_operand 1); writable = false })
             ~length:(Copy (Lowered.make_local_place count)))
    | Storage_model | View_model | Array_model ->
        raise_bug "a model, which exists only in specifications"
  in
  let lower_runtime (runtime : Intrinsic.runtime) =
    let byte = Ground.make_builtin UInt8 in
    let make_number_constant number : Lowered.operand =
      let integer =
        match
          classify_scalar env
            (Ground.make_builtin (Intrinsic.convert_libc_scalar (Libc.classify_number number)))
        with
        | Integer integer -> integer
        | _ -> raise_bug "a number of the C library that is not an integer"
      in
      Constant
        (Integer (integer, Z.of_int (Libc.evaluate_number (Memory_layout.system env) number)))
    in
    let load_text_at address ~is_present =
      Emit_c.Builder.emit builder
        (Assign
           (is_present, Binary (Not_equal, Copy (Lowered.make_local_place address), Constant Null)));
      let elements = Emit_c.Builder.allocate_local builder (Raw (Pointer (Data byte))) in
      let count = allocate_uint64_local () in
      Emit_c.Builder.emit builder
        (Assign (Lowered.make_local_place elements, Use (Constant (Bytes ""))));
      Emit_c.Builder.emit builder
        (Assign (Lowered.make_local_place count, Use (Lowered.make_uint64_constant 0)));
      Emit_c.Builder.emit_when builder (Copy is_present) (fun () ->
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
    match runtime with
    | Crash ->
        let message = read (read_argument 0) in
        let bytes =
          match (Memory_layout.of_type env types.string_slice).form with
          | Struct [ only ] -> Lowered.project message (Field only.name)
          | _ -> raise_bug "a StringSlice that is not a record of one field"
        in
        Emit_c.Builder.finish builder
          (Fail
             {
               failure = Panic;
               message = Copy (Storage.project_view_elements bytes);
               length = Copy (Storage.project_view_length bytes);
               site;
               reported;
               trace;
             });
        Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder)
    | Handle_from ->
        set
          (Build
             {
               ty = Ground.make_builtin Handle;
               variant = None;
               fields = [ ("descriptor", read_operand 0) ];
             })
    | Handle_descriptor ->
        set (Use (Copy (Lowered.project (read (read_argument 0)) (Field "descriptor"))))
    | Shared_new ->
        let ty = read_type_argument 0 in
        let block = Emit_c.Builder.allocate_local builder (Raw (Pointer Opaque)) in
        call ~result:(Lowered.make_local_place block) Shared_allocate
          [ Constant (Size_of ty); Constant (Alignment_of ty) ];
        if (Memory_layout.of_type env ty).size > 0 then begin
          let typed =
            Emit_c.Builder.allocate_local builder (Pointer { target = Value ty; writable = true })
          in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place typed, Use (Copy (Lowered.make_local_place block))));
          Emit_c.Builder.emit builder
            (Assign ({ root = Local typed; projections = [ Deref ] }, Use (read_operand 0)))
        end;
        set
          (Build
             {
               ty = Named { path = Intrinsic.make_builtin_path Shared; arguments = [ Type ty ] };
               variant = None;
               fields = [ ("value", Copy (Lowered.make_local_place block)) ];
             })
    | Shared_key ->
        set
          (Convert (Copy (Lowered.project (read (read_argument 0)) (Field "value")), Integer UInt64))
    | Shared_update -> raise_bug "shared_update is lowered with the call of its function value"
    | Holds_invariant -> raise_bug "holds_invariant is lowered with its type's invariant"
    | Handle_release ->
        let released =
          Emit_c.Builder.allocate_local builder
            (Value (Named { path = Intrinsic.make_builtin_path Handle; arguments = [] }))
        in
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place released, Use (read_operand 0)));
        set (Use (Copy (Lowered.project (Lowered.make_local_place released) (Field "descriptor"))))
    | Run_test -> call Run_test [ read_operand 0 ]
    | Coroutine_start ->
        call ?result:destination Coroutine_start [ Copy (read (read_argument 0)); read_operand 1 ]
    | Coroutine_resume -> call ?result:destination Coroutine_resume [ read_operand 0 ]
    | Coroutine_suspend -> call Coroutine_suspend []
    | Tasks_spawn ->
        call ?result:destination Tasks_spawn
          [ read_operand 0; Copy (read (read_argument 1)); read_operand 2 ]
    | Report_tests_to -> call Report_tests_to [ read_operand 0 ]
    | Live_blocks -> call ?result:destination Live_blocks []
    | System_is_os os -> set (Use (Constant (Bool ((Memory_layout.system env).os = os))))
    | System_is_architecture architecture ->
        set (Use (Constant (Bool ((Memory_layout.system env).architecture = architecture))))
    | Environment_entry ->
        let environment = Emit_c.Builder.allocate_local builder (Raw (Pointer Opaque)) in
        call ~result:(Lowered.make_local_place environment) Environment [];
        let position = allocate_uint64_local () in
        Emit_c.Builder.emit builder
          (Assign (Lowered.make_local_place position, Use (Lowered.make_uint64_constant 0)));
        let entry = Emit_c.Builder.allocate_local builder (Raw (Nullable_pointer (Data byte))) in
        let test = Emit_c.Builder.allocate_block builder
        and next = Emit_c.Builder.allocate_block builder
        and after = Emit_c.Builder.allocate_block builder in
        Emit_c.Builder.finish builder (Goto test);
        Emit_c.Builder.start builder test;
        call ~result:(Lowered.make_local_place entry) Program_argument
          [ Copy (Lowered.make_local_place environment); Copy (Lowered.make_local_place position) ];
        let last = Emit_c.Builder.allocate_local builder (Raw Bool)
        and reached = Emit_c.Builder.allocate_local builder (Raw Bool) in
        let stop = Emit_c.Builder.allocate_local builder (Raw Bool) in
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place last,
               Binary (Equal, Copy (Lowered.make_local_place entry), Constant Null) ));
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place reached,
               Binary (Equal, Copy (Lowered.make_local_place position), read_operand 0) ));
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
               Binary (Add, Copy (Lowered.make_local_place position), Lowered.make_uint64_constant 1)
             ));
        Emit_c.Builder.finish builder (Goto test);
        Emit_c.Builder.start builder after;
        load_text_at entry ~is_present:(extract_place (read_argument 1))
    | Libc function_ when not (Libc.is_available (Memory_layout.system env) function_) ->
        fail Panic
          (Printf.sprintf "this system's C library has no %s" (Libc.show_function function_));
        Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder)
    | Libc function_ -> (
        let ground scalar =
          Ground.Named
            {
              path = Intrinsic.make_builtin_path (Intrinsic.convert_libc_scalar scalar);
              arguments = [];
            }
        in
        let { Libc.parameters; result; _ } = Libc.make_signature function_ in
        let after = ref [] in
        let next = ref 0 in
        let take_argument_index () =
          let index = !next in
          incr next;
          index
        in
        let call_arguments =
          List.map
            (fun (_, (passes : Libc.passes)) : Lowered.operand ->
              match passes with
              | Value _ -> read_operand (take_argument_index ())
              | Elements _ ->
                  Copy
                    (Storage.project_view_elements
                       (extract_place (read_argument (take_argument_index ()))))
              | Room _ ->
                  let storage = extract_place (read_argument (take_argument_index ())) in
                  Address { place = index_element storage (copy_length storage); writable = true }
              | Elements_to_change _ ->
                  Copy
                    (Storage.project_buffer
                       (extract_place (read_argument (take_argument_index ()))))
              | Written (scalar, names) ->
                  let structure =
                    Emit_c.Builder.allocate_local builder
                      (Value
                         (Named
                            {
                              path = Intrinsic.make_builtin_path Array;
                              arguments =
                                [ Type (ground scalar); Value (Z.of_int (List.length names)) ];
                            }))
                  in
                  List.iteri
                    (fun index _ ->
                      let written = extract_place (read_argument (take_argument_index ())) in
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
              | Fixed number -> make_number_constant number)
            parameters
        in
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
        let cast_to_uint64 operand : Lowered.operand =
          let count = allocate_uint64_local () in
          Emit_c.Builder.emit builder
            (Assign (Lowered.make_local_place count, Convert (operand, Integer UInt64)));
          Copy (Lowered.make_local_place count)
        in
        let find_count (extent : Libc.extent) : Lowered.operand option =
          match extent with
          | Counted { by; each } -> (
              match List.find_opt (fun (name, _, _) -> name = by) passed with
              | Some (_, _, index) ->
                  let count = cast_to_uint64 (read_operand index) in
                  if each = 1 then Some count
                  else begin
                    let scaled = allocate_uint64_local () in
                    Emit_c.Builder.emit builder
                      (Assign
                         ( Lowered.make_local_place scaled,
                           Binary (Multiply, count, Lowered.make_uint64_constant each) ));
                    Some (Copy (Lowered.make_local_place scaled))
                  end
              | None -> raise_bug "a C library row counts by %s, which it does not take" by)
          | Exactly elements -> Some (Lowered.make_uint64_constant elements)
          | Number number -> Some (cast_to_uint64 (make_number_constant number))
          | Through_zero -> None
        in
        List.iter
          (fun (_, (passes : Libc.passes option), index) ->
            match passes with
            | Some (Room (_, extent)) ->
                Option.iter
                  (fun count ->
                    check_if
                      (Binary (Greater, count, compute_room (extract_place (read_argument index))))
                      "a call of the C library with less room than it writes")
                  (find_count extent)
            | Some (Elements_to_change (_, extent)) ->
                Option.iter
                  (fun count ->
                    check_if
                      (Binary (Greater, count, copy_length (extract_place (read_argument index))))
                      "a call of the C library with fewer elements than it mutates")
                  (find_count extent)
            | Some (Elements (element, extent)) -> (
                let view = extract_place (read_argument index) in
                match find_count extent with
                | Some count ->
                    check_if
                      (Binary (Greater, count, copy_view_length view))
                      "a call of the C library with fewer elements than it reads"
                | None ->
                    let message =
                      "a call of the C library with text that does not end with a zero"
                    in
                    let zero : Lowered.operand =
                      match classify_scalar env (ground element) with
                      | Integer integer -> Constant (Integer (integer, Z.zero))
                      | _ -> raise_bug "a C library row reads up to a zero that is not an integer"
                    in
                    check_if
                      (Binary (Equal, copy_view_length view, Lowered.make_uint64_constant 0))
                      message;
                    let last = allocate_uint64_local () in
                    Emit_c.Builder.emit builder
                      (Assign
                         ( Lowered.make_local_place last,
                           Binary (Subtract, copy_view_length view, Lowered.make_uint64_constant 1)
                         ));
                    check_if
                      (Binary
                         ( Not_equal,
                           Copy
                             (Storage.index_view_element view
                                (Copy (Lowered.make_local_place last))),
                           zero ))
                      message)
            | Some (Value _ | Written _ | Always _ | Fixed _) | None -> ())
          passed;
        let target = Lowered.Foreign (Libc.make_declaration (Memory_layout.system env) function_) in
        let emit_bracket intrinsic =
          if Libc.is_blocking function_ then
            Emit_c.Builder.emit builder
              (Call { target = Intrinsic intrinsic; arguments = []; result = Discarded })
        in
        let call result =
          emit_bracket Blocking_begin;
          Emit_c.Builder.emit builder (Call { target; arguments = call_arguments; result });
          emit_bracket Blocking_end;
          List.iter (fun write -> write ()) (List.rev !after)
        in
        match result with
        | Returns _ ->
            call (match destination with Some place -> Returned place | None -> Discarded)
        | Never ->
            call Discarded;
            Emit_c.Builder.finish builder Unreachable;
            Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder)
        | Points_at scalar ->
            let address =
              Emit_c.Builder.allocate_local builder (Raw (Pointer (Data (ground scalar))))
            in
            call (Returned (Lowered.make_local_place address));
            set (Use (Copy (Lowered.project (Lowered.make_local_place address) Deref)))
        | Text ->
            let address =
              Emit_c.Builder.allocate_local builder (Raw (Nullable_pointer (Data byte)))
            in
            call (Returned (Lowered.make_local_place address));
            load_text_at address
              ~is_present:(extract_place (read_argument (take_argument_index ()))))
    | Libc_number number -> set (Use (make_number_constant number))
  in
  match operation with
  | Lend lend -> Some (lower_lend lend)
  | Scalar scalar ->
      lower_scalar scalar;
      None
  | Buffer buffer ->
      lower_buffer buffer;
      None
  | Runtime runtime ->
      lower_runtime runtime;
      None
