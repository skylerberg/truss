open Lir_builder

let bug format = Compiler_bug.bug ~stage:"Intrinsics" format

type argument = Place of Lir.place | Value of Lir.operand
type types = { usize : Ground.ty; string_slice : Ground.ty }

let operand = function Place place -> Lir.Copy place | Value operand -> operand
let place = function Place place -> place | Value _ -> bug "an operation on storage given a value"

(* Where a value that is only read is: it arrives as a place, or as a copy
   of one. *)
let read = function
  | Place place | Value (Copy place) -> place
  | Value _ -> bug "a value to read that is in no place"

let scalar env (ty : Ground.ty) =
  match (Memory_layout.of_type env ty).form with
  | Scalar scalar -> scalar
  | _ -> bug "%s is not a number" (Ground.to_string ty)

let lower ?(checks = false) ?(value_arguments = []) env builder types operation ~type_arguments
    arguments ~destination ~site =
  let set rvalue =
    Option.iter
      (fun destination_place -> emit builder (Assign (destination_place, rvalue)))
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
    let result = match result with Some place -> Lir.Returned place | None -> Discarded in
    emit builder (Call { target = Intrinsic intrinsic; arguments; result })
  in
  let into intrinsic = call ?result:destination intrinsic (List.map operand arguments) in
  let usize_local name = local builder ~name (Value types.usize) in
  let element () = type_argument 0 in
  let element_layout ?element:element_type () =
    Memory_layout.of_type env
      (match element_type with Some element -> element | None -> element ())
  in
  let length storage = Lir.Copy (Storage.length storage) in
  let view_length view = Lir.Copy (Storage.view_length view) in
  let element_at = Storage.at in
  (* Ends the run with a panic where [failed] holds. *)
  let panic_when failed message =
    let fail = block builder and go_on = block builder in
    branch builder failed ~yes:fail ~no:go_on;
    start builder fail;
    finish builder
      (Fail
         {
           failure = Panic;
           message = Constant (Bytes message);
           length = usize (String.length message);
           site;
           caller = None;
         });
    start builder go_on
  in
  (* Gives the storage a buffer of its own with room for exactly [capacity]
     elements, which is at least as many as it has. A buffer it owns is
     made larger; elements it does not own, as static ones are, are copied
     to a new one and never freed. *)
  let set_capacity ?element storage capacity =
    let layout = element_layout ?element () in
    let bytes = usize_local "bytes" and too_many = local builder (Raw Bool) in
    call ~result:(at too_many) Multiply_overflow
      [ capacity; usize layout.size; Address { place = at bytes; writable = true } ];
    panic_when (Copy (at too_many)) "out of memory";
    let buffer = local builder (Raw (Pointer Opaque)) in
    let owns = local builder (Raw Bool) and borrows = local builder (Raw Bool) in
    emit builder (Assign (at owns, Binary (Not_equal, Copy (Storage.capacity storage), usize 0)));
    emit builder (Assign (at borrows, Unary (Not, Copy (at owns))));
    when_ builder
      (Copy (at owns))
      (fun () ->
        let held = usize_local "held" in
        emit builder
          (Assign (at held, Binary (Multiply, Copy (Storage.capacity storage), usize layout.size)));
        call ~result:(at buffer) Reallocate
          [ Copy (Storage.buffer storage); Copy (at held); Copy (at bytes); usize layout.alignment ]);
    when_ builder
      (Copy (at borrows))
      (fun () ->
        call ~result:(at buffer) Allocate [ Copy (at bytes); usize layout.alignment ];
        let used = usize_local "used" in
        emit builder (Assign (at used, Binary (Multiply, length storage, usize layout.size)));
        call Copy_bytes [ Copy (at buffer); Copy (Storage.buffer storage); Copy (at used) ]);
    emit builder (Assign (Storage.buffer storage, Use (Copy (at buffer))));
    emit builder (Assign (Storage.capacity storage, Use capacity))
  in
  (* Static storage gets a buffer of its own before it is written. *)
  let own ?element storage =
    let storage = place storage in
    let borrowed = local builder (Raw Bool) in
    emit builder
      (Assign (at borrowed, Binary (Greater, length storage, Copy (Storage.capacity storage))));
    when_ builder (Copy (at borrowed)) (fun () -> set_capacity ?element storage (length storage))
  in
  let add_to_length storage amount =
    emit builder (Assign (Storage.length storage, Binary (Add, length storage, amount)))
  in
  let lent place = Some place in
  (* In a checked build, ends the run with a panic where [failed] holds. A
     checked build does not wait for proofs, so it checks each operation
     that is undefined in C, or gives a wrong value, where its precondition
     does not hold. These are the only checks: no [requires] clause is
     evaluated when a program runs. *)
  let panic_if (failed : Lir.rvalue) message =
    (* A comparison's value where its operands decide it: two
       constants, or an unsigned value and zero. Such a comparison is not
       written. GCC reports a comparison of an unsigned value with zero
       that always or never holds, and the tests compile the C with every
       warning an error. *)
    let decided =
      let unsigned_zero : Lir.operand -> bool = function
        | Constant (Integer ((UInt8 | UInt16 | UInt32 | UInt64 | USize), zero)) -> Z.sign zero = 0
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
          finish builder
            (Fail
               {
                 failure = Panic;
                 message = Constant (Bytes message);
                 length = usize (String.length message);
                 site;
                 caller = None;
               });
          start builder (block builder)
      | None ->
          let holds = local builder (Raw Bool) in
          emit builder (Assign (at holds, failed));
          panic_when (Copy (at holds)) message
  in
  let check_index index count =
    panic_if (Binary (Greater_equal, index, count)) "index out of bounds"
  in
  (* How many more elements a storage has room for. A static storage has a
     capacity below its length, and has none. *)
  let room storage : Lir.operand =
    let room = local builder ~name:"room" (Value types.usize) in
    let any = local builder (Raw Bool) in
    emit builder (Assign (at room, Use (usize 0)));
    emit builder
      (Assign (at any, Binary (Greater, Copy (Storage.capacity storage), length storage)));
    when_ builder
      (Copy (at any))
      (fun () ->
        emit builder
          (Assign (at room, Binary (Subtract, Copy (Storage.capacity storage), length storage))));
    Copy (at room)
  in
  match (operation : Intrinsic.operation) with
  | Storage_at ->
      let storage = place (argument 0) in
      check_index (value 1) (length storage);
      lent (element_at storage (value 1))
  | Storage_at_mut ->
      check_index (value 1) (length (place (argument 0)));
      own (argument 0);
      lent (element_at (place (argument 0)) (value 1))
  | View_at | View_at_mut ->
      let view = place (argument 0) in
      check_index (value 1) (view_length view);
      lent (Storage.view_at view (value 1))
  | Array_at_mut ->
      (match value_arguments with
      | [ count ] -> check_index (value 1) (Constant (Integer (USize, count)))
      | _ -> bug "array_at_mut without the array's length");
      lent (place (argument 0) / Index (value 1))
  | _ ->
      let integer_argument () =
        match (Memory_layout.of_type env (type_argument 0)).form with
        | Scalar (Integer integer) -> Some integer
        | _ -> None
      in
      (* Integer arithmetic that panics on overflow in a checked build; it wraps
     otherwise, which the prover shows never happens. *)
      let checked_arithmetic op overflow =
        match integer_argument () with
        | Some _ when checks ->
            let result = local builder (Value (type_argument 0)) in
            let over = local builder (Raw Bool) in
            call ~result:(at over) overflow
              [ value 0; value 1; Address { place = at result; writable = true } ];
            panic_when (Copy (at over)) "arithmetic overflow";
            set (Use (Copy (at result)))
        | _ -> binary op
      in
      (* Integer division that panics on a zero divisor, and on the one quotient
     that does not fit, the least value over -1, in a checked build. *)
      let checked_division op =
        match integer_argument () with
        | Some integer when checks ->
            let zero = local builder (Raw Bool) in
            emit builder
              (Assign (at zero, Binary (Equal, value 1, Constant (Integer (integer, Z.zero)))));
            panic_when (Copy (at zero)) "division by zero";
            (match integer with
            | Int8 | Int16 | Int32 | Int64 | ISize ->
                let bits = 8 * Memory_layout.integer_size (Memory_layout.target env) integer in
                let least = Z.neg (Z.shift_left Z.one (bits - 1)) in
                let by_minus_one = local builder (Raw Bool)
                and of_least = local builder (Raw Bool) in
                let both = local builder (Raw Bool) in
                emit builder
                  (Assign
                     ( at by_minus_one,
                       Binary (Equal, value 1, Constant (Integer (integer, Z.minus_one))) ));
                emit builder
                  (Assign (at of_least, Binary (Equal, value 0, Constant (Integer (integer, least)))));
                emit builder
                  (Assign (at both, Binary (Bit_and, Copy (at by_minus_one), Copy (at of_least))));
                panic_when (Copy (at both)) "arithmetic overflow"
            | _ -> ());
            binary op
        | _ -> binary op
      in
      let byte : Ground.ty = Named { path = Intrinsic.builtin_path UInt8; arguments = [] } in
      (* A number of the C library's headers, with the value this system
         gives it. *)
      let number_constant number : Lir.operand =
        let integer =
          match
            scalar env
              (Named
                 {
                   path = Intrinsic.builtin_path (Intrinsic.libc_builtin (Libc.number_type number));
                   arguments = [];
                 })
          with
          | Integer integer -> integer
          | _ -> bug "a number of the C library that is not an integer"
        in
        Constant (Integer (integer, Z.of_int (Libc.value (Memory_layout.target env).system number)))
      in
      (* The text at an address that may be null: the bytes up to a zero
         byte, as a view, with [is_present] saying whether the address was
         there. A view's address is never null, so text that is not there
         is an empty view of static bytes. *)
      let text_at address ~is_present =
        emit builder (Assign (is_present, Binary (Not_equal, Copy (at address), Constant Null)));
        let elements = local builder (Raw (Pointer (Data byte))) in
        let count = usize_local "length" in
        emit builder (Assign (at elements, Use (Constant (Bytes ""))));
        emit builder (Assign (at count, Use (usize 0)));
        when_ builder (Copy is_present) (fun () ->
            emit builder (Assign (at elements, Use (Copy (at address))));
            call ~result:(at count) Terminated_length [ Copy (at address) ]);
        set
          (Storage.view (Storage.view_of_elements byte)
             ~elements:(Copy (at elements))
             ~length:(Copy (at count)))
      in
      (match (operation : Intrinsic.operation) with
      | Storage_at | Storage_at_mut | View_at | View_at_mut | Array_at_mut -> ()
      | Add -> checked_arithmetic Add Add_overflow
      | Subtract -> checked_arithmetic Subtract Subtract_overflow
      | Multiply -> checked_arithmetic Multiply Multiply_overflow
      | Divide -> checked_division Divide
      | Remainder -> checked_division Remainder
      | Negate -> (
          (* The least value of a signed type has no negation in the type. *)
          match integer_argument () with
          | Some ((Int8 | Int16 | Int32 | Int64 | ISize) as integer) when checks ->
              let bits = 8 * Memory_layout.integer_size (Memory_layout.target env) integer in
              let least = Z.neg (Z.shift_left Z.one (bits - 1)) in
              let of_least = local builder (Raw Bool) in
              emit builder
                (Assign (at of_least, Binary (Equal, value 0, Constant (Integer (integer, least)))));
              panic_when (Copy (at of_least)) "arithmetic overflow";
              unary Negate
          | _ -> unary Negate)
      | Wrapping_add -> binary Add
      | Wrapping_subtract -> binary Subtract
      | Wrapping_multiply -> binary Multiply
      | Add_overflows | Subtract_overflows | Multiply_overflows ->
          let ignored = local builder (Value (type_argument 0)) in
          call ?result:destination
            (match operation with
            | Add_overflows -> Add_overflow
            | Subtract_overflows -> Subtract_overflow
            | _ -> Multiply_overflow)
            [ value 0; value 1; Address { place = at ignored; writable = true } ]
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
          (* The bytes both views have, then the lengths. *)
          let left = place (argument 0) and right = place (argument 1) in
          let shorter = local builder (Raw Bool) in
          let count = usize_local "count" in
          emit builder (Assign (at shorter, Binary (Less, view_length left, view_length right)));
          emit builder (Assign (at count, Use (view_length right)));
          when_ builder
            (Copy (at shorter))
            (fun () -> emit builder (Assign (at count, Use (view_length left))));
          let order = local builder (Raw (Integer Int32)) in
          call ~result:(at order) Compare_bytes
            [
              Copy (Storage.view_elements left); Copy (Storage.view_elements right); Copy (at count);
            ];
          let same = local builder (Raw Bool) in
          emit builder
            (Assign (at same, Binary (Equal, Copy (at order), Constant (Integer (Int32, Z.zero)))));
          when_ builder
            (Copy (at same))
            (fun () ->
              let longer = local builder (Raw Bool) and shorter = local builder (Raw Bool) in
              emit builder
                (Assign (at longer, Binary (Greater, view_length left, view_length right)));
              emit builder (Assign (at shorter, Binary (Less, view_length left, view_length right)));
              let first = local builder (Raw (Integer Int32))
              and second = local builder (Raw (Integer Int32)) in
              emit builder (Assign (at first, Convert (Copy (at longer), Integer Int32)));
              emit builder (Assign (at second, Convert (Copy (at shorter), Integer Int32)));
              emit builder (Assign (at order, Binary (Subtract, Copy (at first), Copy (at second)))));
          set (Convert (Copy (at order), Integer Int8))
      | Bit_and -> binary Bit_and
      | Bit_or -> binary Bit_or
      | Bit_xor -> binary Bit_xor
      | Complement -> unary Complement
      | Shift_left | Shift_right ->
          (* The emitted C masks the amount to the type's width, so a shift
             by the width or more, or by a negative amount, would give a
             wrong value. The amount has a type of its own. *)
          (match (integer_argument (), scalar env (type_argument 1)) with
          | Some integer, Integer amount ->
              let bits = 8 * Memory_layout.integer_size (Memory_layout.target env) integer in
              let constant number : Lir.operand = Constant (Integer (amount, Z.of_int number)) in
              (match amount with
              | Int8 | Int16 | Int32 | Int64 | ISize ->
                  panic_if (Binary (Less, value 1, constant 0)) "shift amount out of range"
              | _ -> ());
              panic_if (Binary (Greater_equal, value 1, constant bits)) "shift amount out of range"
          | _ -> ());
          binary (if operation = Shift_left then Shift_left else Shift_right)
      | Convert | Fits -> (
          (* Whether a value of [Source] fits [Target]: a test of each bound of
         [Target] that [Source] can pass, each of which [Source] can hold. *)
          let target = Memory_layout.target env in
          let fits () : Lir.rvalue =
            match (scalar env (type_argument 0), scalar env (type_argument 1)) with
            | Integer source, Integer target_integer -> (
                let source_low, source_high = Memory_layout.integer_range target source in
                let low, high = Memory_layout.integer_range target target_integer in
                let constant value = Lir.Constant (Integer (source, value)) in
                let tests =
                  (if Z.lt source_low low then [ (Lir.Greater_equal, low) ] else [])
                  @ if Z.gt source_high high then [ (Lir.Less_equal, high) ] else []
                in
                let results =
                  List.map
                    (fun (op, bound) ->
                      let result = local builder (Raw Bool) in
                      emit builder (Assign (at result, Binary (op, value 0, constant bound)));
                      Lir.Copy (at result))
                    tests
                in
                match results with
                | [] -> Use (Constant (Bool true))
                | [ only ] -> Use only
                | [ first; second ] -> Binary (Bit_and, first, second)
                | _ -> bug "more than two bounds")
            | ((Float32 | Float64) as source), Integer target_integer ->
                (* A float fits an integer type where it is a number and the
                 whole number it is cut down to is in the type's range: it
                 is above the least value less one, and below the greatest
                 plus one. The second is a power of two, which every float
                 type holds exactly. Where the first is not held exactly,
                 no float lies between it and the least value. A float
                 that is not a number passes neither test. *)
                let low, high = Memory_layout.integer_range target target_integer in
                let held bound =
                  match source with
                  | Float32 ->
                      Int32.float_of_bits (Int32.bits_of_float (Z.to_float bound))
                      = Z.to_float bound
                      && Z.equal (Z.of_float (Z.to_float bound)) bound
                  | _ -> Z.equal (Z.of_float (Z.to_float bound)) bound
                in
                let constant bound : Lir.operand =
                  match source with
                  | Float32 -> Constant (Float32 (Int32.bits_of_float (Z.to_float bound)))
                  | _ -> Constant (Float64 (Int64.bits_of_float (Z.to_float bound)))
                in
                let above = local builder (Raw Bool) and below = local builder (Raw Bool) in
                let under = Z.pred low in
                emit builder
                  (Assign
                     ( at above,
                       if held under then Binary (Ieee_less, constant under, value 0)
                       else Binary (Ieee_less_equal, constant low, value 0) ));
                emit builder
                  (Assign (at below, Binary (Ieee_less, value 0, constant (Z.succ high))));
                Binary (Bit_and, Copy (at above), Copy (at below))
            | _ -> bug "fits between these types"
          in
          match (operation, scalar env (type_argument 0), scalar env (type_argument 1)) with
          | Fits, _, _ -> set (fits ())
          | _, (Float32 | Float64), Integer _ ->
              (* A float that is out of an integer type's range has no
                 conversion to it in C. A conversion between integer types
                 is defined for every value: it keeps the low bits, which
                 the standard library relies on, as where it hashes a
                 negative number. *)
              if checks then begin
                let in_range = local builder (Raw Bool) in
                emit builder (Assign (at in_range, fits ()));
                panic_if (Unary (Not, Copy (at in_range))) "conversion out of range"
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
          let same = local builder (Raw Bool) in
          emit builder (Assign (at same, Binary (Ieee_equal, value 0, value 0)));
          set (Unary (Not, Copy (at same)))
      | Storage_empty -> set (Storage.empty (Storage.of_elements (element ())))
      | Storage_with_capacity ->
          let ty = Storage.of_elements (element ()) in
          let result = local builder (Value ty) in
          emit builder (Assign (at result, Storage.empty ty));
          let any = local builder (Raw Bool) in
          emit builder (Assign (at any, Binary (Greater, value 0, usize 0)));
          when_ builder (Copy (at any)) (fun () -> set_capacity (at result) (value 0));
          set (Use (Move (at result)))
      | Storage_length -> set (Use (length (place (argument 0))))
      | Storage_capacity -> set (Use (Copy (Storage.capacity (place (argument 0)))))
      | Storage_set_capacity ->
          let storage = place (argument 0) in
          panic_if
            (Binary (Less, value 1, length storage))
            "a storage's capacity set to less than its length";
          set_capacity storage (value 1)
      | Storage_lengthen ->
          (* The new elements are the ones the C library wrote into the spare capacity. *)
          let storage = place (argument 0) in
          if checks then
            panic_if
              (Binary (Greater, value 1, room storage))
              "a storage lengthened to more than its capacity";
          add_to_length storage (value 1)
      | Storage_shorten ->
          (* Static storage stays static: it is told apart by its capacity,
             and nothing is written to its elements. *)
          let storage = place (argument 0) in
          panic_if
            (Binary (Greater, value 1, length storage))
            "a storage shortened to more than its length";
          emit builder (Assign (Storage.length storage, Use (value 1)))
      | Storage_push ->
          let storage = place (argument 0) in
          panic_if
            (Binary (Greater_equal, length storage, Copy (Storage.capacity storage)))
            "an element pushed to a storage that has no room";
          emit builder (Assign (element_at storage (length storage), Use (value 1)));
          add_to_length storage (usize 1)
      | Storage_pop ->
          let storage = place (argument 0) in
          panic_if
            (Binary (Equal, length storage, usize 0))
            "an element popped from an empty storage";
          emit builder (Assign (Storage.length storage, Binary (Subtract, length storage, usize 1)));
          set (Use (Move (element_at storage (length storage))))
      | Storage_insert ->
          let storage = place (argument 0) in
          let index = value 1 in
          panic_if (Binary (Greater, index, length storage)) "index out of bounds";
          panic_if
            (Binary (Greater_equal, length storage, Copy (Storage.capacity storage)))
            "an element inserted into a storage that has no room";
          let after = usize_local "after" in
          let bytes = usize_local "bytes" in
          emit builder (Assign (at after, Binary (Add, index, usize 1)));
          emit builder (Assign (at bytes, Binary (Subtract, length storage, index)));
          emit builder
            (Assign (at bytes, Binary (Multiply, Copy (at bytes), usize (element_layout ()).size)));
          call Move_bytes
            [
              Address { place = element_at storage (Copy (at after)); writable = true };
              Address { place = element_at storage index; writable = true };
              Copy (at bytes);
            ];
          emit builder (Assign (element_at storage index, Use (value 2)));
          add_to_length storage (usize 1)
      | Storage_remove ->
          check_index (value 1) (length (place (argument 0)));
          own (argument 0);
          let storage = place (argument 0) in
          let index = value 1 in
          set (Use (Move (element_at storage index)));
          let after = usize_local "after" in
          let bytes = usize_local "bytes" in
          emit builder (Assign (at after, Binary (Add, index, usize 1)));
          emit builder (Assign (at bytes, Binary (Subtract, length storage, Copy (at after))));
          emit builder
            (Assign (at bytes, Binary (Multiply, Copy (at bytes), usize (element_layout ()).size)));
          call Move_bytes
            [
              Address { place = element_at storage index; writable = true };
              Address { place = element_at storage (Copy (at after)); writable = true };
              Copy (at bytes);
            ];
          emit builder (Assign (Storage.length storage, Binary (Subtract, length storage, usize 1)))
      | Storage_swap ->
          check_index (value 1) (length (place (argument 0)));
          check_index (value 2) (length (place (argument 0)));
          own (argument 0);
          let storage = place (argument 0) in
          let held = local builder (Value (element ())) in
          emit builder (Assign (at held, Use (Move (element_at storage (value 1)))));
          emit builder
            (Assign (element_at storage (value 1), Use (Move (element_at storage (value 2)))));
          emit builder (Assign (element_at storage (value 2), Use (Move (at held))))
      | Storage_from_array ->
          (* The array's bytes are the elements, so the whole array is moved
             into the new buffer at once. *)
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
          let ty = Storage.of_elements (element ()) in
          let result = local builder (Value ty) in
          emit builder (Assign (at result, Storage.empty ty));
          if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
            set_capacity (at result) (Constant (Integer (USize, count)));
            let untyped = local builder (Raw (Pointer Opaque)) in
            emit builder (Assign (at untyped, Use (Copy (Storage.buffer (at result)))));
            let typed = local builder (Pointer { target = Value array_ty; writable = true }) in
            emit builder (Assign (at typed, Use (Copy (at untyped))));
            emit builder (Assign ({ root = Local typed; projections = [ Deref ] }, Use (value 0)))
          end;
          add_to_length (at result) (Constant (Integer (USize, count)));
          set (Use (Move (at result)))
      | Array_from_storage ->
          (* The storage's buffer holds the elements one after another, as
             the array does, so the whole array is read out of it at once.
             The storage is moved into a local that nothing drops: its
             elements are the array's now, and only its buffer is freed. *)
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
            at (local builder ~borrowed:true (Value (Storage.of_elements (element ()))))
          in
          emit builder (Assign (moved_storage, Use (Move (place (argument 0)))));
          if checks then begin
            let other = local builder (Raw Bool) in
            emit builder
              (Assign
                 ( at other,
                   Binary (Not_equal, length moved_storage, Constant (Integer (USize, count))) ));
            panic_when (Copy (at other)) "a storage made into an array of another length"
          end;
          if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
            let untyped = local builder (Raw (Pointer Opaque)) in
            emit builder (Assign (at untyped, Use (Copy (Storage.buffer moved_storage))));
            let typed = local builder (Pointer { target = Value array_ty; writable = true }) in
            emit builder (Assign (at typed, Use (Copy (at untyped))));
            set (Use (Move { root = Local typed; projections = [ Deref ] }))
          end;
          (* Static elements have no buffer to free. *)
          let owns = local builder (Raw Bool) in
          emit builder
            (Assign (at owns, Binary (Greater, Copy (Storage.capacity moved_storage), usize 0)));
          when_ builder
            (Copy (at owns))
            (fun () -> call Free [ Copy (Storage.buffer moved_storage) ])
      | Array_view ->
          (* An array's elements are one after another from its start. An
             array with no bytes has no address, and its view is of
             nothing. *)
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
          let elements : Lir.operand =
            if Memory_layout.has_zero_size env array_ty then Constant (Bytes "")
            else Address { place = read (argument 0) / Index (usize 0); writable = false }
          in
          set
            (Storage.view
               (Storage.view_of_elements (element ()))
               ~elements
               ~length:(Constant (Integer (USize, count))))
      | View_swap ->
          check_index (value 1) (view_length (place (argument 0)));
          check_index (value 2) (view_length (place (argument 0)));
          let element_at index = Storage.view_at (place (argument 0)) index in
          let held = local builder (Value (element ())) in
          emit builder (Assign (at held, Use (Move (element_at (value 1)))));
          emit builder (Assign (element_at (value 1), Use (Move (element_at (value 2)))));
          emit builder (Assign (element_at (value 2), Use (Move (at held))))
      | (Storage_take_view | View_take_view | Array_take_view) as operation ->
          (* The view is of the owner's own elements, so there is nothing to
             write. A checked build makes sure that it is. *)
          if checks then begin
            let owner = place (argument 0) and part = place (argument 1) in
            let from = value 2 in
            let first, owner_length =
              match operation with
              | Storage_take_view -> (element_at owner from, length owner)
              | View_take_view -> (Storage.view_at owner from, view_length owner)
              | _ ->
                  let count =
                    match value_arguments with
                    | [ count ] -> count
                    | _ -> bug "array_take_view without the array's length"
                  in
                  (owner / Index from, Lir.Constant (Integer (USize, count)))
            in
            let message = "a view taken back is not of these elements" in
            let stop = usize_local "stop" in
            emit builder (Assign (at stop, Binary (Add, from, view_length part)));
            let beyond = local builder (Raw Bool) in
            emit builder (Assign (at beyond, Binary (Greater, Copy (at stop), owner_length)));
            panic_when (Copy (at beyond)) message;
            if (element_layout ()).size > 0 then begin
              (* An empty view may be of nothing, and then has no address
                 to compare. *)
              let go_on = block builder and compare = block builder in
              let empty = local builder (Raw Bool) in
              emit builder (Assign (at empty, Binary (Equal, view_length part, usize 0)));
              branch builder (Copy (at empty)) ~yes:go_on ~no:compare;
              start builder compare;
              let expected =
                local builder (Pointer { target = Value (element ()); writable = false })
              in
              emit builder (Assign (at expected, Use (Address { place = first; writable = false })));
              let expected_address = usize_local "expected" and address = usize_local "address" in
              emit builder
                (Assign (at expected_address, Convert (Copy (at expected), Integer USize)));
              emit builder
                (Assign (at address, Convert (Copy (Storage.view_elements part), Integer USize)));
              let apart = local builder (Raw Bool) in
              emit builder
                (Assign (at apart, Binary (Not_equal, Copy (at address), Copy (at expected_address))));
              panic_when (Copy (at apart)) message;
              finish builder (Goto go_on);
              start builder go_on
            end
          end
      | (Storage_view | Storage_view_mut) as operation ->
          if operation = Storage_view_mut then own (argument 0);
          let storage = place (argument 0) in
          set
            (Storage.view
               (Storage.view_of_elements (element ()))
               ~elements:(Copy (Storage.buffer storage))
               ~length:(length storage))
      | View_length -> set (Use (view_length (place (argument 0))))
      | View_address ->
          set (Convert (Copy (Storage.view_elements (place (argument 0))), Integer USize))
      | View_slice ->
          let view = place (argument 0) in
          panic_if (Binary (Greater, value 1, value 2)) "slice out of bounds";
          panic_if (Binary (Greater, value 2, view_length view)) "slice out of bounds";
          let count = usize_local "count" in
          emit builder (Assign (at count, Binary (Subtract, value 2, value 1)));
          set
            (Storage.view
               (Storage.view_of_elements (element ()))
               ~elements:(Address { place = Storage.view_at view (value 1); writable = false })
               ~length:(Copy (at count)))
      | Storage_model | View_model | Array_model ->
          bug "a model, which exists only in specifications"
      | Crash ->
          (* The message is a [StringSlice], a record of one field: its view of
         bytes. *)
          let message = read (argument 0) in
          let bytes =
            match (Memory_layout.of_type env types.string_slice).form with
            | Struct [ only ] -> message / Field only.name
            | _ -> bug "a StringSlice that is not a record of one field"
          in
          finish builder
            (Fail
               {
                 failure = Panic;
                 message = Copy (Storage.view_elements bytes);
                 length = Copy (Storage.view_length bytes);
                 site;
                 caller = None;
               });
          start builder (block builder)
      | Handle_from ->
          set
            (Build
               {
                 ty = Named { path = Intrinsic.builtin_path Handle; arguments = [] };
                 variant = None;
                 fields = [ ("descriptor", value 0) ];
               })
      | Handle_descriptor -> set (Use (Copy (read (argument 0) / Field "descriptor")))
      | Shared_new ->
          let ty = type_argument 0 in
          let block = local builder (Raw (Pointer Opaque)) in
          call ~result:(at block) Shared_allocate
            [ Constant (Size_of ty); Constant (Alignment_of ty) ];
          if (Memory_layout.of_type env ty).size > 0 then begin
            (* The pointer is [borrowed] so that drop elaboration does not
               track the block's contents, which the [Shared] owns. *)
            let typed =
              local builder ~borrowed:true (Pointer { target = Value ty; writable = true })
            in
            emit builder (Assign (at typed, Use (Copy (at block))));
            emit builder (Assign ({ root = Local typed; projections = [ Deref ] }, Use (value 0)))
          end;
          set
            (Build
               {
                 ty = Named { path = Intrinsic.builtin_path Shared; arguments = [ Type ty ] };
                 variant = None;
                 fields = [ ("value", Copy (at block)) ];
               })
      | Shared_key -> set (Convert (Copy (read (argument 0) / Field "value"), Integer UInt64))
      | Shared_update -> bug "shared_update is lowered with the call of its function value"
      | Handle_release ->
          (* The handle is moved into a local that nothing drops, so its
             descriptor stays open. *)
          let released =
            local builder ~borrowed:true
              (Value (Named { path = Intrinsic.builtin_path Handle; arguments = [] }))
          in
          emit builder (Assign (at released, Use (value 0)));
          set (Use (Copy (at released / Field "descriptor")))
      | Run_test -> call Run_test [ value 0 ]
      | Coroutine_start ->
          call ?result:destination Coroutine_start [ Copy (read (argument 0)); value 1 ]
      | Coroutine_resume -> call ?result:destination Coroutine_resume [ value 0 ]
      | Coroutine_suspend -> call Coroutine_suspend []
      | Tasks_spawn ->
          call ?result:destination Tasks_spawn [ value 0; Copy (read (argument 1)); value 2 ]
      | Report_tests_to -> call Report_tests_to [ value 0 ]
      | Live_blocks -> call ?result:destination Live_blocks []
      | System_is_os os -> set (Use (Constant (Bool ((Memory_layout.target env).system.os = os))))
      | System_is_architecture architecture ->
          set
            (Use (Constant (Bool ((Memory_layout.target env).system.architecture = architecture))))
      | Environment_entry ->
          (* The entries are counted from the first each time, so the null
             address after the last is never passed. *)
          let environment = local builder (Raw (Pointer Opaque)) in
          call ~result:(at environment) Environment [];
          let position = usize_local "position" in
          emit builder (Assign (at position, Use (usize 0)));
          let entry = local builder (Raw (Nullable_pointer (Data byte))) in
          let test = block builder and next = block builder and after = block builder in
          finish builder (Goto test);
          start builder test;
          call ~result:(at entry) Program_argument [ Copy (at environment); Copy (at position) ];
          let last = local builder (Raw Bool) and reached = local builder (Raw Bool) in
          let stop = local builder (Raw Bool) in
          emit builder (Assign (at last, Binary (Equal, Copy (at entry), Constant Null)));
          emit builder (Assign (at reached, Binary (Equal, Copy (at position), value 0)));
          emit builder (Assign (at stop, Binary (Bit_or, Copy (at last), Copy (at reached))));
          branch builder (Copy (at stop)) ~yes:after ~no:next;
          start builder next;
          emit builder (Assign (at position, Binary (Add, Copy (at position), usize 1)));
          finish builder (Goto test);
          start builder after;
          text_at entry ~is_present:(place (argument 1))
      | Libc function_ when not (Libc.available (Memory_layout.target env).system function_) ->
          (* The standard library asks which system it is built for before
             it calls a function that only some have. *)
          let message =
            Printf.sprintf "this system's C library has no %s" (Libc.function_name function_)
          in
          finish builder
            (Fail
               {
                 failure = Panic;
                 message = Constant (Bytes message);
                 length = usize (String.length message);
                 site;
                 caller = None;
               });
          start builder (block builder)
      | Libc function_ -> (
          let ground scalar =
            Ground.Named
              { path = Intrinsic.builtin_path (Intrinsic.libc_builtin scalar); arguments = [] }
          in
          let { Libc.parameters; result; _ } = Libc.signature function_ in
          (* The values copied back after the call: a structure's numbers to the
             arguments they were written for. *)
          let after = ref [] in
          let next = ref 0 in
          let next_argument () =
            let index = !next in
            incr next;
            index
          in
          let call_arguments =
            List.map
              (fun (_, (passes : Libc.passes)) : Lir.operand ->
                match passes with
                | Value _ -> value (next_argument ())
                | Elements _ -> Copy (Storage.view_elements (place (argument (next_argument ()))))
                | Room _ ->
                    let storage = place (argument (next_argument ())) in
                    Address { place = element_at storage (length storage); writable = true }
                | Elements_to_change (scalar, _) ->
                    let storage = argument (next_argument ()) in
                    own ~element:(ground scalar) storage;
                    Copy (Storage.buffer (place storage))
                | Written (scalar, names) ->
                    let structure =
                      local builder
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
                        emit builder
                          (Assign (at structure / Index (usize index), Use (Copy written)));
                        after :=
                          (fun () ->
                            emit builder
                              (Assign (written, Use (Copy (at structure / Index (usize index))))))
                          :: !after)
                      names;
                    Address { place = at structure; writable = true }
                | Always number -> usize number
                | Fixed number -> number_constant number)
              parameters
          in
          (* A checked build checks the prover's preconditions for each
             call: a view has the elements that the function reads, and a
             storage has the room that it writes into, or the elements that
             it changes. A function that reads up to a zero is given
             elements that end with one. *)
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
                      (* A count can be one of a structure's numbers, as the
                         length that [getsockopt] is given and writes. *)
                      List.map
                        (fun name ->
                          let index = !position in
                          incr position;
                          (name, None, index))
                        names
                  | Always _ | Fixed _ -> [])
                parameters
            in
            let as_usize operand : Lir.operand =
              let count = usize_local "count" in
              emit builder (Assign (at count, Convert (operand, Integer USize)));
              Copy (at count)
            in
            let counted (extent : Libc.extent) : Lir.operand option =
              match extent with
              | Counted { by; each } -> (
                  match List.find_opt (fun (name, _, _) -> name = by) passed with
                  | Some (_, _, index) ->
                      let count = as_usize (value index) in
                      if each = 1 then Some count
                      else begin
                        let scaled = usize_local "count" in
                        emit builder (Assign (at scaled, Binary (Multiply, count, usize each)));
                        Some (Copy (at scaled))
                      end
                  | None -> bug "a C library row counts by %s, which it does not take" by)
              | Exactly elements -> Some (usize elements)
              | Number number -> Some (as_usize (number_constant number))
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
                          "a call of the C library with fewer elements than it changes")
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
                        let zero : Lir.operand =
                          match scalar env (ground element) with
                          | Integer integer -> Constant (Integer (integer, Z.zero))
                          | _ -> bug "a C library row reads up to a zero that is not an integer"
                        in
                        panic_if (Binary (Equal, view_length view, usize 0)) message;
                        let last = usize_local "last" in
                        emit builder
                          (Assign (at last, Binary (Subtract, view_length view, usize 1)));
                        panic_if
                          (Binary (Not_equal, Copy (Storage.view_at view (Copy (at last))), zero))
                          message)
                | Some (Value _ | Written _ | Always _ | Fixed _) | None -> ())
              passed
          end;
          let target = Lir.Foreign (Libc.declaration (Memory_layout.target env).system function_) in
          (* A call that can block is bracketed, so that the runtime knows
             the thread is blocked while it lasts. *)
          let bracket intrinsic =
            if Libc.blocks function_ then
              emit builder
                (Call { target = Intrinsic intrinsic; arguments = []; result = Discarded })
          in
          let call result =
            bracket Blocking_begin;
            emit builder (Call { target; arguments = call_arguments; result });
            bracket Blocking_end;
            List.iter (fun write -> write ()) (List.rev !after)
          in
          match result with
          | Returns _ ->
              call (match destination with Some place -> Returned place | None -> Discarded)
          | Never ->
              call Discarded;
              finish builder Unreachable;
              start builder (block builder)
          | Points_at scalar ->
              let address = local builder (Raw (Pointer (Data (ground scalar)))) in
              call (Returned (at address));
              set (Use (Copy (at address / Deref)))
          | Text ->
              let address = local builder (Raw (Nullable_pointer (Data byte))) in
              call (Returned (at address));
              text_at address ~is_present:(place (argument (next_argument ()))))
      | Libc_number number -> set (Use (number_constant number)));
      None
