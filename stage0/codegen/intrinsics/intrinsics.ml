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

let integer_range (integer : Memory_layout.integer) bytes =
  let bits = 8 * bytes in
  match integer with
  | Int8 | Int16 | Int32 | Int64 | ISize ->
      (Z.neg (Z.shift_left Z.one (bits - 1)), Z.pred (Z.shift_left Z.one (bits - 1)))
  | UInt8 | UInt16 | UInt32 | UInt64 | USize -> (Z.zero, Z.pred (Z.shift_left Z.one bits))

let lower ?(checks = false) ?(value_arguments = []) env b types operation ~type_arguments arguments
    ~destination ~site =
  let set rvalue = Option.iter (fun d -> emit b (Assign (d, rvalue))) destination in
  let argument i = List.nth arguments i in
  let value i = operand (argument i) in
  let type_argument i =
    match List.nth_opt type_arguments i with Some ty -> ty | None -> bug "a missing type argument"
  in
  let binary op = set (Binary (op, value 0, value 1)) in
  let unary op = set (Unary (op, value 0)) in
  let call ?result intrinsic arguments =
    let result = match result with Some place -> Lir.Returned place | None -> Discarded in
    emit b (Call { target = Intrinsic intrinsic; arguments; result })
  in
  let into intrinsic = call ?result:destination intrinsic (List.map operand arguments) in
  let usize_local name = local b ~name (Value types.usize) in
  let element () = type_argument 0 in
  let element_layout ?element:given () =
    Memory_layout.of_type env (match given with Some element -> element | None -> element ())
  in
  let length storage = Lir.Copy (Storage.length storage) in
  let view_length view = Lir.Copy (Storage.view_length view) in
  let element_at = Storage.at in
  (* Ends the run with a panic where [failed] holds. *)
  let panic_when failed message =
    let fail = block b and go_on = block b in
    finish b (Switch { value = failed; cases = [ (Z.one, fail) ]; default = Some go_on });
    start b fail;
    finish b
      (Fail
         {
           failure = Panic;
           message = Constant (Bytes message);
           length = usize (String.length message);
           site;
         });
    start b go_on
  in
  (* Gives the storage a buffer of its own with room for exactly [capacity]
     elements, which is at least as many as it has. A buffer it owns is
     made larger; elements it does not own, as static ones are, are copied
     to a new one and never freed. *)
  let set_capacity ?element storage capacity =
    let layout = element_layout ?element () in
    let bytes = usize_local "bytes" and too_many = local b (Raw Bool) in
    call ~result:(at too_many) Multiply_overflow
      [ capacity; usize layout.size; Address { place = at bytes; writable = true } ];
    panic_when (Copy (at too_many)) "out of memory";
    let buffer = local b (Raw (Pointer Opaque)) in
    let owns = local b (Raw Bool) and borrows = local b (Raw Bool) in
    emit b (Assign (at owns, Binary (Not_equal, Copy (Storage.capacity storage), usize 0)));
    emit b (Assign (at borrows, Unary (Not, Copy (at owns))));
    when_ b
      (Copy (at owns))
      (fun () ->
        let held = usize_local "held" in
        emit b
          (Assign (at held, Binary (Multiply, Copy (Storage.capacity storage), usize layout.size)));
        call ~result:(at buffer) Reallocate
          [ Copy (Storage.buffer storage); Copy (at held); Copy (at bytes); usize layout.alignment ]);
    when_ b
      (Copy (at borrows))
      (fun () ->
        call ~result:(at buffer) Allocate [ Copy (at bytes); usize layout.alignment ];
        let used = usize_local "used" in
        emit b (Assign (at used, Binary (Multiply, length storage, usize layout.size)));
        call Copy_bytes [ Copy (at buffer); Copy (Storage.buffer storage); Copy (at used) ]);
    emit b (Assign (Storage.buffer storage, Use (Copy (at buffer))));
    emit b (Assign (Storage.capacity storage, Use capacity))
  in
  (* Static storage gets a buffer of its own before it is written. *)
  let own ?element storage =
    let storage = place storage in
    let borrowed = local b (Raw Bool) in
    emit b (Assign (at borrowed, Binary (Greater, length storage, Copy (Storage.capacity storage))));
    when_ b (Copy (at borrowed)) (fun () -> set_capacity ?element storage (length storage))
  in
  let add_to_length storage amount =
    emit b (Assign (Storage.length storage, Binary (Add, length storage, amount)))
  in
  let lent place = Some place in
  match (operation : Intrinsic.operation) with
  | Storage_at -> lent (element_at (place (argument 0)) (value 1))
  | Storage_at_mut ->
      own (argument 0);
      lent (element_at (place (argument 0)) (value 1))
  | View_at | View_at_mut -> lent (Storage.view_at (place (argument 0)) (value 1))
  | Array_at_mut -> lent (place (argument 0) / Index (value 1))
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
            let result = local b (Value (type_argument 0)) in
            let over = local b (Raw Bool) in
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
            let zero = local b (Raw Bool) in
            emit b (Assign (at zero, Binary (Equal, value 1, Constant (Integer (integer, Z.zero)))));
            panic_when (Copy (at zero)) "division by zero";
            (match integer with
            | Int8 | Int16 | Int32 | Int64 | ISize ->
                let bits = 8 * Memory_layout.integer_size (Memory_layout.target env) integer in
                let least = Z.neg (Z.shift_left Z.one (bits - 1)) in
                let by_minus_one = local b (Raw Bool) and of_least = local b (Raw Bool) in
                let both = local b (Raw Bool) in
                emit b
                  (Assign
                     ( at by_minus_one,
                       Binary (Equal, value 1, Constant (Integer (integer, Z.minus_one))) ));
                emit b
                  (Assign (at of_least, Binary (Equal, value 0, Constant (Integer (integer, least)))));
                emit b
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
         byte, as a view, with [found] saying whether the address was
         there. A view's address is never null, so text that is not there
         is an empty view of static bytes. *)
      let text_at address ~found =
        emit b (Assign (found, Binary (Not_equal, Copy (at address), Constant Null)));
        let elements = local b (Raw (Pointer (Data byte))) in
        let count = usize_local "length" in
        emit b (Assign (at elements, Use (Constant (Bytes ""))));
        emit b (Assign (at count, Use (usize 0)));
        when_ b (Copy found) (fun () ->
            emit b (Assign (at elements, Use (Copy (at address))));
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
              let of_least = local b (Raw Bool) in
              emit b
                (Assign (at of_least, Binary (Equal, value 0, Constant (Integer (integer, least)))));
              panic_when (Copy (at of_least)) "arithmetic overflow";
              unary Negate
          | _ -> unary Negate)
      | Wrapping_add -> binary Add
      | Wrapping_subtract -> binary Subtract
      | Wrapping_multiply -> binary Multiply
      | Add_overflows | Subtract_overflows | Multiply_overflows ->
          let ignored = local b (Value (type_argument 0)) in
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
          let shorter = local b (Raw Bool) in
          let count = usize_local "count" in
          emit b (Assign (at shorter, Binary (Less, view_length left, view_length right)));
          emit b (Assign (at count, Use (view_length right)));
          when_ b (Copy (at shorter)) (fun () -> emit b (Assign (at count, Use (view_length left))));
          let order = local b (Raw (Integer Int32)) in
          call ~result:(at order) Compare_bytes
            [
              Copy (Storage.view_elements left); Copy (Storage.view_elements right); Copy (at count);
            ];
          let same = local b (Raw Bool) in
          emit b
            (Assign (at same, Binary (Equal, Copy (at order), Constant (Integer (Int32, Z.zero)))));
          when_ b
            (Copy (at same))
            (fun () ->
              let longer = local b (Raw Bool) and shorter = local b (Raw Bool) in
              emit b (Assign (at longer, Binary (Greater, view_length left, view_length right)));
              emit b (Assign (at shorter, Binary (Less, view_length left, view_length right)));
              let first = local b (Raw (Integer Int32))
              and second = local b (Raw (Integer Int32)) in
              emit b (Assign (at first, Convert (Copy (at longer), Integer Int32)));
              emit b (Assign (at second, Convert (Copy (at shorter), Integer Int32)));
              emit b (Assign (at order, Binary (Subtract, Copy (at first), Copy (at second)))));
          set (Convert (Copy (at order), Integer Int8))
      | Bit_and -> binary Bit_and
      | Bit_or -> binary Bit_or
      | Bit_xor -> binary Bit_xor
      | Complement -> unary Complement
      | Shift_left -> binary Shift_left
      | Shift_right -> binary Shift_right
      | Convert -> set (Convert (value 0, scalar env (type_argument 1)))
      | Fits -> (
          (* Whether a value of [Source] fits [Target]: a test of each bound of
         [Target] that [Source] can pass, each of which [Source] can hold. *)
          let target = Memory_layout.target env in
          match (scalar env (type_argument 0), scalar env (type_argument 1)) with
          | Integer source, Integer target_integer ->
              let source_low, source_high =
                integer_range source (Memory_layout.integer_size target source)
              in
              let low, high =
                integer_range target_integer (Memory_layout.integer_size target target_integer)
              in
              let constant value = Lir.Constant (Integer (source, value)) in
              let tests =
                (if Z.lt source_low low then [ (Lir.Greater_equal, low) ] else [])
                @ if Z.gt source_high high then [ (Lir.Less_equal, high) ] else []
              in
              let results =
                List.map
                  (fun (op, bound) ->
                    let result = local b (Raw Bool) in
                    emit b (Assign (at result, Binary (op, value 0, constant bound)));
                    Lir.Copy (at result))
                  tests
              in
              set
                (match results with
                | [] -> Use (Constant (Bool true))
                | [ only ] -> Use only
                | [ first; second ] -> Binary (Bit_and, first, second)
                | _ -> bug "more than two bounds")
          | _ -> bug "fits between types that are not integers")
      | Square_root -> into Square_root
      | Fused_multiply_add -> into Fused_multiply_add
      | Floor -> into Floor
      | Ceiling -> into Ceiling
      | Truncate -> into Truncate
      | Round_to_even -> into Round_even
      | To_bits -> into Float_bits
      | From_bits -> into Float_from_bits
      | Is_nan ->
          let same = local b (Raw Bool) in
          emit b (Assign (at same, Binary (Ieee_equal, value 0, value 0)));
          set (Unary (Not, Copy (at same)))
      | Storage_empty -> set (Storage.empty (Storage.of_elements (element ())))
      | Storage_with_capacity ->
          let ty = Storage.of_elements (element ()) in
          let result = local b (Value ty) in
          emit b (Assign (at result, Storage.empty ty));
          let any = local b (Raw Bool) in
          emit b (Assign (at any, Binary (Greater, value 0, usize 0)));
          when_ b (Copy (at any)) (fun () -> set_capacity (at result) (value 0));
          set (Use (Move (at result)))
      | Storage_length -> set (Use (length (place (argument 0))))
      | Storage_capacity -> set (Use (Copy (Storage.capacity (place (argument 0)))))
      | Storage_set_capacity -> set_capacity (place (argument 0)) (value 1)
      | Storage_lengthen -> add_to_length (place (argument 0)) (value 1)
      | Storage_push ->
          let storage = place (argument 0) in
          emit b (Assign (element_at storage (length storage), Use (value 1)));
          add_to_length storage (usize 1)
      | Storage_pop ->
          let storage = place (argument 0) in
          emit b (Assign (Storage.length storage, Binary (Subtract, length storage, usize 1)));
          set (Use (Move (element_at storage (length storage))))
      | Storage_insert ->
          let storage = place (argument 0) in
          let index = value 1 in
          let after = usize_local "after" in
          let bytes = usize_local "bytes" in
          emit b (Assign (at after, Binary (Add, index, usize 1)));
          emit b (Assign (at bytes, Binary (Subtract, length storage, index)));
          emit b
            (Assign (at bytes, Binary (Multiply, Copy (at bytes), usize (element_layout ()).size)));
          call Move_bytes
            [
              Address { place = element_at storage (Copy (at after)); writable = true };
              Address { place = element_at storage index; writable = true };
              Copy (at bytes);
            ];
          emit b (Assign (element_at storage index, Use (value 2)));
          add_to_length storage (usize 1)
      | Storage_remove ->
          own (argument 0);
          let storage = place (argument 0) in
          let index = value 1 in
          set (Use (Move (element_at storage index)));
          let after = usize_local "after" in
          let bytes = usize_local "bytes" in
          emit b (Assign (at after, Binary (Add, index, usize 1)));
          emit b (Assign (at bytes, Binary (Subtract, length storage, Copy (at after))));
          emit b
            (Assign (at bytes, Binary (Multiply, Copy (at bytes), usize (element_layout ()).size)));
          call Move_bytes
            [
              Address { place = element_at storage index; writable = true };
              Address { place = element_at storage (Copy (at after)); writable = true };
              Copy (at bytes);
            ];
          emit b (Assign (Storage.length storage, Binary (Subtract, length storage, usize 1)))
      | Storage_swap ->
          own (argument 0);
          let storage = place (argument 0) in
          let held = local b (Value (element ())) in
          emit b (Assign (at held, Use (Move (element_at storage (value 1)))));
          emit b (Assign (element_at storage (value 1), Use (Move (element_at storage (value 2)))));
          emit b (Assign (element_at storage (value 2), Use (Move (at held))))
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
          let result = local b (Value ty) in
          emit b (Assign (at result, Storage.empty ty));
          if Z.sign count > 0 && (Memory_layout.of_type env array_ty).size > 0 then begin
            set_capacity (at result) (Constant (Integer (USize, count)));
            let untyped = local b (Raw (Pointer Opaque)) in
            emit b (Assign (at untyped, Use (Copy (Storage.buffer (at result)))));
            let typed = local b (Pointer { target = Value array_ty; writable = true }) in
            emit b (Assign (at typed, Use (Copy (at untyped))));
            emit b (Assign ({ root = Local typed; projections = [ Deref ] }, Use (value 0)))
          end;
          add_to_length (at result) (Constant (Integer (USize, count)));
          set (Use (Move (at result)))
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
            if (Memory_layout.of_type env array_ty).size = 0 then Constant (Bytes "")
            else Address { place = read (argument 0) / Index (usize 0); writable = false }
          in
          set
            (Storage.view
               (Storage.view_of_elements (element ()))
               ~elements
               ~length:(Constant (Integer (USize, count))))
      | View_swap ->
          let element_at index = Storage.view_at (place (argument 0)) index in
          let held = local b (Value (element ())) in
          emit b (Assign (at held, Use (Move (element_at (value 1)))));
          emit b (Assign (element_at (value 1), Use (Move (element_at (value 2)))));
          emit b (Assign (element_at (value 2), Use (Move (at held))))
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
            emit b (Assign (at stop, Binary (Add, from, view_length part)));
            let beyond = local b (Raw Bool) in
            emit b (Assign (at beyond, Binary (Greater, Copy (at stop), owner_length)));
            panic_when (Copy (at beyond)) message;
            if (element_layout ()).size > 0 then begin
              (* An empty view may be of nothing, and then has no address
                 to compare. *)
              let go_on = block b and compare = block b in
              let empty = local b (Raw Bool) in
              emit b (Assign (at empty, Binary (Equal, view_length part, usize 0)));
              finish b
                (Switch
                   { value = Copy (at empty); cases = [ (Z.one, go_on) ]; default = Some compare });
              start b compare;
              let expected = local b (Pointer { target = Value (element ()); writable = false }) in
              emit b (Assign (at expected, Use (Address { place = first; writable = false })));
              let expected_address = usize_local "expected" and address = usize_local "address" in
              emit b (Assign (at expected_address, Convert (Copy (at expected), Integer USize)));
              emit b
                (Assign (at address, Convert (Copy (Storage.view_elements part), Integer USize)));
              let apart = local b (Raw Bool) in
              emit b
                (Assign (at apart, Binary (Not_equal, Copy (at address), Copy (at expected_address))));
              panic_when (Copy (at apart)) message;
              finish b (Goto go_on);
              start b go_on
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
          let count = usize_local "count" in
          emit b (Assign (at count, Binary (Subtract, value 2, value 1)));
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
          finish b
            (Fail
               {
                 failure = Panic;
                 message = Copy (Storage.view_elements bytes);
                 length = Copy (Storage.view_length bytes);
                 site;
               });
          start b (block b)
      | Handle_from ->
          set
            (Build
               {
                 ty = Named { path = Intrinsic.builtin_path Handle; arguments = [] };
                 variant = None;
                 fields = [ ("descriptor", value 0) ];
               })
      | Handle_descriptor -> set (Use (Copy (read (argument 0) / Field "descriptor")))
      | Handle_release ->
          (* The handle is moved into a local that nothing drops, so its
             descriptor stays open. *)
          let released =
            local b ~borrowed:true
              (Value (Named { path = Intrinsic.builtin_path Handle; arguments = [] }))
          in
          emit b (Assign (at released, Use (value 0)));
          set (Use (Copy (at released / Field "descriptor")))
      | Run_test -> call Run_test [ value 0 ]
      | Report_tests_to -> call Report_tests_to [ value 0 ]
      | Live_blocks -> call ?result:destination Live_blocks []
      | System_is_os os -> set (Use (Constant (Bool ((Memory_layout.target env).system.os = os))))
      | System_is_architecture architecture ->
          set
            (Use (Constant (Bool ((Memory_layout.target env).system.architecture = architecture))))
      | Environment_entry ->
          (* The entries are counted from the first each time, so the null
             address after the last is never passed. *)
          let environment = local b (Raw (Pointer Opaque)) in
          call ~result:(at environment) Environment [];
          let position = usize_local "position" in
          emit b (Assign (at position, Use (usize 0)));
          let entry = local b (Raw (Nullable_pointer (Data byte))) in
          let test = block b and next = block b and after = block b in
          finish b (Goto test);
          start b test;
          call ~result:(at entry) Program_argument [ Copy (at environment); Copy (at position) ];
          let last = local b (Raw Bool) and reached = local b (Raw Bool) in
          let stop = local b (Raw Bool) in
          emit b (Assign (at last, Binary (Equal, Copy (at entry), Constant Null)));
          emit b (Assign (at reached, Binary (Equal, Copy (at position), value 0)));
          emit b (Assign (at stop, Binary (Bit_or, Copy (at last), Copy (at reached))));
          finish b
            (Switch { value = Copy (at stop); cases = [ (Z.one, after) ]; default = Some next });
          start b next;
          emit b (Assign (at position, Binary (Add, Copy (at position), usize 1)));
          finish b (Goto test);
          start b after;
          text_at entry ~found:(place (argument 1))
      | Libc function_ when not (Libc.available (Memory_layout.target env).system function_) ->
          (* The standard library asks which system it is built for before
             it calls a function that only some have. *)
          let message =
            Printf.sprintf "this system's C library has no %s" (Libc.function_name function_)
          in
          finish b
            (Fail
               {
                 failure = Panic;
                 message = Constant (Bytes message);
                 length = usize (String.length message);
                 site;
               });
          start b (block b)
      | Libc function_ -> (
          let ground scalar =
            Ground.Named
              { path = Intrinsic.builtin_path (Intrinsic.libc_builtin scalar); arguments = [] }
          in
          let { Libc.parameters; result; _ } = Libc.signature function_ in
          (* What goes on after the call: a structure's numbers to the
             arguments they were written for. *)
          let after = ref [] in
          let next = ref 0 in
          let taken () =
            let index = !next in
            incr next;
            index
          in
          let given =
            List.map
              (fun (_, (passes : Libc.passes)) : Lir.operand ->
                match passes with
                | Value _ -> value (taken ())
                | Elements _ -> Copy (Storage.view_elements (place (argument (taken ()))))
                | Room _ ->
                    let storage = place (argument (taken ())) in
                    Address { place = element_at storage (length storage); writable = true }
                | Elements_to_change (scalar, _) ->
                    let storage = argument (taken ()) in
                    own ~element:(ground scalar) storage;
                    Copy (Storage.buffer (place storage))
                | Written (scalar, names) ->
                    let structure =
                      local b
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
                        let written = place (argument (taken ())) in
                        after :=
                          (fun () ->
                            emit b
                              (Assign (written, Use (Copy (at structure / Index (usize index))))))
                          :: !after)
                      names;
                    Address { place = at structure; writable = true }
                | Always number -> usize number
                | Fixed number -> number_constant number)
              parameters
          in
          let target = Lir.Foreign (Libc.declaration (Memory_layout.target env).system function_) in
          let call result =
            emit b (Call { target; arguments = given; result });
            List.iter (fun write -> write ()) (List.rev !after)
          in
          match result with
          | Returns _ ->
              call (match destination with Some place -> Returned place | None -> Discarded)
          | Never ->
              call Discarded;
              finish b Unreachable;
              start b (block b)
          | Points_at scalar ->
              let address = local b (Raw (Pointer (Data (ground scalar)))) in
              call (Returned (at address));
              set (Use (Copy (at address / Deref)))
          | Text ->
              let address = local b (Raw (Nullable_pointer (Data byte))) in
              call (Returned (at address));
              text_at address ~found:(place (argument (taken ()))))
      | Libc_number number -> set (Use (number_constant number)));
      None
