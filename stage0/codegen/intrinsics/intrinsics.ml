open Lir_builder

let bug format = Compiler_bug.bug ~stage:"Intrinsics" format

type argument = Place of Lir.place | Value of Lir.operand
type types = { usize : Ground.ty; isize : Ground.ty; string_slice : Ground.ty }

let operand = function Place place -> Lir.Copy place | Value operand -> operand
let place = function Place place -> place | Value _ -> bug "an operation on storage given a value"

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

let lower ?(checks = false) env b types operation ~type_arguments arguments ~destination ~site =
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
  (* The storage's element: the type argument, or bytes for the system's
     operations, which take none. *)
  let element () =
    match operation with
    | Intrinsic.Read_bytes | Random_fill | Write_float | Environment_variable | Handle_read ->
        Ground.Named { path = Intrinsic.builtin_path UInt8; arguments = [] }
    | _ -> type_argument 0
  in
  let element_layout () = Memory_layout.of_type env (element ()) in
  let field storage name = storage / Lir.Field name in
  let length storage = Lir.Copy (field storage "length") in
  let element_at storage index = field storage "buffer" / Index index in
  (* Gives the storage room for at least [minimum] elements. *)
  let grow storage minimum =
    let layout = element_layout () in
    call Grow
      [
        Address { place = field storage "buffer"; writable = true };
        length storage;
        Address { place = field storage "capacity"; writable = true };
        usize layout.size;
        usize layout.alignment;
        minimum;
      ]
  in
  (* Grows the storage when [condition], a comparison of the length against
     the capacity, holds. *)
  let grow_when op storage minimum =
    let needed = local b (Raw Bool) in
    emit b (Assign (at needed, Binary (op, minimum, Copy (field storage "capacity"))));
    when_ b (Copy (at needed)) (fun () -> grow storage minimum)
  in
  (* Static storage gets a buffer of its own before it is written. *)
  let own storage = grow_when Greater (place storage) (length (place storage)) in
  let add_to_length storage amount =
    emit b (Assign (field storage "length", Binary (Add, length storage, amount)))
  in
  let lent place = Some place in
  match (operation : Intrinsic.operation) with
  | Storage_at -> lent (element_at (place (argument 0)) (value 1))
  | Storage_at_mut ->
      own (argument 0);
      lent (element_at (place (argument 0)) (value 1))
  | View_at -> lent (place (argument 0) / Field "elements" / Index (value 1))
  | _ ->
      let integer_argument () =
        match (Memory_layout.of_type env (type_argument 0)).form with
        | Scalar (Integer integer) -> Some integer
        | _ -> None
      in
      (* In a checked build, ends the run with a panic where [failed] holds. *)
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
      (match (operation : Intrinsic.operation) with
      | Storage_at | Storage_at_mut | View_at -> ()
      | Add -> checked_arithmetic Add Add_overflow
      | Subtract -> checked_arithmetic Subtract Subtract_overflow
      | Multiply -> checked_arithmetic Multiply Multiply_overflow
      | Divide -> checked_division Divide
      | Remainder -> checked_division Remainder
      | Negate -> unary Negate
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
          emit b (Assign (at shorter, Binary (Less, length left, length right)));
          emit b (Assign (at count, Use (length right)));
          when_ b (Copy (at shorter)) (fun () -> emit b (Assign (at count, Use (length left))));
          let order = local b (Raw (Integer Int32)) in
          call ~result:(at order) Compare_bytes
            [ Copy (left / Field "elements"); Copy (right / Field "elements"); Copy (at count) ];
          let same = local b (Raw Bool) in
          emit b
            (Assign (at same, Binary (Equal, Copy (at order), Constant (Integer (Int32, Z.zero)))));
          when_ b
            (Copy (at same))
            (fun () ->
              let longer = local b (Raw Bool) and shorter = local b (Raw Bool) in
              emit b (Assign (at longer, Binary (Greater, length left, length right)));
              emit b (Assign (at shorter, Binary (Less, length left, length right)));
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
      | Storage_empty ->
          (* An empty storage's buffer points at nothing, but is never null,
         which is the niche [Option] of a storage uses. *)
          set
            (Build
               {
                 ty =
                   Named
                     { path = Intrinsic.builtin_path Storage; arguments = [ Type (element ()) ] };
                 variant = None;
                 fields =
                   [ ("buffer", Constant (Bytes "")); ("length", usize 0); ("capacity", usize 0) ];
               })
      | Storage_with_capacity ->
          let ty =
            Ground.Named
              { path = Intrinsic.builtin_path Storage; arguments = [ Type (element ()) ] }
          in
          let result = local b (Value ty) in
          emit b
            (Assign
               ( at result,
                 Build
                   {
                     ty;
                     variant = None;
                     fields =
                       [
                         ("buffer", Constant (Bytes "")); ("length", usize 0); ("capacity", usize 0);
                       ];
                   } ));
          grow_when Greater (at result) (value 0);
          set (Use (Move (at result)))
      | Storage_length -> set (Use (length (place (argument 0))))
      | Storage_capacity -> set (Use (Copy (field (place (argument 0)) "capacity")))
      | Storage_reserve ->
          let storage = place (argument 0) in
          let wanted = usize_local "wanted" in
          emit b (Assign (at wanted, Binary (Add, length storage, value 1)));
          grow_when Greater storage (Copy (at wanted))
      | Storage_push ->
          let storage = place (argument 0) in
          let wanted = usize_local "wanted" in
          emit b (Assign (at wanted, Binary (Add, length storage, usize 1)));
          grow_when Greater storage (Copy (at wanted));
          emit b (Assign (element_at storage (length storage), Use (value 1)));
          add_to_length storage (usize 1)
      | Storage_pop ->
          let storage = place (argument 0) in
          emit b (Assign (field storage "length", Binary (Subtract, length storage, usize 1)));
          set (Use (Move (element_at storage (length storage))))
      | Storage_insert ->
          let storage = place (argument 0) in
          let index = value 1 in
          let wanted = usize_local "wanted" in
          emit b (Assign (at wanted, Binary (Add, length storage, usize 1)));
          grow_when Greater storage (Copy (at wanted));
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
          emit b (Assign (field storage "length", Binary (Subtract, length storage, usize 1)))
      | Storage_swap ->
          own (argument 0);
          let storage = place (argument 0) in
          let held = local b (Value (element ())) in
          emit b (Assign (at held, Use (Move (element_at storage (value 1)))));
          emit b (Assign (element_at storage (value 1), Use (Move (element_at storage (value 2)))));
          emit b (Assign (element_at storage (value 2), Use (Move (at held))))
      | Storage_view ->
          let storage = place (argument 0) in
          set
            (Build
               {
                 ty =
                   Named { path = Intrinsic.builtin_path View; arguments = [ Type (element ()) ] };
                 variant = None;
                 fields =
                   [ ("elements", Copy (field storage "buffer")); ("length", length storage) ];
               })
      | View_length -> set (Use (length (place (argument 0))))
      | View_slice ->
          let view = place (argument 0) in
          let count = usize_local "count" in
          emit b (Assign (at count, Binary (Subtract, value 2, value 1)));
          set
            (Build
               {
                 ty =
                   Named { path = Intrinsic.builtin_path View; arguments = [ Type (element ()) ] };
                 variant = None;
                 fields =
                   [
                     ( "elements",
                       Address
                         { place = view / Field "elements" / Index (value 1); writable = false } );
                     ("length", Copy (at count));
                   ];
               })
      | Crash ->
          (* The message is a [StringSlice], a record of one field: its view of
         bytes. *)
          let message = place (argument 0) in
          let bytes =
            match (Memory_layout.of_type env types.string_slice).form with
            | Struct [ only ] -> message / Field only.name
            | _ -> bug "a StringSlice that is not a record of one field"
          in
          finish b
            (Fail
               {
                 failure = Panic;
                 message = Copy (bytes / Field "elements");
                 length = Copy (bytes / Field "length");
                 site;
               });
          start b (block b)
      | Write_bytes ->
          let view = place (argument 1) in
          call ?result:destination System_write
            [ value 0; Copy (view / Field "elements"); Copy (view / Field "length") ]
      | Read_bytes ->
          let storage = place (argument 1) in
          let count = value 2 in
          let wanted = usize_local "wanted" in
          emit b (Assign (at wanted, Binary (Add, length storage, count)));
          grow_when Greater storage (Copy (at wanted));
          let got = local b ~name:"got" (Value types.isize) in
          call ~result:(at got) System_read
            [
              value 0;
              Address { place = element_at storage (length storage); writable = true };
              count;
            ];
          let read_some = local b (Raw Bool) in
          emit b
            (Assign
               (at read_some, Binary (Greater, Copy (at got), Constant (Integer (ISize, Z.zero)))));
          when_ b
            (Copy (at read_some))
            (fun () ->
              let count = usize_local "count" in
              emit b (Assign (at count, Convert (Copy (at got), Integer USize)));
              add_to_length storage (Copy (at count)));
          set (Use (Copy (at got)))
      | Write_float ->
          let storage = place (argument 0) in
          let wanted = usize_local "wanted" in
          emit b (Assign (at wanted, Binary (Add, length storage, usize Lir.float_text_limit)));
          grow_when Greater storage (Copy (at wanted));
          let count = usize_local "count" in
          call ~result:(at count) Float_text
            [ value 1; Address { place = element_at storage (length storage); writable = true } ];
          add_to_length storage (Copy (at count))
      | Open_file ->
          let path = place (argument 0) in
          let descriptor = local b ~name:"descriptor" (Raw (Integer Int32)) in
          call ~result:(at descriptor) System_open
            [
              Copy (path / Field "elements");
              Copy (path / Field "length");
              value 1;
              Address { place = place (argument 2); writable = true };
            ];
          set
            (Build
               {
                 ty = Named { path = Intrinsic.builtin_path Handle; arguments = [] };
                 variant = None;
                 fields = [ ("descriptor", Copy (at descriptor)) ];
               })
      | Handle_write ->
          let view = place (argument 1) in
          call ?result:destination System_write
            [
              Copy (place (argument 0) / Field "descriptor");
              Copy (view / Field "elements");
              Copy (view / Field "length");
            ]
      | Handle_read ->
          let storage = place (argument 1) in
          let count = value 2 in
          let wanted = usize_local "wanted" in
          emit b (Assign (at wanted, Binary (Add, length storage, count)));
          grow_when Greater storage (Copy (at wanted));
          let got = local b ~name:"got" (Value types.isize) in
          call ~result:(at got) System_read
            [
              Copy (place (argument 0) / Field "descriptor");
              Address { place = element_at storage (length storage); writable = true };
              count;
            ];
          let read_some = local b (Raw Bool) in
          emit b
            (Assign
               (at read_some, Binary (Greater, Copy (at got), Constant (Integer (ISize, Z.zero)))));
          when_ b
            (Copy (at read_some))
            (fun () ->
              let read = usize_local "read" in
              emit b (Assign (at read, Convert (Copy (at got), Integer USize)));
              add_to_length storage (Copy (at read)));
          set (Use (Copy (at got)))
      | Run_process ->
          let program = place (argument 0) and packed = place (argument 1) in
          call ?result:destination System_run
            [
              Copy (program / Field "elements");
              Copy (program / Field "length");
              Copy (packed / Field "elements");
              Copy (packed / Field "length");
              Address { place = place (argument 2); writable = true };
            ]
      | Environment_variable ->
          let name = place (argument 0) in
          let storage = place (argument 1) in
          let found = local b ~name:"found" (Raw (Nullable_pointer Opaque)) in
          let count = usize_local "count" in
          call ~result:(at found) System_environment
            [
              Copy (name / Field "elements");
              Copy (name / Field "length");
              Address { place = at count; writable = true };
            ];
          let present = local b ~name:"present" (Raw Bool) in
          emit b (Assign (at present, Binary (Not_equal, Copy (at found), Constant Null)));
          when_ b
            (Copy (at present))
            (fun () ->
              let wanted = usize_local "wanted" in
              emit b (Assign (at wanted, Binary (Add, length storage, Copy (at count))));
              grow_when Greater storage (Copy (at wanted));
              call Copy_bytes
                [
                  Address { place = element_at storage (length storage); writable = true };
                  Copy (at found);
                  Copy (at count);
                ];
              add_to_length storage (Copy (at count)));
          set (Use (Copy (at present)))
      | Clock_now -> call ?result:destination Clock_now []
      | Random_fill ->
          let storage = place (argument 0) in
          let count = value 1 in
          let wanted = usize_local "wanted" in
          emit b (Assign (at wanted, Binary (Add, length storage, count)));
          grow_when Greater storage (Copy (at wanted));
          call Random_fill
            [ Address { place = element_at storage (length storage); writable = true }; count ];
          add_to_length storage count);
      None
