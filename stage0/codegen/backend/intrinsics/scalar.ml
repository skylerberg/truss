let raise_bug format = Context.raise_bug format

let lower (context : Context.t) (scalar : Intrinsic.scalar) =
  let builder = context.builder in
  let env = context.env in
  let destination = context.destination in
  let arguments = context.arguments in
  let set = Context.set context in
  let read_operand = Context.read_operand context in
  let read_type_argument = Context.read_type_argument context in
  let call = Context.call context in
  let fail_obligation_when = Context.fail_obligation_when context in
  let make_operand = Context.make_operand in
  let classify_scalar = Context.classify_scalar in
  let set_binary op = set (Binary (op, read_operand 0, read_operand 1)) in
  let set_comparison comparison = set (Compare (comparison, read_operand 0, read_operand 1)) in
  let set_unary op = set (Unary (op, read_operand 0)) in
  let call_into intrinsic = call ?result:destination intrinsic (List.map make_operand arguments) in
  let find_integer_argument () =
    match (Memory_layout.of_type env (read_type_argument 0)).form with
    | Scalar (Integer integer) -> Some integer
    | _ -> None
  in
  let lower_checked_arithmetic op overflow =
    match find_integer_argument () with
    | Some _ ->
        let result = Emit_c.Ir_builder.allocate_local builder (Value (read_type_argument 0)) in
        let over = Emit_c.Ir_builder.allocate_local builder (Raw Bool) in
        call ~result:(Lowered.make_local_place over) overflow
          [
            read_operand 0;
            read_operand 1;
            Address { place = Lowered.make_local_place result; writable = true };
          ];
        fail_obligation_when (Holds (Copy (Lowered.make_local_place over))) "arithmetic overflow";
        set (Use (Copy (Lowered.make_local_place result)))
    | _ -> set_binary op
  in
  let lower_checked_division op =
    match find_integer_argument () with
    | Some integer ->
        fail_obligation_when
          (Test (Equal, read_operand 1, Constant (Integer (integer, Z.zero))))
          "division by zero";
        (match integer with
        | Int8 | Int16 | Int32 | Int64 ->
            let bits = 8 * Memory_layout.compute_integer_size integer in
            let least = Z.neg (Z.shift_left Z.one (bits - 1)) in
            fail_obligation_when
              (Conjunction
                 ( Test (Equal, read_operand 1, Constant (Integer (integer, Z.minus_one))),
                   Test (Equal, read_operand 0, Constant (Integer (integer, least))) ))
              "arithmetic overflow"
        | _ -> ());
        set_binary op
    | _ -> set_binary op
  in
  let lower_overflow_test overflow =
    let ignored = Emit_c.Ir_builder.allocate_local builder (Value (read_type_argument 0)) in
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
        let make_constant number : Lowered.operand = Constant (Integer (amount, Z.of_int number)) in
        (match amount with
        | Int8 | Int16 | Int32 | Int64 ->
            fail_obligation_when
              (Test (Less, read_operand 1, make_constant 0))
              "shift amount out of range"
        | _ -> ());
        fail_obligation_when
          (Test (Greater_equal, read_operand 1, make_constant bits))
          "shift amount out of range"
    | _ -> ());
    set_binary op
  in
  let make_fits_test () : Emit_c.Ir_builder.condition =
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
        match
          List.map
            (fun (op, bound) : Emit_c.Ir_builder.condition ->
              Test (op, read_operand 0, make_constant bound))
            tests
        with
        | [] -> Holds (Constant (Bool true))
        | first :: rest ->
            List.fold_left (fun all test -> Emit_c.Ir_builder.Conjunction (all, test)) first rest)
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
        let under = Z.pred low in
        Conjunction
          ( Test
              (if is_held under then (Ieee_less, make_constant under, read_operand 0)
               else (Ieee_less_equal, make_constant low, read_operand 0)),
            Test (Ieee_less, read_operand 0, make_constant (Z.succ high)) )
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
          fail_obligation_when
            (Test (Equal, read_operand 0, Constant (Integer (integer, least))))
            "arithmetic overflow";
          set_unary Negate
      | _ -> set_unary Negate)
  | Wrapping_add -> set_binary Add
  | Wrapping_subtract -> set_binary Subtract
  | Wrapping_multiply -> set_binary Multiply
  | Add_overflows -> lower_overflow_test Add_overflow
  | Subtract_overflows -> lower_overflow_test Subtract_overflow
  | Multiply_overflows -> lower_overflow_test Multiply_overflow
  | Equal -> set_comparison Equal
  | Less -> set_comparison Less
  | Ieee_equal -> set_comparison Ieee_equal
  | Ieee_less -> set_comparison Ieee_less
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
  | Fits -> set (Emit_c.Ir_builder.evaluate builder (make_fits_test ()))
  | Convert ->
      (match
         (classify_scalar env (read_type_argument 0), classify_scalar env (read_type_argument 1))
       with
      | (Float32 | Float64), Integer _ ->
          fail_obligation_when (Negation (make_fits_test ())) "conversion out of range"
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
      set
        (Emit_c.Ir_builder.evaluate builder
           (Negation (Test (Ieee_equal, read_operand 0, read_operand 0))))
