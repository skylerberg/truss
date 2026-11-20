let is_test (context : State.context) =
  match context.current with Path.Test _ -> true | _ -> false

let bitwise_operations : Intrinsic.scalar list =
  [
    Bit_and;
    Bit_or;
    Bit_xor;
    Complement;
    Shift_left;
    Shift_right;
    Rotate_left;
    Rotate_right;
    Swap_bytes;
  ]

let find_bitwise_operation : Logic.symbol -> _ = function
  | Opaque_operation { operation; integer = Some (bits, signed); _ }
    when List.mem operation bitwise_operations ->
      Some (operation, bits, signed)
  | _ -> None

let add_bitwise_definitions (query : Logic.query) =
  let bitwise_terms = ref [] in
  let rec walk bound = function
    | Logic.Apply (name, arguments) as term ->
        (if find_bitwise_operation name <> None && not (List.mem_assoc term !bitwise_terms) then
           let named = List.filter (fun (symbol, _) -> Logic.mentions [ symbol ] term) bound in
           bitwise_terms := (term, named) :: !bitwise_terms);
        List.iter (walk bound) arguments
    | Logic.Forall (symbols, _, body) | Logic.Exists (symbols, body) -> walk (symbols @ bound) body
    | term -> List.iter (walk bound) (Logic.list_arguments term)
  in
  List.iter (walk []) (query.goal :: query.facts);
  let find_definition term =
    match term with
    | Logic.Apply (name, arguments) -> (
        match (find_bitwise_operation name, arguments) with
        | Some (operation, bits, signed), first :: rest ->
            let convert_to_bits value = Logic.Operation (Int2bv { width = bits }, [ value ]) in
            let operand_bits = convert_to_bits first in
            let result =
              match (operation, rest) with
              | Intrinsic.Complement, _ -> Some (Logic.Operation (Bvnot, [ operand_bits ]))
              | Bit_and, [ second_operand ] ->
                  Some (Logic.Operation (Bvand, [ operand_bits; convert_to_bits second_operand ]))
              | Bit_or, [ second_operand ] ->
                  Some (Logic.Operation (Bvor, [ operand_bits; convert_to_bits second_operand ]))
              | Bit_xor, [ second_operand ] ->
                  Some (Logic.Operation (Bvxor, [ operand_bits; convert_to_bits second_operand ]))
              | Shift_left, [ second_operand ] ->
                  Some (Logic.Operation (Bvshl, [ operand_bits; convert_to_bits second_operand ]))
              | Shift_right, [ second_operand ] ->
                  Some
                    (Logic.Operation
                       ( (if signed then Bvashr else Bvlshr),
                         [ operand_bits; convert_to_bits second_operand ] ))
              | (Rotate_left | Rotate_right), [ second_operand ] ->
                  let by =
                    convert_to_bits (Logic.Operation (Mod, [ second_operand; Logic.int bits ]))
                  in
                  let rest = Logic.Operation (Bvsub, [ convert_to_bits (Logic.int bits); by ]) in
                  let towards, back =
                    if operation = Rotate_left then (Logic.Bvshl, Logic.Bvlshr)
                    else (Logic.Bvlshr, Logic.Bvshl)
                  in
                  Some
                    (Logic.Operation
                       ( Bvor,
                         [
                           Logic.Operation (towards, [ operand_bits; by ]);
                           Logic.Operation (back, [ operand_bits; rest ]);
                         ] ))
              | Swap_bytes, _ ->
                  let extract_byte index =
                    Logic.Operation
                      (Extract { high = (8 * index) + 7; low = 8 * index }, [ operand_bits ])
                  in
                  let bytes = List.init (bits / 8) extract_byte in
                  Some
                    (List.fold_left
                       (fun swapped next -> Logic.Operation (Concat, [ swapped; next ]))
                       (List.hd bytes) (List.tl bytes))
              | _ -> None
            in
            Option.map
              (fun result ->
                Logic.equal term (Logic.integer_of_bits ~is_signed:signed ~width:bits result))
              result
        | _ -> None)
    | _ -> None
  in
  let find_defined (term, named) =
    Option.map
      (fun definition -> if named = [] then definition else Logic.forall (named, definition))
      (find_definition term)
  in
  { query with facts = query.facts @ List.filter_map find_defined (List.rev !bitwise_terms) }

let assert_bit_vector (context : State.context) frame ~named ~origin
    ~(read : State.frame -> Logic.term) =
  let saved_facts = context.facts and saved_decisions = context.decisions in
  let saved_stated = Tables.Stated_table.copy context.stated in
  context.facts <- [];
  context.decisions <- [];
  let isolated =
    {
      frame with
      State.condition = Logic.Boolean true;
      bound = [];
      binders = [];
      makes_obligations = false;
    }
  in
  let isolated =
    List.fold_left
      (fun (inside : State.frame) (local, ty) ->
        let symbol =
          Facts.declare_fresh context inside "asserted" (Facts.declare_sort context ty)
        in
        Facts.assume context inside (Facts.make_in_range ty symbol);
        match local with
        | Core.Self -> { inside with self = Some symbol }
        | _ -> { inside with locals = Locals.add (Core_local local) symbol inside.locals })
      isolated named
  in
  let term = read isolated in
  let obligation =
    Facts.make_obligation context
      { isolated with makes_obligations = true }
      Assertion
      (Facts.locate context frame.source origin)
      [
        Text "`";
        Facts.quote frame.source origin;
        Text "` may not hold for every value of the variables it names.";
      ]
      term
  in
  let cited = if frame.source.key <> context.home then Some (frame.source.key, origin) else None in
  context.obligations <-
    { obligation with query = add_bitwise_definitions obligation.query; cited }
    :: context.obligations;
  context.facts <- saved_facts;
  context.decisions <- saved_decisions;
  Tables.Stated_table.reset context.stated;
  Tables.Stated_table.iter (Tables.Stated_table.replace context.stated) saved_stated

let check_assertion context frame ~origin ~bit_vector term =
  (match bit_vector with
  | Some (named, read) when not (is_test context) ->
      assert_bit_vector context frame ~named ~origin ~read
  | _ -> ());
  if is_test context || bit_vector <> None then Facts.assume context frame term
  else
    Facts.oblige context frame Assertion
      (Facts.locate context frame.source origin)
      [ Text "`"; Facts.quote frame.source origin; Text "` may not hold." ]
      term
