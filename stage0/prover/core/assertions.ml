open State
open Facts

let is_test context = match context.current with Path.Test _ -> true | _ -> false

let bitwise_operations : Intrinsic.operation list =
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

let bitwise_of : Logic.symbol -> _ = function
  | Opaque_operation { operation; integer = Some (bits, signed); _ }
    when List.mem operation bitwise_operations ->
      Some (operation, bits, signed)
  | _ -> None

let exactly (query : Logic.query) =
  let bitwise_terms = ref [] in
  let rec walk bound = function
    | Logic.Apply (name, arguments) as term ->
        (if bitwise_of name <> None && not (List.mem_assoc term !bitwise_terms) then
           let named = List.filter (fun (symbol, _) -> Logic.mentions [ symbol ] term) bound in
           bitwise_terms := (term, named) :: !bitwise_terms);
        List.iter (walk bound) arguments
    | Logic.Forall (symbols, _, body) | Logic.Exists (symbols, body) -> walk (symbols @ bound) body
    | term -> List.iter (walk bound) (Logic.arguments term)
  in
  List.iter (walk []) (query.goal :: query.facts);
  let definition term =
    match term with
    | Logic.Apply (name, arguments) -> (
        match (bitwise_of name, arguments) with
        | Some (operation, bits, signed), first :: rest ->
            let bits_of value = Logic.Operation (Printf.sprintf "(_ int2bv %d)" bits, [ value ]) in
            let operand_bits = bits_of first in
            let result =
              match (operation, rest) with
              | Intrinsic.Complement, _ -> Some (Logic.Operation ("bvnot", [ operand_bits ]))
              | Bit_and, [ second_operand ] ->
                  Some (Logic.Operation ("bvand", [ operand_bits; bits_of second_operand ]))
              | Bit_or, [ second_operand ] ->
                  Some (Logic.Operation ("bvor", [ operand_bits; bits_of second_operand ]))
              | Bit_xor, [ second_operand ] ->
                  Some (Logic.Operation ("bvxor", [ operand_bits; bits_of second_operand ]))
              | Shift_left, [ second_operand ] ->
                  Some (Logic.Operation ("bvshl", [ operand_bits; bits_of second_operand ]))
              | Shift_right, [ second_operand ] ->
                  Some
                    (Logic.Operation
                       ( (if signed then "bvashr" else "bvlshr"),
                         [ operand_bits; bits_of second_operand ] ))
              | (Rotate_left | Rotate_right), [ second_operand ] ->
                  let by = bits_of (Logic.Operation ("mod", [ second_operand; Logic.int bits ])) in
                  let rest = Logic.Operation ("bvsub", [ bits_of (Logic.int bits); by ]) in
                  let towards, back =
                    if operation = Rotate_left then ("bvshl", "bvlshr") else ("bvlshr", "bvshl")
                  in
                  Some
                    (Logic.Operation
                       ( "bvor",
                         [
                           Logic.Operation (towards, [ operand_bits; by ]);
                           Logic.Operation (back, [ operand_bits; rest ]);
                         ] ))
              | Swap_bytes, _ ->
                  let byte index =
                    Logic.Operation
                      ( Printf.sprintf "(_ extract %d %d)" ((8 * index) + 7) (8 * index),
                        [ operand_bits ] )
                  in
                  let bytes = List.init (bits / 8) byte in
                  Some
                    (List.fold_left
                       (fun swapped next -> Logic.Operation ("concat", [ swapped; next ]))
                       (List.hd bytes) (List.tl bytes))
              | _ -> None
            in
            Option.map
              (fun result ->
                let unsigned = Logic.Operation ("bv2nat", [ result ]) in
                let value =
                  if signed then
                    let half = Logic.Integer (Z.shift_left Z.one (bits - 1)) in
                    Logic.ite
                      (Logic.Operation (">=", [ unsigned; half ]))
                      (Logic.Operation ("-", [ unsigned; Logic.Integer (Z.shift_left Z.one bits) ]))
                      unsigned
                  else unsigned
                in
                Logic.equal term value)
              result
        | _ -> None)
    | _ -> None
  in
  let defined (term, named) =
    Option.map
      (fun definition -> if named = [] then definition else Logic.forall (named, definition))
      (definition term)
  in
  { query with facts = query.facts @ List.filter_map defined (List.rev !bitwise_terms) }

let bit_vector_assertion context frame ~named ~origin ~(read : frame -> Logic.term) =
  let saved_facts = context.facts and saved_decisions = context.decisions in
  let saved_stated = Hashtbl.copy context.stated in
  context.facts <- [];
  context.decisions <- [];
  let isolated =
    {
      frame with
      condition = Logic.Boolean true;
      bound = [];
      binders = [];
      makes_obligations = false;
    }
  in
  let isolated =
    List.fold_left
      (fun (inside : frame) (local, ty) ->
        let symbol = fresh context inside "asserted" (sort_of context ty) in
        assume context inside (in_range ty symbol);
        match local with
        | Core.Self -> { inside with self = Some symbol }
        | _ -> { inside with locals = Locals.add local symbol inside.locals })
      isolated named
  in
  let term = read isolated in
  let obligation =
    make_obligation context
      { isolated with makes_obligations = true }
      Assertion (span_of frame.source origin)
      (Printf.sprintf "`%s` may not hold for every value of the variables it names."
         (quote frame.source origin))
      term
  in
  context.obligations <- { obligation with query = exactly obligation.query } :: context.obligations;
  context.facts <- saved_facts;
  context.decisions <- saved_decisions;
  Hashtbl.reset context.stated;
  Hashtbl.iter (Hashtbl.replace context.stated) saved_stated

let assertion context frame ~origin ~bit_vector term =
  (match bit_vector with
  | Some (named, read) when not (is_test context) ->
      bit_vector_assertion context frame ~named ~origin ~read
  | _ -> ());
  if is_test context || bit_vector <> None then assume context frame term
  else
    oblige context frame Assertion (span_of frame.source origin)
      (Printf.sprintf "`%s` may not hold." (quote frame.source origin))
      term
