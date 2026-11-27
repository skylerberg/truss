let find_signature (environment : State.environment) =
  match environment.lookups.interface.names.read_definition environment.home with
  | { kind = Function { signature; body; _ }; _ } -> Some (signature, body)
  | _ -> None

let make_uses_fix (environment : State.environment) capability : Catalog.Prover.fix list =
  match find_signature environment with
  | Some (signature, body) when not environment.inherits_precondition ->
      [
        (match
           ( List.find_opt
               (fun (clause : Syntax.clause) ->
                 match clause.kind with Uses _ -> true | _ -> false)
               signature.clauses,
             signature.clauses )
         with
        | Some uses, _ -> Add_to_uses { capability; uses = Written uses.id }
        | None, first :: _ -> Add_uses { capability; place = Before_clause (Written first.id) }
        | None, [] -> Add_uses { capability; place = Before_body (Written body.id) });
      ]
  | Some _ | None -> []

let find_parameter_name (frame : State.frame) symbol =
  Option.map (Option.value ~default:"self") (List.assoc_opt symbol frame.entry)

let collect_codes codes = if List.mem None codes then None else Some (List.filter_map Fun.id codes)

let rec find_value_code frame : Logic.term -> Catalog.Code.t option = function
  | Logic.Operation (Add, (_ :: _ :: _ as parts)) ->
      Option.map (fun parts -> Catalog.Code.Sum parts) (find_value_codes frame parts)
  | Logic.Operation (Multiply, (_ :: _ :: _ as parts)) ->
      Option.map (fun parts -> Catalog.Code.Product parts) (find_value_codes frame parts)
  | Logic.Operation (Subtract, [ left; right ]) -> (
      match (find_value_code frame left, find_value_code frame right) with
      | Some left, Some right -> Some (Difference (left, right))
      | _ -> None)
  | Logic.Operation (Negate, [ Logic.Operation (Negate, [ inner ]) ]) -> find_value_code frame inner
  | Logic.Operation (Negate, [ inner ]) ->
      Option.map (fun inner -> Catalog.Code.Negated inner) (find_value_code frame inner)
  | Logic.Apply (Logic.Symbol.Field { field; variant = None; _ }, [ receiver ]) ->
      Option.map
        (fun receiver -> Catalog.Code.Field { receiver; field })
        (find_value_code frame receiver)
  | Logic.Symbol symbol ->
      Option.map (fun name -> Catalog.Code.Name name) (find_parameter_name frame symbol)
  | Logic.Integer value -> Some (Integer value)
  | Logic.Boolean value -> Some (Boolean value)
  | _ -> None

and find_value_codes (frame : State.frame) parts =
  collect_codes (List.map (find_value_code frame) parts)

let find_comparison_operator : Logic.operator -> Language.Comparison.t option = function
  | Less -> Some Less
  | Less_equal -> Some Less_equal
  | Greater -> Some Greater
  | Greater_equal -> Some Greater_equal
  | Equal -> Some Equal
  | _ -> None

let find_goal_code (frame : State.frame) term =
  let rec find_goal (term : Logic.term) : Catalog.Code.t option =
    match term with
    | Operation (And, parts) -> (
        match List.filter (fun part -> not (Logic.is_valid part)) parts with
        | [] -> None
        | [ part ] -> find_goal part
        | parts ->
            Option.map
              (fun parts -> Catalog.Code.All parts)
              (collect_codes (List.map find_goal parts)))
    | Operation (Or, parts) ->
        Option.map (fun parts -> Catalog.Code.Any parts) (collect_codes (List.map find_goal parts))
    | Operation (Not, [ inner ]) ->
        Option.map (fun inner -> Catalog.Code.Not inner) (find_goal inner)
    | Operation (Implies, [ premise; conclusion ]) -> (
        match (find_goal premise, find_goal conclusion) with
        | Some premise, Some conclusion -> Some (Implies { premise; conclusion })
        | _ -> None)
    | Operation (operator, [ left; right ]) -> (
        match find_comparison_operator operator with
        | Some comparison -> find_comparison left comparison right
        | None -> find_value_code frame term)
    | term -> find_value_code frame term
  and find_comparison left comparison right =
    match (find_value_code frame left, find_value_code frame right) with
    | Some left, Some right -> Some (Catalog.Code.Compared { left; comparison; right })
    | _ -> None
  in
  let rec find_conclusion : Logic.term -> Logic.term = function
    | Operation (Implies, [ _; conclusion ]) -> find_conclusion conclusion
    | conclusion -> conclusion
  in
  if
    List.exists
      (fun symbol -> List.mem_assoc symbol frame.entry)
      (Logic.list_free_constants (find_conclusion term))
  then find_goal term
  else None

let read_requires_clause (signature : Syntax.signature) (origin : Core.origin) =
  let expression = match origin with Written id | Desugared { construct = id; _ } -> id in
  match
    List.find_opt
      (fun (clause : Syntax.clause) ->
        match clause.kind with Requires written -> written.id = expression | _ -> false)
      signature.clauses
  with
  | Some clause -> clause
  | None -> Facts.raise_bug "a `requires` is read that the signature does not write"

let add_requires (frame : State.frame) required : Catalog.Prover.fix list =
  match find_signature frame.environment with
  | Some (signature, body) when not frame.environment.inherits_precondition ->
      let place : Catalog.Prover.clause_place =
        match frame.requires_being_read with
        | Some origin -> Before_clause (Written (read_requires_clause signature origin).id)
        | None -> Before_body (Written body.id)
      in
      [
        Add_requires
          {
            place;
            required;
            premise =
              (match frame.condition with
              | Logic.Boolean true -> None
              | condition -> find_goal_code frame condition);
            condition = frame.environment.condition;
          };
      ]
  | Some _ | None -> []

let find_parameter_code (frame : State.frame) term =
  if
    Facts.is_home frame
    && (not (Logic.has_quantifier term))
    &&
    match Logic.list_free_constants term with
    | _ :: _ as names -> List.for_all (fun name -> List.mem_assoc name frame.entry) names
    | [] -> false
  then find_value_code frame term
  else None

let find_integer_limits ty = if Types.is_builtin Character ty then None else Encoding.find_bounds ty
let make_limit ty limit = Catalog.Code.Limit { type_ = ty; limit }
let make_comparison left comparison right = Catalog.Code.Compared { left; comparison; right }

let make_range_fix frame ty term =
  match (find_integer_limits ty, find_parameter_code frame term) with
  | Some (low, _), Some value ->
      let least = if Z.sign low = 0 then Catalog.Code.Integer Z.zero else make_limit ty Minimum in
      add_requires frame
        [
          Clause
            (All
               [
                 make_comparison least Less_equal value;
                 make_comparison value Less_equal (make_limit ty Maximum);
               ]);
        ]
  | _ -> []

let make_overflow_fix frame ty (operation : Intrinsic.scalar) left right exact =
  match find_integer_limits ty with
  | None -> []
  | Some (low, high) -> (
      let is_unsigned = Z.sign low = 0 in
      let bound_on_left =
        match (right, find_parameter_code frame left) with
        | Logic.Integer amount, Some value -> (
            let magnitude = Catalog.Code.Integer (Z.abs amount) in
            let bound_by comparison bound written =
              if Z.leq low bound && Z.leq bound high then
                Some (make_comparison value comparison written)
              else None
            in
            match operation with
            | Add when Z.sign amount > 0 ->
                bound_by Less_equal (Z.sub high amount)
                  (Difference (make_limit ty Maximum, magnitude))
            | Add when Z.sign amount < 0 ->
                bound_by Greater_equal (Z.sub low amount) (Sum [ make_limit ty Minimum; magnitude ])
            | Subtract when Z.sign amount > 0 && is_unsigned ->
                bound_by Greater_equal amount magnitude
            | Subtract when Z.sign amount > 0 ->
                bound_by Greater_equal (Z.add low amount) (Sum [ make_limit ty Minimum; magnitude ])
            | Subtract when Z.sign amount < 0 ->
                bound_by Less_equal (Z.add high amount)
                  (Difference (make_limit ty Maximum, magnitude))
            | Multiply when Z.sign amount > 0 && is_unsigned ->
                bound_by Less_equal (Z.div high amount)
                  (Quotient (make_limit ty Maximum, magnitude))
            | _ -> None)
        | _ -> None
      in
      match (bound_on_left, operation) with
      | Some required, _ -> add_requires frame [ Clause required ]
      | None, (Add | Multiply) when is_unsigned -> (
          match find_parameter_code frame exact with
          | Some value ->
              add_requires frame
                [ Clause (make_comparison value Less_equal (make_limit ty Maximum)) ]
          | None -> [])
      | None, Subtract when is_unsigned -> []
      | None, _ -> make_range_fix frame ty exact)

let make_division_overflow_fix frame ty left right =
  match (find_integer_limits ty, find_parameter_code frame left) with
  | Some _, Some dividend -> (
      let dividend_not_minimum = make_comparison dividend Not_equal (make_limit ty Minimum) in
      match right with
      | Logic.Integer divisor when Z.equal divisor Z.minus_one ->
          add_requires frame [ Clause dividend_not_minimum ]
      | _ -> (
          match find_parameter_code frame right with
          | Some divisor ->
              add_requires frame
                [
                  Clause
                    (Any
                       [
                         dividend_not_minimum;
                         make_comparison divisor Not_equal (Integer Z.minus_one);
                       ]);
                ]
          | None -> []))
  | _ -> []

let make_negation_fix frame ty inner =
  match (find_integer_limits ty, find_parameter_code frame inner) with
  | Some _, Some value ->
      add_requires frame [ Clause (make_comparison value Not_equal (make_limit ty Minimum)) ]
  | _ -> []

let list_type_names substitution =
  let named =
    List.fold_left
      (fun named ((parameter : Types.parameter), ty) ->
        if
          List.exists
            (fun (other, other_type) -> other = parameter.name && Types.equal other_type ty)
            named
        then named
        else named @ [ (parameter.name, ty) ])
      []
      (Types.list_type_arguments substitution)
  in
  List.filter
    (fun (name, _) -> List.length (List.filter (fun (other, _) -> other = name) named) = 1)
    named

let list_required_fixes (frame : State.frame) (clauses : State.clauses)
    (requirement : Mir.requirement) term (values : State.passed list) ~type_names =
  let clause = requirement.clause in
  let is_fixed name =
    List.mem_assoc name frame.entry
    ||
    match name with
    | Logic.Symbol.Constant _ | Evaluated (Constant_value _) | Literal _ -> true
    | _ -> false
  in
  let list_written () =
    List.filter_map
      (fun (index, (parameter : Mir.parameter)) ->
        Option.bind
          (List.find_opt (fun (passed : State.passed) -> passed.position = index) values)
          (fun (passed : State.passed) ->
            Option.map (fun code -> (parameter.local, code)) (find_value_code frame passed.term)))
      (List.mapi (fun index parameter -> (index, parameter)) clauses.parameters)
  in
  if
    Facts.is_home frame
    && List.for_all is_fixed (Logic.list_free_constants term)
    && List.exists (fun name -> List.mem_assoc name frame.entry) (Logic.list_free_constants term)
    && not (Logic.is_refuted term)
  then begin
    let written = list_written () in
    let replacements =
      List.map
        (fun (local, origin) ->
          Option.map (fun code -> (origin, code)) (List.assoc_opt local written))
        requirement.names
    in
    if List.for_all Option.is_some replacements then
      add_requires frame
        [
          Substituted_clause
            {
              clause = { key = clauses.callee.key; origin = clause.origin };
              replacements = List.filter_map Fun.id replacements;
              type_names;
            };
        ]
    else []
  end
  else []
