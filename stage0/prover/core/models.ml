type quantified_range =
  | Range_of_type of Types.ty
  | Range_of_integers of { low : Logic.term; high : Logic.term; inclusive : bool; type_ : Types.ty }

let run_under_binder :
    'read.
    State.context ->
    State.frame ->
    Logic.symbol ->
    Logic.sort ->
    Logic.term ->
    (State.frame -> 'read) ->
    State.frame * 'read * (Logic.term -> Logic.term) =
 fun context frame bound_symbol sort premise read ->
  let body_frame =
    Facts.restrict { frame with binders = (bound_symbol, sort, premise) :: frame.binders } premise
  in
  let facts = ref [] in
  context.scopes <- (bound_symbol, facts) :: context.scopes;
  context.quantifier_symbols <- bound_symbol :: context.quantifier_symbols;
  let body =
    Fun.protect
      ~finally:(fun () -> context.scopes <- List.tl context.scopes)
      (fun () -> read body_frame)
  in
  let with_facts term =
    if !facts <> [] then Tables.Term_table.replace context.quantifier_facts term (List.rev !facts);
    term
  in
  (body_frame, body, with_facts)

let sequence_path : Path.t = Well_known.make_path Sequence

let make_sequence_type element =
  Types.Named { path = sequence_path; arguments = [ Types.Type element ] }

let make_sequence_length context element term =
  let path = Path.Method { owner = sequence_path; name = "length"; receiver = Read } in
  let symbol = Logic.Symbol.Function { callee = path; instance = [ Types.Type element ] } in
  Facts.declare context
    (Logic.Function (symbol, [ Facts.declare_sort context (make_sequence_type element) ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let rec index_sequence (context : State.context) element term index =
  let sequence = make_sequence_type element in
  let index_trait = Well_known.make_path Index in
  match
    Mir.Call_edges.list_impls_for context.lookups.interface Path.standard_package [ index_trait ]
      sequence
  with
  | impl :: _ ->
      let path = Path.Method { owner = impl; name = "at"; receiver = Read } in
      let symbol = Logic.Symbol.Function { callee = path; instance = [ Types.Type sequence ] } in
      Facts.declare context
        (Logic.Function
           ( symbol,
             [ Facts.declare_sort context sequence; Logic.Int ],
             Facts.declare_sort context element ));
      let at sequence index = Logic.Apply (symbol, [ sequence; index ]) in
      if context.ranking && Facts.find_constructors context element <> None then
        Facts.run_once context (Ranked_elements sequence) (fun () ->
            let each = Logic.Symbol.Variable { label = "ranked.sequence"; numbers = [] }
            and index = Logic.Symbol.Variable { label = "ranked.index"; numbers = [] } in
            let ranked = Logic.Symbol each and position = Logic.Symbol index in
            let below = rank context element (at ranked position) in
            let fact =
              Logic.forall
                ( [ (each, Facts.declare_sort context sequence); (index, Logic.Int) ],
                  Logic.(
                    Operation ("<=", [ int 0; position ])
                    &&& Operation ("<", [ position; make_sequence_length context element ranked ])
                    ==> (Operation ("<=", [ int 0; below ])
                        &&& Operation ("<", [ below; rank context sequence ranked ]))) )
            in
            Facts.add_fact context fact);
      Some (at term index)
  | [] -> None

and rank context ty term =
  let symbol = Logic.Symbol.Rank ty in
  Facts.declare context (Logic.Function (symbol, [ Facts.declare_sort context ty ], Logic.Int));
  (match ty with
  | Types.Named { path; arguments = [ Types.Type element ] }
    when context.ranking && Path.equal path sequence_path ->
      ignore (index_sequence context element term (Logic.int 0))
  | _ -> ());
  Logic.Apply (symbol, [ term ])

let make_finite_function context (ty : Types.ty) name output inputs =
  match ty with
  | Types.Named { path; arguments } ->
      let symbol =
        Logic.Symbol.Function
          { callee = Path.Method { owner = path; name; receiver = Read }; instance = arguments }
      in
      Facts.declare context
        (Logic.Function (symbol, Facts.declare_sort context ty :: List.map snd inputs, output));
      fun term -> Logic.Apply (symbol, term :: List.map fst inputs)
  | _ -> fun term -> term

let finite_set_path : Path.t = Well_known.make_path Finite_set

let substitute_value_term context (value : Types.value) =
  match value with
  | Known number -> Logic.Integer number
  | Value_parameter parameter ->
      let symbol = Logic.Symbol.Generic_value { owner = parameter.owner; name = parameter.name } in
      Facts.run_once context (In_range symbol) (fun () ->
          Facts.declare context (Logic.Constant (symbol, Int));
          Facts.add_fact context
            (Facts.make_in_range (Types.make_builtin UInt64) (Logic.Symbol symbol)));
      Logic.Symbol symbol
  | Value_variable _ -> Facts.raise_unsupported Whole_definition "an unsolved size"

let rank_model (context : State.context) (ty : Types.ty) ~(model : Types.ty) symbol =
  if context.ranking then
    Facts.run_once context (Ranked_model symbol) (fun () ->
        let each = Logic.Symbol.Variable { label = "ranked.value"; numbers = [] } in
        let fact =
          Logic.forall
            ( [ (each, Facts.declare_sort context ty) ],
              Logic.Operation
                ( "<=",
                  [
                    rank context model (Logic.Apply (symbol, [ Logic.Symbol each ]));
                    rank context ty (Logic.Symbol each);
                  ] ) )
        in
        Facts.add_fact context fact)

let compute_model_function (context : State.context) (ty : Types.ty) ~(model : Types.ty) =
  let model_trait = Well_known.make_path Model in
  let packages =
    match ty with
    | Types.Named { path; _ } ->
        List.sort_uniq compare [ Path.standard_package; Path.locate_package path ]
    | _ -> [ Path.standard_package ]
  in
  let declared_model =
    Interface.Impls.normalize context.lookups.interface ~list_bounds:Interface.Impls.list_no_bounds
      (Projection
         {
           base = ty;
           trait = { trait = model_trait; trait_arguments = []; associated = [] };
           name = "Value";
         })
  in
  match
    List.concat_map
      (fun package ->
        Mir.Call_edges.list_impls_for context.lookups.interface package [ model_trait ] ty)
      packages
  with
  | impl :: _ when Types.equal declared_model model ->
      let path = Path.Method { owner = impl; name = "model"; receiver = Read } in
      let symbol = Logic.Symbol.Function { callee = path; instance = [ Types.Type ty ] } in
      Facts.declare context
        (Logic.Function (symbol, [ Facts.declare_sort context ty ], Facts.declare_sort context model));
      rank_model context ty ~model symbol;
      (match ty with
      | Types.Named { path; arguments = [ Types.Type element; Types.Value count ] }
        when Intrinsic.builtin_of_path path = Some Array ->
          Facts.run_once context (Array_length symbol) (fun () ->
              let each = Logic.Symbol.Variable { label = "array.value"; numbers = [] } in
              let elements = Logic.Apply (symbol, [ Logic.Symbol each ]) in
              Facts.add_fact context
                (Logic.forall
                   ( [ (each, Facts.declare_sort context ty) ],
                     Logic.equal
                       (make_sequence_length context element elements)
                       (substitute_value_term context count) )))
      | _ -> ());
      Some (fun term -> Logic.Apply (symbol, [ term ]))
  | _ -> None

let find_model_function (context : State.context) (ty : Types.ty) ~(model : Types.ty) =
  let key = (ty, model) in
  match Tables.Model_table.find_opt context.models key with
  | Some model_fn -> model_fn
  | None ->
      let model_fn = compute_model_function context ty ~model in
      Tables.Model_table.replace context.models key model_fn;
      model_fn

let find_model context (ty : Types.ty) term ~element =
  Option.map
    (fun model_of -> model_of term)
    (find_model_function context ty ~model:(make_sequence_type element))

let quantify_over (context : State.context) (frame : State.frame) (quantifier : Core.quantifier)
    (range : quantified_range) ~bind ~read =
  let make ?count bound_symbol sort premise body_frame bound_value =
    let mark = context.fresh in
    let body_frame, (after, body_value), with_facts =
      run_under_binder context body_frame bound_symbol sort premise (fun body_frame ->
          read body_frame bound_value)
    in
    let bound = [ (bound_symbol, sort) ] in
    let frame =
      match count with
      | Some count when frame.makes_obligations ->
          Operations.spend context frame (fun counter ->
              let spent =
                match
                  (List.assoc_opt counter body_frame.spent, List.assoc_opt counter after.State.spent)
                with
                | Some start, Some total -> Costs.since ~start total
                | _ -> Costs.zero
              in
              if
                Facts.mentions_fresh_after context mark spent
                || Logic.mentions [ bound_symbol ] spent
              then Operations.declare_unknown_amount context frame counter
              else
                match counter.counting with
                | Units ->
                    Costs.plus
                      (Costs.times (Costs.at_least_zero count) (Costs.plus spent (Logic.int 1)))
                      (Logic.int 1)
                | At_most | Exactly ->
                    if spent = Costs.zero then Costs.zero
                    else Operations.declare_unknown_amount context frame counter)
      | _ -> frame
    in
    let term =
      match quantifier with
      | Forall -> Logic.forall (bound, Logic.( ==> ) premise body_value)
      | Exists -> Logic.Exists (bound, Logic.( &&& ) premise body_value)
    in
    (frame, with_facts term)
  in
  let symbol = Facts.make_fresh_name context "bound" in
  let inner = { frame with bound = symbol :: frame.bound } in
  let each = Logic.Symbol symbol in
  match range with
  | Range_of_type ty ->
      let inner = bind inner each ty in
      make symbol (Facts.declare_sort context ty)
        (Logic.( &&& ) (Facts.make_in_range ty each)
           (Validity.make_validity context inner ~assuming:true ty each))
        inner each
  | Range_of_integers { low; high; inclusive; type_ } ->
      let inner = bind inner each type_ in
      let premise =
        Logic.(
          Operation ("<=", [ low; each ])
          &&& Operation ((if inclusive then "<=" else "<"), [ each; high ]))
      in
      let count =
        if inclusive then Costs.plus (Costs.minus high low) (Logic.int 1) else Costs.minus high low
      in
      make ~count symbol Int premise inner each

let rec make_value_term context (frame : State.frame) (value : Types.value) =
  match value with
  | Value_parameter parameter -> (
      match List.assoc_opt parameter frame.substitution with
      | Some (Types.Value argument) when argument <> Value_parameter parameter ->
          make_value_term context frame argument
      | _ -> substitute_value_term context value)
  | Known _ | Value_variable _ -> substitute_value_term context value

let make_array_model context frame (ty : Types.ty) term =
  match ty with
  | Types.Named { arguments = [ Types.Type element; Types.Value count ]; _ } -> (
      match find_model context ty term ~element with
      | Some sequence ->
          Facts.assume context frame
            (Logic.equal
               (make_sequence_length context element sequence)
               (make_value_term context frame count));
          sequence
      | None -> Facts.raise_unsupported Whole_definition "the elements of `%s`" (Types.show ty))
  | _ -> Facts.raise_unsupported Whole_definition "the elements of `%s`" (Types.show ty)
