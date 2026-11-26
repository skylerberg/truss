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
  let body, with_facts =
    Query.run_under_binder context.query bound_symbol (fun () -> read body_frame)
  in
  (body_frame, body, with_facts)

let sequence_path : Path.t = Well_known.make_path Sequence

let make_sequence_type element =
  Types.Named { path = sequence_path; arguments = [ Types.Type element ] }

let make_sequence_length context element term =
  let symbol =
    Logic.Symbol.Function
      {
        callee = Well_known.make_method_path Sequence_length;
        type_arguments = [ Types.Type element ];
      }
  in
  Facts.declare context
    (Logic.Function
       (symbol, [ Encoding.declare_sort context (make_sequence_type element) ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let rec index_sequence (context : State.context) element term index =
  let sequence = make_sequence_type element in
  let index_trait = Well_known.make_path Index in
  match
    Interface.Impls.list_impls_of_trait_for_type context.lookups.interface ~trait:index_trait
      ~type_:sequence_path Path.standard_package
  with
  | impl :: _ ->
      let symbol =
        Logic.Symbol.Function
          {
            callee = Well_known.make_impl_method_path Index_at ~impl;
            type_arguments = [ Types.Type sequence ];
          }
      in
      Facts.declare context
        (Logic.Function
           ( symbol,
             [ Encoding.declare_sort context sequence; Logic.Int ],
             Encoding.declare_sort context element ));
      let at sequence index = Logic.Apply (symbol, [ sequence; index ]) in
      if context.ranking && Encoding.find_constructors context element <> None then
        Facts.run_once context (Ranked_elements sequence) (fun () ->
            let each = Logic.Symbol.Variable { label = "ranked.sequence"; numbers = [] }
            and index = Logic.Symbol.Variable { label = "ranked.index"; numbers = [] } in
            let ranked = Logic.Symbol each and position = Logic.Symbol index in
            let below = rank context element (at ranked position) in
            let fact =
              Logic.forall
                ( [ (each, Encoding.declare_sort context sequence); (index, Logic.Int) ],
                  Logic.(
                    less_equal (int 0) position
                    &&& less position (make_sequence_length context element ranked)
                    ==> less below (rank context sequence ranked)) )
            in
            Facts.add_fact context fact);
      Some (at term index)
  | [] -> None

and rank context ty term =
  let symbol = Logic.Symbol.Rank ty in
  Facts.declare context (Logic.Function (symbol, [ Encoding.declare_sort context ty ], Logic.Int));
  Facts.run_once context (Non_negative_rank ty) (fun () ->
      let each = Logic.Symbol.Variable { label = "ranked.value"; numbers = [] } in
      Facts.add_fact context
        (Logic.forall
           ( [ (each, Encoding.declare_sort context ty) ],
             Logic.less_equal (Logic.int 0) (Logic.Apply (symbol, [ Logic.Symbol each ])) )));
  (match ty with
  | Types.Named { path; arguments = [ Types.Type element ] }
    when context.ranking && Path.equal path sequence_path ->
      ignore (index_sequence context element term (Logic.int 0))
  | _ -> ());
  Logic.Apply (symbol, [ term ])

let make_finite_function context method_ ~arguments output inputs =
  let symbol =
    Logic.Symbol.Function
      { callee = Well_known.make_method_path method_; type_arguments = arguments }
  in
  let finite =
    Types.Named { path = Well_known.make_path (Well_known.locate_method method_).owner; arguments }
  in
  Facts.declare context
    (Logic.Function (symbol, Encoding.declare_sort context finite :: List.map snd inputs, output));
  fun term -> Logic.Apply (symbol, term :: List.map fst inputs)

let substitute_value_term context (value : Types.value) =
  match value with
  | Known number -> Logic.Integer number
  | Value_parameter parameter ->
      let symbol = Logic.Symbol.Generic_value { owner = parameter.owner; name = parameter.name } in
      Facts.run_once context (In_range symbol) (fun () ->
          Facts.declare context (Logic.Constant (symbol, Int));
          Facts.add_fact context
            (Encoding.make_in_range (Types.make_builtin UInt64) (Logic.Symbol symbol)));
      Logic.Symbol symbol
  | Value_variable _ -> Facts.raise_unsupported Whole_definition Unsolved_size
  | Value_error _ -> Facts.raise_bug "a value with an error, which no proof reaches"

let is_model_built_from_contents : Path.t -> bool = function
  | Impl { module_; trait; for_type } ->
      module_.package = Path.standard_package
      && Path.equal trait.path (Well_known.make_path Model)
      && (Well_known.find_builtin_type for_type = Some Array
         || List.exists
              (fun name -> Path.equal for_type (Well_known.make_path name))
              [ List; List_cursor; String; Literal; Set; Sorted_set; Map; Sorted_map ])
  | Top _ | Method _ | Member_constant _ | Derived _ | Test _ | Law_proof _ | Unresolved _ -> false

let rank_model (context : State.context) (ty : Types.ty) ~(model : Types.ty) ~impl symbol =
  if context.ranking && is_model_built_from_contents impl then
    Facts.run_once context (Ranked_model symbol) (fun () ->
        let each = Logic.Symbol.Variable { label = "ranked.value"; numbers = [] } in
        let fact =
          Logic.forall
            ( [ (each, Encoding.declare_sort context ty) ],
              Logic.less_equal
                (rank context model (Logic.Apply (symbol, [ Logic.Symbol each ])))
                (rank context ty (Logic.Symbol each)) )
        in
        Facts.add_fact context fact)

let model_trait : Types.trait_reference =
  { trait = Well_known.make_path Model; trait_arguments = []; associated = [] }

let find_model_impl (context : State.context) (ty : Types.ty) ~(model : Types.ty) =
  let interface = context.lookups.interface and list_bounds = Interface.Impls.list_no_bounds in
  let value =
    Types.erase_views
      (Interface.Impls.normalize interface ~list_bounds
         (Projection
            { base = ty; trait = model_trait; name = Well_known.show_associated Model_value }))
  in
  if value = model then Option.map fst (Encoding.find_impl context model_trait ty) else None

let compute_model_function (context : State.context) (ty : Types.ty) ~(model : Types.ty) =
  match find_model_impl context ty ~model with
  | Some impl ->
      let symbol =
        Logic.Symbol.Function
          {
            callee = Well_known.make_impl_method_path Model_model ~impl;
            type_arguments = Facts.list_method_type_arguments model_trait ~self_type:ty [];
          }
      in
      Facts.declare context
        (Logic.Function
           (symbol, [ Encoding.declare_sort context ty ], Encoding.declare_sort context model));
      rank_model context ty ~model ~impl symbol;
      (match ty with
      | Types.Named { path; arguments = [ Types.Type element; Types.Value count ] }
        when Well_known.find_builtin_type path = Some Array ->
          Facts.run_once context (Array_length symbol) (fun () ->
              let each = Logic.Symbol.Variable { label = "array.value"; numbers = [] } in
              let elements = Logic.Apply (symbol, [ Logic.Symbol each ]) in
              Facts.add_fact context
                (Logic.forall
                   ( [ (each, Encoding.declare_sort context ty) ],
                     Logic.equal
                       (make_sequence_length context element elements)
                       (substitute_value_term context count) )))
      | _ -> ());
      Some (fun term -> Logic.Apply (symbol, [ term ]))
  | None -> None

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

let quantify_over (context : State.context) (frame : State.frame)
    (quantifier : Language.Quantifier.t) (range : quantified_range) ~bind ~read =
  let make ?count bound_symbol sort premise body_frame bound_value =
    let mark = Query.mark context.query in
    let body_frame, (after, body_value), with_facts =
      run_under_binder context body_frame bound_symbol sort premise (fun body_frame ->
          read body_frame bound_value)
    in
    let bound = [ (bound_symbol, sort) ] in
    let frame =
      match count with
      | Some count when frame.makes_obligations ->
          Counters.spend_quantifier context frame ~count ~mark ~bound:bound_symbol
            ~before:body_frame ~after
      | _ -> frame
    in
    let term =
      match quantifier with
      | Forall -> Logic.forall (bound, Logic.( ==> ) premise body_value)
      | Exists -> Logic.Exists (bound, Logic.( &&& ) premise body_value)
    in
    if Facts.is_in_home_package context frame.source then
      Query.note_written_quantifier context.query term;
    (frame, with_facts term)
  in
  let symbol = Facts.make_fresh_name context "bound" in
  let inner = { frame with bound = symbol :: frame.bound } in
  let each = Logic.Symbol symbol in
  match range with
  | Range_of_type ty ->
      let inner = bind inner each ty in
      make symbol
        (Encoding.declare_sort context ty)
        (Validity.make_validity context inner ~assuming:true ~includes_ranges:true ty each)
        inner each
  | Range_of_integers { low; high; inclusive; type_ } ->
      let inner = bind inner each type_ in
      make
        ~count:(Encoding.count_values type_ ~low ~high ~inclusive)
        symbol Int
        (Encoding.make_in_values type_ each ~low ~high ~inclusive)
        inner each

let rec make_value_term context (frame : State.frame) (value : Types.value) =
  match value with
  | Value_parameter parameter -> (
      match Types.find_argument parameter frame.substitution with
      | Some (Types.Value argument) when argument <> Value_parameter parameter ->
          make_value_term context frame argument
      | _ -> substitute_value_term context value)
  | Known _ | Value_variable _ | Value_error _ -> substitute_value_term context value

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
      | None -> Facts.raise_unsupported Whole_definition (Elements_of ty))
  | _ -> Facts.raise_unsupported Whole_definition (Elements_of ty)
