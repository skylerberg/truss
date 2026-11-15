open State
open Facts
open Validity
open Operations

type quantified_range =
  | Range_of_type of Types.ty
  | Range_of_integers of { low : Logic.term; high : Logic.term; inclusive : bool; type_ : Types.ty }
  | Range_of_collection of {
      collection_type : Types.ty;
      collected : Logic.term;
      element : Types.ty;
      span : span;
    }

let under_binder :
    'read.
    context ->
    frame ->
    Logic.symbol ->
    Logic.sort ->
    Logic.term ->
    (frame -> 'read) ->
    frame * 'read * (Logic.term -> Logic.term) =
 fun context frame bound_symbol sort premise read ->
  let body_frame =
    restrict { frame with binders = (bound_symbol, sort, premise) :: frame.binders } premise
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
    if !facts <> [] then Hashtbl.replace context.quantifier_facts term (List.rev !facts);
    term
  in
  (body_frame, body, with_facts)

let sequence_path : Path.t = Well_known.path Sequence
let sequence_type element = Types.Named { path = sequence_path; arguments = [ Types.Type element ] }

let sequence_length context element term =
  let path = Path.Method { owner = sequence_path; name = "length"; receiver = Read } in
  let symbol = Symbol.Function { callee = path; instance = [ Types.Type element ] } in
  declare context (Logic.Function (symbol, [ sort_of context (sequence_type element) ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let rec sequence_at context element term index =
  let sequence = sequence_type element in
  let index_trait = Well_known.path Index in
  match
    Call_graph.impls_for
      (Query.demand context.database Call_graph.package_impls Path.standard_package)
      [ index_trait ] sequence
  with
  | impl :: _ ->
      let path = Path.Method { owner = impl; name = "at"; receiver = Read } in
      let symbol = Symbol.Function { callee = path; instance = [ Types.Type sequence ] } in
      declare context
        (Logic.Function (symbol, [ sort_of context sequence; Logic.Int ], sort_of context element));
      let at sequence index = Logic.Apply (symbol, [ sequence; index ]) in
      if context.ranking && constructors context element <> None then
        once context (Ranked_elements sequence) (fun () ->
            let each = Symbol.Variable { label = "ranked.sequence"; numbers = [] }
            and index = Symbol.Variable { label = "ranked.index"; numbers = [] } in
            let ranked = Logic.Symbol each and position = Logic.Symbol index in
            let below = rank context element (at ranked position) in
            let fact =
              Logic.forall
                ( [ (each, sort_of context sequence); (index, Logic.Int) ],
                  Logic.(
                    Operation ("<=", [ int 0; position ])
                    &&& Operation ("<", [ position; sequence_length context element ranked ])
                    ==> (Operation ("<=", [ int 0; below ])
                        &&& Operation ("<", [ below; rank context sequence ranked ]))) )
            in
            add_fact context fact);
      Some (at term index)
  | [] -> None

and rank context ty term =
  let symbol = Symbol.Rank ty in
  declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Int));
  (match ty with
  | Types.Named { path; arguments = [ Types.Type element ] }
    when context.ranking && Path.equal path sequence_path ->
      ignore (sequence_at context element term (Logic.int 0))
  | _ -> ());
  Logic.Apply (symbol, [ term ])

let finite_function context (ty : Types.ty) name output inputs =
  match ty with
  | Types.Named { path; arguments } ->
      let symbol =
        Symbol.Function
          { callee = Path.Method { owner = path; name; receiver = Read }; instance = arguments }
      in
      declare context (Logic.Function (symbol, sort_of context ty :: List.map snd inputs, output));
      fun term -> Logic.Apply (symbol, term :: List.map fst inputs)
  | _ -> fun term -> term

let finite_set_path : Path.t = Well_known.path Finite_set

let substituted_value_term context (value : Types.value) =
  match value with
  | Known number -> Logic.Integer number
  | Value_parameter parameter ->
      let symbol = Symbol.Generic_value { owner = parameter.owner; name = parameter.name } in
      once context (In_range symbol) (fun () ->
          declare context (Logic.Constant (symbol, Int));
          add_fact context (in_range (Types.builtin UInt64) (Logic.Symbol symbol)));
      Logic.Symbol symbol
  | Value_variable _ -> raise (Foreign_unsupported "an unsolved size")

let model_ranked context (ty : Types.ty) ~(model : Types.ty) symbol =
  if context.ranking then
    once context (Ranked_model symbol) (fun () ->
        let each = Symbol.Variable { label = "ranked.value"; numbers = [] } in
        let fact =
          Logic.forall
            ( [ (each, sort_of context ty) ],
              Logic.Operation
                ( "<=",
                  [
                    rank context model (Logic.Apply (symbol, [ Logic.Symbol each ]));
                    rank context ty (Logic.Symbol each);
                  ] ) )
        in
        add_fact context fact)

let find_model_function context (ty : Types.ty) ~(model : Types.ty) =
  let model_trait = Well_known.path Model in
  match
    Call_graph.impls_for
      (Query.demand context.database Call_graph.package_impls Path.standard_package)
      [ model_trait ] ty
  with
  | impl :: _ ->
      let path = Path.Method { owner = impl; name = "model"; receiver = Read } in
      let symbol = Symbol.Function { callee = path; instance = [ Types.Type ty ] } in
      declare context (Logic.Function (symbol, [ sort_of context ty ], sort_of context model));
      model_ranked context ty ~model symbol;
      (match ty with
      | Types.Named { path; arguments = [ Types.Type element; Types.Value count ] }
        when Intrinsic.builtin_of_path path = Some Array ->
          once context (Array_length symbol) (fun () ->
              let each = Symbol.Variable { label = "array.value"; numbers = [] } in
              let elements = Logic.Apply (symbol, [ Logic.Symbol each ]) in
              add_fact context
                (Logic.forall
                   ( [ (each, sort_of context ty) ],
                     Logic.equal
                       (sequence_length context element elements)
                       (substituted_value_term context count) )))
      | _ -> ());
      Some (fun term -> Logic.Apply (symbol, [ term ]))
  | [] -> None

let model_function context (ty : Types.ty) ~(model : Types.ty) =
  let key = (ty, model) in
  match Hashtbl.find_opt context.models key with
  | Some model_fn -> model_fn
  | None ->
      let model_fn = find_model_function context ty ~model in
      Hashtbl.replace context.models key model_fn;
      model_fn

let rec model_of context (ty : Types.ty) term ~element =
  model_as context ty term ~model:(sequence_type element)

and model_as context (ty : Types.ty) term ~(model : Types.ty) =
  Option.map (fun model_of -> model_of term) (model_function context ty ~model)

let quantified_over context frame (quantifier : Syntax.quantifier) (range : quantified_range) ~bind
    ~read =
  let make ?count bound_symbol sort premise body_frame bound_value =
    let mark = context.fresh in
    let body_frame, (after, body_value), with_facts =
      under_binder context body_frame bound_symbol sort premise (fun body_frame ->
          read body_frame bound_value)
    in
    let bound = [ (bound_symbol, sort) ] in
    let frame =
      match count with
      | Some count when frame.makes_obligations ->
          spend context frame (fun counter ->
              let spent =
                match
                  (List.assoc_opt counter body_frame.spent, List.assoc_opt counter after.spent)
                with
                | Some start, Some total -> Costs.since ~start total
                | _ -> Costs.zero
              in
              if mentions_fresh_after context mark spent || Logic.mentions [ bound_symbol ] spent
              then unknown_amount context frame counter
              else
                match counter.counting with
                | Units ->
                    Costs.plus
                      (Costs.times (Costs.at_least_zero count) (Costs.plus spent (Logic.int 1)))
                      (Logic.int 1)
                | At_most | Exactly ->
                    if spent = Costs.zero then Costs.zero else unknown_amount context frame counter)
      | _ -> frame
    in
    let term =
      match quantifier with
      | Forall -> Logic.forall (bound, Logic.( ==> ) premise body_value)
      | Exists -> Logic.Exists (bound, Logic.( &&& ) premise body_value)
    in
    Some (frame, with_facts term)
  in
  let symbol = fresh_name context "bound" in
  let inner = { frame with bound = symbol :: frame.bound } in
  let each = Logic.Symbol symbol in
  match range with
  | Range_of_type ty ->
      let _, inner = bind inner each ty in
      make symbol (sort_of context ty)
        (Logic.( &&& ) (in_range ty each) (validity context inner ~assuming:true ty each))
        inner each
  | Range_of_integers { low; high; inclusive; type_ } ->
      let _, inner = bind inner each type_ in
      let premise =
        Logic.(
          Operation ("<=", [ low; each ])
          &&& Operation ((if inclusive then "<=" else "<"), [ each; high ]))
      in
      let count =
        if inclusive then Costs.plus (Costs.minus high low) (Logic.int 1) else Costs.minus high low
      in
      make ~count symbol Int premise inner each
  | Range_of_collection { collection_type; collected; element; span } -> (
      let set_path = Well_known.path Set in
      match collection_type with
      | Types.Named { path; _ } when Path.equal path set_path || Path.equal path finite_set_path ->
          let finite = Types.Named { path = finite_set_path; arguments = [ Types.Type element ] } in
          let model =
            if Path.equal path finite_set_path then Some collected
            else model_as context collection_type collected ~model:finite
          in
          let model =
            match model with
            | Some model -> model
            | None -> unsupported span "a quantifier over `%s`" (Types.show collection_type)
          in
          let matched, inner = bind inner each element in
          make symbol (sort_of context element)
            (Logic.( &&& )
               (finite_function context finite "contains" Logic.Bool
                  [ (each, sort_of context element) ]
                  model)
               matched)
            inner each
      | _ -> (
          let sequence =
            match collection_type with
            | Types.Named { path; _ } when Path.equal path sequence_path -> Some collected
            | _ -> model_of context collection_type collected ~element
          in
          match sequence with
          | Some sequence -> (
              match sequence_at context element sequence each with
              | Some element_value ->
                  let length = sequence_length context element sequence in
                  let matched, inner = bind inner element_value element in
                  make ~count:length symbol Int
                    Logic.(
                      Operation ("<=", [ int 0; each ])
                      &&& Operation ("<", [ each; length ])
                      &&& matched)
                    inner element_value
              | None -> unsupported span "a quantifier over `%s`" (Types.show collection_type))
          | None -> unsupported span "a quantifier over `%s`" (Types.show collection_type)))

let rec value_term context frame (value : Types.value) =
  match value with
  | Value_parameter parameter -> (
      match List.assoc_opt parameter frame.substitution with
      | Some (Types.Value argument) when argument <> Value_parameter parameter ->
          value_term context frame argument
      | _ -> substituted_value_term context value)
  | Known _ | Value_variable _ -> substituted_value_term context value

let array_model context frame (ty : Types.ty) term =
  match ty with
  | Types.Named { arguments = [ Types.Type element; Types.Value count ]; _ } -> (
      match model_of context ty term ~element with
      | Some sequence ->
          assume context frame
            (Logic.equal
               (sequence_length context element sequence)
               (value_term context frame count));
          sequence
      | None -> raise (Foreign_unsupported (Printf.sprintf "the elements of `%s`" (Types.show ty))))
  | _ -> raise (Foreign_unsupported (Printf.sprintf "the elements of `%s`" (Types.show ty)))
