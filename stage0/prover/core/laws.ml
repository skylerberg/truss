let list_laws (environment : State.environment) trait =
  match environment.lookups.interface.names.find_key trait with
  | Some key ->
      let source = Contracts.read_source_at_key environment.lookups key in
      List.map
        (fun (law : Mir.law) -> (source, law))
        (environment.lookups.mir.read_contract_part key).laws
  | None -> []

let list_law_parameter_types ~substitution (law : Mir.law) =
  List.map (fun (_, type_) -> Types.substitute_erased substitution type_) law.parameters

let bind_law_parameters frame source ~substitution (law : Mir.law) terms =
  let types = list_law_parameter_types ~substitution law in
  let locals, types =
    List.fold_left2
      (fun (locals, types_) ((local, _), ty) term ->
        (Locals.add (Core_local local) term locals, Locals.add (Core_local local) ty types_))
      (Locals.empty, Locals.empty)
      (List.combine law.parameters types)
      terms
  in
  {
    frame with
    State.source;
    locals;
    types;
    old_locals = locals;
    self = None;
    old_self = None;
    result = None;
    makes_obligations = false;
    substitution;
    self_type = None;
  }

let bound_law_parameters (frame : State.frame) symbols types ~below =
  match below with
  | None -> Some (Logic.Boolean true)
  | Some bound ->
      let environment = frame.environment in
      let compared =
        List.map2
          (fun symbol ty ->
            match
              Mir.Size_change.classify_holding environment.lookups.interface
                ~heads:environment.inductive_heads ty
            with
            | Whole | Within ->
                Some
                  (Logic.less
                     (Models.rank environment frame.query (Types.erase_views ty)
                        (Logic.Symbol symbol))
                     bound)
            | Out_of_reach _ -> None
            | Absent | Consumed -> Some (Logic.Boolean true))
          symbols types
      in
      if List.mem None compared then None
      else Some (Logic.conjunction (List.filter_map Fun.id compared))

let make_law_fact ?below (frame : State.frame) source ~substitution (law : Mir.law) =
  let types = list_law_parameter_types ~substitution law in
  if List.exists (fun ty -> Types.is_error ty) types then None
  else begin
    let number = Query.take_fresh_number frame.query in
    let symbols =
      List.mapi
        (fun index _ -> Logic.Symbol.Variable { label = "law"; numbers = [ number; index ] })
        types
    in
    let inside =
      bind_law_parameters
        { frame with bound = symbols @ frame.bound; condition = Logic.Boolean true }
        source ~substitution law
        (List.map (fun symbol -> Logic.Symbol symbol) symbols)
    in
    try
      Option.map
        (fun smaller ->
          let premise =
            Logic.conjunction
              (List.map
                 (fun clause -> snd (Validity.read_specification inside clause))
                 law.requires)
          in
          let valid =
            Logic.conjunction
              (List.map2
                 (fun symbol ty ->
                   Logic.( &&& )
                     (Encoding.make_in_range ty (Logic.Symbol symbol))
                     (Validity.make_validity inside ~assuming:true ty (Logic.Symbol symbol)))
                 symbols types)
          in
          let _, holds = Validity.read_specification inside law.states in
          Logic.forall
            ( List.map2 (fun symbol ty -> (symbol, Encoding.sort_of ty)) symbols types,
              Logic.( ==> ) (Logic.conjunction [ valid; smaller; premise ]) holds ))
        (bound_law_parameters frame symbols types ~below)
    with Facts.Unsupported _ -> None
  end

let rec list_applied_functions (term : Logic.term) =
  match term with
  | Apply ((Function _ as symbol), arguments) ->
      symbol :: List.concat_map list_applied_functions arguments
  | Apply (_, arguments) | Operation (_, arguments) ->
      List.concat_map list_applied_functions arguments
  | Is (_, argument) -> list_applied_functions argument
  | Forall (_, _, body) | Exists (_, body) -> list_applied_functions body
  | Symbol _ | Integer _ | Boolean _ | Bits _ -> []

let list_group_functions (environment : State.environment) fact =
  List.sort_uniq compare
    (List.filter
       (fun (symbol : Logic.symbol) ->
         match symbol with
         | Function { callee; _ } ->
             List.exists (Path.equal callee) (environment.lookups.list_proof_group environment.node)
         | _ -> false)
       (list_applied_functions fact))

let make_law_facts ?below (frame : State.frame) source ~substitution law =
  match make_law_fact ?below frame source ~substitution law with
  | Some fact_ when Option.is_some below -> (
      match list_group_functions frame.environment fact_ with
      | [] -> [ fact_ ]
      | functions ->
          fact_
          :: Option.to_list
               (Contract_axioms.run_limiting frame.query functions (fun () ->
                    make_law_fact ?below frame source ~substitution law)))
  | Some fact_ -> [ fact_ ]
  | None -> []

let assume_laws (frame : State.frame) (trait : Types.trait_reference) (ty : Types.ty) =
  let environment = frame.environment in
  List.iter
    (fun (required : Types.trait_reference) ->
      let impl = Option.map fst (Encoding.find_impl environment required ty) in
      let impls, assumptions =
        Mir.Call_edges.list_impls_of_bounds environment.lookups.interface [ (ty, required) ]
      in
      let assume key ?below () =
        Query.run_once frame.query key @@ fun () ->
        let substitution = Contracts.make_trait_substitution environment.lookups required ty in
        List.iter
          (fun (source, (law : Mir.law)) ->
            match make_law_facts ?below frame source ~substitution law with
            | [] -> ()
            | facts ->
                Option.iter
                  (fun impl ->
                    List.iter (Query.add_hole frame.query)
                      (Contracts.list_law_holes environment.lookups impl required ty law.name))
                  impl;
                List.iter
                  (Facts.add_theorem frame
                     ~because:(match impl with Some impl -> Proven_by impl | None -> Hypothesis))
                  facts)
          (list_laws environment required.trait)
      in
      if
        not
          (environment.proven_laws = Some (required, ty)
          || List.exists (Cycles.is_in_proof_cycle environment) impls)
      then assume (Laws_of (required, ty)) ()
      else
        match Termination.read_induction_bound frame with
        | Some bound
          when not
                 (Termination.makes_inductive_values environment ~generics:[]
                    ~substitution:Types.no_substitution assumptions) ->
            assume (Laws_of_smaller_values (required, ty)) ~below:bound ()
        | Some _ | None -> ())
    (Interface.Properties.list_bound_closure environment.lookups.interface ~self:ty trait)
