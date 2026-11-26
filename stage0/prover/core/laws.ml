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

let make_law_fact (frame : State.frame) source ~substitution (law : Mir.law) =
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
      let premise =
        Logic.conjunction
          (List.map (fun clause -> snd (Validity.read_specification inside clause)) law.requires)
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
      Some
        (Logic.forall
           ( List.map2 (fun symbol ty -> (symbol, Encoding.sort_of ty)) symbols types,
             Logic.( ==> ) (Logic.( &&& ) valid premise) holds ))
    with Facts.Unsupported _ -> None
  end

let assume_laws (frame : State.frame) (trait : Types.trait_reference) (ty : Types.ty) =
  List.iter
    (fun (required : Types.trait_reference) ->
      let key = (required, ty) in
      let impl = Option.map fst (Encoding.find_impl frame.environment required ty) in
      let is_proven_with_this_proof =
        match impl with
        | Some impl -> Cycles.is_in_proof_cycle frame.environment impl
        | None -> false
      in
      if not (is_proven_with_this_proof || frame.environment.proven_laws = Some key) then
        Query.run_once frame.query (Laws_of (required, ty)) @@ fun () ->
        let substitution =
          Contracts.make_trait_substitution frame.environment.lookups required ty
        in
        List.iter
          (fun (source, (law : Mir.law)) ->
            match make_law_fact frame source ~substitution law with
            | Some fact_ ->
                Option.iter
                  (fun impl ->
                    List.iter (Query.add_hole frame.query)
                      (Contracts.list_law_holes frame.environment.lookups impl required ty law.name))
                  impl;
                Facts.add_axiom frame fact_
            | None -> ())
          (list_laws frame.environment required.trait))
    (Interface.Properties.list_bound_closure frame.environment.lookups.interface ~self:ty trait)
