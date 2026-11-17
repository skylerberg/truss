let check_callback_requires context frame (site : Invocation.site) through
    (values : State.passed list) =
  match through with
  | Some (_, _, Invocation.Forwarded local) -> (
      match Validity.find_own_callback context local with
      | Some (name, { inputs; requires }) when List.length inputs = List.length values ->
          let inside =
            Validity.make_callback_contract_frame frame inputs
              (List.map (fun (passed : State.passed) -> passed.term) values)
          in
          List.iter
            (fun (clause : Mir.formula) ->
              Facts.oblige context frame Requires
                (Facts.locate context frame.source site.origin)
                [
                  Text "`";
                  Facts.quote frame.source clause.origin;
                  Text (Printf.sprintf "` may not hold for this call through `%s`." name);
                ]
                (snd (Validity.read_specification context inside clause)))
            requires
      | _ -> ())
  | _ -> ()

let calls_updating_helper (context : State.context) (invocation : Invocation.t) =
  match invocation.callee with
  | Function { path; _ } -> Contracts.is_updating_helper context.lookups path
  | _ -> false

let list_laws (context : State.context) trait =
  match context.lookups.interface.names.find_key trait with
  | Some key ->
      let source = Contracts.read_source_at_key context.lookups key in
      List.map
        (fun (law : Mir.law) -> (source, law))
        (context.lookups.mir.read_contract_part key).laws
  | None -> []

let list_law_parameter_types ~substitution (law : Mir.law) =
  List.map (fun (_, type_) -> Types.substitute substitution type_) law.parameters

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

let make_law_fact (context : State.context) (frame : State.frame) source ~substitution
    (law : Mir.law) =
  let types = list_law_parameter_types ~substitution law in
  if List.exists (fun ty -> Types.is_error ty) types then None
  else begin
    context.fresh <- context.fresh + 1;
    let symbols =
      List.mapi
        (fun index _ -> Logic.Symbol.Variable { label = "law"; numbers = [ context.fresh; index ] })
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
          (List.map
             (fun clause -> snd (Validity.read_specification context inside clause))
             law.requires)
      in
      let range =
        Logic.conjunction
          (List.map2 (fun symbol ty -> Facts.make_in_range ty (Logic.Symbol symbol)) symbols types)
      in
      let _, holds = Validity.read_specification context inside law.states in
      Some
        (Logic.forall
           ( List.map2 (fun symbol ty -> (symbol, Facts.declare_sort context ty)) symbols types,
             Logic.( ==> ) (Logic.( &&& ) range premise) holds ))
    with Facts.Unsupported _ -> None
  end

let assume_laws (context : State.context) frame ~at (trait : Types.trait_reference) (ty : Types.ty)
    =
  let key = (trait, ty) in
  if not (List.mem key context.laws_assumed) then begin
    context.laws_assumed <- key :: context.laws_assumed;
    List.iter
      (fun (required : Types.trait_reference) ->
        let substitution = Contracts.make_trait_substitution context.lookups required ty in
        let impl = Option.map fst (Operations.find_concrete_impl context required ty) in
        List.iter
          (fun (source, (law : Mir.law)) ->
            match make_law_fact context frame source ~substitution law with
            | Some fact_ ->
                (match impl with
                | Some impl when Contracts.is_law_unshown context.lookups impl required ty law.name
                  ->
                    context.holes <- (context.home, at) :: context.holes
                | _ -> ());
                Facts.add_frame_fact context frame fact_
            | None -> ())
          (list_laws context required.trait))
      (Interface.Properties.list_bound_closure context.lookups.interface ~self:ty trait)
  end

let template_trait : Path.t = Well_known.make_path From_template

let has_method_cost (context : State.context) (callee : Invocation.callee) (path : Path.t) =
  match (callee, path) with
  | Trait_method { trait; evidence = Bound; _ }, Method { owner; _ }
    when Path.equal owner trait.trait ->
      true
  | Trait_method _, _ -> (
      match Interface.Impls.read_signature context.lookups.interface path with
      | Some (signature : Types.signature) -> Types.terminates signature.uses
      | None -> true)
  | (Function _ | Capability_method _ | Intrinsic _ | Indirect ()), _ -> false

let check_named_callback context (frame : State.frame) (invocation : Invocation.t)
    (passed : State.passed) ~origin path (contract : State.contract) (values : State.passed list) =
  let location = Facts.locate context frame.source origin in
  let own = List.hd contract.parts in
  match Validity.find_parameter_type context frame invocation passed.position with
  | Some (Types.Function expected) ->
      let inputs = Validity.declare_callback_arguments context frame expected.inputs in
      let known = List.map (fun (passed : State.passed) -> (passed.position, passed.term)) values in
      let promised =
        Logic.conjunction
          (Validity.list_callback_facts context frame invocation passed.position known inputs)
      in
      let at_call = Facts.restrict frame promised in
      if List.length own.parameters = List.length inputs then
        let inside =
          Validity.bind_part_arguments frame own
            ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
            ~substitution:Types.no_substitution
        in
        List.iter
          (fun (requirement : Mir.formula) ->
            Facts.oblige context at_call Requires location
              [
                Text
                  (Printf.sprintf
                     "`%s` may not accept every argument this parameter's type promises it: its `"
                     (Path.show path));
                Facts.quote own.callee requirement.origin;
                Text "` may not hold.";
              ]
              (snd (Validity.read_specification context inside requirement)))
          (Facts.list_clauses own.requires)
  | _ ->
      if own.requires <> [] then
        Facts.raise_unsupported location
          "a function passed for a parameter whose type the prover cannot read"
