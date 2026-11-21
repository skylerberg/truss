let check_callback_requires context frame (site : Invocation.site) through
    (values : State.passed list) =
  match through with
  | Some (_, _, Invocation.Forwarded local) -> (
      match Validity.find_own_callback context local with
      | Some (name, { inputs; requires; _ }) when List.length inputs = List.length values ->
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
                  Text
                    (Printf.sprintf "` may not hold for %s through `%s`."
                       (Facts.describe_call context
                          (Facts.locate context frame.source site.origin)
                          ())
                       name);
                ]
                (snd (Validity.read_specification context inside clause)))
            requires
      | _ -> ())
  | _ -> ()

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

let assume_laws (context : State.context) frame (trait : Types.trait_reference) (ty : Types.ty) =
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
                Option.iter
                  (fun impl ->
                    List.iter (Facts.add_hole context)
                      (Contracts.list_law_holes context.lookups impl required ty law.name))
                  impl;
                Facts.add_frame_fact context frame fact_
            | None -> ())
          (list_laws context required.trait))
      (Interface.Properties.list_bound_closure context.lookups.interface ~self:ty trait)
  end

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

let read_named_ensures context (frame : State.frame) (clauses : State.clauses)
    (expected : Types.function_type) ~entries ~exits ~result =
  let inside =
    Validity.bind_arguments frame clauses
      ~arguments:(List.mapi (fun index entry -> (index, entry)) entries)
      ~substitution:Types.no_substitution
  in
  let inside =
    List.fold_left2
      (fun (inside : State.frame) (parameter : Mir.parameter) (((mode : Language.Mode.t), _), exit_)
         ->
        match (mode, parameter.local) with
        | Mut, Self -> { inside with self = Some exit_ }
        | Mut, local -> { inside with locals = Locals.add (Core_local local) exit_ inside.locals }
        | (Read | Own), _ -> inside)
      { inside with result = Some result }
      clauses.parameters
      (List.combine expected.inputs exits)
  in
  List.filter_map
    (fun (clause : Mir.formula) ->
      match
        Conditions.find_obligation_condition
          (Conditions.decide context ~substitution:Types.no_substitution clause.holds_when)
      with
      | Some _ -> Some (snd (Validity.read_specification context inside clause))
      | None -> None)
    clauses.ensures

let add_named_relation context frame (expected : Types.function_type) callee_term
    (clauses : State.clauses) =
  let variable label index input =
    (Facts.make_variable label ~numbers:[ index ], Facts.declare_sort context input)
  in
  let inputs =
    List.mapi (fun index (_, input) -> variable "named.argument" index input) expected.inputs
  in
  let changed =
    List.mapi
      (fun index ((mode : Language.Mode.t), input) ->
        match mode with Mut -> Some (variable "named.changed" index input) | Read | Own -> None)
      expected.inputs
  in
  let returned = variable "named.result" 0 expected.output in
  let entries = List.map (fun (name, _) -> Logic.Symbol name) inputs in
  let exits =
    List.map2
      (fun entry changed ->
        match changed with Some (name, _) -> Logic.Symbol name | None -> entry)
      entries changed
  in
  let result = Logic.Symbol (fst returned) in
  let parameters = inputs @ List.filter_map Fun.id changed @ [ returned ] in
  let holds = Lambdas.make_callback_ensures context expected callee_term ~entries ~exits ~result in
  if Lambdas.is_in_the_logic expected then
    Facts.add_frame_fact context frame
      (Logic.forall ~trigger:[ holds ]
         ( parameters,
           Logic.equal holds
             (Logic.equal result (Lambdas.apply_function context expected callee_term entries)) ));
  let mark = context.State.fresh in
  let facts_mark = List.length context.facts in
  let read = read_named_ensures context frame clauses expected ~entries ~exits ~result in
  let bound = List.map fst parameters in
  let is_inside_the_relation fact =
    Logic.mentions bound fact || Facts.mentions_fresh_after context mark fact
  in
  let added = Lambdas.list_facts_since context facts_mark in
  context.facts <-
    List.filter (fun fact -> not (is_inside_the_relation fact)) added
    @ List.drop (List.length added) context.facts;
  match read with
  | [] -> ()
  | ensures when List.exists (Facts.mentions_fresh_after context mark) ensures -> ()
  | ensures ->
      Facts.add_frame_fact context frame
        (Logic.forall ~trigger:[ holds ]
           (parameters, Logic.( ==> ) holds (Logic.conjunction ensures)))

let check_named_callback context (frame : State.frame) (invocation : Invocation.t)
    (passed : State.passed) ~origin path (contract : State.contract) (values : State.passed list) =
  let location = Facts.locate context frame.source origin in
  let callee_clauses = contract.callee_clauses in
  match Validity.find_parameter_type context frame invocation passed.position with
  | Some (Types.Function expected) ->
      let inputs = Validity.declare_callback_arguments context frame expected.inputs in
      let known = List.map (fun (passed : State.passed) -> (passed.position, passed.term)) values in
      let promised =
        Logic.conjunction
          (Validity.list_callback_facts context frame invocation passed.position known inputs)
      in
      let at_call = Facts.restrict frame promised in
      if List.length callee_clauses.parameters = List.length inputs then (
        let inside =
          Validity.bind_arguments frame callee_clauses
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
                Facts.quote callee_clauses.callee requirement.origin;
                Text "` may not hold.";
              ]
              (snd (Validity.read_specification context inside requirement)))
          (Facts.list_clauses callee_clauses.requires);
        if List.length callee_clauses.parameters = List.length expected.inputs then begin
          add_named_relation context frame expected passed.term callee_clauses;
          Validity.check_callback_promises context frame ~location invocation passed
            ~described:
              (Printf.sprintf "and the `ensures` of `%s` may not promise it." (Path.show path))
            ~assume:(fun at_call expected ~entries ~exits ~result ->
              List.iter (Facts.assume context at_call)
                (read_named_ensures context at_call callee_clauses expected ~entries ~exits ~result))
            values
        end)
  | _ ->
      if callee_clauses.requires <> [] then
        Facts.raise_unsupported location
          "a function passed for a parameter whose type the prover cannot read"
