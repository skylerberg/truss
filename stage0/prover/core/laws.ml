module Symbol = Logic.Symbol

let check_callback_requires context frame (site : Invocation.site) through
    (values : State.passed list) =
  match through with
  | Some (_, _, Invocation.Forwarded local) -> (
      match Validity.own_callback context local with
      | Some (name, { inputs; requires }) when List.length inputs = List.length values ->
          let inside =
            Validity.callback_contract_frame frame inputs
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
                (snd (Validity.specification_value context inside clause)))
            requires
      | _ -> ())
  | _ -> ()

let calls_updating_helper (context : State.context) (invocation : Invocation.t) =
  match invocation.callee with
  | Function { path; _ } -> Contracts.is_updating_helper context.lookups path
  | _ -> false

let laws_of (context : State.context) trait =
  match context.lookups.interface.names.key trait with
  | Some key ->
      let source = Contracts.source_at_key context.lookups key in
      List.map (fun (law : Mir.law) -> (source, law)) (context.lookups.mir.contract_part key).laws
  | None -> []

let law_parameter_types ~substitution (law : Mir.law) =
  List.map (fun (_, type_) -> Types.substitute substitution type_) law.parameters

let law_frame frame source ~substitution (law : Mir.law) terms =
  let types = law_parameter_types ~substitution law in
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

let law_fact (context : State.context) (frame : State.frame) source ~substitution (law : Mir.law) =
  let types = law_parameter_types ~substitution law in
  if List.exists (fun ty -> Types.is_error ty) types then None
  else begin
    context.fresh <- context.fresh + 1;
    let symbols =
      List.mapi
        (fun index _ -> Symbol.Variable { label = "law"; numbers = [ context.fresh; index ] })
        types
    in
    let inside =
      law_frame
        { frame with bound = symbols @ frame.bound; condition = Logic.Boolean true }
        source ~substitution law
        (List.map (fun symbol -> Logic.Symbol symbol) symbols)
    in
    try
      let premise =
        Logic.conjunction
          (List.map
             (fun clause -> snd (Validity.specification_value context inside clause))
             law.requires)
      in
      let range =
        Logic.conjunction
          (List.map2 (fun symbol ty -> Facts.in_range ty (Logic.Symbol symbol)) symbols types)
      in
      let _, holds = Validity.specification_value context inside law.states in
      Some
        (Logic.forall
           ( List.map2 (fun symbol ty -> (symbol, Facts.sort_of context ty)) symbols types,
             Logic.( ==> ) (Logic.( &&& ) range premise) holds ))
    with Facts.Unsupported _ | Facts.Foreign_unsupported _ -> None
  end

let assume_laws (context : State.context) frame ~at (trait : Types.trait_reference) (ty : Types.ty)
    =
  let key = (trait, ty) in
  if not (List.mem key context.laws_assumed) then begin
    context.laws_assumed <- key :: context.laws_assumed;
    List.iter
      (fun path ->
        let required =
          if Path.equal path trait.trait then trait
          else { Types.trait = path; trait_arguments = []; associated = [] }
        in
        let substitution = Contracts.trait_substitution context.lookups required ty in
        let impl = Option.map fst (Operations.concrete_impl context required ty) in
        List.iter
          (fun (source, (law : Mir.law)) ->
            match law_fact context frame source ~substitution law with
            | Some fact_ ->
                (match impl with
                | Some impl when Contracts.law_unshown context.lookups impl required ty law.name ->
                    context.holes <- (context.home, at) :: context.holes
                | _ -> ());
                Facts.fact context frame fact_
            | None -> ())
          (laws_of context path))
      (Mir.Call_edges.traits_with_required context.lookups.interface trait.trait)
  end

let template_trait : Path.t = Well_known.path From_template

let signature_terminates (context : State.context) path =
  match Interface.Impls.read_signature context.lookups.interface path with
  | Some (signature : Types.signature) -> signature.terminates
  | None -> true

let keeps_cost context path (contract : State.contract) (asked : Types.cost) =
  let constant = Contracts.literal in
  let same (cost : Mir.cost) =
    match (asked.resource, cost.resource) with
    | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
    | _ -> false
  in
  match asked with
  | { resource = Time; bound = Finite_cost; _ } -> signature_terminates context path
  | { resource = Calls _; _ } -> false
  | _ -> (
      match
        List.find_map
          (fun (part : State.part) ->
            List.find_map (fun cost -> if same cost then Some cost else None) part.costs)
          contract.parts
      with
      | Some cost -> (
          match (asked.bound, cost.bound) with
          | Order_of, (Order_of value | At_most value | Exactly value) -> constant value <> None
          | No_more_than (Some most), (At_most value | Exactly value) -> (
              match constant value with Some limit -> Z.leq limit most | None -> false)
          | Exactly_cost (Some exact), Exactly value -> constant value = Some exact
          | _ -> false)
      | None -> false)

let check_named_callback context (frame : State.frame) (invocation : Invocation.t)
    (passed : State.passed) ~origin path (contract : State.contract) (values : State.passed list) =
  let location = Facts.locate context frame.source origin in
  let own = List.hd contract.parts in
  match Validity.parameter_type context frame invocation passed.position with
  | Some (Types.Function expected) ->
      let inputs = Validity.callback_arguments context frame expected.inputs in
      let known = List.map (fun (passed : State.passed) -> (passed.position, passed.term)) values in
      let promised =
        Logic.conjunction
          (Validity.callback_facts context frame invocation passed.position known inputs)
      in
      let at_call = Facts.restrict frame promised in
      (if List.length own.parameters = List.length inputs then
         let inside =
           Validity.part_frame frame own
             ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
             ~substitution:[]
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
               (snd (Validity.specification_value context inside requirement)))
           (Facts.clauses own.requires));
      List.iter
        (fun (cost : Types.cost) ->
          if not (keeps_cost context path contract cost) then
            Facts.oblige context frame Cost location
              [
                Text
                  (Printf.sprintf
                     "`%s` does not promise the contract this parameter's type, `%s`, asks of a \
                      function passed for it."
                     (Path.show path)
                     (Types.show (Types.Function expected)));
              ]
              (Logic.Boolean false))
        expected.costs
  | _ ->
      if own.requires <> [] || own.costs <> [] then
        Facts.unsupported location
          "a function passed for a parameter whose type the prover cannot read"
