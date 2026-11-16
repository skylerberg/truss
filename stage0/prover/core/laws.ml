open Core
open State
open Facts
open Contracts
open Validity
open Operations

let check_callback_requires context frame (site : Invocation.site) through (values : passed list) =
  match through with
  | Some (_, _, Invocation.Forwarded local) -> (
      match own_callback context local with
      | Some (name, { inputs; requires }) when List.length inputs = List.length values ->
          let inside =
            callback_contract_frame frame inputs
              (List.map (fun (passed : passed) -> passed.term) values)
          in
          List.iter
            (fun (clause : Mir.formula) ->
              oblige context frame Requires
                (locate context frame.source site.origin)
                [
                  Text "`";
                  quote frame.source clause.origin;
                  Text (Printf.sprintf "` may not hold for this call through `%s`." name);
                ]
                (snd (specification_value context inside clause)))
            requires
      | _ -> ())
  | _ -> ()

let calls_updating_helper context (invocation : Invocation.t) =
  match invocation.callee with
  | Function { path; _ } -> is_updating_helper context.lookups path
  | _ -> false

let laws_of context trait =
  match context.lookups.interface.names.key trait with
  | Some key ->
      let source = source_at_key context.lookups key in
      List.map (fun (law : Mir.law) -> (source, law)) (context.lookups.mir.contract_part key).laws
  | None -> []

let law_parameter_types ~substitution (law : Mir.law) =
  List.map (fun (_, type_) -> Types.substitute substitution type_) law.parameters

let law_frame frame source ~substitution (law : Mir.law) terms =
  let types = law_parameter_types ~substitution law in
  let locals, types =
    List.fold_left2
      (fun (locals, types_) ((local, _), ty) term ->
        (Locals.add local term locals, Locals.add local ty types_))
      (Locals.empty, Locals.empty)
      (List.combine law.parameters types)
      terms
  in
  {
    frame with
    source;
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

let law_fact context frame source ~substitution (law : Mir.law) =
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
          (List.map (fun clause -> snd (specification_value context inside clause)) law.requires)
      in
      let range =
        Logic.conjunction
          (List.map2 (fun symbol ty -> in_range ty (Logic.Symbol symbol)) symbols types)
      in
      let _, holds = specification_value context inside law.states in
      Some
        (Logic.forall
           ( List.map2 (fun symbol ty -> (symbol, sort_of context ty)) symbols types,
             Logic.( ==> ) (Logic.( &&& ) range premise) holds ))
    with Unsupported _ | Foreign_unsupported _ -> None
  end

let assume_laws context frame ~at (trait : Types.trait_reference) (ty : Types.ty) =
  let key = (trait, ty) in
  if not (List.mem key context.laws_assumed) then begin
    context.laws_assumed <- key :: context.laws_assumed;
    List.iter
      (fun path ->
        let required =
          if Path.equal path trait.trait then trait
          else { Types.trait = path; trait_arguments = []; associated = [] }
        in
        let substitution = trait_substitution context.lookups required ty in
        let impl = Option.map fst (concrete_impl context required ty) in
        List.iter
          (fun (source, (law : Mir.law)) ->
            match law_fact context frame source ~substitution law with
            | Some fact_ ->
                (match impl with
                | Some impl when law_unshown context.lookups impl required ty law.name ->
                    context.holes <- (context.home, at) :: context.holes
                | _ -> ());
                fact context frame fact_
            | None -> ())
          (laws_of context path))
      (Mir.Call_edges.traits_with_required context.lookups.interface trait.trait)
  end

let template_trait : Path.t = Well_known.path From_template

let signature_terminates context path =
  match Interface.Impls.read_signature context.lookups.interface path with
  | Some (signature : Types.signature) -> signature.terminates
  | None -> true

let keeps_cost context path (contract : contract) (asked : Types.cost) =
  let constant = literal in
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
          (fun (part : part) ->
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

let check_named_callback context frame (invocation : Invocation.t) (passed : passed) ~origin path
    (contract : contract) (values : passed list) =
  let location = locate context frame.source origin in
  let own = List.hd contract.parts in
  match parameter_type context frame invocation passed.position with
  | Some (Types.Function expected) ->
      let inputs = callback_arguments context frame expected.inputs in
      let known = List.map (fun (passed : passed) -> (passed.position, passed.term)) values in
      let promised =
        Logic.conjunction (callback_facts context frame invocation passed.position known inputs)
      in
      let at_call = restrict frame promised in
      (if List.length own.parameters = List.length inputs then
         let inside =
           part_frame frame own
             ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
             ~substitution:[]
         in
         List.iter
           (fun (requirement : Mir.formula) ->
             oblige context at_call Requires location
               [
                 Text
                   (Printf.sprintf
                      "`%s` may not accept every argument this parameter's type promises it: its `"
                      (Path.show path));
                 quote own.callee requirement.origin;
                 Text "` may not hold.";
               ]
               (snd (specification_value context inside requirement)))
           (clauses own.requires));
      List.iter
        (fun (cost : Types.cost) ->
          if not (keeps_cost context path contract cost) then
            oblige context frame Cost location
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
        unsupported location "a function passed for a parameter whose type the prover cannot read"
