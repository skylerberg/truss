let is_in_recursion_group (context : State.context) node =
  let is_inherited_from declaration member =
    match context.lookups.mir.find_form_origin member with
    | Some (Inherited key, _) -> Path.equal key.path declaration
    | Some ((Written _ | Derived _), _) | None -> false
  in
  List.exists (Path.equal node) (context.lookups.list_recursion_group context.node)
  ||
  match context.node with
  | Method { owner; _ }
    when Option.is_some (Interface.Definition.find_trait_interface context.lookups.interface owner)
    ->
      List.exists (is_inherited_from context.node) (context.lookups.list_recursion_group node)
  | _ -> false

let find_group_member (context : State.context) (frame : State.frame) callee =
  match
    (Mir.Call_edges.resolve_callee context.lookups.interface frame.substitution callee).target
  with
  | Some target when is_in_recursion_group context target -> Some target
  | Some _ | None -> None

let is_constant_expression (code : Mir.t) =
  let is_made_for_a_literal : Mir.operand Core.target -> bool = function
    | Function { path; _ } -> Path.equal path (Well_known.make_method_path List_from_storage)
    | Trait_method { trait; _ } ->
        Path.equal trait.trait (Well_known.make_path From_elements)
        || Path.equal trait.trait (Well_known.make_path From_entries)
    | Intrinsic _ -> true
    | Capability_method _ | Indirect _ -> false
  in
  let calls_function = ref false in
  Mir.iter_code
    (fun statement ->
      match Mir.find_callee statement with
      | Some callee when not (is_made_for_a_literal callee.target) -> calls_function := true
      | Some _ | None -> ())
    code;
  not !calls_function

let is_evaluated_constant (context : State.context) path code =
  (not (is_constant_expression code))
  && context.lookups.list_recursion_group path = []
  && Option.is_none
       (Types.find_specification_only_type
          (Interface.Definition.read_constant_type context.lookups.interface path))

let make_catalog_dependency (dependency : Mir.Call_edges.dependency) : Catalog.Prover.dependency =
  {
    kind = (match dependency.kind with Read -> Reads | Direct_call -> Calls | Supplied _ -> Uses);
    path = dependency.path;
    omitted =
      Option.map
        (fun (omitted : Mir.Call_edges.omitted) : Catalog.Prover.omitted ->
          match omitted with
          | Field field -> Omitted_field field
          | Argument parameter -> Omitted_argument parameter)
        dependency.omitted;
  }

let reject_constant_cycle (context : State.context) (frame : State.frame) (code : Mir.t) =
  if context.lookups.list_recursion_group context.node <> [] then
    List.iter
      (fun (dependency : Mir.Call_edges.dependency) ->
        if is_in_recursion_group context dependency.path then
          Facts.oblige context frame (Node dependency.origin)
            (Constant_cycle
               { cyclic = context.node; dependency = make_catalog_dependency dependency })
            (Logic.Boolean false))
      (Mir.Call_edges.list_dependencies
         { interface = context.lookups.interface; mir = context.lookups.mir }
         Types.no_substitution code)

type circular_proof = { location : Obligation.location; proof : Catalog.Prover.circular_proof }

let is_in_proof_cycle (context : State.context) path =
  List.exists (Path.equal path) (context.lookups.list_proof_group context.node)
  && not (is_in_recursion_group context path)

let has_proof_cycle (context : State.context) =
  List.exists
    (fun member -> not (is_in_recursion_group context member))
    (context.lookups.list_proof_group context.node)

let list_circular_dependencies context ~make_proof dependencies =
  List.filter_map
    (fun (dependency : Mir.Call_edges.dependency) ->
      if is_in_proof_cycle context dependency.path then
        Some
          {
            location = Obligation.Node dependency.origin;
            proof = make_proof (make_catalog_dependency dependency);
          }
      else None)
    dependencies

let list_circular_instance_uses (context : State.context) (frame : State.frame) lookups =
  let reported = ref [] in
  List.filter_map
    (fun (instance : Mir.Call_edges.instance_use) ->
      match List.find_opt (is_in_proof_cycle context) instance.dependencies with
      | Some dependency when not (List.exists (Path.equal dependency) !reported) ->
          reported := dependency :: !reported;
          Some
            {
              location =
                (match instance.used.origin with
                | Some origin -> Facts.locate context frame.source origin
                | None -> Whole_definition);
              proof =
                Circular_instance { type_ = instance.used.type_; dependency; cyclic = context.node };
            }
      | Some _ | None -> None)
    (Mir.Call_edges.list_instance_uses lookups context.node)

let list_impls_of_required_traits (context : State.context) =
  match Interface.Definition.find_impl_interface context.lookups.interface context.node with
  | Some impl ->
      List.filter_map
        (fun required -> Option.map fst (Facts.find_impl context required impl.for_type))
        (Interface.Properties.list_bound_closure context.lookups.interface ~self:impl.for_type
           impl.implements)
  | None -> []

let list_circular_laws (context : State.context) (frame : State.frame) =
  let lookups : Mir.Call_edges.lookups =
    { interface = context.lookups.interface; mir = context.lookups.mir }
  in
  let required = list_impls_of_required_traits context in
  List.filter_map
    (fun (laws : Mir.Call_edges.assumed_laws) ->
      if is_in_proof_cycle context laws.impl && not (List.exists (Path.equal laws.impl) required)
      then
        Some
          {
            location =
              (match laws.origin with
              | Some origin -> Facts.locate context frame.source origin
              | None -> Whole_definition);
            proof = Circular_laws { trait = laws.trait; type_ = laws.type_ };
          }
      else None)
    (Mir.Call_edges.list_assumed_laws lookups context.node)

let list_circular_clauses (context : State.context) frame ~type_ =
  let lookups : Mir.Call_edges.lookups =
    { interface = context.lookups.interface; mir = context.lookups.mir }
  in
  let make_proof clause dependency : Catalog.Prover.circular_proof =
    Circular_clause { clause; type_; dependency }
  in
  if has_proof_cycle context then
    list_circular_dependencies context ~make_proof:(make_proof Invariant_clause)
      (Mir.Call_edges.list_invariant_dependencies lookups context.node)
    @ list_circular_dependencies context ~make_proof:(make_proof Potential_clause)
        (Mir.Call_edges.list_potential_dependencies lookups context.node)
    @ list_circular_instance_uses context frame lookups
  else []

let has_circular_clause lookups group member =
  List.exists
    (fun (dependency : Mir.Call_edges.dependency) -> List.exists (Path.equal dependency.path) group)
    (Mir.Call_edges.list_invariant_dependencies lookups member
    @ Mir.Call_edges.list_potential_dependencies lookups member)

let list_circular_contracts (context : State.context) frame =
  if not (has_proof_cycle context) then []
  else
    let lookups : Mir.Call_edges.lookups =
      { interface = context.lookups.interface; mir = context.lookups.mir }
    in
    let written = Mir.Call_edges.list_contract_dependencies lookups context.node in
    let is_written (inherited : Mir.Call_edges.dependency) =
      List.exists
        (fun (dependency : Mir.Call_edges.dependency) -> Path.equal dependency.path inherited.path)
        written
    in
    match
      list_circular_dependencies context
        ~make_proof:(fun dependency -> Circular_contract { cyclic = context.node; dependency })
        written
      @ List.map
          (fun (circular : circular_proof) -> { circular with location = Whole_definition })
          (list_circular_dependencies context
             ~make_proof:(fun dependency ->
               Circular_inherited_contract { cyclic = context.node; dependency })
             (List.filter
                (fun inherited -> not (is_written inherited))
                (Mir.Call_edges.list_inherited_contract_dependencies lookups context.node)))
      @ list_circular_instance_uses context frame lookups
    with
    | [] -> []
    | circular ->
        let group = context.lookups.list_proof_group context.node in
        if List.exists (has_circular_clause lookups group) group then [] else circular

let reject_circular_proof context frame (circular : circular_proof) =
  Facts.oblige context frame circular.location (Circular_proof circular.proof) (Logic.Boolean false)
