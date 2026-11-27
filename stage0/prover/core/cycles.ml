let is_in_recursion_group (environment : State.environment) node =
  let is_inherited_from declaration member =
    match environment.lookups.mir.find_form_origin member with
    | Some (Inherited key, _) -> Path.equal key.path declaration
    | Some ((Written _ | Derived _), _) | None -> false
  in
  List.exists (Path.equal node) (environment.lookups.list_recursion_group environment.node)
  ||
  match environment.node with
  | Method { owner; _ }
    when Option.is_some
           (Interface.Definition.find_trait_interface environment.lookups.interface owner) ->
      List.exists
        (is_inherited_from environment.node)
        (environment.lookups.list_recursion_group node)
  | _ -> false

let find_group_member (frame : State.frame) callee =
  match
    (Mir.Call_edges.resolve_callee frame.environment.lookups.interface frame.substitution callee)
      .target
  with
  | Some target when is_in_recursion_group frame.environment target -> Some target
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

let is_evaluated_constant (environment : State.environment) path code =
  (not (is_constant_expression code))
  && environment.lookups.list_recursion_group path = []
  && Option.is_none
       (Types.find_specification_only_type
          (Interface.Definition.read_constant_type environment.lookups.interface path))

let make_catalog_dependency (environment : State.environment)
    (dependency : Mir.Call_edges.dependency) : Catalog.Prover.dependency =
  {
    kind = (match dependency.kind with Read -> Reads | Direct_call -> Calls | Supplied _ -> Uses);
    path = dependency.path;
    omitted =
      Option.map
        (fun (default : Path.t) : Catalog.Prover.omitted ->
          match default with
          | Default { owner; variant = None; name }
            when Option.is_none
                   (Interface.Definition.find_type_interface environment.lookups.interface owner) ->
              Omitted_argument name
          | _ -> Omitted_field (Path.show_name default))
        dependency.default;
  }

let reject_constant_cycle (frame : State.frame) ~is_constant (code : Mir.t) =
  let environment = frame.environment in
  if environment.lookups.list_recursion_group environment.node <> [] then
    List.iter
      (fun (dependency : Mir.Call_edges.dependency) ->
        let reject cyclic =
          Obligations.oblige frame (Node dependency.origin)
            (Constant_cycle { cyclic; dependency = make_catalog_dependency environment dependency })
            (Logic.Boolean false)
        in
        match
          (is_in_recursion_group environment dependency.path, is_constant, dependency.default)
        with
        | true, true, _ -> reject environment.node
        | true, false, Some default -> reject default
        | true, false, None | false, _, _ -> ())
      (Mir.Call_edges.list_dependencies
         { interface = environment.lookups.interface; mir = environment.lookups.mir }
         ~home:(Path.locate_package environment.node)
         Types.no_substitution code)

type circular_proof = { location : Obligation.location; proof : Catalog.Prover.circular_proof }

let is_in_proof_cycle (environment : State.environment) path =
  List.exists (Path.equal path) (environment.lookups.list_proof_group environment.node)
  && not (is_in_recursion_group environment path)

let has_proof_cycle (environment : State.environment) =
  List.exists
    (fun member -> not (is_in_recursion_group environment member))
    (environment.lookups.list_proof_group environment.node)

let list_circular_dependencies (environment : State.environment) ~make_proof dependencies =
  List.filter_map
    (fun (dependency : Mir.Call_edges.dependency) ->
      if is_in_proof_cycle environment dependency.path then
        Some
          {
            location = Obligation.Node dependency.origin;
            proof = make_proof (make_catalog_dependency environment dependency);
          }
      else None)
    dependencies

let list_circular_instance_uses (frame : State.frame) lookups =
  let reported = ref [] in
  List.filter_map
    (fun (instance : Mir.Call_edges.instance_use) ->
      match List.find_opt (is_in_proof_cycle frame.environment) instance.dependencies with
      | Some dependency when not (List.exists (Path.equal dependency) !reported) ->
          reported := dependency :: !reported;
          Some
            {
              location =
                (match instance.used.origin with
                | Some origin -> Facts.locate frame origin
                | None -> Whole_definition);
              proof =
                Circular_instance
                  { type_ = instance.used.type_; dependency; cyclic = frame.environment.node };
            }
      | Some _ | None -> None)
    (Mir.Call_edges.list_instance_uses lookups frame.environment.node)

let list_impls_of_required_traits (environment : State.environment) =
  match Interface.Definition.find_impl_interface environment.lookups.interface environment.node with
  | Some impl ->
      List.filter_map
        (fun required -> Option.map fst (Encoding.find_impl environment required impl.for_type))
        (Interface.Properties.list_bound_closure environment.lookups.interface ~self:impl.for_type
           impl.implements)
  | None -> []

let proves_laws (environment : State.environment) =
  match Interface.Definition.find_interface environment.lookups.interface environment.node with
  | Some (Interface.Environment.Law_proof_interface _) -> true
  | Some _ | None ->
      Option.is_some
        (Interface.Definition.find_impl_interface environment.lookups.interface environment.node)

let list_circular_laws (frame : State.frame) =
  let lookups : Mir.Call_edges.lookups =
    { interface = frame.environment.lookups.interface; mir = frame.environment.lookups.mir }
  in
  let required = list_impls_of_required_traits frame.environment in
  let assumes_its_own = proves_laws frame.environment in
  List.filter_map
    (fun (laws : Mir.Call_edges.assumed_laws) ->
      if
        is_in_proof_cycle frame.environment laws.impl
        && (laws.is_assumed_by_the_callee
           || (assumes_its_own && not (List.exists (Path.equal laws.impl) required)))
      then
        Some
          {
            location =
              (match laws.origin with
              | Some origin -> Facts.locate frame origin
              | None -> Whole_definition);
            proof = Circular_laws { trait = laws.trait; type_ = laws.type_ };
          }
      else None)
    (Mir.Call_edges.list_assumed_laws lookups frame.environment.node)

let list_circular_clauses (frame : State.frame) ~type_ =
  let lookups : Mir.Call_edges.lookups =
    { interface = frame.environment.lookups.interface; mir = frame.environment.lookups.mir }
  in
  let make_proof clause dependency : Catalog.Prover.circular_proof =
    Circular_clause { clause; type_; dependency }
  in
  if has_proof_cycle frame.environment then
    list_circular_dependencies frame.environment ~make_proof:(make_proof Invariant_clause)
      (Mir.Call_edges.list_invariant_dependencies lookups frame.environment.node)
    @ list_circular_dependencies frame.environment ~make_proof:(make_proof Potential_clause)
        (Mir.Call_edges.list_potential_dependencies lookups frame.environment.node)
    @ list_circular_instance_uses frame lookups
  else []

let has_circular_clause lookups group member =
  List.exists
    (fun (dependency : Mir.Call_edges.dependency) -> List.exists (Path.equal dependency.path) group)
    (Mir.Call_edges.list_invariant_dependencies lookups member
    @ Mir.Call_edges.list_potential_dependencies lookups member)

let list_circular_contracts (frame : State.frame) =
  if not (has_proof_cycle frame.environment) then []
  else
    let lookups : Mir.Call_edges.lookups =
      { interface = frame.environment.lookups.interface; mir = frame.environment.lookups.mir }
    in
    let written = Mir.Call_edges.list_contract_dependencies lookups frame.environment.node in
    let is_written (inherited : Mir.Call_edges.dependency) =
      List.exists
        (fun (dependency : Mir.Call_edges.dependency) -> Path.equal dependency.path inherited.path)
        written
    in
    match
      list_circular_dependencies frame.environment
        ~make_proof:(fun dependency ->
          Circular_contract { cyclic = frame.environment.node; dependency })
        written
      @ List.map
          (fun (circular : circular_proof) -> { circular with location = Whole_definition })
          (list_circular_dependencies frame.environment
             ~make_proof:(fun dependency ->
               Circular_inherited_contract { cyclic = frame.environment.node; dependency })
             (List.filter
                (fun inherited -> not (is_written inherited))
                (Mir.Call_edges.list_inherited_contract_dependencies lookups frame.environment.node)))
      @ list_circular_instance_uses frame lookups
    with
    | [] -> []
    | circular ->
        let group = frame.environment.lookups.list_proof_group frame.environment.node in
        if List.exists (has_circular_clause lookups group) group then [] else circular

let list_circular_proofs (frame : State.frame) =
  list_circular_laws frame
  @ if proves_laws frame.environment then [] else list_circular_contracts frame

let reject_circular_proof frame (circular : circular_proof) =
  Obligations.oblige frame circular.location (Circular_proof circular.proof) (Logic.Boolean false)
