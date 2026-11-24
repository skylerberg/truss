let resolve_capability (names : Resolve.Names.lookups) ~package (capability : Grant.capability) :
    Path.t option =
  let find_visible_capability (module_ : Path.module_) name =
    if not (Resolve.Names.is_visible_module names ~from:{ package; modules = [] } module_) then None
    else
      match names.find module_ name with
      | Some { kind = Capability; visibility; _ }
        when Resolve.Names.is_visible_to_package ~package module_ visibility ->
          Some (Path.Top { module_; name })
      | _ -> None
  in
  match capability with
  | Prelude name -> find_visible_capability Grant.prelude_capability_module name
  | Full_path { module_names; name } ->
      Option.bind (names.split_module module_names) (fun module_ ->
          find_visible_capability module_ name)

let resolve_grant names ~package capabilities : Environment.grant =
  let resolved =
    List.map
      (fun capability -> (capability, resolve_capability names ~package capability))
      capabilities
  in
  {
    capabilities = List.filter_map snd resolved;
    unknown =
      List.filter_map
        (fun (capability, path) -> if path = None then Some capability else None)
        resolved;
  }

let needs_grant ~package ~of_ = of_ <> package && of_ <> Path.standard_package

let list_missing (lookups : Lookups.t) ~package ~of_ (uses : Types.capability_set) =
  if not (needs_grant ~package ~of_) then []
  else
    let granted =
      match lookups.find_grant package of_ with Some grant -> grant.capabilities | None -> []
    in
    List.filter
      (fun path -> not (List.exists (Path.equal path) granted))
      (List.filter_map
         (function
           | Types.Built_in builtin_capability ->
               Some (Well_known.make_builtin_capability_path builtin_capability)
           | Capability path -> Some path
           | Capability_parameter _ | Capability_projection _ | Capability_variable _
           | Capability_error _ ->
               None
           | Capability_unless _ | Capability_unless_values _ ->
               Compiler_bug.raise_bug ~stage:"Interface" "a capability's base has a condition")
         (List.map Types.find_base (Types.list_capabilities uses)))

let rec list_evidence_uses lookups ~list_bounds (evidence : Impls.solution) =
  match evidence with
  | Evidence (Impl { impl; substitution }) -> (
      match Definition.find_impl_interface lookups impl with
      | None -> []
      | Some interface ->
          ( impl,
            interface,
            List.fold_left
              (fun uses (name, receiver) ->
                match Impls.read_signature lookups (Method { owner = impl; name; receiver }) with
                | Some signature -> Types.union_capabilities uses signature.uses
                | None -> uses)
              interface.impl_uses interface.impl_methods )
          :: List.concat_map
               (fun (argument, bound) ->
                 match Impls.find_evidence lookups ~list_bounds argument bound with
                 | Some nested -> list_evidence_uses lookups ~list_bounds nested
                 | None -> [])
               (Impls.list_required_bounds interface.impl_generics substitution))
  | _ -> []

let list_missing_in_impls lookups ~package impls =
  List.concat_map
    (fun (impl, (interface : Types.impl_interface), uses) ->
      let of_ = Path.locate_package impl in
      List.map
        (fun capability -> (interface, of_, capability))
        (list_missing lookups ~package ~of_ uses))
    impls
