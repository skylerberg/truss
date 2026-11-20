let resolve_capability (names : Resolve.Names.lookups) ~package (capability : Grant.capability) :
    Path.t option =
  let find_visible_capability (module_ : Path.module_) name =
    if not (Resolve.Names.is_visible_module names ~from:{ package; modules = [] } module_) then None
    else
      match names.find module_ name with
      | Some { kind = Capability; visibility; _ }
        when module_.package = package || Resolve.Names.is_public visibility ->
          Some (Path.Top { module_; name })
      | _ -> None
  in
  match capability with
  | Prelude name -> find_visible_capability Grant.prelude_capability_module name
  | Full_path { module_names; name } ->
      Option.bind (names.split_module module_names) (fun module_ ->
          find_visible_capability module_ name)

let show_as_written : Path.t -> string = function
  | Top { module_; name } ->
      Grant.show_capability
        (Grant.make_capability ~module_names:(Path.list_module_parts module_) name)
  | path ->
      Compiler_bug.raise_bug ~stage:"Interface" "the capability %s is not a definition of a module"
        (Path.show path)

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

let describe_not_a_capability ~dependency capability =
  Printf.sprintf
    "`%s`, in the entry for `%s`, names no capability. A grant names a capability of the prelude \
     by its name, such as `Clock`, and any other by its full path."
    (Grant.show_capability capability)
    (Path.show_package dependency)

let list_missing (lookups : Lookups.t) ~package ~of_ (uses : Types.capability_set) =
  if of_ = package || of_ = Path.standard_package then []
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

let describe_missing ~subject ~of_ capability =
  let of_ = Path.show_package of_ in
  Printf.sprintf
    "%s uses `%s`, which the manifest does not grant `%s`. To grant it, add \"%s\" to the entry \
     for `%s` in `truss.toml`."
    subject (show_as_written capability) of_ (show_as_written capability) of_

let rec list_evidence_uses lookups ~list_bounds (evidence : Impls.evidence) =
  match evidence with
  | From_impl { impl; substitution } -> (
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

let describe_missing_in_impls lookups ~package impls =
  List.concat_map
    (fun (impl, (interface : Types.impl_interface), uses) ->
      let of_ = Path.locate_package impl in
      List.map
        (describe_missing
           ~subject:
             (Printf.sprintf "The `impl` of `%s` for `%s`"
                (Types.show_trait interface.implements)
                (Types.show interface.for_type))
           ~of_)
        (list_missing lookups ~package ~of_ uses))
    impls
