module Names = Resolve.Names

let resolve_capability (lookups : Lookups.t) ~package written : Path.t option =
  let visible_capability (module_ : Path.module_) name =
    if not (Names.is_visible_module lookups.names ~from:{ package; modules = [] } module_) then None
    else
      match lookups.names.find module_ name with
      | Some { kind = Capability; visibility; _ }
        when module_.package = package || Names.is_public visibility ->
          Some (Path.Top { module_; name })
      | _ -> None
  in
  match Option.map List.rev (Path.parse_names written) with
  | Some [ name ] ->
      Option.bind (Resolve.Prelude.find_type name) (fun module_ -> visible_capability module_ name)
  | Some (name :: modules) -> (
      match lookups.names.split_module (List.rev modules) with
      | Some module_ -> visible_capability module_ name
      | None -> None)
  | Some [] | None -> None

let show_as_written (path : Path.t) =
  match path with
  | Top { module_; name } when Resolve.Prelude.find_type name = Some module_ -> name
  | _ -> Path.show path

let resolve_grant lookups ~package written_capabilities : Environment.grant =
  let resolved =
    List.map (fun name -> (name, resolve_capability lookups ~package name)) written_capabilities
  in
  {
    capabilities = List.filter_map snd resolved;
    unknown = List.filter_map (fun (name, path) -> if path = None then Some name else None) resolved;
  }

let describe_not_a_capability ~dependency name =
  Printf.sprintf
    "`%s`, in the entry for `%s`, names no capability. A grant names a capability of the prelude \
     by its name, such as `Clock`, and any other by its full path."
    name (Path.show_package dependency)

let list_missing (lookups : Lookups.t) ~package ~of_ (uses : Types.capability_set) =
  if of_ = package || of_ = Path.standard_package then []
  else
    let granted =
      match lookups.granted package of_ with Some grant -> grant.capabilities | None -> []
    in
    List.filter_map
      (function
        | Types.Capability path when not (List.exists (Path.equal path) granted) -> Some path
        | _ -> None)
      (uses :> Types.capability list)

let describe_missing ~subject ~of_ capability =
  let of_ = Path.show_package of_ in
  Printf.sprintf
    "%s uses `%s`, which the manifest does not grant `%s`. To grant it, add \"%s\" to the entry \
     for `%s` in `truss.toml`."
    subject (show_as_written capability) of_ (show_as_written capability) of_

let rec list_evidence_uses lookups ~bounds ?(depth = 0) (evidence : Impls.evidence) =
  match evidence with
  | From_impl { impl; substitution } when depth < 16 -> (
      match Impls.impl_interface lookups impl with
      | None -> []
      | Some interface ->
          ( impl,
            interface,
            List.fold_left
              (fun uses (name, receiver) ->
                match Impls.signature lookups (Method { owner = impl; name; receiver }) with
                | Some signature -> Types.capability_union uses signature.uses
                | None -> uses)
              interface.impl_uses interface.impl_methods )
          :: List.concat_map
               (fun (argument, bound) ->
                 match Impls.implements lookups ~bounds argument bound with
                 | Some nested -> list_evidence_uses lookups ~bounds ~depth:(depth + 1) nested
                 | None -> [])
               (Impls.required interface.impl_generics substitution))
  | _ -> []

let describe_missing_in_impls lookups ~package impls =
  List.concat_map
    (fun (impl, (interface : Types.impl_interface), uses) ->
      let of_ = Path.package impl in
      List.map
        (describe_missing
           ~subject:
             (Printf.sprintf "The `impl` of `%s` for `%s`"
                (Types.show_trait interface.implements)
                (Types.show interface.for_type))
           ~of_)
        (list_missing lookups ~package ~of_ uses))
    impls

let describe_missing_in_evidence lookups ~package ~bounds evidence =
  describe_missing_in_impls lookups ~package (list_evidence_uses lookups ~bounds evidence)
