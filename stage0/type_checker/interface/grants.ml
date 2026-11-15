module Names = Resolve.Names

let capability (lookups : Lookups.t) ~package written : Path.t option =
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

let written (path : Path.t) =
  match path with
  | Top { module_; name } when Resolve.Prelude.find_type name = Some module_ -> name
  | _ -> Path.show path

let grant lookups ~package (entry : Manifest.dependency) : Environment.grant =
  let resolved_entries =
    List.map (fun name -> (name, capability lookups ~package name)) entry.capabilities
  in
  {
    capabilities = List.filter_map snd resolved_entries;
    unknown =
      List.filter_map (fun (name, path) -> if path = None then Some name else None) resolved_entries;
  }

let missing (lookups : Lookups.t) ~package ~of_ (uses : Types.capability_set) =
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

let message ~subject ~of_ capability =
  let of_ = Path.show_package of_ in
  Printf.sprintf
    "%s uses `%s`, which the manifest does not grant `%s`. To grant it, add \"%s\" to the entry \
     for `%s` in `truss.toml`."
    subject (written capability) of_ (written capability) of_

let rec evidence_uses lookups ~bounds ?(depth = 0) (evidence : Impls.evidence) =
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
                 | Some nested -> evidence_uses lookups ~bounds ~depth:(depth + 1) nested
                 | None -> [])
               (Impls.required interface.impl_generics substitution))
  | _ -> []

let messages lookups ~package impls =
  List.concat_map
    (fun (impl, (interface : Types.impl_interface), uses) ->
      let of_ = Path.package impl in
      List.map
        (message
           ~subject:
             (Printf.sprintf "The `impl` of `%s` for `%s`"
                (Types.show_trait interface.implements)
                (Types.show interface.for_type))
           ~of_)
        (missing lookups ~package ~of_ uses))
    impls

let evidence_messages lookups ~package ~bounds evidence =
  messages lookups ~package (evidence_uses lookups ~bounds evidence)
