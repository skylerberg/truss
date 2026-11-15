let visible_packages (lookups : Lookups.t) (package : Path.package) =
  List.sort_uniq compare
    (Path.standard_package :: package :: lookups.interface.names.dependency_names package)

let own_methods (lookups : Lookups.t) owner name =
  List.filter_map
    (fun (key : Resolve.Names.key) ->
      match key.path with Method { receiver; _ } -> Some (receiver, key.path) | _ -> None)
    (lookups.interface.names.members owner name)

let own_constant (lookups : Lookups.t) owner name =
  List.find_map
    (fun (key : Resolve.Names.key) ->
      match key.path with Member_constant _ -> Some key.path | _ -> None)
    (lookups.interface.names.members owner name)

let trait_methods (lookups : Lookups.t) trait name =
  match Interface.Definition.trait_interface lookups.interface trait with
  | Some interface ->
      List.filter
        (fun (method_ : Types.trait_method) -> method_.method_name = name)
        interface.methods
  | None -> []

let trait_method lookups trait name receiver =
  List.find_opt
    (fun (method_ : Types.trait_method) -> method_.method_receiver = receiver)
    (trait_methods lookups trait name)

let fields (lookups : Lookups.t) path arguments =
  Option.bind (Interface.Definition.type_interface lookups.interface path) (fun interface ->
      Types.fields_of interface arguments)

let variants (lookups : Lookups.t) path arguments =
  Option.bind (Interface.Definition.type_interface lookups.interface path) (fun interface ->
      Types.variants_of interface arguments)

let fields_visible (lookups : Lookups.t) ~package (path : Path.t) =
  match Interface.Definition.type_interface lookups.interface path with
  | Some { opaque = true; _ } -> Path.package path = package
  | _ -> true

let method_signature (lookups : Lookups.t) trait method_ =
  Interface.Definition.method_signature lookups.interface ~owner:trait method_
