let list_own_methods (lookups : Lookups.t) owner name =
  List.filter_map
    (fun (key : Resolve.Names.key) ->
      match key.path with Method { receiver; _ } -> Some (receiver, key.path) | _ -> None)
    (lookups.interface.names.list_members owner name)

let find_own_constant (lookups : Lookups.t) owner name =
  List.find_map
    (fun (key : Resolve.Names.key) ->
      match key.path with Member_constant _ -> Some key.path | _ -> None)
    (lookups.interface.names.list_members owner name)

let list_trait_methods (lookups : Lookups.t) trait name =
  match Interface.Definition.read_trait_interface lookups.interface trait with
  | Some interface ->
      List.filter
        (fun (method_ : Types.trait_method) -> method_.method_name = name)
        interface.methods
  | None -> []

let find_trait_method lookups trait name receiver =
  List.find_opt
    (fun (method_ : Types.trait_method) -> method_.method_receiver = receiver)
    (list_trait_methods lookups trait name)

let find_fields (lookups : Lookups.t) path arguments =
  Option.bind (Interface.Definition.read_type_interface lookups.interface path) (fun interface ->
      Types.instantiate_fields interface arguments)

let find_variants (lookups : Lookups.t) path arguments =
  Option.bind (Interface.Definition.read_type_interface lookups.interface path) (fun interface ->
      Types.instantiate_variants interface arguments)

let are_fields_visible (lookups : Lookups.t) ~package (path : Path.t) =
  match Interface.Definition.read_type_interface lookups.interface path with
  | Some { opaque = true; _ } -> Path.locate_package path = package
  | _ -> true

let read_method_signature (lookups : Lookups.t) trait method_ =
  Interface.Definition.read_method_signature lookups.interface ~owner:trait method_
