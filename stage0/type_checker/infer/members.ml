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
  match Interface.Definition.read_trait_interface lookups.interface trait with
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
  Option.bind (Interface.Definition.read_type_interface lookups.interface path) (fun interface ->
      Types.instantiate_fields interface arguments)

let variants (lookups : Lookups.t) path arguments =
  Option.bind (Interface.Definition.read_type_interface lookups.interface path) (fun interface ->
      Types.instantiate_variants interface arguments)

let fields_visible (lookups : Lookups.t) ~package (path : Path.t) =
  match Interface.Definition.read_type_interface lookups.interface path with
  | Some { opaque = true; _ } -> Path.package path = package
  | _ -> true

let method_signature (lookups : Lookups.t) trait method_ =
  Interface.Definition.read_method_signature lookups.interface ~owner:trait method_
