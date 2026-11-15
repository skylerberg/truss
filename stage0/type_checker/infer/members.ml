module Names = Resolve.Names
module Environment = Interface.Environment

let visible_packages database (package : Path.package) =
  List.sort_uniq compare
    (Path.standard_package :: package :: Query.demand database Packages.dependency_names package)

let own_methods database owner name =
  List.filter_map
    (fun (key : Names.key) ->
      match key.path with Method { receiver; _ } -> Some (receiver, key.path) | _ -> None)
    (Query.demand database Names.members (owner, name))

let own_constant database owner name =
  List.find_map
    (fun (key : Names.key) -> match key.path with Member_constant _ -> Some key.path | _ -> None)
    (Query.demand database Names.members (owner, name))

let trait_methods database trait name =
  match Query.demand database Environment.trait_interface trait with
  | Some interface ->
      List.filter
        (fun (method_ : Types.trait_method) -> method_.method_name = name)
        interface.methods
  | None -> []

let trait_method database trait name receiver =
  List.find_opt
    (fun (method_ : Types.trait_method) -> method_.method_receiver = receiver)
    (trait_methods database trait name)

let substitution_for database path arguments =
  match Query.demand database Environment.type_interface path with
  | Some interface ->
      Option.value ~default:[] (Types.substitution_of interface.type_generics arguments)
  | None -> []

let fields database path arguments =
  match Query.demand database Environment.type_interface path with
  | Some { shape = Record fields; _ } ->
      let substitution = substitution_for database path arguments in
      Some
        (List.map
           (fun (field : Types.field) ->
             { field with field_type = Types.substitute substitution field.field_type })
           fields)
  | _ -> None

let variants database path arguments =
  match Query.demand database Environment.type_interface path with
  | Some { shape = Sum variants; _ } ->
      let substitution = substitution_for database path arguments in
      Some
        (List.map
           (fun (variant : Types.variant) ->
             {
               variant with
               fields =
                 Option.map
                   (List.map (fun (field : Types.field) ->
                        { field with field_type = Types.substitute substitution field.field_type }))
                   variant.fields;
             })
           variants)
  | _ -> None

let shape database path =
  match Query.demand database Environment.type_interface path with
  | Some interface -> Some interface.shape
  | None -> None

let broken database path =
  match shape database path with Some (Error_shape report) -> Some report | _ -> None

let fields_visible database ~package (path : Path.t) =
  match Query.demand database Environment.type_interface path with
  | Some { opaque = true; _ } -> Path.package path = package
  | _ -> true
