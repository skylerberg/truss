(* Looking up a name after a dot: fields, a type's own methods, trait
   methods, and a type's static members. *)

module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment

(* The traits that declare a method with this name, among those a dot-call
   may find: the standard library's, the calling package's, and those of
   the packages its manifest lists. One query per package and name. *)
let traits_declaring =
  Query.query ~name:"traits_declaring" ~phase:Interfaces ~saved:true
    ~show:(fun (package, name) -> package ^ " " ^ name)
    (fun database (package, name) ->
      match Workspace.package database package with
      | None -> []
      | Some package ->
          List.concat_map
            (fun module_ ->
              List.filter_map
                (fun (declaration : Names.declaration) ->
                  if declaration.kind <> Trait || declaration.ordinal <> 0 then None
                  else
                    match Query.demand database Environment.trait_interface declaration.path with
                    | Some trait
                      when List.exists
                             (fun (method_ : T.trait_method) -> method_.method_name = name)
                             trait.methods ->
                        Some declaration.path
                    | _ -> None)
                (Query.demand database Names.declarations module_))
            package.modules)

let visible_packages database (package : string) =
  let dependencies =
    match Workspace.package database package with
    | Some package ->
        List.map
          (fun (dependency : Workspace.dependency) -> dependency.package)
          package.dependencies
    | None -> []
  in
  List.sort_uniq compare ("standard" :: package :: dependencies)

(* A type's own methods with a name: one per receiver. *)
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
      List.filter (fun (method_ : T.trait_method) -> method_.method_name = name) interface.methods
  | None -> []

(* The fields of a record type, with its type arguments substituted. *)
let substitution_for database path arguments =
  match Query.demand database Environment.type_interface path with
  | Some interface -> Option.value ~default:[] (T.substitution_of interface.type_generics arguments)
  | None -> []

let fields database path arguments =
  match Query.demand database Environment.type_interface path with
  | Some { shape = Record fields; _ } ->
      let substitution = substitution_for database path arguments in
      Some
        (List.map
           (fun (field : T.field) ->
             { field with field_type = T.substitute substitution field.field_type })
           fields)
  | _ -> None

let variants database path arguments =
  match Query.demand database Environment.type_interface path with
  | Some { shape = Sum variants; _ } ->
      let substitution = substitution_for database path arguments in
      Some
        (List.map
           (fun (variant : T.variant) ->
             {
               variant with
               fields =
                 Option.map
                   (List.map (fun (field : T.field) ->
                        { field with field_type = T.substitute substitution field.field_type }))
                   variant.fields;
             })
           variants)
  | _ -> None

let shape database path =
  match Query.demand database Environment.type_interface path with
  | Some interface -> Some interface.shape
  | None -> None

(* The report of a type whose definition did not parse, of which everything
   is accepted. *)
let broken database path =
  match shape database path with Some (Error_shape report) -> Some report | _ -> None

(* Whether code in a package may see a type's fields: an opaque type's
   fields are visible only in its own package. *)
let fields_visible database ~package (path : Path.t) =
  match Query.demand database Environment.type_interface path with
  | Some { opaque = true; _ } -> Path.package path = package
  | _ -> true
