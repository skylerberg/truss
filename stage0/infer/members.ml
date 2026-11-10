(* Looking up a name after a dot: fields, a type's own methods, trait
   methods, and a type's static members. *)

module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment

(* The packages whose traits a dot-call may find: the standard library, the
   calling package, and those its manifest lists. *)
let visible_packages database (package : string) =
  List.sort_uniq compare
    ("standard" :: package
    :: List.map
         (fun (dependency : Workspace.dependency) -> dependency.package)
         (Query.demand database Workspace.dependencies package))

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

(* A trait's versions of a method: one for each way it takes [self]. *)
let trait_methods database trait name =
  match Query.demand database Environment.trait_interface trait with
  | Some interface ->
      List.filter (fun (method_ : T.trait_method) -> method_.method_name = name) interface.methods
  | None -> []

let trait_method database trait name receiver =
  List.find_opt
    (fun (method_ : T.trait_method) -> method_.method_receiver = receiver)
    (trait_methods database trait name)

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
