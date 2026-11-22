let lookup_member (state : State.state) member =
  Resolve.Names.lookup_member state.lookups.interface.names ~from:state.key.module_ member

let lookup_method state owner name receiver : Path.t Resolve.Names.lookup =
  lookup_member state (Method { owner; name; receiver })

let list_member_lookups (state : State.state) owner name =
  Resolve.Names.list_member_lookups state.lookups.interface.names ~from:state.key.module_ owner name

let list_methods owner name : Path.t list =
  List.map
    (fun receiver : Path.t -> Method { owner; name; receiver })
    [ Path.Static; Instance Read; Instance Mut; Instance Own ]

let list_method_lookups state owner name =
  List.map
    (Resolve.Names.choose_member (list_member_lookups state owner name))
    (list_methods owner name)

let has_visible_method state owner name =
  match Resolve.Names.choose_visible (list_method_lookups state owner name) with
  | Visible _ -> true
  | Hidden _ | Absent -> false

let make_hidden_error state span (hidden, visibility) =
  State.make_error_type state Member_not_visible span
    (Resolve.Names.describe_hidden hidden visibility)

let list_trait_methods (lookups : Lookups.t) trait name =
  match Interface.Definition.find_trait_interface lookups.interface trait with
  | Some interface ->
      List.filter
        (fun (method_ : Types.trait_method) -> method_.method_name = name)
        interface.methods
  | None -> []

let find_fields (lookups : Lookups.t) path arguments =
  Option.bind (Interface.Definition.find_type_interface lookups.interface path) (fun interface ->
      Types.instantiate_fields interface arguments)

let find_variants (lookups : Lookups.t) path arguments =
  Option.bind (Interface.Definition.find_type_interface lookups.interface path) (fun interface ->
      Types.instantiate_variants interface arguments)

let are_fields_visible (lookups : Lookups.t) ~package (path : Path.t) =
  Path.locate_package path = package
  ||
  match Interface.Definition.find_type_interface lookups.interface path with
  | Some { opaque; _ } -> not opaque
  | None -> true

let is_tuple_type (lookups : Lookups.t) (path : Path.t) =
  match Interface.Definition.find_type_interface lookups.interface path with
  | Some { is_tuple; _ } -> is_tuple
  | None -> false

let list_trait_generics (lookups : Lookups.t) trait =
  match Interface.Definition.find_trait_interface lookups.interface trait with
  | Some interface -> interface.trait_generics
  | None -> []

let read_method_signature signatures (lookups : Lookups.t) trait method_ =
  Signatures.read_of_method signatures lookups.interface ~owner:trait method_
