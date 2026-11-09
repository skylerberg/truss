(* Whether a type is [Copyable], [Plain], or a view, worked out from its
   shape, as a condition on its type arguments. See TYPECHECKER.md,
   "Properties of types".

   An opaque type has [Copyable] or [Plain] only when it declares so with
   [derives], and then exactly when its type arguments have it, as for a
   derived [impl]: changing its hidden fields never changes what other code
   may do with it. A generic parameter has them only when bounded, and so
   does an associated type, by its declared bounds. Whether a type is a
   view is part of its shape, so it is worked out from the fields. *)

module T = Types

let core name : Path.t = Top { module_ = { package = "standard"; modules = [ "core" ] }; name }
let copyable_trait = core "Copyable"
let plain_trait = core "Plain"

(* Every trait a bound gives a type, with the traits each requires, and
   [Self] in what they require replaced by the type. *)
let rec bound_closure database ?(seen = []) ~self (bound : T.trait_reference) =
  if List.exists (fun (other : T.trait_reference) -> Path.equal other.trait bound.trait) seen then
    []
  else
    let required =
      match Query.demand database Environment.trait_interface bound.trait with
      | Some trait ->
          let substitution =
            (({ owner = bound.trait; name = "Self" } : T.parameter), T.Type self)
            :: List.combine
                 (List.map (fun (generic : T.generic) -> generic.generic) trait.trait_generics)
                 (if List.length trait.trait_generics = List.length bound.trait_arguments then
                    bound.trait_arguments
                  else List.map (fun _ -> T.Type T.Error) trait.trait_generics)
          in
          List.map (T.substitute_trait substitution) trait.requires
      | None -> []
    in
    bound :: List.concat_map (bound_closure database ~seen:(bound :: seen) ~self) required

(* The bounds an associated type is declared with, for a base type: the
   [Key: Hash] in [trait Keyed { type Key: Hash }]. *)
let associated_bounds database ~base (trait : T.trait_reference) name =
  match Query.demand database Environment.trait_interface trait.trait with
  | Some interface -> (
      match
        List.find_opt
          (fun (associated : T.associated_type) -> associated.associated_name = name)
          interface.associated_types
      with
      | Some associated ->
          let substitution =
            (({ owner = trait.trait; name = "Self" } : T.parameter), T.Type base)
            :: List.combine
                 (List.map (fun (generic : T.generic) -> generic.generic) interface.trait_generics)
                 (if List.length interface.trait_generics = List.length trait.trait_arguments then
                    trait.trait_arguments
                  else List.map (fun _ -> T.Type T.Error) interface.trait_generics)
          in
          List.map (T.substitute_trait substitution) associated.associated_bounds
      | None -> [])
  | None -> []

(* The traits a type is known to have from bounds: a generic parameter's,
   or a projection's declared ones, each with what it requires. *)
let known_bounds database ~bounds (type_ : T.ty) =
  match type_ with
  | T.Parameter parameter -> List.concat_map (bound_closure database ~self:type_) (bounds parameter)
  | T.Projection { base; trait; name } ->
      List.concat_map
        (bound_closure database ~self:type_)
        (associated_bounds database ~base trait name)
  | _ -> []

let has_bound database ~bounds type_ trait =
  List.exists
    (fun (bound : T.trait_reference) -> Path.equal bound.trait trait)
    (known_bounds database ~bounds type_)

type property = Copyable | Plain | View

let substitution_of (interface : T.type_interface) arguments =
  if List.length interface.type_generics = List.length arguments then
    List.combine
      (List.map (fun (generic : T.generic) -> generic.generic) interface.type_generics)
      arguments
  else []

(* A definition met again while working out its own property holds, which
   ends recursive types, and types that contain themselves with growing
   arguments, which the recursive-type check reports. *)
let rec has database ~bounds ?(visiting = []) property (type_ : T.ty) =
  let recurse = has database ~bounds ~visiting property in
  match type_ with
  | T.Error | T.Hole | T.Variable _ | T.Never | T.Literal _ | T.Integer -> property <> View
  | T.Parameter _ | T.Projection _ -> (
      match property with
      | Copyable ->
          has_bound database ~bounds type_ copyable_trait
          || has_bound database ~bounds type_ plain_trait
      | Plain -> has_bound database ~bounds type_ plain_trait
      | View -> false)
  | T.Function _ -> property <> View
  | T.Any trait -> (
      let closure = bound_closure database ~self:type_ trait in
      match property with
      | Copyable ->
          List.exists
            (fun (bound : T.trait_reference) ->
              Path.equal bound.trait copyable_trait || Path.equal bound.trait plain_trait)
            closure
      | Plain -> false
      | View -> List.exists (fun (_, associated) -> recurse associated) trait.associated)
  | T.Cursor { method_; arguments } -> (
      (* A cursor from an [own self] method owns what it goes over; one from
         a [self] method views it. *)
      match (property, method_) with
      | View, Method { receiver = Own; _ } ->
          List.exists (function T.Type type_ -> recurse type_ | T.Value _ -> false) arguments
      | View, _ -> true
      | (Copyable | Plain), _ -> false)
  | T.Named { path; arguments } -> (
      let argument_types =
        List.filter_map (function T.Type type_ -> Some type_ | T.Value _ -> None) arguments
      in
      match Intrinsic.builtin_of_path path with
      | Some Storage -> (
          match property with
          | Copyable -> List.for_all recurse argument_types
          | Plain -> false
          | View -> List.exists recurse argument_types)
      | Some View -> true
      | Some Array -> (
          match property with
          | Copyable | Plain -> List.for_all recurse argument_types
          | View -> List.exists recurse argument_types)
      | Some _ -> property <> View
      | None -> (
          if List.exists (Path.equal path) visiting then property <> View
          else
            match Query.demand database Environment.type_interface path with
            | None -> false
            | Some interface -> (
                let visiting = path :: visiting in
                let recurse = has database ~bounds ~visiting property in
                let substitution = substitution_of interface arguments in
                let field_types fields =
                  List.map
                    (fun (field : T.field) -> T.substitute substitution field.field_type)
                    fields
                in
                let contents, allocates =
                  match interface.shape with
                  | Record fields -> (field_types fields, false)
                  | Sum variants ->
                      ( List.concat_map
                          (fun (variant : T.variant) ->
                            field_types (Option.value ~default:[] variant.fields))
                          variants,
                        List.exists (fun (variant : T.variant) -> variant.indirect) variants )
                  | Todo_type | Builtin_type _ | Error_shape -> ([], false)
                in
                match interface.shape with
                | Error_shape -> property <> View
                | Todo_type -> false
                | _ -> (
                    match property with
                    | View -> List.exists recurse contents
                    | Copyable | Plain ->
                        if interface.opaque then
                          let declared trait = List.exists (Path.equal trait) interface.derives in
                          (if property = Copyable then
                             declared copyable_trait || declared plain_trait
                           else declared plain_trait)
                          && List.for_all recurse argument_types
                        else List.for_all recurse contents && not (property = Plain && allocates))))
      )

let copyable database ~bounds type_ = has database ~bounds Copyable type_
let plain database ~bounds type_ = has database ~bounds Plain type_
let is_view database ~bounds type_ = has database ~bounds View type_
