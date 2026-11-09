(* Whether a type is [Copyable], [Plain], or a view, worked out from its
   shape, as a condition on its type arguments. See TYPECHECKER.md,
   "Properties of types".

   An opaque type is [Copyable] or [Plain] only when it declares so with
   [derives], so changing its hidden fields never changes what other code
   may do with it. A generic parameter has them only when bounded. Whether
   a type is a view is always worked out from its fields, since it is part
   of the shape. *)

module T = Types

let core name : Path.t = Top { module_ = { package = "standard"; modules = [ "core" ] }; name }
let copyable_trait = core "Copyable"
let plain_trait = core "Plain"

(* Every trait a bound gives, with the traits each requires. *)
let rec bound_closure database ?(seen = []) (bound : T.trait_reference) =
  if List.exists (fun (other : T.trait_reference) -> Path.equal other.trait bound.trait) seen then
    []
  else
    let required =
      match Query.demand database Environment.trait_interface bound.trait with
      | Some trait ->
          let substitution =
            List.combine
              (List.map (fun (generic : T.generic) -> generic.generic) trait.trait_generics)
              (if List.length trait.trait_generics = List.length bound.trait_arguments then
                 bound.trait_arguments
               else List.map (fun _ -> T.Type T.Error) trait.trait_generics)
          in
          List.map (T.substitute_trait substitution) trait.requires
      | None -> []
    in
    bound :: List.concat_map (bound_closure database ~seen:(bound :: seen)) required

let bounded database ~bounds parameter trait =
  List.exists
    (fun (bound : T.trait_reference) -> Path.equal bound.trait trait)
    (List.concat_map (bound_closure database) (bounds parameter))

type property = Copyable | Plain | View

(* The types a value of the type holds in place or owns, with its own type
   arguments substituted, and whether it allocates on the heap itself. *)
let parts database (path : Path.t) arguments =
  match Query.demand database Environment.type_interface path with
  | None -> None
  | Some interface ->
      let substitution =
        if List.length interface.type_generics = List.length arguments then
          List.combine
            (List.map (fun (generic : T.generic) -> generic.generic) interface.type_generics)
            arguments
        else []
      in
      let field_types fields =
        List.map (fun (field : T.field) -> T.substitute substitution field.field_type) fields
      in
      Some
        ( interface,
          match interface.shape with
          | Record fields -> (field_types fields, false)
          | Sum variants ->
              ( List.concat_map
                  (fun (variant : T.variant) ->
                    field_types (Option.value ~default:[] variant.fields))
                  variants,
                List.exists (fun (variant : T.variant) -> variant.indirect) variants )
          | Todo_type | Builtin_type _ | Error_shape -> ([], false) )

let rec has database ~bounds ?(visiting = []) property (type_ : T.ty) =
  let recurse = has database ~bounds ~visiting property in
  match type_ with
  | T.Error | T.Hole | T.Variable _ | T.Never -> property <> View
  | T.Literal _ | T.Integer -> property <> View
  | T.Parameter parameter -> (
      match property with
      | Copyable ->
          bounded database ~bounds parameter copyable_trait
          || bounded database ~bounds parameter plain_trait
      | Plain -> bounded database ~bounds parameter plain_trait
      | View -> false)
  | T.Projection _ -> false
  | T.Function _ -> property <> View
  | T.Any trait -> (
      match property with
      | Copyable ->
          List.exists
            (fun (bound : T.trait_reference) ->
              Path.equal bound.trait copyable_trait || Path.equal bound.trait plain_trait)
            (bound_closure database trait)
      | Plain -> false
      | View -> List.exists (fun (_, associated) -> recurse associated) trait.associated)
  | T.Cursor _ -> property = View
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
          if List.mem (path, arguments) visiting then property <> View
          else
            let visiting = (path, arguments) :: visiting in
            let recurse = has database ~bounds ~visiting property in
            match parts database path arguments with
            | None -> false
            | Some (interface, (contents, allocates)) -> (
                match interface.shape with
                | Error_shape -> property <> View
                | Todo_type -> false
                | _ -> (
                    match property with
                    | View -> List.exists recurse contents
                    | Copyable | Plain ->
                        let declared trait = List.exists (Path.equal trait) interface.derives in
                        let from_fields =
                          List.for_all recurse contents && not (property = Plain && allocates)
                        in
                        if interface.opaque then
                          (if property = Copyable then
                             declared copyable_trait || declared plain_trait
                           else declared plain_trait)
                          && from_fields
                        else from_fields))))

let copyable database ~bounds type_ = has database ~bounds Copyable type_
let plain database ~bounds type_ = has database ~bounds Plain type_
let is_view database ~bounds type_ = has database ~bounds View type_
