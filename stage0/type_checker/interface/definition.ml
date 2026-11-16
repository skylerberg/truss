let read_interface (lookups : Lookups.t) path =
  Option.map (fun key -> (lookups.elaborated_interface key).interface) (lookups.names.key path)

let list_declared_fields (lookups : Lookups.t) path =
  let list_names (written : Syntax.field list) =
    List.filter_map
      (fun (field : Syntax.field) ->
        match field.kind with
        | Field_declaration { name; _ } -> Some name.text
        | Field_error -> None)
      written
  in
  match Option.map lookups.names.definition (lookups.names.key path) with
  | Some { kind = Type_definition { body = Fields written; _ }; _ } ->
      [ (None, list_names written) ]
  | Some { kind = Type_definition { body = Variants variants; _ }; _ } ->
      List.map
        (fun (variant : Syntax.variant) ->
          (Some variant.name.text, list_names (Option.value ~default:[] variant.fields)))
        variants
  | _ -> []

let sort_in_declared_order lookups path ~variant ~name fields =
  match List.assoc_opt variant (list_declared_fields lookups path) with
  | Some declared ->
      let find_position field =
        let rec find index = function
          | [] -> index
          | declared_name :: rest ->
              if declared_name = name field then index else find (index + 1) rest
        in
        find 0 declared
      in
      List.stable_sort (fun left right -> compare (find_position left) (find_position right)) fields
  | None -> fields

let make_builtin_shape builtin : Types.type_interface =
  let element : Types.parameter = { owner = Intrinsic.builtin_path builtin; name = "Element" } in
  let count : Types.parameter = { owner = Intrinsic.builtin_path builtin; name = "count" } in
  let type_generics : Types.generic list =
    match builtin with
    | Array ->
        [ { generic = element; kind = Type_generic [] }; { generic = count; kind = Value_generic } ]
    | Storage | View -> [ { generic = element; kind = Type_generic [] } ]
    | Shared ->
        let storable : Types.trait_reference =
          { trait = Well_known.path Storable; trait_arguments = []; associated = [] }
        in
        [
          {
            generic = { owner = Intrinsic.builtin_path builtin; name = "Value" };
            kind = Type_generic [ storable ];
          };
        ]
    | _ -> []
  in
  { type_generics; shape = Builtin_type builtin; opaque = true; derives = [] }

let read_type_interface lookups (path : Path.t) =
  match Intrinsic.builtin_of_path path with
  | Some builtin -> Some (make_builtin_shape builtin)
  | None -> (
      match read_interface lookups path with Some (Type_interface type_) -> Some type_ | _ -> None)

let read_declared_signature lookups (path : Path.t) =
  match read_interface lookups path with
  | Some (Function_interface signature | Theorem_interface signature) -> Some signature
  | _ -> None

let read_trait_interface lookups (path : Path.t) =
  match read_interface lookups path with Some (Trait_interface trait) -> Some trait | _ -> None

let read_impl_interface (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Derived { type_; trait } -> lookups.derived_interface ~type_ ~trait
  | _ -> (
      match read_interface lookups path with Some (Impl_interface impl) -> Some impl | _ -> None)

let read_test_uses lookups path =
  match read_interface lookups path with Some (Test_interface uses) -> Some uses | _ -> None

let read_constant_type lookups (path : Path.t) =
  match read_interface lookups path with
  | Some (Constant_interface constant) -> Some constant.constant_type
  | _ -> None

let read_method_signature lookups ~owner (method_ : Types.trait_method) =
  let path =
    Path.Method { owner; name = method_.method_name; receiver = method_.method_receiver }
  in
  match read_declared_signature lookups path with
  | Some signature -> signature
  | None -> Compiler_bug.bug ~stage:"Interface" "the method `%s` has no signature" (Path.show path)

let is_specification = function
  | Environment.Function_interface signature | Theorem_interface signature ->
      signature.specification_only
  | Law_proof_interface _ -> true
  | Type_interface _ | Trait_interface _ | Impl_interface _ | Constant_interface _
  | Test_interface _ | Error_interface _ ->
      false
