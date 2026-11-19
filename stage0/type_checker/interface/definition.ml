let find_interface (lookups : Lookups.t) path =
  Option.map
    (fun key -> (lookups.read_elaborated_interface key).interface)
    (lookups.names.find_key path)

let list_declared_fields (lookups : Lookups.t) path =
  let list_names (written : Syntax.field list) =
    List.filter_map
      (fun (field : Syntax.field) ->
        match field.kind with
        | Field_declaration { name; _ } -> Some name.text
        | Field_error -> None)
      written
  in
  match Option.map lookups.names.read_definition (lookups.names.find_key path) with
  | Some { kind = Type_definition { body = Fields written; _ }; _ } ->
      [ (None, list_names written) ]
  | Some { kind = Type_definition { body = Variants variants; _ }; _ } ->
      List.map
        (fun (variant : Syntax.variant) ->
          (Some variant.name.text, list_names (Option.value ~default:[] variant.fields)))
        variants
  | _ -> []

let sort_in_declared_order lookups path ~variant ~name_of fields =
  match List.assoc_opt variant (list_declared_fields lookups path) with
  | Some declared ->
      let locate_position field =
        Option.value ~default:(List.length declared)
          (List.find_index (fun declared_name -> declared_name = name_of field) declared)
      in
      List.stable_sort
        (fun left right -> compare (locate_position left) (locate_position right))
        fields
  | None -> fields

let make_builtin_shape (builtin : Language.Builtin_type.t) : Types.type_interface =
  let bounds : Types.trait_reference list =
    match builtin with
    | Shared -> [ { trait = Well_known.make_path Storable; trait_arguments = []; associated = [] } ]
    | _ -> []
  in
  let type_generics =
    List.map
      (fun (name, (kind : Resolve.Names.generic_kind)) : Types.generic ->
        {
          generic = { owner = Well_known.make_builtin_type_path builtin; name };
          kind = (match kind with Type_kind -> Type_generic bounds | Value_kind -> Value_generic);
        })
      (Resolve.Names.list_builtin_generics builtin)
  in
  { type_generics; shape = Builtin_type builtin; opaque = true; derives = [] }

let find_type_interface lookups (path : Path.t) =
  match Well_known.find_builtin_type path with
  | Some builtin -> Some (make_builtin_shape builtin)
  | None -> (
      match find_interface lookups path with Some (Type_interface type_) -> Some type_ | _ -> None)

let find_declared_signature lookups (path : Path.t) =
  match find_interface lookups path with
  | Some (Function_interface signature | Theorem_interface signature | Test_interface signature) ->
      Some signature
  | _ -> None

let find_trait_interface lookups (path : Path.t) =
  match find_interface lookups path with Some (Trait_interface trait) -> Some trait | _ -> None

let find_impl_interface (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Derived { type_; trait } -> lookups.find_derived_interface ~type_ ~trait
  | _ -> (
      match find_interface lookups path with Some (Impl_interface impl) -> Some impl | _ -> None)

let read_type_interface lookups path =
  match find_type_interface lookups path with
  | Some interface -> interface
  | None -> Compiler_bug.raise_bug ~stage:"Interface" "%s is not a type" (Path.show path)

let read_trait_interface lookups path =
  match find_trait_interface lookups path with
  | Some interface -> interface
  | None -> Compiler_bug.raise_bug ~stage:"Interface" "%s is not a trait" (Path.show path)

let read_impl_interface lookups path =
  match find_impl_interface lookups path with
  | Some interface -> interface
  | None -> Compiler_bug.raise_bug ~stage:"Interface" "%s is not an impl" (Path.show path)

let is_external_test lookups path =
  match find_interface lookups path with
  | Some (Test_interface signature) ->
      Types.exists_capability
        (function
          | Types.Built_in (Panic | Run_forever) -> false
          | Built_in System
          | Capability _ | Capability_parameter _ | Capability_projection _ | Capability_variable _
          | Capability_error _ ->
              true
          | Capability_unless _ ->
              Compiler_bug.raise_bug ~stage:"Interface" "a capability's base has a condition")
        signature.uses
  | _ -> Compiler_bug.raise_bug ~stage:"Interface" "%s has no test interface" (Path.show path)

let find_real_implementation (lookups : Lookups.t) capability =
  match
    List.filter
      (function Path.Impl { module_; _ } -> Well_known.is_system_module module_ | _ -> false)
      (lookups.names.list_impls_of_trait Path.standard_package capability)
  with
  | [] -> None
  | [ impl ] -> Some impl
  | impls ->
      Compiler_bug.raise_bug ~stage:"Interface" "%s has %d real implementations: %s"
        (Path.show capability) (List.length impls)
        (String.concat ", " (List.map Path.show impls))

let find_constant_type lookups (path : Path.t) =
  match find_interface lookups path with
  | Some (Constant_interface constant) -> Some constant.constant_type
  | _ -> None

let read_constant_type lookups path =
  match find_constant_type lookups path with
  | Some ty -> ty
  | None -> Compiler_bug.raise_bug ~stage:"Interface" "%s is not a constant" (Path.show path)

let find_shadowed_constant (lookups : Lookups.t) module_ ~name ~type_ =
  match lookups.names.find module_ name with
  | Some ({ kind = Constant; _ } : Resolve.Names.entry) -> (
      let path : Path.t = Top { module_; name } in
      match find_constant_type lookups path with
      | Some constant_type when Types.equal constant_type type_ -> Some path
      | _ -> None)
  | _ -> None

let read_method_signature lookups ~owner (method_ : Types.trait_method) =
  let path =
    Path.Method { owner; name = method_.method_name; receiver = method_.method_receiver }
  in
  match find_declared_signature lookups path with
  | Some signature -> signature
  | None ->
      Compiler_bug.raise_bug ~stage:"Interface" "the method `%s` has no signature" (Path.show path)

let find_trait_method lookups trait ~name ~receiver =
  Option.bind (find_trait_interface lookups trait) (fun (interface : Types.trait_interface) ->
      List.find_opt
        (fun declared -> Types.is_implemented_by interface declared ~name ~receiver)
        interface.methods)

let is_specification = function
  | Environment.Function_interface signature
  | Theorem_interface signature
  | Test_interface signature ->
      signature.specification_only
  | Law_proof_interface _ -> true
  | Type_interface _ | Trait_interface _ | Impl_interface _ | Constant_interface _
  | Error_interface _ ->
      false
