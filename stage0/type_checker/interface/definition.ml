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

let make_builtin_shape builtin : Types.type_interface =
  let element : Types.parameter =
    { owner = Intrinsic.make_builtin_path builtin; name = "Element" }
  in
  let count : Types.parameter = { owner = Intrinsic.make_builtin_path builtin; name = "count" } in
  let type_generics : Types.generic list =
    match builtin with
    | Array ->
        [ { generic = element; kind = Type_generic [] }; { generic = count; kind = Value_generic } ]
    | Storage | View -> [ { generic = element; kind = Type_generic [] } ]
    | Shared ->
        let storable : Types.trait_reference =
          { trait = Well_known.make_path Storable; trait_arguments = []; associated = [] }
        in
        [
          {
            generic = { owner = Intrinsic.make_builtin_path builtin; name = "Value" };
            kind = Type_generic [ storable ];
          };
        ]
    | _ -> []
  in
  { type_generics; shape = Builtin_type builtin; opaque = true; derives = [] }

let find_type_interface lookups (path : Path.t) =
  match Intrinsic.builtin_of_path path with
  | Some builtin -> Some (make_builtin_shape builtin)
  | None -> (
      match find_interface lookups path with Some (Type_interface type_) -> Some type_ | _ -> None)

let find_declared_signature lookups (path : Path.t) =
  match find_interface lookups path with
  | Some (Function_interface signature | Theorem_interface signature) -> Some signature
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

let read_test_uses lookups path =
  match find_interface lookups path with
  | Some (Test_interface uses) -> uses
  | _ -> Compiler_bug.raise_bug ~stage:"Interface" "%s has no test interface" (Path.show path)

let is_external_test lookups path = read_test_uses lookups path <> Types.no_capabilities

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

let read_method_signature lookups ~owner (method_ : Types.trait_method) =
  let path =
    Path.Method { owner; name = method_.method_name; receiver = method_.method_receiver }
  in
  match find_declared_signature lookups path with
  | Some signature -> signature
  | None ->
      Compiler_bug.raise_bug ~stage:"Interface" "the method `%s` has no signature" (Path.show path)

type declaring_clause =
  | Own_uses
  | Impl_uses of { capability : Path.t }
  | Associated_capability_set of { name : string; is_defined : bool }

type capability_declaration =
  | Declared_by of declaring_clause
  | Fixed_by_trait of { trait : Types.trait_reference; method_name : string }

let find_self_capability_set (trait : Types.trait_interface) ~trait_path
    (signature : Types.signature) =
  List.find_map
    (function
      | Types.Capability_projection { base = Parameter parameter; name; _ }
        when Path.equal parameter.owner trait_path
             && Types.is_self_parameter parameter
             && List.mem name trait.associated_capabilities ->
          Some name
      | _ -> None)
    (signature.uses :> Types.capability list)

let find_capability_declaration lookups (path : Path.t) =
  let ( let* ) = Option.bind in
  match path with
  | Method { owner = (Impl _ | Derived _) as owner; name; receiver } ->
      let* impl = find_impl_interface lookups owner in
      let trait_path = impl.implements.trait in
      let* trait = find_trait_interface lookups trait_path in
      if trait.is_capability then Some (Declared_by (Impl_uses { capability = trait_path }))
      else
        let* declared =
          List.find_opt
            (fun declared -> Types.is_implemented_by trait declared ~name ~receiver)
            trait.methods
        in
        let* signature =
          find_declared_signature lookups
            (Method
               {
                 owner = trait_path;
                 name = declared.method_name;
                 receiver = declared.method_receiver;
               })
        in
        Some
          (match find_self_capability_set trait ~trait_path signature with
          | Some set ->
              Declared_by
                (Associated_capability_set
                   { name = set; is_defined = List.mem_assoc set impl.capability_sets })
          | None -> Fixed_by_trait { trait = impl.implements; method_name = name })
  | Top _ | Method _ | Test _ -> Some (Declared_by Own_uses)
  | Member_constant _ | Impl _ | Derived _ | Law_proof _ | Unresolved _ ->
      Compiler_bug.raise_bug ~stage:"Interface" "%s declares no capabilities" (Path.show path)

let show_declaring_clause clause capability =
  match clause with
  | Own_uses -> Printf.sprintf "`uses %s`" capability
  | Impl_uses _ -> Printf.sprintf "`uses %s` on the `impl`" capability
  | Associated_capability_set { name; is_defined = true } ->
      Printf.sprintf "`%s` in the `impl`'s `capability %s`" capability name
  | Associated_capability_set { name; is_defined = false } ->
      Printf.sprintf "`capability %s = %s` in the `impl`" name capability

let is_specification = function
  | Environment.Function_interface signature | Theorem_interface signature ->
      signature.specification_only
  | Law_proof_interface _ -> true
  | Type_interface _ | Trait_interface _ | Impl_interface _ | Constant_interface _
  | Test_interface _ | Error_interface _ ->
      false
