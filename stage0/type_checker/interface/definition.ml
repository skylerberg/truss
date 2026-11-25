let find_interface (lookups : Lookups.t) path = lookups.find_interface path

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
  { type_generics; shape = Builtin_type builtin; opaque = true; is_tuple = false; derives = [] }

let find_type_interface lookups (path : Path.t) =
  match Well_known.find_builtin_type path with
  | Some builtin -> Some (make_builtin_shape builtin)
  | None -> (
      match find_interface lookups path with Some (Type_interface type_) -> Some type_ | _ -> None)

type field_path_error =
  | Broken_type
  | No_fields of { type_ : Types.ty; prefix : string list }
  | Variant_fields of { type_ : Types.ty; prefix : string list }
  | Hidden_fields of Types.ty
  | Unknown_field of { type_ : Types.ty; field : string; candidates : string list }

let find_field_path_type lookups ~package (parameter_type : Types.ty) field_path =
  let rec walk (ty : Types.ty) prefix = function
    | [] -> Ok ty
    | field :: fields -> (
        match ty with
        | Error _ -> Error Broken_type
        | Named { path; arguments } -> (
            match find_type_interface lookups path with
            | Some ({ shape = Record _; _ } as interface) -> (
                if interface.opaque && Path.locate_package path <> package then
                  Error (Hidden_fields ty)
                else
                  let fields_of_type =
                    Option.value ~default:[] (Types.instantiate_fields interface arguments)
                  in
                  match
                    List.find_opt
                      (fun (written : Types.field) -> written.field_name = field)
                      fields_of_type
                  with
                  | Some written -> walk written.field_type (prefix @ [ field ]) fields
                  | None ->
                      Error
                        (Unknown_field
                           {
                             type_ = ty;
                             field;
                             candidates =
                               List.map
                                 (fun (written : Types.field) -> written.field_name)
                                 fields_of_type;
                           }))
            | Some { shape = Sum _; _ } -> Error (Variant_fields { type_ = ty; prefix })
            | Some { shape = Todo_type | Builtin_type _; _ } | None ->
                Error (No_fields { type_ = ty; prefix }))
        | _ -> Error (No_fields { type_ = ty; prefix }))
  in
  walk parameter_type [] field_path

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
          | Capability_unless _ | Capability_unless_values _ ->
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

let find_method_of_trait (interface : Types.trait_interface) ~name ~receiver =
  List.find_opt
    (fun declared -> Types.is_implemented_by interface declared ~name ~receiver)
    interface.methods

let find_trait_method lookups trait ~name ~receiver =
  Option.bind (find_trait_interface lookups trait) (find_method_of_trait ~name ~receiver)

let is_specification = function
  | Environment.Function_interface signature
  | Theorem_interface signature
  | Test_interface signature ->
      signature.specification_only
  | Law_proof_interface _ -> true
  | Type_interface _ | Trait_interface _ | Impl_interface _ | Constant_interface _
  | Error_interface _ ->
      false

let list_derives_entries (resolved : Resolve.resolved) (clauses : Syntax.type_clause list) =
  List.concat_map
    (fun (clause : Syntax.type_clause) ->
      match clause.kind with
      | Derives traits ->
          List.filter_map
            (fun (written : Syntax.path_type) ->
              match resolved.names.(written.path.last.id) with
              | Some (Resolve.Definition (_, trait)) -> Some (clause, written, trait)
              | _ -> None)
            traits
      | Type_invariant _ | Potential _ -> [])
    clauses
