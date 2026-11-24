let raise_bug format = Compiler_bug.raise_bug ~stage:"Lower" format

type context = {
  lookups : Lookups.t;
  env : Memory_layout.env;
  drop_and_copy : Drop_and_copy.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
}

let make_monomorphic_context (interface : Interface.Lookups.t) : Monomorphic.context =
  {
    find_type_interface = Interface.Definition.find_type_interface interface;
    normalize = Interface.Impls.normalize interface ~list_bounds:Interface.Impls.list_no_bounds;
    normalize_capabilities =
      Interface.Impls.normalize_capabilities interface ~list_bounds:Interface.Impls.list_no_bounds;
  }

let uint64 = Ground.make_builtin UInt64
let string : Ground.ty = Named { path = Well_known.make_path String; arguments = [] }

let make_context ~env (lookups : Lookups.t) =
  let monomorphic = make_monomorphic_context lookups.interface in
  {
    lookups;
    env;
    drop_and_copy = Drop_and_copy.create env;
    monomorphic;
    types = { uint64; string };
    bool = Ground.make_builtin Bool;
  }

type written = { spans : Source.Definition_span.t array; text : string }

type code = {
  definition : Path.t;
  written : written option;
  enclosing_impl : Path.t option;
  result : Types.result;
  substitution : Types.substitution;
  uses : Types.capability_set;
  assumes_condition : bool;
}

let make_unwritten_code ~definition ~substitution ~result =
  {
    definition;
    written = None;
    enclosing_impl = None;
    result;
    substitution;
    uses = Types.no_capabilities;
    assumes_condition = false;
  }

let read_written context key =
  {
    spans = context.lookups.interface.names.read_spans key;
    text = context.lookups.interface.names.read_text key;
  }

let make_default_code context (code : code) ~(source : Resolve.Names.key) ~substitution =
  {
    code with
    definition = source.path;
    written = Some (read_written context source);
    enclosing_impl = None;
    substitution = Types.substitute_substitution code.substitution substitution;
  }

let bind = Monomorphic.make_substitution

let read_impl_interface context impl =
  Interface.Definition.read_impl_interface context.lookups.interface impl

let read_trait_interface context trait =
  Interface.Definition.read_trait_interface context.lookups.interface trait

let read_signature context (path : Path.t) =
  match Interface.Impls.read_signature context.lookups.interface path with
  | Some signature -> signature
  | None -> raise_bug "no signature for %s" (Path.show path)

let make_function_code context ~enclosing_impl (key : Resolve.Names.key)
    ~(interface : Types.signature) ~substitution =
  {
    definition = key.path;
    written = Some (read_written context key);
    enclosing_impl;
    result = interface.output;
    substitution;
    uses = interface.uses;
    assumes_condition = false;
  }

let make_declared_code context ~impl ~(declaration : Resolve.Names.key) ~trait_substitution
    (path : Path.t) (instantiation : Ground.instantiation) =
  let substitution =
    Monomorphic.make_signature_substitution (read_signature context path) instantiation
  in
  let impl_interface = read_impl_interface context impl in
  let trait = impl_interface.implements.trait in
  let trait_signature = read_signature context declaration.path in
  let count = List.length impl_interface.impl_generics in
  let of_trait =
    Types.substitute_substitution
      (bind impl_interface.impl_generics (List.take count instantiation.type_arguments))
      trait_substitution
  in
  let own_generics =
    List.filter
      (fun (generic : Types.generic) -> not (Path.equal generic.generic.owner trait))
      trait_signature.generics
  in
  let own = List.drop count instantiation.type_arguments in
  make_function_code context ~enclosing_impl:(Some impl) declaration ~interface:trait_signature
    ~substitution:
      (Types.combine_substitutions of_trait
         (Types.combine_substitutions (bind own_generics own)
            (Types.combine_substitutions substitution
               (Types.make_capability_substitution trait_signature.capability_parameters
                  (Monomorphic.convert_capability_arguments instantiation)))))

let make_code context (path : Path.t) (instantiation : Ground.instantiation) : code =
  match path with
  | Top _ | Method _ | Test _ -> (
      let interface = read_signature context path in
      let substitution = Monomorphic.make_signature_substitution interface instantiation in
      let enclosing_impl =
        match path with
        | Method { owner = (Impl _ | Derived _) as impl; _ } -> Some impl
        | _ -> None
      in
      match (context.lookups.mir.find_form_origin path, path) with
      | Some (Written key, _), _ ->
          make_function_code context ~enclosing_impl key ~interface ~substitution
      | Some (Derived type_key, _), _ ->
          {
            (make_unwritten_code ~definition:type_key.path ~substitution ~result:interface.output) with
            written = Some (read_written context type_key);
            enclosing_impl;
          }
      | ( Some (Inherited declaration, trait_substitution),
          Method { owner = (Impl _ | Derived _) as impl; _ } ) ->
          make_declared_code context ~impl ~declaration ~trait_substitution path instantiation
      | Some (Inherited _, _), _ ->
          raise_bug "%s inherits a method outside an impl" (Path.show path)
      | None, _ -> raise_bug "%s is not a function" (Path.show path))
  | Member_constant _ | Impl _ | Derived _ | Law_proof _ | Unresolved _ ->
      raise_bug "%s is not code" (Path.show path)

let panic_path = Well_known.make_builtin_capability_path Panic
let list_evidence context = Monomorphic.list_capabilities context.monomorphic

let has_panic_condition (uses : Types.capability_set) =
  Types.has_capability (Capability_unless_values (Built_in Panic)) uses

let remove_panic_condition (uses : Types.capability_set) =
  Types.replace_capabilities
    (function Types.Capability_unless_values _ -> Some Types.no_capabilities | _ -> None)
    uses

let classify_result context substitution (result : Types.result) =
  match result with
  | Returns Never -> (Convention.Nothing, false)
  | Returns ty ->
      ( Convention.classify_result context.env
          (Monomorphic.ground context.monomorphic substitution ty),
        true )
  | Lends (mode, ty) ->
      let part = Monomorphic.ground context.monomorphic substitution ty in
      ( (if Memory_layout.has_zero_size context.env part then Convention.Nothing
         else Convention.Returned (Pointer { target = Value part; writable = mode = Mut })),
        true )

let list_lending_parameters context substitution (result : Types.result) : Lowered.ty list =
  match result with
  | Lends (_, ty) ->
      let part = Monomorphic.ground context.monomorphic substitution ty in
      (if Memory_layout.has_zero_size context.env part then []
       else [ Lowered.Pointer { target = Value part; writable = true } ])
      @ [ Pointer { target = Lend; writable = true }; Raw (Pointer Opaque) ]
  | Returns _ -> []

let make_c_signature context substitution ~(parameters : (Language.Mode.t * Types.ty) list)
    ?(uses = Types.no_capabilities) (result : Types.result) : Lowered.signature * Convention.result
    =
  let ground ty = Monomorphic.ground context.monomorphic substitution ty in
  let result_ty, returns = classify_result context substitution result in
  let written =
    List.filter_map
      (fun (mode, ty) -> Convention.classify_parameter context.env mode (ground ty))
      parameters
  in
  let evidence =
    List.map (fun _ -> Convention.evidence) (list_evidence context substitution uses)
  in
  let lending = list_lending_parameters context substitution result in
  (Convention.make_signature ~returns (written @ evidence @ lending) result_ty, result_ty)

let list_interface_parameters (signature : Types.signature) =
  Option.to_list signature.receiver
  @ List.map (fun (info : Types.parameter_info) -> (info.mode, info.type_)) signature.parameters
