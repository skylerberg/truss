module Names = Resolve.Names

let bug format = Compiler_bug.bug ~stage:"Lower" format

type context = {
  lookups : Lookups.t;
  env : Memory_layout.env;
  drop_and_copy : Drop_and_copy.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
  checks : bool;
}

let monomorphic (interface : Interface.Lookups.t) : Monomorphic.context =
  {
    type_interface = Interface.Definition.read_type_interface interface;
    normalize = Interface.Impls.normalize interface ~bounds:Interface.Impls.no_bounds;
    normalize_capabilities =
      Interface.Impls.normalize_capabilities interface ~bounds:Interface.Impls.no_bounds;
  }

let uint64 = Ground.builtin UInt64
let string_slice : Ground.ty = Named { path = Well_known.path String_slice; arguments = [] }

let context (settings : Lookups.settings) ~env (lookups : Lookups.t) =
  let monomorphic = monomorphic lookups.interface in
  {
    lookups;
    env;
    drop_and_copy = Drop_and_copy.create env;
    monomorphic;
    types = { uint64; string_slice };
    bool = Ground.builtin Bool;
    checks = settings.checks;
  }

let test_key path = Instance.Code { path; type_arguments = [] }

type written = { spans : Source.Definition_span.t array; text : string }

type code = {
  definition : Path.t;
  written : written option;
  enclosing_impl : Path.t option;
  result : Types.result;
  substitution : Types.substitution;
  uses : Types.capability_set;
  real : Path.t list;
  has_defaults : bool;
}

let unwritten ~definition ~substitution ~result =
  {
    definition;
    written = None;
    enclosing_impl = None;
    result;
    substitution;
    uses = Types.no_capabilities;
    real = [];
    has_defaults = false;
  }

let read_written context key =
  {
    spans = context.lookups.interface.names.spans key;
    text = context.lookups.interface.names.text key;
  }

let bind = Monomorphic.substitution

let impl_interface context impl =
  match Interface.Definition.read_impl_interface context.lookups.interface impl with
  | Some position -> position
  | None -> bug "no interface for %s" (Path.show impl)

let trait_substitution context impl =
  match Interface.Impls.make_impl_substitution context.lookups.interface impl with
  | Some substitution -> substitution
  | None -> bug "no trait for %s" (Path.show impl)

let signature_of context (path : Path.t) =
  match Interface.Impls.read_signature context.lookups.interface path with
  | Some signature -> signature
  | None -> bug "no signature for %s" (Path.show path)

let code_of context (path : Path.t) type_arguments : code =
  let function_code ~enclosing_impl (key : Names.key) ~(interface : Types.signature) ~substitution =
    {
      definition = key.path;
      written = Some (read_written context key);
      enclosing_impl;
      result = interface.output;
      substitution;
      uses = interface.uses;
      real = [];
      has_defaults =
        List.exists
          (fun (parameter : Types.parameter_info) -> parameter.has_default)
          interface.parameters;
    }
  in
  match path with
  | Test _ -> (
      match Resolve.Names.definition_of_path context.lookups.interface.names path with
      | Some (key, { kind = Test _; _ }) ->
          {
            (unwritten ~definition:path ~substitution:[] ~result:(Returns Types.unit)) with
            written = Some (read_written context key);
            real =
              (match Interface.Definition.read_test_uses context.lookups.interface path with
              | Some uses ->
                  List.filter_map
                    (function Types.Capability path -> Some path | _ -> None)
                    (uses :> Types.capability list)
              | None -> []);
          }
      | _ -> bug "%s is not a test" (Path.show path))
  | Top _ | Method _ -> (
      let interface = signature_of context path in
      let substitution = bind interface.generics type_arguments in
      let enclosing_impl =
        match path with
        | Method { owner = (Impl _ | Derived _) as impl; _ } -> Some impl
        | _ -> None
      in
      match (context.lookups.mir.form_origin path, path) with
      | Some (Written key, _), _ -> function_code ~enclosing_impl key ~interface ~substitution
      | Some (Derived type_key, _), _ ->
          {
            (unwritten ~definition:type_key.path ~substitution ~result:interface.output) with
            written = Some (read_written context type_key);
            enclosing_impl;
          }
      | Some (Inherited provided, _), Method { owner = (Impl _ | Derived _) as impl; _ } ->
          let trait = (impl_interface context impl).implements.trait in
          let trait_signature = signature_of context provided.path in
          let count = List.length (impl_interface context impl).impl_generics in
          let of_impl = List.filteri (fun position _ -> position < count) substitution in
          let of_trait =
            List.map
              (fun (parameter, argument) -> (parameter, Types.substitute_argument of_impl argument))
              (trait_substitution context impl)
          in
          let own_generics =
            List.filter
              (fun (generic : Types.generic) -> not (Path.equal generic.generic.owner trait))
              trait_signature.generics
          in
          let own = List.filteri (fun position _ -> position >= count) type_arguments in
          function_code ~enclosing_impl provided ~interface:trait_signature
            ~substitution:(of_trait @ bind own_generics own @ substitution)
      | Some (Inherited _, _), _ -> bug "%s inherits a method outside an impl" (Path.show path)
      | None, _ -> bug "%s is not a function" (Path.show path))
  | Member_constant _ | Impl _ | Derived _ | Law_proof _ | Unresolved _ ->
      bug "%s is not code" (Path.show path)

let panic_path = Monomorphic.panic_capability
let evidence_for context = Monomorphic.evidence_for context.monomorphic

let result_of context substitution (result : Types.result) =
  match result with
  | Returns Never -> (Convention.Nothing, false)
  | Returns ty ->
      (Convention.result context.env (Monomorphic.ground context.monomorphic substitution ty), true)
  | Lends (mode, ty) ->
      let part = Monomorphic.ground context.monomorphic substitution ty in
      ( (if Memory_layout.has_zero_size context.env part then Convention.Nothing
         else Convention.Returned (Pointer { target = Value part; writable = mode = Mut })),
        true )

let lending_parameters context substitution (result : Types.result) : Lowered.ty list =
  match result with
  | Lends (_, ty) ->
      let part = Monomorphic.ground context.monomorphic substitution ty in
      (if Memory_layout.has_zero_size context.env part then []
       else [ Lowered.Pointer { target = Value part; writable = true } ])
      @ [ Pointer { target = Lend; writable = true }; Raw (Pointer Opaque) ]
  | Returns _ -> []

let c_signature context substitution ~(parameters : (Types.mode * Types.ty) list) ~has_defaults
    ?(uses = Types.no_capabilities) (result : Types.result) : Lowered.signature * Convention.result
    =
  let ground ty = Monomorphic.ground context.monomorphic substitution ty in
  let result_ty, returns = result_of context substitution result in
  let written =
    List.filter_map
      (fun (mode, ty) -> Convention.parameter context.env (Monomorphic.mode mode) (ground ty))
      parameters
  in
  let mask = if has_defaults then [ Lowered.Raw (Integer UInt64) ] else [] in
  let evidence = List.map (fun _ -> Convention.evidence) (evidence_for context substitution uses) in
  let lending = lending_parameters context substitution result in
  (Convention.signature ~returns (written @ mask @ evidence @ lending) result_ty, result_ty)

let template_clauses context from_template clauses =
  match Mir.contract_of_path context.lookups.mir from_template with
  | Some { form = contract; _ } ->
      List.map
        (fun position ->
          match List.nth_opt contract.requires position with
          | Some ({ clause; is_executable = true; _ } : Mir.requirement) ->
              Mir.code_of_formula clause
          | Some { is_executable = false; _ } | None ->
              bug "clause %d of %s cannot be run" position (Path.show from_template))
        clauses
  | None -> bug "%s is not a function" (Path.show from_template)

let has_defaults (signature : Types.signature) =
  List.exists (fun (parameter : Types.parameter_info) -> parameter.has_default) signature.parameters

let interface_parameters (signature : Types.signature) =
  (match signature.receiver with
    | Some (receiver, ty) ->
        [ ((match receiver with Mut -> Types.Mut | Own -> Own | Read | Static -> Read), ty) ]
    | None -> [])
  @ List.map (fun (info : Types.parameter_info) -> (info.mode, info.type_)) signature.parameters
