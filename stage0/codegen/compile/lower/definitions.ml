module Names = Resolve.Names

let bug format = Compiler_bug.bug ~stage:"Lower" format

type context = {
  lookups : Lookups.t;
  constant : Path.t -> Lowered.static_value option;
  env : Memory_layout.env;
  glue : Glue.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
  checks : bool;
}

let debug_form : Ground.ty -> Glue.debug_form = function
  | Named { path; _ } -> (
      match Well_known.of_path path with
      | Some (String | String_slice) -> Text
      | Some (List | Slice) -> Sequence
      | _ -> Structure)
  | _ -> Structure

let monomorphic (interface : Interface.Lookups.t) : Monomorphic.context =
  {
    type_interface = Interface.Definition.type_interface interface;
    normalize = Interface.Impls.normalize interface ~bounds:Interface.Impls.no_bounds;
    normalize_capabilities =
      Interface.Impls.normalize_capabilities interface ~bounds:Interface.Impls.no_bounds;
  }

let uint64 = Monomorphic.builtin UInt64
let string_slice : Ground.ty = Named { path = Well_known.path String_slice; arguments = [] }

let context (settings : Lookups.settings) ~constant ~env (lookups : Lookups.t) =
  let monomorphic = monomorphic lookups.interface in
  {
    lookups;
    constant;
    env;
    glue =
      Glue.create env
        ~representation:(Monomorphic.representation monomorphic)
        ~uint64 ~debug_form ();
    monomorphic;
    types = { uint64; string_slice };
    bool = Monomorphic.builtin Bool;
    checks = settings.checks;
  }

let test_key path = Instance.Code { path; type_arguments = [] }

type code = {
  definition_key : Names.key;
  anchor : Path.t;
  enclosing_impl : Path.t option;
  text : string;
  result : Types.result;
  substitution : Types.substitution;
  uses : Types.capability_set;
  real : Path.t list;
  has_defaults : bool;
}

let unwritten ~definition_key ~anchor ~substitution ~result =
  {
    definition_key;
    anchor;
    enclosing_impl = None;
    text = "";
    result;
    substitution;
    uses = Types.no_capabilities;
    real = [];
    has_defaults = false;
  }

let key_of context path =
  match context.lookups.interface.names.key path with
  | Some key -> key
  | None -> bug "no definition for %s" (Path.show path)

let text_of context key =
  match context.lookups.interface.names.text key with Some text -> text | None -> ""

let bind = Monomorphic.substitution

let impl_interface context impl =
  match Interface.Impls.impl_interface context.lookups.interface impl with
  | Some position -> position
  | None -> bug "no interface for %s" (Path.show impl)

let trait_substitution context impl =
  match Interface.Impls.trait_substitution context.lookups.interface impl with
  | Some substitution -> substitution
  | None -> bug "no trait for %s" (Path.show impl)

let signature_of context (path : Path.t) =
  match Interface.Impls.signature context.lookups.interface path with
  | Some signature -> signature
  | None -> bug "no signature for %s" (Path.show path)

let written context path =
  match Resolve.Names.definition_of_path context.lookups.interface.names path with
  | Some (key, { kind = Function { signature; body }; _ }) -> Some (key, signature, body)
  | _ -> None

let code_of context (path : Path.t) type_arguments : code =
  let function_code ~anchor ~enclosing_impl (key, _, _) ~(interface : Types.signature) ~substitution
      =
    {
      definition_key = key;
      anchor;
      enclosing_impl;
      text = text_of context key;
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
            (unwritten ~definition_key:key ~anchor:path ~substitution:[]
               ~result:(Returns Types.unit))
            with
            text = text_of context key;
            real =
              (match Interface.Definition.test_uses context.lookups.interface path with
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
      match (written context path, path) with
      | Some code, _ -> function_code ~anchor:path ~enclosing_impl code ~interface ~substitution
      | None, Method { owner = Derived { type_; _ }; _ }
        when Mir.is_generated context.lookups.mir path ->
          {
            (unwritten ~definition_key:(key_of context type_) ~anchor:path ~substitution
               ~result:interface.output)
            with
            enclosing_impl;
          }
      | None, Method { owner = (Impl _ | Derived _) as impl; name; receiver } -> (
          let trait = (impl_interface context impl).implements.trait in
          let provided = Path.Method { owner = trait; name; receiver } in
          match written context provided with
          | Some code ->
              let trait_signature = signature_of context provided in
              let count = List.length (impl_interface context impl).impl_generics in
              let of_impl = List.filteri (fun position _ -> position < count) substitution in
              let of_trait =
                List.map
                  (fun (parameter, argument) ->
                    (parameter, Types.substitute_argument of_impl argument))
                  (trait_substitution context impl)
              in
              let own_generics =
                List.filter
                  (fun (generic : Types.generic) -> not (Path.equal generic.generic.owner trait))
                  trait_signature.generics
              in
              let own = List.filteri (fun position _ -> position >= count) type_arguments in
              function_code ~anchor:provided ~enclosing_impl code ~interface:trait_signature
                ~substitution:(of_trait @ bind own_generics own @ substitution)
          | None -> bug "%s neither writes nor is given %s" (Path.show impl) name)
      | None, _ -> bug "%s is not a function" (Path.show path))
  | Member_constant _ | Impl _ | Derived _ | Law_proof _ -> bug "%s is not code" (Path.show path)

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
  | Some contract ->
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
