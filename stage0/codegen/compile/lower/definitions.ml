(* Lowering's inputs: its context, and the code and the signature of the
   instance being lowered. *)
module Names = Resolve.Names
module Environment = Interface.Environment

let bug format = Compiler_bug.bug ~stage:"Lower" format

type context = {
  database : Query.context;
  env : Memory_layout.env;
  glue : Glue.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
  checks : bool;
  constant : Path.t -> Lowered.static_value option;
}

(* The standard library's text types print as quoted text and its lists and
   slices as lists. *)
let debug_form : Ground.ty -> Glue.debug_form = function
  | Named { path; _ } -> (
      match Well_known.of_path path with
      | Some (String | String_slice) -> Text
      | Some (List | Slice) -> Sequence
      | _ -> Structure)
  | _ -> Structure

let context ?(checks = false) ~constant database target =
  let rec monomorphic : Monomorphic.context =
    {
      type_interface = (fun path -> Query.demand database Environment.type_interface path);
      normalize = Interface.Impls.normalize database ~bounds:(fun _ -> []);
      normalize_capabilities = Interface.Impls.normalize_capabilities database ~bounds:(fun _ -> []);
    }
  and context =
    lazy
      (let env = Memory_layout.create target ~shape_of:(Monomorphic.shape monomorphic) in
       let usize = Monomorphic.builtin USize in
       {
         database;
         env;
         glue =
           Glue.create env
             ~representation:(Monomorphic.representation monomorphic)
             ~usize ~debug_form ();
         monomorphic;
         types =
           { usize; string_slice = Named { path = Well_known.path String_slice; arguments = [] } };
         bool = Monomorphic.builtin Bool;
         checks;
         constant = (fun path -> constant (Lazy.force context) path);
       })
  in
  Lazy.force context

let test_key path = Instance.Code { path; type_arguments = [] }

type code = {
  definition_key : Names.key;  (** The definition that holds the body *)
  anchor : Path.t;
  enclosing_impl : Path.t option;
  text : string;  (** The definition's source text, for positions and messages *)
  result : Types.result;
  substitution : Types.substitution;
  uses : Types.capability_set;
  real : Path.t list;
      (** The capabilities the code gets the real implementations of, as [main]'s do: an external
          test's [uses] *)
  has_defaults : bool;
}

let demand context query key = Query.demand context.database query key

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
  match demand context Interface.Summary.key path with
  | Some key -> key
  | None -> bug "no definition for %s" (Path.show path)

let text_of context key = match demand context Names.text key with Some text -> text | None -> ""
let bind = Monomorphic.substitution

let impl_interface context impl =
  match Interface.Impls.impl_interface context.database impl with
  | Some position -> position
  | None -> bug "no interface for %s" (Path.show impl)

(* The instantiation of an [impl]'s [Self] and its trait's parameters, in terms of
   the [impl]'s own generic parameters. *)
let trait_substitution context impl =
  match Interface.Impls.trait_substitution context.database impl with
  | Some substitution -> substitution
  | None -> bug "no trait for %s" (Path.show impl)

let signature_of context (path : Path.t) =
  match Interface.Impls.signature context.database path with
  | Some signature -> signature
  | None -> bug "no signature for %s" (Path.show path)

(* A function written in source at a path: its definition's key, its
   signature, and its body. Each method of an [impl] or a trait is one. *)
let written context path =
  match Interface.Summary.definition context.database path with
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
      let key = key_of context path in
      match demand context Names.definition key with
      | Some { kind = Test _; _ } ->
          {
            (unwritten ~definition_key:key ~anchor:path ~substitution:[]
               ~result:(Returns Types.unit))
            with
            text = text_of context key;
            real =
              (match demand context Environment.interface path with
              | Some (Test_interface uses) ->
                  List.filter_map
                    (function Types.Capability path -> Some path | _ -> None)
                    (uses :> Types.capability list)
              | _ -> []);
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
        when demand context Infer.derived path <> None ->
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

(* How a function's result is passed, and whether it returns at all. *)
let result_of context substitution (result : Types.result) =
  match result with
  | Returns Never -> (Convention.Nothing, false)
  | Returns ty ->
      (Convention.result context.env (Monomorphic.ground context.monomorphic substitution ty), true)
  | Lends (mode, ty) ->
      (* A lending method returns a pointer to its part, or nothing for a
         part of zero size. *)
      let part = Monomorphic.ground context.monomorphic substitution ty in
      ( (if Memory_layout.has_zero_size context.env part then Convention.Nothing
         else Convention.Returned (Pointer { target = Value part; writable = mode = Mut })),
        true )

(* The trailing parameters of a lending method. The first is the slot: a
   pointer to storage of the caller's, where the method builds a part that
   is not a place it was passed, such as a constructor of such places or a
   value that it made. It is null where the caller has no storage that
   lasts as long as the lend: the method then allocates from the lend
   record. A part of zero size has no slot. The second is a pointer to the
   caller's {!Lowered.Lend}, where the method defers the lend's cleanup:
   the values to drop and the places to write back. The third is a pointer
   to the call site, where a lending method of the standard library
   reports a check that fails in it: an index out of bounds is the
   caller's error. *)
let lending_parameters context substitution (result : Types.result) : Lowered.ty list =
  match result with
  | Lends (_, ty) ->
      let part = Monomorphic.ground context.monomorphic substitution ty in
      (if Memory_layout.has_zero_size context.env part then []
       else [ Lowered.Pointer { target = Value part; writable = true } ])
      @ [ Pointer { target = Lend; writable = true }; Raw (Pointer Opaque) ]
  | Returns _ -> []

(* The C signature of a function from its interface, after substitution:
   the result pointer when the result is too large, each parameter, the
   mask of defaults passed when there are defaults, the evidence for each
   capability it uses, and then a lending method's trailing parameters. *)
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

let has_defaults (signature : Types.signature) =
  List.exists (fun (parameter : Types.parameter_info) -> parameter.has_default) signature.parameters

let interface_parameters (signature : Types.signature) =
  (match signature.receiver with
    | Some (receiver, ty) ->
        [ ((match receiver with Mut -> Types.Mut | Own -> Own | Read | Static -> Read), ty) ]
    | None -> [])
  @ List.map (fun (info : Types.parameter_info) -> (info.mode, info.type_)) signature.parameters
