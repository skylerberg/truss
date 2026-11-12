(* What lowering reads: its context, and the code and the signature of the
   instance being lowered. *)

module S = Syntax
module T = Types
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
  cursor_fields : (Ground.yielding -> (string * Memory_layout.member) list) ref;
      (** The fields of a pulled method's cursor, which the driver gives from its pulled lowering *)
  checks : bool;
      (** Whether the program checks, as it runs, each operation that is undefined or wrong where
          its precondition does not hold: an index, a slice, arithmetic, a shift, a call of the C
          library, and [unreachable]. No [requires] clause is evaluated. *)
  constant : (Path.t -> Lir.static_value option) ref;
      (** Another constant's value, where it folds, which the driver reads through whatever keeps
          each constant's lowering, so that one is folded once and what reads it is known *)
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

let context ?(checks = false) database target =
  let cursor_fields = ref (fun _ -> bug "no driver gives cursors their fields") in
  let monomorphic : Monomorphic.context =
    {
      type_interface = (fun path -> Query.demand database Environment.type_interface path);
      normalize = Interface.Impls.normalize database ~bounds:(fun _ -> []);
      normalize_capabilities = Interface.Impls.normalize_capabilities database ~bounds:(fun _ -> []);
      cursor_fields = (fun yielding -> !cursor_fields yielding);
    }
  in
  let env = Memory_layout.create target ~shape_of:(Monomorphic.shape monomorphic) in
  let usize = Monomorphic.builtin USize in
  {
    database;
    env;
    glue =
      Glue.create env ~representation:(Monomorphic.representation monomorphic) ~usize ~debug_form ();
    monomorphic;
    types = { usize; string_slice = Named { path = Well_known.path String_slice; arguments = [] } };
    bool = Monomorphic.builtin Bool;
    cursor_fields;
    checks;
    constant = ref (fun path -> bug "no driver gives the value of %s" (Path.show path));
  }

let test_key path = Instance.Code { path; type_arguments = [] }

(* Finding the code of an instance *)

(* Where a function is written, and what its generic parameters stand for in
   this instance. Its body is in the core form of the definition. *)
type code = {
  definition_key : Names.key;  (** The definition that holds the body *)
  anchor : Path.t;  (** The definition positions in the body are relative to *)
  within : Path.t option;
      (** The [impl] this is a method of, whether the [impl] writes it or leaves it to its trait *)
  text : string;  (** The definition's source text, for positions and messages *)
  result : T.result;
  substitution : T.substitution;
  uses : T.capability list;
  real : Path.t list;
      (** The capabilities the code gets the real implementations of, as [main]'s do: an external
          test's [uses] *)
  has_defaults : bool;
}

let demand context query key = Query.demand context.database query key

(* The code of a function lowering writes itself, which has no source: only
   what its positions are relative to, what its generic parameters stand
   for, and its result. *)
let unwritten ~definition_key ~anchor ~substitution ~result =
  {
    definition_key;
    anchor;
    within = None;
    text = "";
    result;
    substitution;
    uses = [];
    real = [];
    has_defaults = false;
  }

let key_of context path =
  match demand context Interface.Summary.key path with
  | Some key -> key
  | None -> bug "no definition for %s" (Path.show path)

let text_of context key = match demand context Names.text key with Some text -> text | None -> ""
let back = Monomorphic.back
let bind = Monomorphic.substitution

let impl_interface context impl =
  match Interface.Impls.impl_interface context.database impl with
  | Some i -> i
  | None -> bug "no interface for %s" (Path.show impl)

(* What an [impl]'s [Self] and its trait's parameters stand for, in terms of
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
  let function_code ~anchor ~within (key, _, _) ~(interface : T.signature) ~substitution =
    {
      definition_key = key;
      anchor;
      within;
      text = text_of context key;
      result = interface.output;
      substitution;
      uses = interface.uses;
      real = [];
      has_defaults = List.exists (fun (p : T.parameter_info) -> p.has_default) interface.parameters;
    }
  in
  match path with
  | Test _ -> (
      let key = key_of context path in
      match demand context Names.definition key with
      | Some { kind = Test _; _ } ->
          {
            (unwritten ~definition_key:key ~anchor:path ~substitution:[] ~result:(Returns T.unit)) with
            text = text_of context key;
            real =
              (match demand context Environment.interface path with
              | Some (Test_interface uses) ->
                  List.filter_map (function T.Capability path -> Some path | _ -> None) uses
              | _ -> []);
          }
      | _ -> bug "%s is not a test" (Path.show path))
  | Top _ | Method _ -> (
      let interface = signature_of context path in
      let substitution = bind interface.generics type_arguments in
      let within =
        match path with
        | Method { owner = (Impl _ | Derived _) as impl; _ } -> Some impl
        | _ -> None
      in
      match (written context path, path) with
      | Some code, _ -> function_code ~anchor:path ~within code ~interface ~substitution
      | None, Method { owner = (Impl _ | Derived _) as impl; name; receiver } -> (
          (* A method the [impl] leaves to its trait: the trait's own code,
             read with what the trait's [Self] and parameters stand for in
             the [impl], at this instance's arguments for the [impl]'s
             parameters, which come first. *)
          let trait = (impl_interface context impl).implements.trait in
          let provided = Path.Method { owner = trait; name; receiver } in
          match written context provided with
          | Some code ->
              let trait_signature = signature_of context provided in
              let count = List.length (impl_interface context impl).impl_generics in
              let of_impl = List.filteri (fun i _ -> i < count) substitution in
              let of_trait =
                List.map
                  (fun (parameter, argument) -> (parameter, T.substitute_argument of_impl argument))
                  (trait_substitution context impl)
              in
              let own_generics =
                List.filter
                  (fun (generic : T.generic) -> not (Path.equal generic.generic.owner trait))
                  trait_signature.generics
              in
              let own = List.filteri (fun i _ -> i >= count) type_arguments in
              function_code ~anchor:provided ~within code ~interface:trait_signature
                ~substitution:(of_trait @ bind own_generics own @ substitution)
          | None -> bug "%s neither writes nor is given %s" (Path.show impl) name)
      | None, _ -> bug "%s is not a function" (Path.show path))
  | Member_constant _ | Impl _ | Derived _ | Law_proof _ -> bug "%s is not code" (Path.show path)

let panic_path = Monomorphic.panic_capability
let evidence_for context = Monomorphic.evidence_for context.monomorphic

(* How a function's result is passed, and whether it returns at all. *)
let result_of context substitution (result : T.result) =
  match result with
  | Returns Never -> (Convention.Nothing, false)
  | Returns ty ->
      (Convention.result context.env (Monomorphic.ground context.monomorphic substitution ty), true)
  | Yields _ | Lends _ -> (Convention.Nothing, true)

(* The C signature of a function from its interface, after substitution:
   the result pointer when the result is too large, each parameter, the
   mask of defaults passed when there are defaults, and then the evidence
   for each capability it uses. *)
let lir_signature context substitution ~(parameters : (T.mode * T.ty) list) ~has_defaults
    ?(uses = []) (result : T.result) : Lir.signature * Convention.result =
  let ground ty = Monomorphic.ground context.monomorphic substitution ty in
  let result_ty, returns = result_of context substitution result in
  let written =
    List.filter_map
      (fun (mode, ty) -> Convention.parameter context.env (Monomorphic.mode mode) (ground ty))
      parameters
  in
  let mask = if has_defaults then [ Lir.Raw (Integer UInt64) ] else [] in
  let evidence = List.map (fun _ -> Convention.evidence) (evidence_for context substitution uses) in
  (Convention.signature ~returns (written @ mask @ evidence) result_ty, result_ty)

let has_defaults (signature : T.signature) =
  List.exists (fun (p : T.parameter_info) -> p.has_default) signature.parameters

let interface_parameters (signature : T.signature) =
  (match signature.receiver with
    | Some (receiver, ty) ->
        [ ((match receiver with Mut -> T.Mut | Own -> Own | Read | Static -> Read), ty) ]
    | None -> [])
  @ List.map (fun (info : T.parameter_info) -> (info.mode, info.type_)) signature.parameters
