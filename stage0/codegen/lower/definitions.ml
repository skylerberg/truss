(* What lowering reads: its context, and the code, the signature, and the
   tables of the instance being lowered. *)

module S = Syntax
module C = Checked
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
      (** Whether the program checks at run time what the prover would prove: [requires] clauses,
          integer overflow, and division *)
  constant : (Path.t -> Lir.static_value option) ref;
      (** Another constant's value, where it folds, which the driver reads through whatever keeps
          each constant's lowering, so that one is folded once and what reads it is known *)
}

let standard_text name : Ground.ty =
  Named
    {
      path = Top { module_ = { package = "standard"; modules = [ "text" ] }; name };
      arguments = [];
    }

let context ?(checks = false) database target =
  let cursor_fields = ref (fun _ -> bug "no driver gives cursors their fields") in
  let monomorphic : Monomorphic.context =
    {
      type_interface = (fun path -> Query.demand database Environment.type_interface path);
      normalize = Interface.Impls.normalize database ~bounds:(fun _ -> []);
      capabilities = (fun _ -> []);
      cursor_fields = (fun yielding -> !cursor_fields yielding);
    }
  in
  let env = Memory_layout.create target ~shape_of:(Monomorphic.shape monomorphic) in
  let usize = Monomorphic.builtin USize in
  {
    database;
    env;
    glue =
      Glue.create env ~kind_of:(Monomorphic.kind monomorphic) ~usize
        ~debug_form:Monomorphic.debug_form ();
    monomorphic;
    types = { usize; isize = Monomorphic.builtin ISize; string_slice = standard_text "StringSlice" };
    bool = Monomorphic.builtin Bool;
    cursor_fields;
    checks;
    constant = ref (fun path -> bug "no driver gives the value of %s" (Path.show path));
  }

let test_key path = Instance.Code { path; type_arguments = [] }

(* Finding the code of an instance *)

(* A function's body, where it is written, and what its generic parameters
   stand for in this instance. *)
type code = {
  definition_key : Names.key;  (** The definition whose tree and checked form hold the body *)
  anchor : Path.t;  (** The definition positions in the body are relative to *)
  text : string;  (** The definition's source text, for positions and messages *)
  checked : C.t;
  parameters : S.parameter list;
  body : S.block;
  result : T.result;
  parameter_types : (T.mode * T.ty * S.parameter) list;  (** In order, [self] first *)
  substitution : T.substitution;
  uses : T.capability list;
  real : Path.t list;
      (** The capabilities the code gets the real implementations of, as [main]'s do: an external
          test's [uses] *)
  has_defaults : bool;
  requires : S.expression list;  (** The [requires] clauses, which a checked build tests on entry *)
}

let demand context query key = Query.demand context.database query key

(* The code of a function lowering writes itself, which has no source: only
   what its positions are relative to, what its generic parameters stand
   for, and its result. *)
let unwritten ~definition_key ~anchor ~substitution ~result =
  {
    definition_key;
    anchor;
    text = "";
    checked = Checked.create 0;
    parameters = [];
    body = { statements = []; span = S.Span.make 0 0; id = 0 };
    result;
    parameter_types = [];
    substitution;
    uses = [];
    real = [];
    has_defaults = false;
    requires = [];
  }

let key_of context path =
  match demand context Interface.Summary.key path with
  | Some key -> key
  | None -> bug "no definition for %s" (Path.show path)

let checked_of context key =
  match demand context Infer.checked key with
  | Some result -> result.checked
  | None -> bug "no checked form for %s" (Names.show_key key)

let text_of context key = match demand context Names.text key with Some text -> text | None -> ""

let receiver_of (parameters : S.parameter list) : Path.receiver =
  match parameters with
  | { kind = Self_parameter None; _ } :: _ -> Read
  | { kind = Self_parameter (Some Mut); _ } :: _ -> Mut
  | { kind = Self_parameter (Some Own); _ } :: _ -> Own
  | _ -> Static

let name_of (signature : S.signature) =
  match signature.name with Plain_name name -> name.text | Member_name (_, name) -> name.text

let back = Monomorphic.back
let back_argument = Monomorphic.back_argument
let bind = Monomorphic.substitution

let impl_interface context impl =
  match Interface.Impls.impl_interface context.database impl with
  | Some i -> i
  | None -> bug "no interface for %s" (Path.show impl)

(* What an [impl]'s [Self] and its trait's parameters stand for. *)
let self_substitution context (impl : T.impl_interface) =
  let trait = impl.implements.trait in
  let trait_interface =
    match demand context Environment.trait_interface trait with
    | Some i -> i
    | None -> bug "no interface for %s" (Path.show trait)
  in
  ({ T.owner = trait; name = "Self" }, T.Type impl.for_type)
  :: List.map2
       (fun (generic : T.generic) argument -> (generic.generic, argument))
       trait_interface.trait_generics impl.implements.trait_arguments

let rec signature_of context (path : Path.t) =
  match demand context Environment.signature path with
  | Some signature -> (
      (* An [impl]'s method is an instance of the [impl]'s parameters as well
         as its own, which come first, and uses what the [impl] uses. *)
      match path with
      | Method { owner = Impl _ as owner; _ } ->
          let impl = impl_interface context owner in
          let missing =
            List.filter
              (fun (g : T.generic) ->
                not (List.exists (fun (h : T.generic) -> h.generic = g.generic) signature.generics))
              impl.impl_generics
          in
          (* Its [impl]'s [uses] are its own too. *)
          let uses =
            signature.uses
            @ List.filter
                (fun capability -> not (List.mem capability signature.uses))
                impl.impl_uses
          in
          { signature with generics = missing @ signature.generics; uses }
      | _ -> signature)
  | None -> (
      match path with
      | Method { owner = (Impl _ | Derived _) as owner; name; receiver } ->
          (* A method the [impl] leaves to its trait, or one of a derived
             [impl]: the trait's signature, with [Self] and the trait's
             parameters standing for what the [impl] gives them. *)
          let impl = impl_interface context owner in
          let trait = impl.implements.trait in
          let trait_signature = signature_of context (Method { owner = trait; name; receiver }) in
          let substitution = self_substitution context impl in
          let substitute = T.substitute substitution in
          let result : T.result -> T.result = function
            | Returns ty -> Returns (substitute ty)
            | Yields (m, ty) -> Yields (m, substitute ty)
            | Lends (m, ty) -> Lends (m, substitute ty)
          in
          {
            trait_signature with
            generics =
              impl.impl_generics
              @ List.filter
                  (fun (g : T.generic) -> not (Path.equal g.generic.owner trait))
                  trait_signature.generics;
            receiver = Option.map (fun (r, ty) -> (r, substitute ty)) trait_signature.receiver;
            parameters =
              List.map
                (fun (p : T.parameter_info) -> { p with type_ = substitute p.type_ })
                trait_signature.parameters;
            output = result trait_signature.output;
          }
      | _ -> bug "no signature for %s" (Path.show path))

let parameter_types (signature : T.signature) (parameters : S.parameter list) =
  let written =
    List.filter
      (fun (p : S.parameter) -> match p.kind with Self_parameter _ -> false | _ -> true)
      parameters
  in
  let self =
    match (signature.receiver, parameters) with
    | Some (receiver, ty), first :: _ ->
        let mode : T.mode = match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read in
        [ (mode, ty, first) ]
    | _ -> []
  in
  self
  @ List.map2
      (fun (info : T.parameter_info) parameter -> (info.mode, info.type_, parameter))
      signature.parameters written

let code_of context (path : Path.t) type_arguments : code =
  let function_code ~definition_key ~anchor ~checked ~(signature : S.signature) ~body ~interface
      ~substitution =
    {
      definition_key;
      anchor;
      text = text_of context definition_key;
      checked;
      parameters = signature.parameters;
      body;
      result = interface.T.output;
      parameter_types = parameter_types interface signature.parameters;
      substitution;
      uses = interface.uses;
      real = [];
      has_defaults = List.exists (fun (p : T.parameter_info) -> p.has_default) interface.parameters;
      requires =
        List.filter_map
          (fun (clause : S.clause) -> match clause.kind with Requires e -> Some e | _ -> None)
          signature.clauses;
    }
  in
  match path with
  | Test _ -> (
      let key = key_of context path in
      match demand context Names.definition key with
      | Some { kind = Test { body; _ }; _ } ->
          {
            definition_key = key;
            anchor = path;
            text = text_of context key;
            checked = checked_of context key;
            parameters = [];
            body;
            result = Returns T.unit;
            parameter_types = [];
            substitution = [];
            uses = [];
            real =
              (match demand context Environment.interface path with
              | Some (Test_interface uses) ->
                  List.filter_map (function T.Capability path -> Some path | _ -> None) uses
              | _ -> []);
            has_defaults = false;
            requires = [];
          }
      | _ -> bug "%s is not a test" (Path.show path))
  | Method { owner = (Impl _ | Derived _) as impl; name; receiver } -> (
      let interface = signature_of context path in
      let substitution = bind interface.generics type_arguments in
      let written =
        match impl with
        | Derived _ -> None
        | _ -> (
            let impl_key = key_of context impl in
            match demand context Names.definition impl_key with
            | Some { kind = Impl { members; _ }; _ } ->
                List.find_map
                  (fun (member : S.impl_member S.line) ->
                    match member.kind with
                    | Impl_method { signature; body }
                      when name_of signature = name && receiver_of signature.parameters = receiver
                      ->
                        Some (signature, body)
                    | _ -> None)
                  members
            | _ -> bug "%s is not an impl" (Path.show impl))
      in
      match written with
      | Some (signature, body) ->
          let impl_key = key_of context impl in
          function_code ~definition_key:impl_key ~anchor:impl ~checked:(checked_of context impl_key)
            ~signature ~body ~interface ~substitution
      | None -> (
          (* A method the trait provides, compiled for this [impl]: the
             trait's body, with [Self] and the trait's parameters standing
             for what the [impl] gives them. *)
          let impl_interface =
            match Interface.Impls.impl_interface context.database impl with
            | Some i -> i
            | None -> bug "no interface for %s" (Path.show impl)
          in
          let trait = impl_interface.implements.trait in
          let trait_key = key_of context trait in
          let trait_interface =
            match demand context Environment.trait_interface trait with
            | Some i -> i
            | None -> bug "no interface for %s" (Path.show trait)
          in
          let impl_substitution =
            List.filteri (fun i _ -> i < List.length impl_interface.impl_generics) substitution
          in
          let self_substitution =
            ( { T.owner = trait; name = "Self" },
              T.Type (T.substitute impl_substitution impl_interface.for_type) )
            :: List.map2
                 (fun (generic : T.generic) argument ->
                   (generic.generic, T.substitute_argument impl_substitution argument))
                 trait_interface.trait_generics impl_interface.implements.trait_arguments
          in
          match demand context Names.definition trait_key with
          | Some { kind = Trait { members; _ }; _ } -> (
              let provided =
                List.find_map
                  (fun (member : S.trait_member S.line) ->
                    match member.kind with
                    | Trait_method { signature; body = Some body }
                      when name_of signature = name && receiver_of signature.parameters = receiver
                      ->
                        Some (signature, body)
                    | _ -> None)
                  members
              in
              match provided with
              | Some (signature, body) ->
                  let trait_method = Path.Method { owner = trait; name; receiver } in
                  let trait_signature = signature_of context trait_method in
                  let own =
                    List.filteri
                      (fun i _ -> i >= List.length impl_interface.impl_generics)
                      type_arguments
                  in
                  let own_generics =
                    List.filter
                      (fun (generic : T.generic) -> not (Path.equal generic.generic.owner trait))
                      trait_signature.generics
                  in
                  function_code ~definition_key:trait_key ~anchor:trait
                    ~checked:(checked_of context trait_key) ~signature ~body
                    ~interface:trait_signature
                    ~substitution:(self_substitution @ bind own_generics own @ substitution)
              | None -> bug "%s neither writes nor is given %s" (Path.show impl) name)
          | _ -> bug "%s is not a trait" (Path.show trait)))
  | Top _ | Method _ -> (
      let key = key_of context path in
      let interface = signature_of context path in
      match demand context Names.definition key with
      | Some { kind = Function { signature; body }; _ } ->
          function_code ~definition_key:key ~anchor:path ~checked:(checked_of context key)
            ~signature ~body ~interface
            ~substitution:(bind interface.generics type_arguments)
      | _ -> bug "%s is not a function" (Path.show path))
  | Member_constant _ | Impl _ | Derived _ | Law_proof _ -> bug "%s is not code" (Path.show path)

(* The C signature of a function from its interface, after substitution:
   the result pointer when the result is too large, each parameter, the
   mask of defaults passed when there are defaults, and then the evidence
   for each capability it uses. *)
let panic_path : Path.t =
  Top { module_ = { package = "standard"; modules = [ "capabilities" ] }; name = "Panic" }

(* The capabilities a function takes evidence for, in path order: those it
   uses, with capability parameters replaced by what they stand for, but
   [Panic], which has no evidence. *)
let evidence_for (substitution : T.substitution) (uses : T.capability list) =
  List.concat_map
    (function
      | T.Capability path -> [ path ]
      | Capability_parameter p -> (
          match List.assoc_opt p substitution with
          | Some (T.Capabilities set) ->
              List.filter_map (function T.Capability q -> Some q | _ -> None) set
          | _ -> []))
    uses
  |> List.filter (fun path -> not (Path.equal path panic_path))
  |> List.sort_uniq Path.compare

(* How a function's result is passed, and whether it returns at all. *)
let result_of context substitution (result : T.result) =
  match result with
  | Returns Never -> (Convention.Nothing, false)
  | Returns ty ->
      (Convention.result context.env (Monomorphic.ground context.monomorphic substitution ty), true)
  | Yields _ | Lends _ -> (Convention.Nothing, true)

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
  let evidence = List.map (fun _ -> Convention.evidence) (evidence_for substitution uses) in
  (Convention.signature ~returns (written @ mask @ evidence) result_ty, result_ty)

let has_defaults (signature : T.signature) =
  List.exists (fun (p : T.parameter_info) -> p.has_default) signature.parameters

let interface_parameters (signature : T.signature) =
  (match signature.receiver with
    | Some (receiver, ty) ->
        [ ((match receiver with Mut -> T.Mut | Own -> Own | Read | Static -> Read), ty) ]
    | None -> [])
  @ List.map (fun (info : T.parameter_info) -> (info.mode, info.type_)) signature.parameters
