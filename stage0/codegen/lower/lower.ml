open Lir_builder
module S = Syntax
module C = Checked
module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment

let bug format = Printf.ksprintf (fun message -> invalid_arg ("Lower: " ^ message)) format

type context = {
  database : Query.database;
  env : Memory_layout.env;
  glue : Glue.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
  cursor_fields : (Ground.yielding -> (string * Memory_layout.member) list) ref;
      (** The fields of a pulled method's cursor, which the driver gives from its pulled lowering *)
}

let standard_text name : Ground.ty =
  Named
    {
      path = Top { module_ = { package = "standard"; modules = [ "text" ] }; name };
      arguments = [];
    }

let context database target =
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
  has_defaults : bool;
}

let demand context query key = Query.demand context.database query key

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

let rec back : Ground.ty -> T.ty = function
  | Named { path; arguments } -> Named { path; arguments = List.map back_argument arguments }
  | Never -> Never
  | Function f ->
      let mode : Ground.mode -> T.mode = function Read -> Read | Mut -> Mut | Own -> Own in
      Function
        {
          inputs = List.map (fun (m, ty) -> (mode m, back ty)) f.parameters;
          output =
            (match f.result with
            | Returns ty -> Returns (back ty)
            | Yields (m, ty) -> Yields (mode m, back ty)
            | Lends (m, ty) -> Lends (mode m, back ty));
          uses = List.map (fun path -> T.Capability path) f.uses;
          costs = [];
        }
  | Any { trait; arguments; associated } ->
      Any
        {
          trait;
          trait_arguments = List.map back_argument arguments;
          associated = List.map (fun (name, ty) -> (name, back ty)) associated;
        }
  | Cursor { method_; type_arguments } ->
      Cursor { method_; arguments = List.map back_argument type_arguments }

and back_argument : Ground.argument -> T.argument = function
  | Type ty -> Type (back ty)
  | Value v -> Value (Known v)
  | Capabilities set -> Capabilities (List.map (fun path -> T.Capability path) set)

let bind (generics : T.generic list) arguments =
  if List.length generics <> List.length arguments then
    bug "%d generic parameters for %d arguments" (List.length generics) (List.length arguments);
  List.map2
    (fun (generic : T.generic) argument -> (generic.generic, back_argument argument))
    generics arguments

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
      has_defaults = List.exists (fun (p : T.parameter_info) -> p.has_default) interface.parameters;
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
            has_defaults = false;
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

let lir_signature context substitution ~(parameters : (T.mode * T.ty) list) ~has_defaults
    ?(uses = []) (result : T.result) : Lir.signature * Convention.result =
  let ground ty = Monomorphic.ground context.monomorphic substitution ty in
  let result_ty, returns =
    match result with
    | Returns Never -> (Convention.Nothing, false)
    | Returns ty -> (Convention.result context.env (ground ty), true)
    | Yields _ | Lends _ -> (Convention.Nothing, true)
  in
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

(* Lowering one function *)

(* What leaving a scope does: drop what a place still owns, or free the
   heap block a pointer points at, once what is in it has been dropped. *)
type cleanup = Drop_value of Lir.place | Free_pointed of Lir.place
type scope = { mutable owned : cleanup list  (** Most recent first *) }

(* Where [continue] and [break] go, and how many scopes each keeps. *)
type loop = { continue_ : Lir.block; continue_depth : int; break_ : Lir.block; break_depth : int }

(* The code being lowered: the function's own body, or the body of a
   method inlined into it, each with its own tables and names. *)
type frame = {
  code : code;
  bindings : (S.id, Lir.place) Hashtbl.t;
  mutable self_place : Lir.place option;
  on_yield : (Lir.place -> resume:Lir.block -> stop:Lir.block -> unit) option;
      (** In an inlined lending or yielding method, what a [yield] of a place does *)
  inlined : Path.t list;  (** The methods inlined around this frame, to refuse recursion *)
  exit : (Lir.block * int) option;
      (** In an inlined method, where its [return] goes and how many scopes that keeps *)
}

type state = {
  context : context;
  mutable frame : frame;
  b : Lir_builder.t;
  mutable scopes : scope list;  (** Innermost first *)
  mutable loops : loop list;
  mutable temporaries : Lir.place list list;
      (** Of each statement being lowered, innermost first *)
  return_ : Lir.place option;  (** Where a result too large to return is written *)
  result_local : Lir.local option;
  nested : Lir.function_ option list ref;  (** The instance's lambdas, in order *)
  mutable evidence : (Path.t * Lir.operand) list;  (** The evidence for each capability available *)
  pulling : bool;  (** Whether this is a yielding method's pulled version, whose [yield]s stay *)
}

let ground st ty = Monomorphic.ground st.context.monomorphic st.frame.code.substitution ty

let type_of st (id : S.id) =
  match st.frame.code.checked.types.(id) with
  | Some ty -> ground st ty
  | None -> bug "no type for expression %d" id

let raw_type_of st (id : S.id) = st.frame.code.checked.types.(id)
let trivial st ty = Glue.trivial st.context.glue ty
let zero_size st ty = (Memory_layout.of_type st.context.env ty).size = 0

let site st (span : S.span) : Lir.site =
  let text = st.frame.code.text in
  let line = ref 0 and column = ref 1 in
  String.iteri
    (fun i c ->
      if i < span.start then
        if c = '\n' then begin
          incr line;
          column := 1
        end
        else incr column)
    text;
  { definition = st.frame.code.anchor; line = !line; column = !column }

let source st (span : S.span) =
  let text = st.frame.code.text in
  let start = min span.start (String.length text) in
  String.sub text start (min span.stop (String.length text) - start)

let new_local st ?name ty = at (local st.b ?name (Value ty))

(* A temporary that holds an owned value for the rest of the statement. *)
let temporary st ty =
  let place = new_local st ty in
  (match st.temporaries with
  | current :: rest -> st.temporaries <- (place :: current) :: rest
  | [] -> ());
  place

let own_in_scope st place =
  match st.scopes with
  | scope :: _ -> scope.owned <- Drop_value place :: scope.owned
  | [] -> bug "no scope"

(* A heap block the scope frees as it ends, after the drops of what is in it,
   which are owned later and so come first. *)
let free_in_scope st pointer =
  match st.scopes with
  | scope :: _ -> scope.owned <- Free_pointed pointer :: scope.owned
  | [] -> bug "no scope"

let drop_scope st (scope : scope) =
  List.iter
    (function
      | Drop_value place -> emit st.b (Drop place)
      | Free_pointed pointer ->
          emit st.b
            (Call { target = Intrinsic Free; arguments = [ Copy pointer ]; result = Discarded }))
    scope.owned

let drop_temporaries st temporaries = List.iter (fun place -> emit st.b (Drop place)) temporaries

(* Drops everything owned in the scopes inside the [depth] outermost, and
   every pending temporary, as a [return], [break], or [continue] leaves
   them. *)
let leave_to st depth =
  List.iter (drop_temporaries st) st.temporaries;
  List.iteri
    (fun i scope -> if List.length st.scopes - i > depth then drop_scope st scope)
    st.scopes

(* A scope opened here and closed, with its drops, by [close_scope], for a
   condition's names, whose scope ends on more than one path. *)
let open_scope st =
  let scope = { owned = [] } in
  st.scopes <- scope :: st.scopes;
  scope

let close_scope st scope =
  drop_scope st scope;
  match st.scopes with
  | top :: rest when top == scope -> st.scopes <- rest
  | _ -> bug "a scope closed out of order"

let in_scope st f =
  let scope = open_scope st in
  let result = f () in
  close_scope st scope;
  result

let unreachable_block st =
  finish st.b Unreachable;
  start st.b (block st.b)

(* An operand for an owned position: a [var], an [own] argument, a field, a
   returned value. The type checker has made sure a place there is a
   temporary or was marked [own], or copies implicitly. *)
let owned st place ty = if trivial st ty then Lir.Copy place else Lir.Move place
let constant_int integer value = Lir.Constant (Integer (integer, value))

let integer_of st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar (Integer integer) -> integer
  | _ -> bug "%s is not an integer type" (Ground.to_string ty)

let scalar_of st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar scalar -> scalar
  | _ -> bug "%s is not a number" (Ground.to_string ty)

(* Calls *)

(* The instance a trait method's call reaches, once the types are known. *)
let trait_method_key st ~(trait : T.trait_reference) ~name ~receiver ~self_type ~type_arguments
    ~(evidence : C.evidence) =
  let substitute = T.substitute st.frame.code.substitution in
  let impl, arguments =
    match evidence with
    | Impl { impl; arguments } ->
        ( impl,
          List.map (fun (p, a) -> (p, T.substitute_argument st.frame.code.substitution a)) arguments
        )
    | Bound _ -> (
        let self = st.context.monomorphic.normalize (substitute self_type) in
        match
          Interface.Impls.implements st.context.database
            ~bounds:(fun _ -> [])
            self
            (T.substitute_trait st.frame.code.substitution trait)
        with
        | Some (From_impl { impl; substitution }) -> (impl, substitution)
        | _ -> bug "no impl of %s for %s" (T.show_trait trait) (T.show self))
    | Dynamic -> bug "calls through any are not lowered yet"
    | Built_in -> bug "a built-in trait's method"
  in
  let impl_interface =
    match Interface.Impls.impl_interface st.context.database impl with
    | Some i -> i
    | None -> bug "no interface for %s" (Path.show impl)
  in
  let impl_arguments =
    List.map
      (fun (generic : T.generic) ->
        match List.assoc_opt generic.generic arguments with
        | Some argument -> Monomorphic.ground_argument st.context.monomorphic [] argument
        | None -> bug "the impl's parameter %s is not bound" generic.generic.name)
      impl_interface.impl_generics
  in
  Instance.Code
    {
      path = Method { owner = impl; name; receiver };
      type_arguments =
        impl_arguments
        @ List.map
            (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
            type_arguments;
    }

(* An argument as it is passed: by value, by address, or as an owned
   value. *)
(* The operand that gives a place to a parameter that takes it as
   [lir_ty]. *)
let operand_as st (mode : T.mode) ty (place : Lir.place) (lir_ty : Lir.ty option) =
  match lir_ty with
  | None -> None
  | Some (Pointer _) when mode = T.Own -> Some (Lir.Moved_address place)
  | Some (Pointer { writable; _ }) -> Some (Lir.Address { place; writable })
  | Some _ -> ( match mode with Own -> Some (owned st place ty) | Read | Mut -> Some (Copy place))

let pass st (mode : T.mode) ty place =
  operand_as st mode ty place (Convention.parameter st.context.env (Monomorphic.mode mode) ty)

(* How a cursor holds an argument for its method's parameter: an [own]
   argument as a value of its own, since the cursor owns it and may outlive
   the caller's statement, and any other as the parameter takes it. *)
let held context (mode : T.mode) ty =
  match mode with
  | Own -> if (Memory_layout.of_type context.env ty).size = 0 then None else Some (Lir.Value ty)
  | Read | Mut -> Convention.parameter context.env (Monomorphic.mode mode) ty

let hold st mode ty place = operand_as st mode ty place (held st.context mode ty)

(* Calls a function instance with arguments that are places of their
   parameter types, writing the result to [destination]. *)
(* A capability's method: its slot in every table of the capability, and
   its signature. *)
let capability_method context capability name =
  let interface =
    match demand context Environment.trait_interface capability with
    | Some i -> i
    | None -> bug "no interface for %s" (Path.show capability)
  in
  let rec find i = function
    | [] -> bug "%s has no method %s" (Path.show capability) name
    | (m : T.trait_method) :: rest ->
        if m.method_name = name then (i, m.method_signature) else find (i + 1) rest
  in
  find 0 interface.methods

(* The C signature of an entry in a capability's table, which every caller
   and every entry agree on: the evidence, then the method's own. *)
let entry_signature context (signature : T.signature) =
  let lir, result =
    lir_signature context []
      ~parameters:(interface_parameters { signature with receiver = None })
      ~has_defaults:false signature.output
  in
  ({ lir with parameters = Convention.evidence :: lir.parameters }, result)

(* Whether a trait's method can be called through [any]: it has no generic
   parameters of its own, and neither takes nor returns [Self]. *)
let callable_through_any trait (m : T.trait_method) =
  let self = T.Parameter { owner = trait; name = "Self" } in
  let mentions ty = T.equal ty self in
  m.method_receiver <> Static
  && List.for_all
       (fun (g : T.generic) -> Path.equal g.generic.owner trait)
       m.method_signature.generics
  && List.for_all
       (fun (p : T.parameter_info) -> not (mentions p.type_))
       m.method_signature.parameters
  && match m.method_signature.output with Returns ty -> not (mentions ty) | _ -> false

(* The methods of a trait an [any] table has an entry for, in order. *)
let any_methods context trait =
  match demand context Environment.trait_interface trait with
  | Some i -> List.filter (callable_through_any trait) i.methods
  | None -> bug "no interface for %s" (Path.show trait)

(* A method's slot in an [any] table, after the drop in slot 0. *)
let dynamic_slot context trait name =
  let rec find i = function
    | [] -> bug "%s cannot be called through any" name
    | (m : T.trait_method) :: rest ->
        if m.method_name = name then (i, m.method_signature) else find (i + 1) rest
  in
  find 1 (any_methods context trait)

(* The C signature of an entry in an [any] table: the value's pointer, then
   the method's own, with the evidence for what it uses. *)
let any_entry_signature context (signature : T.signature) =
  let lir, result =
    lir_signature context []
      ~parameters:(interface_parameters { signature with receiver = None })
      ~has_defaults:false ~uses:signature.uses signature.output
  in
  ({ lir with parameters = Lir.Raw (Pointer Opaque) :: lir.parameters }, result)

(* The evidence for a capability, where the code being lowered has it. *)
let evidence_of st capability =
  match List.find_opt (fun (path, _) -> Path.equal path capability) st.evidence with
  | Some (_, operand) -> operand
  | None -> bug "no evidence for %s here" (Path.show capability)

let call_instance st key ~(signature : T.signature) ~substitution
    ~(arguments : (T.mode * Ground.ty * Lir.place) list) ~mask ~destination =
  let lir_signature, result =
    lir_signature st.context substitution ~parameters:(interface_parameters signature)
      ~has_defaults:(has_defaults signature) ~uses:signature.uses signature.output
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let mask =
    (if has_defaults signature then [ constant_int UInt64 (Z.of_int mask) ] else [])
    @ List.map (evidence_of st) (evidence_for substitution signature.uses)
  in
  let target = Lir.Direct { function_ = Instance key; signature = lir_signature } in
  emit st.b
    (Call { target; arguments = passed @ mask; result = Convention.destination result destination });
  if not lir_signature.returns then unreachable_block st

(* Expressions *)

let literal st (id : S.id) =
  match st.frame.code.checked.literals.(id) with
  | Some literal -> literal
  | None -> bug "no literal for %d" id

let constant_of st ty (literal : C.literal) : Lir.operand =
  match (literal, scalar_of st ty) with
  | Integer_value value, Integer integer -> constant_int integer value
  | Integer_value value, Character -> Constant (Character (Z.to_int value))
  | Float_value value, Float64 -> Constant (Float64 (Int64.bits_of_float value))
  | Float_value value, Float32 -> Constant (Float32 (Int32.bits_of_float value))
  | _ -> bug "a literal of type %s" (Ground.to_string ty)

(* A string literal's [String]: its bytes as static data, with capacity
   0. *)
let string_value st ty text =
  match Monomorphic.shape st.context.monomorphic ty with
  | Record [ (field, Typed storage) ] ->
      let storage_value =
        Lir.Build
          {
            ty = storage;
            variant = None;
            fields =
              [
                ("buffer", Constant (Bytes text));
                ("length", usize (String.length text));
                ("capacity", usize 0);
              ];
          }
      in
      (field, storage, storage_value)
  | _ -> bug "%s is not a record of storage" (Ground.to_string ty)

(* What a yielding method yields, in an instance. *)
let cursor_element context (yielding : Ground.yielding) =
  let signature = signature_of context yielding.method_ in
  match signature.output with
  | Yields (_, ty) ->
      Monomorphic.ground context.monomorphic (bind signature.generics yielding.type_arguments) ty
  | _ -> bug "%s does not yield" (Path.show yielding.method_)

(* What a cursor's [next] returns: an [Option] of what it yields. *)
let cursor_result context yielding : Ground.ty =
  Named
    {
      path = Top { module_ = { package = "standard"; modules = [ "option" ] }; name = "Option" };
      arguments = [ Type (cursor_element context yielding) ];
    }

(* Calls a trait's method on a value of a ground type, through the [impl]
   the type has, with arguments that are places. *)
(* A trait of the standard library's [core] module. *)
let core name : Path.t = Top { module_ = { package = "standard"; modules = [ "core" ] }; name }

let trait_call st ~trait ~name ~(receiver : Path.receiver) ~self ~arguments ~destination =
  match
    Interface.Impls.implements st.context.database
      ~bounds:(fun _ -> [])
      (back self)
      { trait; trait_arguments = []; associated = [] }
  with
  | Some (From_impl { impl; substitution }) ->
      let interface = impl_interface st.context impl in
      let type_arguments =
        List.map
          (fun (g : T.generic) ->
            match List.assoc_opt g.generic substitution with
            | Some argument -> Monomorphic.ground_argument st.context.monomorphic [] argument
            | None -> bug "an unbound parameter of %s" (Path.show impl))
          interface.impl_generics
      in
      let path = Path.Method { owner = impl; name; receiver } in
      let signature = signature_of st.context path in
      call_instance st
        (Code { path; type_arguments })
        ~signature
        ~substitution:(bind signature.generics type_arguments)
        ~arguments ~mask:0 ~destination
  | _ -> bug "%s has no impl of %s" (Ground.to_string self) (Path.show trait)

let rec expression st (e : S.expression) : Lir.place =
  match e.kind with
  | Parenthesized inner | Mode (_, inner) -> expression st inner
  | Todo | Unreachable | Return _ | Break | Continue ->
      (* These never give a value, so what they are written into is never
         read. *)
      let nowhere = new_local st (Monomorphic.builtin Unit) in
      into st e nowhere;
      nowhere
  | Name _ | Member _ | Self_value | Bracket _ | Call _ -> (
      (* An index or a lending call names a place, as a name does. *)
      match place_expression st e with
      | Some place -> place
      | None ->
          let destination = temporary st (type_of st e.id) in
          into st e destination;
          destination)
  | _ ->
      let ty = type_of st e.id in
      let destination = temporary st ty in
      into st e destination;
      destination

(* The place an expression names, if it names one: a local, a parameter,
   [self], or a field of one. *)
and place_expression st (e : S.expression) : Lir.place option =
  match e.kind with
  | Parenthesized inner | Mode (_, inner) -> place_expression st inner
  | Self_value -> st.frame.self_place
  | (Name _ | Member _) when constant_place st e <> None -> constant_place st e
  | Name _ -> (
      match st.frame.code.checked.meanings.(e.id) with
      | Some (Local_value local) -> (
          match Hashtbl.find_opt st.frame.bindings local with
          | Some place -> Some place
          | None -> bug "local %d is not bound" local)
      | _ -> None)
  | Member (base, name) -> (
      match st.frame.code.checked.meanings.(e.id) with
      | Some (Field_read _) ->
          let base = expression st base in
          Some (base / Field name.text)
      | _ -> None)
  | Bracket (base, items) -> (
      match st.frame.code.checked.calls.(e.id) with
      | Some call_ ->
          let expressions =
            base
            :: List.filter_map (function S.Item e -> Some e | Item_constraint _ -> None) items
          in
          let arguments =
            if call_.arguments <> [] then with_receiver st call_ ~expressions call_.arguments
            else
              List.mapi
                (fun i (e : S.expression) ->
                  { C.expression = e.id; parameter = i; mode = Read; conversion = None })
                expressions
          in
          Some (lend st call_ ~expressions ~arguments)
      | None -> None)
  | Call (_, arguments) when lending_intrinsic st e -> (
      (* [storage_at], [storage_at_mut], and [view_at] lend an element's
         place itself. *)
      match st.frame.code.checked.calls.(e.id) with
      | Some { callee = Intrinsic { operation; type_arguments }; arguments = checked; _ } ->
          let type_arguments =
            List.filter_map
              (fun a ->
                match
                  Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution a
                with
                | Type ty -> Some ty
                | _ -> None)
              type_arguments
          in
          let expressions = List.map (fun (a : S.argument) -> a.value) arguments in
          let values =
            List.map
              (fun (argument : C.argument) ->
                let e =
                  List.find (fun (x : S.expression) -> x.id = argument.expression) expressions
                in
                (argument.parameter, e))
              checked
            |> List.sort (fun (a, _) (b, _) -> Int.compare a b)
            |> List.map (fun (parameter, e) ->
                if parameter = 0 then Intrinsics.Place (expression st e)
                else Intrinsics.Value (operand st e))
          in
          Intrinsics.lower st.context.env st.b st.context.types operation ~type_arguments values
            ~destination:None ~site:(site st e.span)
      | _ -> None)
  | Call (callee, arguments) -> (
      match st.frame.code.checked.calls.(e.id) with
      | Some ({ callee = Function _ | Trait_method _; _ } as call_) when lends st call_ ->
          let expressions = call_expressions call_ callee arguments in
          Some
            (lend st call_ ~expressions
               ~arguments:(with_receiver st call_ ~expressions call_.arguments))
      | _ -> None)
  | _ -> None

(* A constant's static data, which is a read-only place. *)
and constant_place st (e : S.expression) =
  match st.frame.code.checked.meanings.(e.id) with
  | Some (Global { path; _ }) -> (
      match demand st.context Environment.constant_type path with
      | Some ty ->
          Some { Lir.root = Static { key = Constant path; ty = ground st ty }; projections = [] }
      | None -> None)
  | _ -> None

and lending_intrinsic st (e : S.expression) =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Intrinsic { operation = Storage_at | Storage_at_mut | View_at; _ }; _ } -> true
  | _ -> false

(* Whether a call is to a lending method. *)
and lends st (call_ : C.call) =
  match resolve_callee st call_ with
  | Some (path, _) -> (
      match (signature_of st.context path).output with Lends _ -> true | _ -> false)
  | None -> false

(* The instance a call to a function or a trait method reaches. *)
and resolve_callee st (call_ : C.call) =
  match call_.callee with
  | Trait_method { evidence = Dynamic | Built_in; _ } -> None
  | Function { path; type_arguments } ->
      Some
        ( path,
          List.map
            (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
            type_arguments )
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } -> (
      match trait_method_key st ~trait ~name ~receiver ~self_type ~type_arguments ~evidence with
      | Code { path; type_arguments } -> Some (path, type_arguments)
      | _ -> None)
  | _ -> None

and call_expressions (call_ : C.call) (callee : S.expression) (arguments : S.argument list) =
  let expressions = List.map (fun (a : S.argument) -> a.value) arguments in
  match (call_.callee, callee.kind) with
  | Trait_method { receiver = Read | Mut | Own; _ }, Member (receiver, _)
  | Function { path = Method { receiver = Read | Mut | Own; _ }; _ }, Member (receiver, _) ->
      receiver :: expressions
  | _ -> expressions

(* A call's arguments with its receiver, which the checked form does not
   list: the first expression, in the mode the method takes [self] in. *)
and with_receiver st (call_ : C.call) ~(expressions : S.expression list)
    (arguments : C.argument list) =
  let receiver : Path.receiver =
    match call_.callee with
    | Trait_method { receiver; evidence = Dynamic; _ } -> receiver
    | _ -> (
        match resolve_callee st call_ with
        | Some (Method { receiver; _ }, _) -> receiver
        | _ -> Static)
  in
  match (receiver, expressions) with
  | (Read | Mut | Own), first :: _
    when not (List.exists (fun (a : C.argument) -> a.parameter = 0) arguments) ->
      let mode : T.mode = match receiver with Mut -> Mut | Own -> Own | _ -> Read in
      { C.expression = first.id; parameter = 0; mode; conversion = None } :: arguments
  | _ -> arguments

(* The one implicit conversion: a [List] passed where a [Slice] is wanted,
   or a [String] where a [StringSlice] is, becomes a view of it without
   copying, from two of its storage's three fields. *)
and convert st (argument : C.argument) place ty =
  match argument.conversion with
  | Some Owned_to_view -> (
      let view_path (path : Path.t) : Path.t =
        match path with
        | Top { module_ = { package = "standard"; modules = [ "list" ] } as m; name = "List" } ->
            Top { module_ = m; name = "Slice" }
        | Top { module_ = { package = "standard"; modules = [ "text" ] } as m; name = "String" } ->
            Top { module_ = m; name = "StringSlice" }
        | _ -> bug "a view of %s" (Path.show path)
      in
      match ty with
      | Ground.Named { path; arguments } -> (
          let view_ty = Ground.Named { path = view_path path; arguments } in
          match
            ( Monomorphic.shape st.context.monomorphic ty,
              Monomorphic.shape st.context.monomorphic view_ty )
          with
          | Record [ (storage_field, _) ], Record [ (view_field, Typed view) ] ->
              let viewed = new_local st view_ty in
              emit st.b
                (Assign
                   ( viewed / Field view_field,
                     Build
                       {
                         ty = view;
                         variant = None;
                         fields =
                           [
                             ("elements", Copy (place / Field storage_field / Field "buffer"));
                             ("length", Copy (place / Field storage_field / Field "length"));
                           ];
                       } ));
              (viewed, view_ty)
          | _ -> bug "a view of %s" (Ground.to_string ty))
      | _ -> bug "a view of %s" (Ground.to_string ty))
  | Some From_never | Some Function_widening | None -> (place, ty)
  | Some (To_integer | From_integer) -> bug "a conversion that exists only in specifications"

(* The arguments of a call as places, in parameter order. *)
and evaluate_arguments st ~(expressions : S.expression list) ~(arguments : C.argument list) =
  let by_id id = List.find (fun (e : S.expression) -> e.id = id) expressions in
  let evaluate (argument : C.argument) =
    let e = by_id argument.expression in
    let ty = type_of st e.id in
    let place =
      match argument.mode with
      | Mut | Read -> expression st e
      | Own -> (
          match place_expression st e with
          | Some place ->
              let moved = new_local st ty in
              emit st.b (Assign (moved, Use (owned st place ty)));
              moved
          | None -> expression st e)
    in
    let place, ty = convert st argument place ty in
    (argument.parameter, argument.mode, ty, place)
  in
  List.map evaluate arguments
  |> List.sort (fun (a, _, _, _) (b, _, _, _) -> Int.compare a b)
  |> List.map (fun (_, mode, ty, place) -> (mode, ty, place))

(* Inlines a lending or yielding method's body with its parameters bound to
   [arguments], handing each [yield] to [on_yield]. *)
and inline st path type_arguments ~arguments ~on_yield =
  if List.exists (Path.equal path) st.frame.inlined then
    bug "%s yields through recursion, which stage0 does not lower yet" (Path.show path);
  let code = code_of st.context path type_arguments in
  let exit = block st.b in
  let caller = st.frame in
  let frame =
    {
      code;
      bindings = Hashtbl.create 16;
      self_place = None;
      on_yield = Some on_yield;
      inlined = path :: caller.inlined;
      exit = Some (exit, List.length st.scopes);
    }
  in
  if List.length code.parameter_types <> List.length arguments then
    bug "%s takes %d parameters and is given %d arguments" (Path.show path)
      (List.length code.parameter_types)
      (List.length arguments);
  st.frame <- frame;
  in_scope st (fun () ->
      List.iter2
        (fun (mode, _, (parameter : S.parameter)) (_, ty, place) ->
          (match parameter.kind with
          | Self_parameter _ -> frame.self_place <- Some place
          | Named_parameter { name; _ } -> Hashtbl.replace frame.bindings name.id place
          | Parameter_error -> ());
          if mode = T.Own && not (trivial st ty) then own_in_scope st place)
        code.parameter_types arguments;
      block_into st code.body None);
  finish st.b (Goto exit);
  start st.b exit;
  st.frame <- caller

(* The place a lending method lends, by inlining it. Its [yield] must be
   its last statement, so nothing it does after lending can run before the
   caller uses the place. *)
and lend st call_ ~expressions ~arguments =
  match resolve_callee st call_ with
  | Some (path, type_arguments) -> (
      let arguments = evaluate_arguments st ~expressions ~arguments in
      let lent = ref None in
      inline st path type_arguments ~arguments ~on_yield:(fun place ~resume ~stop:_ ->
          lent := Some place;
          finish st.b (Goto resume));
      match !lent with Some place -> place | None -> bug "a lending method that lends nothing")
  | None -> bug "a lending call that is not to a method"

and operand st (e : S.expression) =
  let ty = type_of st e.id in
  match e.kind with
  | Integer _ | Float _ -> constant_of st ty (literal st e.id)
  | Prefix (Negate, ({ kind = Integer _; _ } as inner))
    when st.frame.code.checked.calls.(e.id) = None ->
      negated_literal st ty inner
  | True -> Constant (Bool true)
  | False -> Constant (Bool false)
  | _ -> Copy (expression st e)

(* Writes the value of an expression to [destination]. *)
and into st (e : S.expression) (destination : Lir.place) =
  let ty () = type_of st e.id in
  let assign rvalue = emit st.b (Assign (destination, rvalue)) in
  match e.kind with
  | Parenthesized inner | Mode (_, inner) -> into st inner destination
  | Integer _ | Float _ -> assign (Use (constant_of st (ty ()) (literal st e.id)))
  | True -> assign (Use (Constant (Bool true)))
  | False -> assign (Use (Constant (Bool false)))
  | String _ when st.frame.code.checked.literals.(e.id) <> None ->
      (* A tagged character, such as [Character"a"] or [UInt8"\n"]: a number. *)
      assign (Use (constant_of st (ty ()) (literal st e.id)))
  | String literal when literal.rest = [] && literal.tag = None ->
      let field, storage_ty, storage = string_value st (ty ()) literal.first.value in
      let built = new_local st storage_ty in
      emit st.b (Assign (built, storage));
      assign (Build { ty = ty (); variant = None; fields = [ (field, Move built) ] })
  | Name _ | Self_value | Member _ -> (
      match place_expression st e with
      | Some place -> assign (Use (owned st place (ty ())))
      | None -> name_value st e destination)
  | Call (callee, arguments) -> call st e ~callee ~arguments destination
  | Binary { operator = And | Or; _ } | Is _ ->
      (* A condition's value: whether its jumps reach [yes]. *)
      in_scope st (fun () ->
          let yes = block st.b and no = block st.b and after = block st.b in
          branch st e ~yes ~no;
          start st.b yes;
          assign (Use (Constant (Bool true)));
          finish st.b (Goto after);
          start st.b no;
          assign (Use (Constant (Bool false)));
          finish st.b (Goto after);
          start st.b after)
  | Binary { left; right; _ } -> operator st e [ left; right ] destination
  | Prefix (Negate, ({ kind = Integer _; _ } as inner))
    when st.frame.code.checked.calls.(e.id) = None ->
      assign (Use (negated_literal st (ty ()) inner))
  | Prefix (Not, inner) when st.frame.code.checked.calls.(e.id) = None || is_built_in st e ->
      assign (Unary (Not, operand st inner))
  | Prefix (_, inner) -> operator st e [ inner ] destination
  | Block block -> block_into st block (Some destination)
  | If { condition; then_; else_ } -> if_ st ~condition ~then_ ~else_ (Some destination)
  | Match { scrutinees; arms } -> match_ st ~scrutinees ~arms (Some destination)
  | Return value ->
      return_ st value;
      ()
  | Break -> (
      match st.loops with
      | loop :: _ ->
          leave_to st loop.break_depth;
          finish st.b (Goto loop.break_);
          start st.b (block st.b)
      | [] -> bug "a break outside a loop")
  | Continue -> (
      match st.loops with
      | loop :: _ ->
          leave_to st loop.continue_depth;
          finish st.b (Goto loop.continue_);
          start st.b (block st.b)
      | [] -> bug "a continue outside a loop")
  | Todo ->
      let message = "todo reached" in
      finish st.b
        (Fail
           {
             failure = Todo;
             message = Constant (Bytes message);
             length = usize (String.length message);
             site = site st e.span;
           });
      start st.b (block st.b)
  | Unreachable -> unreachable_block st
  | Echo inner ->
      into st inner destination;
      echo st destination (ty ()) e.span
  | List elements -> list_into st (ty ()) elements destination ~span:e.span
  | Try inner -> try_ st inner destination
  | String literal when literal.tag = None -> interpolate st literal destination
  | String literal -> (
      match st.frame.code.checked.templates.(literal.id) with
      | Some template when template.from_template <> None ->
          template_into st literal template destination ~span:e.span
      | _ -> bug "a tagged string with no template")
  | With (base, updates) -> with_ st base updates destination
  | Lambda { parameters; body } -> lambda st e ~parameters ~body destination
  | Bracket _ -> (
      match place_expression st e with
      | Some place -> assign (Use (owned st place (ty ())))
      | None -> bug "an index with no meaning")
  | Any inner -> any_value st e inner destination
  | Map entries ->
      collection_into st (ty ()) destination ~span:e.span
        (List.map
           (fun ((key : S.expression), (value : S.expression)) ->
             [ (key, type_of st key.id); (value, type_of st value.id) ])
           entries)
  | Range { start = Some start; stop = Some stop; inclusive } ->
      (* A [Range] value: its two ends and whether it includes the last. *)
      let end_ (e : S.expression) = owned st (expression st e) (type_of st e.id) in
      let start = end_ start in
      let stop = end_ stop in
      assign
        (Build
           {
             ty = ty ();
             variant = None;
             fields = [ ("start", start); ("stop", stop); ("inclusive", Constant (Bool inclusive)) ];
           })
  | Provide { implementations; body } -> provide st e implementations body destination
  | Range _ | Quantified _ -> bug "this expression is not lowered yet: %s" (source st e.span)
  | Self_type_value -> bug "Self as a value"
  | Expression_error -> bug "an expression that did not parse"

(* A literal negated directly, which the type checker checked as one
   literal. *)
and negated_literal st ty (inner : S.expression) =
  match literal st inner.id with
  | Integer_value value -> constant_of st ty (Integer_value (Z.neg value))
  | Float_value value -> constant_of st ty (Float_value (Float.neg value))

(* A [[...]] literal: an [Array], filled in place, or a [List], with storage
   of exactly its length, which costs the one allocation DESIGN.md counts. *)
and list_into st ty (elements : S.expression list) destination ~span =
  match ty with
  | Named
      { path = Top { module_ = { package = "standard"; modules = [ "set" ] }; name = "Set" }; _ } ->
      collection_into st ty destination ~span
        (List.map (fun (e : S.expression) -> [ (e, type_of st e.id) ]) elements)
  | _ -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Array _ ->
          List.iteri
            (fun i (e : S.expression) -> into st e (destination / Index (usize i)))
            elements
      | Record [ (_, Typed _) ] ->
          list_of st ty destination ~span
            (List.map (fun (e : S.expression) value -> into st e value) elements)
      | _ -> bug "a list literal of %s, which is not lowered yet" (Ground.to_string ty))

(* A [List] in [destination], with storage of exactly its length, holding
   what each fill writes to the element's place it is given. *)
and list_of st ty destination ~span fills =
  match Monomorphic.shape st.context.monomorphic ty with
  | Record [ (field, Typed storage) ] -> (
      match Monomorphic.kind st.context.monomorphic storage with
      | Storage element ->
          let storage_place = destination / Field field in
          let lower operation arguments destination =
            ignore
              (Intrinsics.lower st.context.env st.b st.context.types operation
                 ~type_arguments:[ element ] arguments ~destination ~site:(site st span))
          in
          lower Storage_with_capacity [ Value (usize (List.length fills)) ] (Some storage_place);
          List.iter
            (fun fill ->
              let value = new_local st element in
              fill value;
              lower Storage_push [ Place storage_place; Value (owned st value element) ] None)
            fills
      | _ -> bug "a list of %s" (Ground.to_string ty))
  | _ -> bug "%s is not a list" (Ground.to_string ty)

(* A tagged string, such as [Sql"..."]: a [Template] of its literal text,
   each piece a [Literal] of static bytes, and its parts, each made the
   tag's [Part] through its [From], given to the tag's [from_template]. *)
and template_into st (literal : S.string_literal) (template : C.template) destination ~span =
  let call_ =
    match template.from_template with Some c -> c | None -> bug "a tag with no from_template"
  in
  let path, type_arguments =
    match resolve_callee st call_ with Some r -> r | None -> bug "a from_template not resolved"
  in
  let signature = signature_of st.context path in
  let substitution = bind signature.generics type_arguments in
  let mode, template_ty =
    match interface_parameters signature with
    | [ (mode, ty) ] -> (mode, Monomorphic.ground st.context.monomorphic substitution ty)
    | _ -> bug "from_template takes one template"
  in
  let field_type ty name =
    match Monomorphic.shape st.context.monomorphic ty with
    | Record fields -> (
        match List.assoc_opt name fields with
        | Some (Memory_layout.Typed ty) -> ty
        | _ -> bug "%s has no field %s" (Ground.to_string ty) name)
    | _ -> bug "%s is not a record" (Ground.to_string ty)
  in
  let element list_ty =
    match Monomorphic.shape st.context.monomorphic list_ty with
    | Record [ (_, Typed storage) ] -> (
        match Monomorphic.kind st.context.monomorphic storage with
        | Storage element -> element
        | _ -> bug "%s is not a list" (Ground.to_string list_ty))
    | _ -> bug "%s is not a list" (Ground.to_string list_ty)
  in
  let literals_ty = field_type template_ty "literals" in
  let parts_ty = field_type template_ty "parts" in
  let literal_ty = element literals_ty in
  let slice_ty = field_type literal_ty "text" in
  let texts =
    literal.first.value :: List.map (fun (_, (text : S.text)) -> text.value) literal.rest
  in
  let built = temporary st template_ty in
  list_of st literals_ty (built / Field "literals") ~span
    (List.map
       (fun text value ->
         let slice = string_place st slice_ty text in
         emit st.b
           (Assign
              (value, Build { ty = literal_ty; variant = None; fields = [ ("text", Copy slice) ] })))
       texts);
  list_of st parts_ty (built / Field "parts") ~span
    (List.map2
       (fun ((part : S.expression), _) conversion value ->
         match conversion with
         | Some (call_ : C.call) ->
             call_with st call_ ~expressions:[ part ] ~arguments:call_.arguments value ~span
         | None -> into st part value)
       literal.rest template.part_conversions);
  call_instance st
    (Code { path; type_arguments })
    ~signature ~substitution
    ~arguments:[ (mode, template_ty, built) ]
    ~mask:0 ~destination

(* A [Set] or [Map] literal: the collection made empty, then each item
   inserted with the type's own [insert], which keeps it in order and keeps
   the last of equal keys. Each item is the arguments [insert] takes after
   the collection. *)
and collection_into st ty destination ~span items =
  let path, arguments =
    match ty with
    | Named { path; arguments } -> (path, arguments)
    | _ -> bug "a collection literal of %s" (Ground.to_string ty)
  in
  (match Monomorphic.shape st.context.monomorphic ty with
  | Record [ (field, Typed list) ] -> list_into st list [] (destination / Field field) ~span
  | _ -> bug "%s is not a record of a list" (Ground.to_string ty));
  let insert = Path.Method { owner = path; name = "insert"; receiver = Mut } in
  let signature = signature_of st.context insert in
  let substitution = bind signature.generics arguments in
  List.iter
    (fun parts ->
      let values =
        List.map
          (fun ((e : S.expression), part_ty) ->
            let value = new_local st part_ty in
            into st e value;
            (T.Own, part_ty, value))
          parts
      in
      call_instance st
        (Code { path = insert; type_arguments = arguments })
        ~signature ~substitution
        ~arguments:((T.Mut, ty, destination) :: values)
        ~mask:0
        ~destination:(new_local st (Monomorphic.builtin Unit)))
    items

(* [provide]: each implementation evaluated once, as a place or a temporary
   that lives to the end of the statement, and for each capability it
   provides, evidence on the stack pointing at it, its table, and the
   evidence it captures from the code around the [provide]. The body runs
   with that evidence. *)
and provide st (e : S.expression) implementations body destination =
  let provides =
    match st.frame.code.checked.provides.(e.id) with
    | Some p -> p.implementations
    | None -> bug "a provide with no meaning"
  in
  let around = st.evidence in
  let rec provided_by (e : S.expression) =
    match List.assoc_opt e.id provides with
    | Some provided -> provided
    | None -> (
        match e.kind with
        | Mode (_, inner) | Parenthesized inner -> provided_by inner
        | _ -> bug "an implementation with no capabilities")
  in
  let added =
    List.concat_map
      (fun (implementation : S.expression) ->
        let ty = type_of st implementation.id in
        let pointer =
          if zero_size st ty then Lir.Constant Null
          else Address { place = expression st implementation; writable = true }
        in
        List.map
          (fun (provided : C.provided) ->
            let interface = impl_interface st.context provided.impl in
            let type_arguments =
              List.map
                (fun (g : T.generic) ->
                  match List.assoc_opt g.generic provided.arguments with
                  | Some a ->
                      Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution
                        a
                  | None -> bug "an unbound parameter of %s" (Path.show provided.impl))
                interface.impl_generics
            in
            let outer =
              List.map
                (fun capability ->
                  match List.find_opt (fun (path, _) -> Path.equal path capability) around with
                  | Some (_, operand) -> operand
                  | None -> bug "no evidence for %s here" (Path.show capability))
                (evidence_for [] interface.impl_uses)
            in
            let slot = local st.b (Evidence (List.length outer)) in
            emit st.b
              (Call
                 {
                   target = Intrinsic Evidence_fill;
                   arguments =
                     Address { place = at slot; writable = true }
                     :: pointer
                     :: Constant (Symbol_address (Table { impl = provided.impl; type_arguments }))
                     :: outer;
                   result = Discarded;
                 });
            (provided.capability, Lir.Address { place = at slot; writable = false }))
          (provided_by implementation))
      implementations
  in
  st.evidence <- added @ around;
  block_into st body (Some destination);
  st.evidence <- around

(* [?]: the error, or [None], returned at once, as the function's own
   result type; otherwise the value inside. *)
and try_ st (inner : S.expression) destination =
  let ty = type_of st inner.id in
  let value = expression st inner in
  let variants =
    match Monomorphic.shape st.context.monomorphic ty with
    | Sum v -> v
    | _ -> bug "? on %s" (Ground.to_string ty)
  in
  let success, failure =
    match List.map (fun (v : Memory_layout.variant_shape) -> v.name) variants with
    | [ "Ok"; "Err" ] -> ("Ok", "Err")
    | [ "Some"; "None" ] -> ("Some", "None")
    | _ -> bug "? on %s" (Ground.to_string ty)
  in
  let fields name =
    (List.find (fun (v : Memory_layout.variant_shape) -> v.name = name) variants).fields
  in
  let failed = local st.b (Raw Bool) in
  emit st.b (Assign (at failed, Is_variant (value, failure)));
  let leave = block st.b and stay = block st.b in
  finish st.b (Switch { value = Copy (at failed); cases = [ (Z.one, leave) ]; default = Some stay });
  start st.b leave;
  let result_ty =
    match st.frame.code.result with
    | Returns t -> ground st t
    | _ -> bug "? in a method that yields"
  in
  let returned =
    List.map
      (fun (name, member) ->
        match member with
        | Memory_layout.Typed field_ty ->
            (name, owned st (value / Variant_field { variant = failure; field = name }) field_ty)
        | Raw _ -> bug "a raw field")
      (fields failure)
  in
  let built = new_local st result_ty in
  emit st.b (Assign (built, Build { ty = result_ty; variant = Some failure; fields = returned }));
  (match (st.return_, st.result_local) with
  | Some pointer, _ -> emit st.b (Assign (pointer, Use (Move built)))
  | None, Some local -> emit st.b (Assign (at local, Use (Move built)))
  | None, None -> ());
  leave_to st 0;
  finish st.b
    (Return (match st.result_local with Some local -> Some (Move (at local)) | None -> None));
  start st.b stay;
  match fields success with
  | [ (name, Typed field_ty) ] ->
      emit st.b
        (Assign
           ( destination,
             Use (owned st (value / Variant_field { variant = success; field = name }) field_ty) ))
  | _ -> bug "? on a variant with more than one field"

(* A call through a function value: its code, given its environment first,
   then the arguments by position. *)
and call_function_value st ~(callee : S.expression) ~(arguments : S.argument list) destination =
  let f =
    match type_of st callee.id with
    | Function f -> f
    | ty -> bug "a call of %s" (Ground.to_string ty)
  in
  let value = expression st callee in
  let signature = Convention.function_value st.context.env f in
  let passed =
    List.concat
      (List.map2
         (fun ((mode : Ground.mode), ty) (argument : S.argument) ->
           let types_mode : T.mode = match mode with Read -> Read | Mut -> Mut | Own -> Own in
           let place =
             match (place_expression st argument.value, mode) with
             | Some place, Own ->
                 let moved = new_local st ty in
                 emit st.b (Assign (moved, Use (owned st place ty)));
                 moved
             | Some place, _ -> place
             | None, _ -> expression st argument.value
           in
           Option.to_list (pass st types_mode ty place))
         f.parameters arguments)
  in
  let target = Lir.Indirect { value = Copy value; signature } in
  match f.result with
  | Returns ty ->
      emit st.b
        (Call
           {
             target;
             arguments = passed;
             result = Convention.(destination (result st.context.env ty)) destination;
           });
      if ty = Never then unreachable_block st
  | Yields _ | Lends _ -> bug "a function value that yields"

(* A lambda: a nested function whose environment holds the address of each
   local it reads, made on the caller's stack, so making one never
   allocates. *)
and lambda st (e : S.expression) ~(parameters : S.pattern list) ~(body : S.block) destination =
  let f =
    match type_of st e.id with Function f -> f | ty -> bug "a lambda of %s" (Ground.to_string ty)
  in
  let captures = Option.value st.frame.code.checked.captures.(e.id) ~default:[] in
  let index = List.length !(st.nested) in
  st.nested := !(st.nested) @ [ None ];
  let captured =
    List.mapi
      (fun i local ->
        let place =
          match Hashtbl.find_opt st.frame.bindings local with
          | Some p -> p
          | None -> bug "an unbound capture"
        in
        let ty =
          match st.frame.code.checked.local_types.(local) with
          | Some ty -> ground st ty
          | None -> bug "a capture with no type"
        in
        (Printf.sprintf "capture%d" i, local, place, ty))
      captures
  in
  let environment =
    List.map
      (fun (name, _, _, ty) -> (name, Lir.Pointer { target = Value ty; writable = false }))
      captured
  in
  (* The caller fills in the environment and makes the value. *)
  let environment_local = at (local st.b (Environment index)) in
  List.iter
    (fun (name, _, place, _) ->
      emit st.b (Assign (environment_local / Field name, Use (Address { place; writable = false }))))
    captured;
  emit st.b
    (Assign
       ( destination,
         Function_value
           {
             code = Nested index;
             environment = Some (Address { place = environment_local; writable = false });
           } ));
  (* The lambda itself. *)
  let b = Lir_builder.create () in
  let environment_parameter = local b ~name:"environment" (Raw (Nullable_pointer Opaque)) in
  let result_ty = match f.result with Returns ty -> ty | _ -> bug "a lambda that yields" in
  let result = Convention.result st.context.env result_ty in
  let return_pointer =
    match result with Through_pointer pointer -> Some (local b ~name:"result" pointer) | _ -> None
  in
  let parameter_places =
    List.map
      (fun ((mode : Ground.mode), ty) ->
        match Convention.parameter st.context.env mode ty with
        | Some (Pointer _ as pointer) ->
            let l = local b pointer in
            (Some l, { Lir.root = Local l; projections = [ Deref ] }, mode, ty)
        | Some lir_ty ->
            let l = local b lir_ty in
            (Some l, at l, mode, ty)
        | None -> (None, at (local b (Value ty)), mode, ty))
      f.parameters
  in
  let result_local =
    match result with Returned ty -> Some (local b ~name:"result" ty) | _ -> None
  in
  let environment_pointer = local b (Pointer { target = Environment index; writable = false }) in
  let inner =
    {
      st with
      frame =
        { st.frame with bindings = Hashtbl.copy st.frame.bindings; on_yield = None; exit = None };
      b;
      scopes = [ { owned = [] } ];
      loops = [];
      temporaries = [];
      return_ =
        Option.map
          (fun pointer -> { Lir.root = Local pointer; projections = [ Deref ] })
          return_pointer;
      result_local;
    }
  in
  start b (block b);
  emit b (Assign (at environment_pointer, Use (Copy (at environment_parameter))));
  List.iter
    (fun (name, local, _, _) ->
      Hashtbl.replace inner.frame.bindings local
        { Lir.root = Local environment_pointer; projections = [ Deref; Field name; Deref ] })
    captured;
  List.iter2
    (fun (pattern : S.pattern) (_, place, (mode : Ground.mode), ty) ->
      bind_pattern inner pattern place ty ~owned:(mode = Own))
    parameters parameter_places;
  let destination =
    match (inner.return_, result_local) with
    | Some pointer, _ -> Some pointer
    | None, Some local -> Some (at local)
    | None, None -> None
  in
  block_into inner body destination;
  drop_scope inner (List.hd inner.scopes);
  finish b (Return (Option.map (fun local -> Lir.Move (at local)) result_local));
  let function_ =
    Lir_builder.build b ?written_result:return_pointer
      ~parameters:
        ((environment_parameter :: Option.to_list return_pointer)
        @ List.filter_map (fun (l, _, _, _) -> l) parameter_places)
      ~result:(match result with Returned ty -> Some ty | _ -> None)
  in
  st.nested :=
    List.mapi (fun i f -> if i = index then Some { function_ with environment } else f) !(st.nested)

(* [base with (field: value)]: the base as an owned value, then each field
   written in place, which costs one write per field. *)
and with_ st (base : S.expression) (updates : S.update list) destination =
  let ty = type_of st base.id in
  (match place_expression st base with
  | Some place -> emit st.b (Assign (destination, Use (owned st place ty)))
  | None -> into st base destination);
  List.iter
    (fun (update : S.update) ->
      match update.kind with
      | Update { field; path; value } -> (
          let target =
            List.fold_left
              (fun place (name : S.name) -> place / Lir.Field name.text)
              destination (field :: path)
          in
          match value with
          | Some value -> into st value target
          | None -> (
              (* [with (x)] uses the local named [x]. *)
              let resolved = demand st.context Resolve.resolved st.frame.code.definition_key in
              match Option.bind resolved (fun r -> r.names.(field.id)) with
              | Some (Local local) -> (
                  match Hashtbl.find_opt st.frame.bindings local with
                  | Some place ->
                      let field_ty =
                        match st.frame.code.checked.local_types.(local) with
                        | Some ty -> ground st ty
                        | None -> bug "a local with no type"
                      in
                      emit st.b (Assign (target, Use (owned st place field_ty)))
                  | None -> bug "an unbound local in with")
              | _ -> bug "with (x) names no local"))
      | Update_error -> bug "an update that did not parse")
    updates

(* An untagged string with interpolation: each piece written into a
   [TextBuilder], the parts through their [Display]. *)
and interpolate st (literal : S.string_literal) destination =
  let text_path name : Path.t =
    Top { module_ = { package = "standard"; modules = [ "text" ] }; name }
  in
  let builder_ty = Ground.Named { path = text_path "TextBuilder"; arguments = [] } in
  let slice_ty = Ground.Named { path = text_path "StringSlice"; arguments = [] } in
  let method_ name receiver = Path.Method { owner = text_path "TextBuilder"; name; receiver } in
  let call path arguments destination =
    let signature = signature_of st.context path in
    call_instance st
      (Code { path; type_arguments = [] })
      ~signature ~substitution:[] ~arguments ~mask:0 ~destination
  in
  let builder = new_local st builder_ty in
  call (method_ "new" Static) [] builder;
  let unit = Monomorphic.builtin Unit in
  let write text =
    if text <> "" then begin
      let slice = new_local st slice_ty in
      (match Monomorphic.shape st.context.monomorphic slice_ty with
      | Record [ (field, Typed view) ] ->
          emit st.b
            (Assign
               ( slice / Field field,
                 Build
                   {
                     ty = view;
                     variant = None;
                     fields =
                       [
                         ("elements", Constant (Bytes text)); ("length", usize (String.length text));
                       ];
                   } ))
      | _ -> bug "a StringSlice that is not a view");
      call (method_ "write" Mut)
        [ (Mut, builder_ty, builder); (Read, slice_ty, slice) ]
        (new_local st unit)
    end
  in
  write literal.first.value;
  List.iter
    (fun ((part : S.expression), (text : S.text)) ->
      let ty = type_of st part.id in
      let place = expression st part in
      trait_call st
        ~trait:(Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Display" })
        ~name:"display" ~receiver:Read ~self:ty
        ~arguments:[ (Read, ty, place); (Mut, builder_ty, builder) ]
        ~destination:(new_local st unit);
      write text.value)
    literal.rest;
  call (method_ "finish" Own) [ (Own, builder_ty, builder) ] destination

(* [any value]: the value moved into a block of its own, the one
   allocation an [any] costs, with the table for its type and trait. *)
and any_value st (e : S.expression) (inner : S.expression) destination =
  let any_ty = type_of st e.id in
  let inner_ty = type_of st inner.id in
  let trait, arguments, associated =
    match any_ty with
    | Any { trait; arguments; associated } -> (trait, arguments, associated)
    | _ -> bug "any of %s" (Ground.to_string any_ty)
  in
  let impl, substitution =
    match
      Interface.Impls.implements st.context.database
        ~bounds:(fun _ -> [])
        (back inner_ty)
        {
          trait;
          trait_arguments = List.map back_argument arguments;
          associated = List.map (fun (name, ty) -> (name, back ty)) associated;
        }
    with
    | Some (From_impl { impl; substitution }) -> (impl, substitution)
    | _ -> bug "%s has no impl of %s" (Ground.to_string inner_ty) (Path.show trait)
  in
  let interface = impl_interface st.context impl in
  let type_arguments =
    List.map
      (fun (g : T.generic) ->
        match List.assoc_opt g.generic substitution with
        | Some a -> Monomorphic.ground_argument st.context.monomorphic [] a
        | None -> bug "an unbound parameter of %s" (Path.show impl))
      interface.impl_generics
  in
  let layout = Memory_layout.of_type st.context.env inner_ty in
  let block = local st.b (Raw (Pointer Opaque)) in
  if layout.size = 0 then emit st.b (Assign (at block, Use (Constant (Bytes ""))))
  else begin
    emit st.b
      (Call
         {
           target = Intrinsic Allocate;
           arguments = [ usize layout.size; usize layout.alignment ];
           result = Returned (at block);
         });
    let typed = local st.b (Pointer { target = Value inner_ty; writable = true }) in
    emit st.b (Assign (at typed, Use (Copy (at block))));
    let value = expression st inner in
    emit st.b
      (Assign ({ root = Local typed; projections = [ Deref ] }, Use (owned st value inner_ty)))
  end;
  emit st.b
    (Assign
       ( destination,
         Build
           {
             ty = any_ty;
             variant = None;
             fields =
               [
                 ("value", Copy (at block));
                 ("vtable", Constant (Symbol_address (Any_table { impl; type_arguments })));
               ];
           } ))

and is_built_in st (e : S.expression) =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Built_in_operator; _ } -> true
  | _ -> false

and echo st place ty span =
  emit st.b (Call { target = Intrinsic Debug_begin; arguments = []; result = Discarded });
  let arguments = if zero_size st ty then [] else [ Lir.Address { place; writable = false } ] in
  emit st.b
    (Call
       {
         target =
           Direct
             {
               function_ = Instance (Debug ty);
               signature = Glue.debug_signature st.context.glue ty;
             };
         arguments;
         result = Discarded;
       });
  let bytes = local st.b (Raw (Pointer Opaque))
  and length = local st.b (Value st.context.types.usize) in
  emit st.b (Call { target = Intrinsic Debug_bytes; arguments = []; result = Returned (at bytes) });
  emit st.b
    (Call { target = Intrinsic Debug_length; arguments = []; result = Returned (at length) });
  emit st.b (Echo { text = Copy (at bytes); length = Copy (at length); site = site st span })

(* A name that is not a place: a variant with no fields, or a constant. *)
and name_value st (e : S.expression) destination =
  match st.frame.code.checked.meanings.(e.id) with
  | Some (Variant_value { type_; variant }) ->
      emit st.b
        (Assign (destination, Build { ty = ground st type_; variant = Some variant; fields = [] }))
  | Some (Global { path; type_arguments }) -> (
      (* A named function as a value: an adapter that takes the
         environment, and ignores it. *)
      match type_of st e.id with
      | Function ty ->
          let function_ =
            Instance.Code
              {
                path;
                type_arguments =
                  List.map
                    (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
                    type_arguments;
              }
          in
          emit st.b
            (Assign
               ( destination,
                 Function_value { code = Instance (Adapter { function_; ty }); environment = None }
               ))
      | ty -> bug "a global of %s" (Ground.to_string ty))
  | Some meaning -> bug "this name is not lowered yet: %s" (C.show_meaning meaning)
  | None -> bug "a name with no meaning: %s" (source st e.span)

(* An operator: a call of the trait method or intrinsic the checked form
   chose, with the operands as its arguments in order, or a built-in
   operation on [Bool] or integers. *)
and operator st (e : S.expression) operands destination =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Built_in_operator; _ } -> (
      let operand_values = List.map (operand st) operands in
      let rvalue : Lir.rvalue =
        match (e.kind, operand_values) with
        | Binary { operator; _ }, [ left; right ] ->
            Binary
              ( (match operator with
                | Bit_and -> Bit_and
                | Bit_or -> Bit_or
                | Bit_xor -> Bit_xor
                | Shift_left -> Shift_left
                | Shift_right -> Shift_right
                | Equal -> Equal
                | Not_equal -> Not_equal
                | Less -> Less
                | Less_equal -> Less_equal
                | Greater -> Greater
                | Greater_equal -> Greater_equal
                | _ -> bug "a built-in binary operator"),
                left,
                right )
        | Prefix (Not, _), [ value ] -> Unary (Not, value)
        | Prefix (Complement, _), [ value ] -> Unary (Complement, value)
        | Prefix (Negate, _), [ value ] -> Unary (Negate, value)
        | _ -> bug "a built-in operator"
      in
      match e.kind with _ -> emit st.b (Assign (destination, rvalue)))
  | Some call_ -> (
      let arguments =
        List.mapi
          (fun i (operand : S.expression) ->
            { C.expression = operand.id; parameter = i; mode = Read; conversion = None })
          operands
      in
      let arguments = if call_.arguments = [] then arguments else call_.arguments in
      (* A comparison is a call of [equal] or [compare], whose result it
         tests. *)
      let test variant ~negate =
        let ordering =
          new_local st
            (Named
               {
                 path =
                   Top
                     { module_ = { package = "standard"; modules = [ "core" ] }; name = "Ordering" };
                 arguments = [];
               })
        in
        call_with st call_ ~expressions:operands ~arguments ordering ~span:e.span;
        let is = local st.b (Raw Bool) in
        emit st.b (Assign (at is, Is_variant (ordering, variant)));
        emit st.b
          (Assign (destination, if negate then Unary (Not, Copy (at is)) else Use (Copy (at is))))
      in
      match e.kind with
      | Binary { operator = Less; _ } -> test "Less" ~negate:false
      | Binary { operator = Less_equal; _ } -> test "Greater" ~negate:true
      | Binary { operator = Greater; _ } -> test "Greater" ~negate:false
      | Binary { operator = Greater_equal; _ } -> test "Less" ~negate:true
      | Binary { operator = Not_equal; _ } ->
          let equal = new_local st st.context.bool in
          call_with st call_ ~expressions:operands ~arguments equal ~span:e.span;
          emit st.b (Assign (destination, Unary (Not, Copy equal)))
      | _ -> call_with st call_ ~expressions:operands ~arguments destination ~span:e.span)
  | None -> bug "an operator with no call: %s" (source st e.span)

and call st (e : S.expression) ~callee ~arguments destination =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Function_value; _ } -> call_function_value st ~callee ~arguments destination
  | Some call_ ->
      let expressions = List.map (fun (a : S.argument) -> a.value) arguments in
      let expressions =
        match (call_.callee, callee.kind) with
        | Trait_method { receiver = Read | Mut | Own; _ }, Member (receiver, _)
        | Function { path = Method { receiver = Read | Mut | Own; _ }; _ }, Member (receiver, _) ->
            receiver :: expressions
        | _ -> expressions
      in
      call_with st call_ ~expressions
        ~arguments:(with_receiver st call_ ~expressions call_.arguments)
        destination ~span:e.span
  | None -> bug "a call with no meaning: %s" (source st e.span)

(* A call whose arguments are [expressions], which the checked form's
   [arguments] say where they go. *)
and call_with st (call_ : C.call) ~(expressions : S.expression list) ~(arguments : C.argument list)
    destination ~span =
  if lends st call_ then
    emit st.b
      (Assign
         ( destination,
           Use (owned st (lend st call_ ~expressions ~arguments) (ground st call_.result)) ))
  else
    let by_id id = List.find (fun (e : S.expression) -> e.id = id) expressions in
    let evaluate (argument : C.argument) =
      let e = by_id argument.expression in
      let ty = type_of st e.id in
      let place =
        match argument.mode with
        | Mut | Read -> expression st e
        | Own -> (
            match place_expression st e with
            | Some place ->
                (* An [own] place moves into a temporary the callee takes. *)
                let moved = new_local st ty in
                emit st.b (Assign (moved, Use (owned st place ty)));
                moved
            | None -> expression st e)
      in
      let place, ty = convert st argument place ty in
      (argument.parameter, argument.mode, ty, place)
    in
    let evaluated = List.map evaluate arguments in
    let in_order = List.sort (fun (a, _, _, _) (b, _, _, _) -> Int.compare a b) evaluated in
    match call_.callee with
    | (Function _ | Trait_method _) when yields_cursor st call_ ->
        (* A yielding method called outside a [for] loop makes a cursor,
           which holds its arguments. *)
        let path, type_arguments = Option.get (resolve_callee st call_) in
        let signature = signature_of st.context path in
        let substitution = bind signature.generics type_arguments in
        let arguments = with_placeholders st signature substitution in_order in
        let passed = List.filter_map (fun (mode, ty, place) -> hold st mode ty place) arguments in
        let evidence = List.map (evidence_of st) (evidence_for substitution signature.uses) in
        let fields =
          List.mapi (fun i operand -> (Printf.sprintf "local%d" i, operand)) (passed @ evidence)
        in
        let cursor = Ground.Cursor { method_ = path; type_arguments } in
        emit st.b
          (Assign
             ( destination,
               Build
                 {
                   ty = cursor;
                   variant = None;
                   fields = ("state", Constant (Integer (UInt32, Z.zero))) :: fields;
                 } ))
    | Trait_method { name = "next"; self_type; evidence = Built_in; _ }
      when match ground st self_type with Cursor _ -> true | _ -> false -> (
        match (ground st self_type, in_order) with
        | Cursor yielding, (_, _, _, cursor) :: _ -> call_next st yielding cursor destination
        | _ -> bug "next with no cursor")
    | Function { path; type_arguments } ->
        let signature = signature_of st.context path in
        let ground_arguments =
          List.map
            (Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution)
            type_arguments
        in
        let substitution = bind signature.generics ground_arguments in
        let mask = default_mask signature call_ in
        call_instance st
          (Code { path; type_arguments = ground_arguments })
          ~signature ~substitution
          ~arguments:(with_placeholders st signature substitution in_order)
          ~mask ~destination
    | Trait_method { trait; name; evidence = Dynamic; _ } -> (
        (* Through an [any] value: the entry in its table. *)
        let slot, signature = dynamic_slot st.context trait.trait name in
        let lir_signature, result = any_entry_signature st.context signature in
        match in_order with
        | (_, _, _, any) :: rest ->
            let passed = List.filter_map (fun (_, mode, ty, place) -> pass st mode ty place) rest in
            let evidence = List.map (evidence_of st) (evidence_for [] signature.uses) in
            let target =
              Lir.Table_call
                {
                  table = Copy (any / Field "vtable");
                  value = Copy (any / Field "value");
                  slot;
                  signature = lir_signature;
                }
            in
            emit st.b
              (Call
                 {
                   target;
                   arguments = passed @ evidence;
                   result = Convention.destination result destination;
                 });
            if not lir_signature.returns then unreachable_block st
        | [] -> bug "a call through any with no receiver")
    | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
        let key = trait_method_key st ~trait ~name ~receiver ~self_type ~type_arguments ~evidence in
        let path = match key with Code { path; _ } -> path | _ -> bug "a trait method's key" in
        let type_arguments =
          match key with Code { type_arguments; _ } -> type_arguments | _ -> []
        in
        let signature = signature_of st.context path in
        let substitution = bind signature.generics type_arguments in
        call_instance st key ~signature ~substitution
          ~arguments:(with_placeholders st signature substitution in_order)
          ~mask:(default_mask signature call_) ~destination
    | Constructor { type_ = _; variant; _ } ->
        let ty = ground st call_.result in
        let names = constructor_fields st ty variant in
        let fields =
          List.map
            (fun (parameter, _, field_ty, place) ->
              (List.nth names parameter, owned st place field_ty))
            in_order
        in
        let fields = fields @ field_defaults st ty variant call_.defaults_left_out in
        emit st.b (Assign (destination, Build { ty; variant; fields }))
    | Intrinsic { operation; type_arguments } -> (
        let type_arguments =
          List.filter_map
            (fun a ->
              match
                Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution a
              with
              | Type ty -> Some ty
              | _ -> None)
            type_arguments
        in
        let intrinsic_arguments =
          List.map
            (fun (_, mode, ty, place) ->
              match (Monomorphic.kind st.context.monomorphic ty, mode) with
              | Storage _, _ -> Intrinsics.Place place
              | _, T.Mut -> Intrinsics.Place place
              | Shape (Record [ ("elements", _); ("length", _) ]), _ -> Intrinsics.Place place
              | _ -> Intrinsics.Value (if mode = T.Own then owned st place ty else Copy place))
            in_order
        in
        match
          Intrinsics.lower st.context.env st.b st.context.types operation ~type_arguments
            intrinsic_arguments ~destination:(Some destination) ~site:(site st span)
        with
        | Some lent -> emit st.b (Assign (destination, Use (Copy lent)))
        | None -> ())
    | Function_value -> bug "a call through a function value, which [call] lowers"
    | Capability_method { capability; _ } when Path.equal capability panic_path -> (
        (* [Panic.crash] has no evidence: it ends the process at once. *)
        match in_order with
        | [ (_, _, _, message) ] ->
            ignore
              (Intrinsics.lower st.context.env st.b st.context.types Crash ~type_arguments:[]
                 [ Intrinsics.Place message ] ~destination:None ~site:(site st span))
        | _ -> bug "Panic.crash takes one message")
    | Capability_method { capability; name } ->
        let slot, signature = capability_method st.context capability name in
        let lir_signature, result = entry_signature st.context signature in
        let passed = List.filter_map (fun (_, mode, ty, place) -> pass st mode ty place) in_order in
        let evidence = evidence_of st capability in
        let target = Lir.Evidence_call { evidence; slot; signature = lir_signature } in
        emit st.b
          (Call { target; arguments = passed; result = Convention.destination result destination });
        if not lir_signature.returns then unreachable_block st
    | Built_in_operator -> bug "a built-in operator called as a function"

(* Every parameter's argument, in order: a parameter left to its default
   gets a placeholder, which the function overwrites from its default. *)
and with_placeholders st (signature : T.signature) substitution in_order =
  List.mapi
    (fun index (mode, ty) ->
      match List.find_opt (fun (parameter, _, _, _) -> parameter = index) in_order with
      | Some (_, mode, ty, place) -> (mode, ty, place)
      | None ->
          ( mode,
            Monomorphic.ground st.context.monomorphic substitution ty,
            new_local st (Monomorphic.ground st.context.monomorphic substitution ty) ))
    (interface_parameters signature)

and yields_cursor st (call_ : C.call) =
  match resolve_callee st call_ with
  | Some (path, _) -> (
      match (signature_of st.context path).output with Yields _ -> true | _ -> false)
  | None -> false

(* [next()] on a cursor: the pulled method's state machine. *)
and call_next st (yielding : Ground.yielding) cursor destination =
  let option = cursor_result st.context yielding in
  let cursor_pointer = Lir.Pointer { target = Value (Cursor yielding); writable = true } in
  let target signature = Lir.Direct { function_ = Instance (Cursor_next yielding); signature } in
  let self = Lir.Address { place = cursor; writable = true } in
  let convention = Convention.result st.context.env option in
  emit st.b
    (Call
       {
         target = target (Convention.signature [ cursor_pointer ] convention);
         arguments = [ self ];
         result = Convention.destination convention destination;
       })

and default_mask (signature : T.signature) (call_ : C.call) =
  let defaulted = List.filter (fun (p : T.parameter_info) -> p.has_default) signature.parameters in
  let bits =
    List.mapi
      (fun i (p : T.parameter_info) ->
        if List.mem p.name call_.defaults_left_out then 0 else 1 lsl i)
      defaulted
  in
  List.fold_left ( lor ) 0 bits

(* The values of the fields left to their defaults: each default lowered
   where the type writes it, with the type's own tables. *)
and field_defaults st ty variant left_out =
  if left_out = [] then []
  else
    let path =
      match ty with Named { path; _ } -> path | _ -> bug "defaults of %s" (Ground.to_string ty)
    in
    let key = key_of st.context path in
    let declared =
      match (demand st.context Names.definition key, variant) with
      | Some { kind = Type_definition { body = Fields fields; _ }; _ }, None -> fields
      | Some { kind = Type_definition { body = Variants variants; _ }; _ }, Some name -> (
          match List.find_opt (fun (v : S.variant) -> v.name.text = name) variants with
          | Some { fields = Some fields; _ } -> fields
          | _ -> [])
      | _ -> bug "the definition of %s" (Path.show path)
    in
    let shape =
      match (Monomorphic.shape st.context.monomorphic ty, variant) with
      | Record fields, None -> fields
      | Sum variants, Some name ->
          (List.find (fun (v : Memory_layout.variant_shape) -> v.name = name) variants).fields
      | _ -> []
    in
    let caller = st.frame in
    let type_args = match ty with Named { arguments; _ } -> arguments | _ -> [] in
    let interface =
      match demand st.context Environment.type_interface path with
      | Some i -> i
      | None -> bug "no interface for %s" (Path.show path)
    in
    let code =
      {
        caller.code with
        definition_key = key;
        anchor = path;
        text = text_of st.context key;
        checked = checked_of st.context key;
        substitution = bind interface.type_generics type_args;
      }
    in
    st.frame <- { caller with code; bindings = Hashtbl.create 1; self_place = None };
    let values =
      List.map
        (fun name ->
          let default =
            List.find_map
              (fun (field : S.field) ->
                match field.kind with
                | Field_declaration { name = n; default = Some d; _ } when n.text = name -> Some d
                | _ -> None)
              declared
          in
          let field_ty =
            match List.assoc_opt name shape with Some (Typed t) -> t | _ -> bug "no field %s" name
          in
          match default with
          | Some d ->
              let value = new_local st field_ty in
              into st d value;
              (name, owned st value field_ty)
          | None -> bug "no default for %s" name)
        left_out
    in
    st.frame <- caller;
    values

(* The fields of a record or a variant, in declaration order, which a
   constructor's parameters are numbered by. *)
and constructor_fields st ty variant =
  match (Monomorphic.shape st.context.monomorphic ty, variant) with
  | Record fields, None -> List.map fst fields
  | Sum variants, Some name -> (
      match List.find_opt (fun (v : Memory_layout.variant_shape) -> v.name = name) variants with
      | Some v -> List.map fst v.fields
      | None -> bug "no variant %s" name)
  | _ -> bug "a constructor of %s" (Ground.to_string ty)

and return_ st value =
  match st.frame.exit with
  | Some (exit, depth) ->
      (* A [return] in an inlined method ends the method. *)
      (match value with Some e -> ignore (expression st e) | None -> ());
      leave_to st depth;
      finish st.b (Goto exit);
      start st.b (block st.b)
  | None ->
      (match (value, st.return_, st.result_local) with
      | Some e, Some pointer, _ -> into st e pointer
      | Some e, None, Some local -> into st e (at local)
      | Some e, None, None -> ignore (expression st e)
      | None, _, _ -> ());
      leave_to st 0;
      finish st.b
        (Return (match st.result_local with Some local -> Some (Move (at local)) | None -> None));
      start st.b (block st.b)

(* Blocks and statements *)

and block_into st (block : S.block) destination =
  in_scope st (fun () ->
      let rec go = function
        | [] -> ()
        | [ ({ S.kind = Expression e; _ } : S.statement) ] -> (
            match destination with
            | Some d ->
                st.temporaries <- [] :: st.temporaries;
                into st e d;
                end_statement st
            | None ->
                statement st
                  { kind = Expression e; span = e.span; blank_line_before = false; id = e.id })
        | s :: rest ->
            statement st s;
            go rest
      in
      go block.statements)

and end_statement st =
  match st.temporaries with
  | current :: rest ->
      drop_temporaries st current;
      st.temporaries <- rest
  | [] -> ()

and statement st (s : S.statement) =
  st.temporaries <- [] :: st.temporaries;
  (match s.kind with
  | Expression e -> ignore (expression st e)
  | Let { mutable_; pattern; value; else_ = None; _ } -> let_ st ~mutable_ pattern value
  | Let { pattern; value; else_ = Some else_; _ } ->
      let place, temporary = scrutinee st value in
      let matched = block st.b and failed = block st.b in
      test_pattern st pattern place (type_of st value.id) ~matched ~failed;
      start st.b failed;
      block_into st else_ None;
      unreachable_block st;
      start st.b matched;
      bind_pattern st pattern place (type_of st value.id) ~owned:temporary
  | Assignment { target; operator = Assign; value } -> (
      match place_expression st target with
      | Some place -> into st value place
      | None -> bug "an assignment to something that is not a place")
  | Assignment { target; value; _ } -> (
      match (place_expression st target, st.frame.code.checked.calls.(s.id)) with
      | Some place, Some call_ ->
          let ty = type_of st target.id in
          let result = new_local st ty in
          let arguments =
            [
              {
                C.expression = target.id;
                parameter = 0;
                mode = (if trivial st ty then Read else Own);
                conversion = None;
              };
              { C.expression = value.id; parameter = 1; mode = Read; conversion = None };
            ]
          in
          call_with st call_ ~expressions:[ target; value ] ~arguments result ~span:s.span;
          emit st.b (Assign (place, Use (owned st result ty)))
      | _ -> bug "a compound assignment that is not lowered: %s" (source st s.span))
  | While { condition; body; _ } ->
      (* Each test's temporaries end before the body or the exit; the names
         it binds live until the body ends. *)
      let test = block st.b and inside = block st.b and failed = block st.b in
      let after = block st.b in
      let depth = List.length st.scopes in
      finish st.b (Goto test);
      start st.b test;
      let scope = open_scope st in
      st.temporaries <- [] :: st.temporaries;
      branch st condition ~yes:inside ~no:failed;
      let temporaries = List.hd st.temporaries in
      st.temporaries <- List.tl st.temporaries;
      start st.b failed;
      drop_temporaries st temporaries;
      drop_scope st scope;
      finish st.b (Goto after);
      start st.b inside;
      drop_temporaries st temporaries;
      st.loops <-
        { continue_ = test; continue_depth = depth; break_ = after; break_depth = depth }
        :: st.loops;
      block_into st body None;
      st.loops <- List.tl st.loops;
      close_scope st scope;
      finish st.b (Goto test);
      start st.b after
  | For { pattern; iterable; body; parallel = _; _ } -> for_ st s ~pattern ~iterable ~body
  | Assert condition ->
      let value = operand st condition in
      let failed = block st.b and after = block st.b in
      finish st.b (Switch { value; cases = [ (Z.one, after) ]; default = Some failed });
      start st.b failed;
      let message = "assert " ^ source st condition.span in
      finish st.b
        (Fail
           {
             failure = Assertion;
             message = Constant (Bytes message);
             length = usize (String.length message);
             site = site st s.span;
           });
      start st.b after
  | Proof _ -> ()
  | Parallel block ->
      (* Stage0 runs a [parallel] block's branches one after another. *)
      List.iter (statement st) block.statements
  | Yield value -> (
      match st.frame.on_yield with
      | Some on_yield ->
          let place = expression st value in
          let resume = block st.b and stop = block st.b in
          on_yield place ~resume ~stop;
          (* The [stop] path: what the method owns is dropped as the loop
             leaves it. *)
          start st.b stop;
          (match st.frame.exit with
          | Some (exit, depth) ->
              leave_to st depth;
              finish st.b (Goto exit)
          | None -> finish st.b Unreachable);
          start st.b resume
      | None when st.pulling ->
          (* In a pulled method, a [yield] stays, for yield lowering to make a
             state of. Its [stop] path drops what the method owns. *)
          let ty = type_of st value.id in
          let place, temporary = scrutinee st value in
          (* [next] gives its caller a value of its own: what the method
             makes, or a copy of a part it yields a view of. *)
          let given =
            if temporary || trivial st ty then place
            else begin
              let copy = new_local st ty in
              Glue.copy_into st.context.glue st.b ~destination:copy ~source:place ty;
              copy
            end
          in
          let resume = block st.b and stop = block st.b in
          finish st.b (Yield { value = owned st given ty; resume; stop = Some stop });
          start st.b stop;
          leave_to st 0;
          finish st.b (Return None);
          start st.b resume
      | None -> bug "a yield outside an inlined method")
  | Statement_error -> bug "a statement that did not parse");
  end_statement st

(* Evaluates an expression once, for a pattern to look into: the place it
   names, or a temporary holding its value, and whether it is a temporary,
   whose parts the pattern's names then own. *)
and scrutinee st (e : S.expression) =
  match place_expression st e with Some place -> (place, false) | None -> (expression st e, true)

and let_ st ~mutable_ (pattern : S.pattern) (value : S.expression) =
  let ty = type_of st value.id in
  match pattern.kind with
  | Wildcard -> ignore (expression st value)
  | Binding_or_constant name -> (
      let bind place =
        Hashtbl.replace st.frame.bindings name.id place;
        if not (trivial st ty) then own_in_scope st place
      in
      match place_expression st value with
      | Some place when (not mutable_) && not (trivial st ty) ->
          (* A [let] of a place views it. *)
          Hashtbl.replace st.frame.bindings name.id (snapshot st place)
      | Some place ->
          let local = at (local st.b ~name:name.text (Value ty)) in
          emit st.b (Assign (local, Use (owned st place ty)));
          bind local
      | None ->
          let local = at (local st.b ~name:name.text (Value ty)) in
          into st value local;
          bind local)
  | _ ->
      let place, temporary = scrutinee st value in
      bind_pattern st pattern place ty ~owned:(temporary || mutable_)

(* A place whose indexes are fixed now, so a view of it means the same
   element however the index variables change later. *)
and snapshot st (place : Lir.place) =
  {
    place with
    projections =
      List.map
        (function
          | Lir.Index (Copy index_place) ->
              let fixed = at (local st.b (Value st.context.types.usize)) in
              emit st.b (Assign (fixed, Use (Copy index_place)));
              Lir.Index (Copy fixed)
          | projection -> projection)
        place.projections;
  }

and for_ st (s : S.statement) ~pattern ~iterable ~body =
  match st.frame.code.checked.loops.(s.id) with
  | Some (Integer_range { element; inclusive }) -> (
      let element = ground st element in
      match iterable.kind with
      | Range { start = Some low; stop = Some high; _ } ->
          let index = at (local st.b ~name:"index" (Value element)) in
          let stop = at (local st.b (Value element)) in
          emit st.b (Assign (index, Use (operand st low)));
          emit st.b (Assign (stop, Use (operand st high)));
          let test = block st.b
          and inside = block st.b
          and step = block st.b
          and after = block st.b in
          finish st.b (Goto test);
          start st.b test;
          let going = local st.b (Raw Bool) in
          emit st.b
            (Assign
               (at going, Binary ((if inclusive then Less_equal else Less), Copy index, Copy stop)));
          finish st.b
            (Switch { value = Copy (at going); cases = [ (Z.one, inside) ]; default = Some after });
          start st.b inside;
          in_scope st (fun () ->
              let bound = at (local st.b (Value element)) in
              emit st.b (Assign (bound, Use (Copy index)));
              bind_pattern st pattern bound element ~owned:true;
              let depth = List.length st.scopes in
              st.loops <-
                {
                  continue_ = step;
                  continue_depth = depth;
                  break_ = after;
                  break_depth = depth - 1;
                }
                :: st.loops;
              block_into st body None;
              st.loops <- List.tl st.loops);
          finish st.b (Goto step);
          start st.b step;
          (* An inclusive range ends at its last value rather than past
             it, which might not fit the type. *)
          if inclusive then begin
            let last = local st.b (Raw Bool) in
            emit st.b (Assign (at last, Binary (Equal, Copy index, Copy stop)));
            let next = block st.b in
            finish st.b
              (Switch { value = Copy (at last); cases = [ (Z.one, after) ]; default = Some next });
            start st.b next
          end;
          emit st.b
            (Assign (index, Binary (Add, Copy index, constant_int (integer_of st element) Z.one)));
          finish st.b (Goto test);
          start st.b after
      | _ -> bug "a counted loop that is not over a range")
  | Some (Yielding { call = call_; mode }) -> (
      let expressions =
        match iterable.kind with
        | Call (callee, arguments) -> call_expressions call_ callee arguments
        | _ -> [ iterable ]
      in
      let arguments =
        if call_.arguments <> [] then with_receiver st call_ ~expressions call_.arguments
        else [ { C.expression = iterable.id; parameter = 0; mode; conversion = None } ]
      in
      match resolve_callee st call_ with
      | Some (path, type_arguments) when List.exists (Path.equal path) st.frame.inlined ->
          recursive_loop st s call_ ~expressions ~arguments ~path ~type_arguments ~pattern ~body
      | Some (path, type_arguments) ->
          let arguments = evaluate_arguments st ~expressions ~arguments in
          let caller = st.frame in
          let depth = List.length st.scopes in
          let after = block st.b in
          inline st path type_arguments ~arguments ~on_yield:(fun place ~resume ~stop ->
              let inner = st.frame in
              st.frame <- caller;
              let element_ty = yielded_type st path type_arguments in
              in_scope st (fun () ->
                  bind_pattern st pattern place element_ty ~owned:(mode = T.Own);
                  st.loops <-
                    {
                      continue_ = resume;
                      continue_depth = List.length st.scopes - 1;
                      break_ = after;
                      break_depth = depth;
                    }
                    :: st.loops;
                  block_into st body None;
                  st.loops <- List.tl st.loops);
              finish st.b (Goto resume);
              ignore stop;
              st.frame <- inner);
          finish st.b (Goto after);
          start st.b after
      | None -> bug "a loop over something that is not a method")
  | Some (Pulled { cursor }) -> (
      (* A cursor, pulled until it ends. *)
      let cursor_ty = ground st cursor in
      let cursor_place = expression st iterable in
      match cursor_ty with
      | Cursor yielding ->
          let option = cursor_result st.context yielding in
          let test = block st.b and inside = block st.b and after = block st.b in
          finish st.b (Goto test);
          start st.b test;
          let next = new_local st option in
          call_next st yielding cursor_place next;
          let more = local st.b (Raw Bool) in
          emit st.b (Assign (at more, Is_variant (next, "Some")));
          finish st.b
            (Switch { value = Copy (at more); cases = [ (Z.one, inside) ]; default = Some after });
          start st.b inside;
          in_scope st (fun () ->
              let element = cursor_element st.context yielding in
              bind_pattern st pattern
                (next / Variant_field { variant = "Some"; field = "value" })
                element ~owned:true;
              let depth = List.length st.scopes in
              st.loops <-
                {
                  continue_ = test;
                  continue_depth = depth;
                  break_ = after;
                  break_depth = depth - 1;
                }
                :: st.loops;
              block_into st body None;
              st.loops <- List.tl st.loops);
          finish st.b (Goto test);
          start st.b after
      | _ -> bug "a pulled loop over %s" (Ground.to_string cursor_ty))
  | None -> bug "a for loop with no meaning"

(* A loop over a yielding method already inlined around it, which yields
   through recursion: inlining it again would never end, so the loop pulls a
   cursor over it instead, held in a heap block of its own so that a cursor
   over the method can hold another, and freed as the loop ends. A pulled
   cursor gives values of their own, so a view the method yields reaches the
   loop as a copy. *)
and recursive_loop st (s : S.statement) call_ ~expressions ~arguments ~path ~type_arguments ~pattern
    ~body =
  let yielding : Ground.yielding = { method_ = path; type_arguments } in
  let element = cursor_element st.context yielding in
  let cursor_ty = Ground.Cursor yielding in
  let after = block st.b in
  in_scope st (fun () ->
      let boxed =
        local st.b ~name:"cursor" (Pointer { target = Value cursor_ty; writable = true })
      in
      emit st.b
        (Call
           {
             target = Intrinsic Allocate;
             arguments = [ Constant (Size_of cursor_ty); Constant (Alignment_of cursor_ty) ];
             result = Returned (at boxed);
           });
      free_in_scope st (at boxed);
      let cursor = { Lir.root = Local boxed; projections = [ Deref ] } in
      call_with st call_ ~expressions ~arguments cursor ~span:s.span;
      own_in_scope st cursor;
      let option = cursor_result st.context yielding in
      let test = block st.b and inside = block st.b and ended = block st.b in
      finish st.b (Goto test);
      start st.b test;
      let next = new_local st option in
      call_next st yielding cursor next;
      let more = local st.b (Raw Bool) in
      emit st.b (Assign (at more, Is_variant (next, "Some")));
      finish st.b
        (Switch { value = Copy (at more); cases = [ (Z.one, inside) ]; default = Some ended });
      start st.b inside;
      let depth = List.length st.scopes in
      in_scope st (fun () ->
          bind_pattern st pattern
            (next / Variant_field { variant = "Some"; field = "value" })
            element ~owned:true;
          st.loops <-
            { continue_ = test; continue_depth = depth; break_ = ended; break_depth = depth }
            :: st.loops;
          block_into st body None;
          st.loops <- List.tl st.loops);
      finish st.b (Goto test);
      start st.b ended);
  finish st.b (Goto after);
  start st.b after

(* The type a yielding method yields, in this instance. *)
and yielded_type st path type_arguments =
  let signature = signature_of st.context path in
  match signature.output with
  | Yields (_, ty) | Lends (_, ty) ->
      Monomorphic.ground st.context.monomorphic (bind signature.generics type_arguments) ty
  | Returns _ -> bug "%s does not yield" (Path.show path)

and if_ st ~condition ~then_ ~else_ destination =
  let yes = block st.b and no = block st.b and after = block st.b in
  (* The names the condition binds are in the [then] block, not the
     [else]. *)
  let scope = open_scope st in
  branch st condition ~yes ~no;
  start st.b yes;
  block_into st then_ destination;
  close_scope st scope;
  finish st.b (Goto after);
  start st.b no;
  drop_scope st scope;
  (match else_ with
  | None -> ()
  | Some (S.Else block) -> block_into st block destination
  | Some (Else_if e) -> (
      match destination with Some d -> into st e d | None -> ignore (expression st e)));
  finish st.b (Goto after);
  start st.b after

(* Lowers a condition as jumps: to [yes] when it holds, and to [no] when it
   does not. The names its [is] tests bind are bound on the way to [yes],
   owned in the current scope, which the caller has opened to cover where
   they can be used and drops on every path out. *)
and branch st (e : S.expression) ~yes ~no =
  match e.kind with
  | Parenthesized inner -> branch st inner ~yes ~no
  | Binary { operator = And; left; right; _ } ->
      let middle = block st.b in
      branch st left ~yes:middle ~no;
      start st.b middle;
      branch st right ~yes ~no
  | Binary { operator = Or; left; right; _ } ->
      let middle = block st.b in
      branch st left ~yes ~no:middle;
      start st.b middle;
      branch st right ~yes ~no
  | Prefix (Not, inner) when st.frame.code.checked.calls.(e.id) = None || is_built_in st e ->
      branch st inner ~yes:no ~no:yes
  | Is { value; pattern; _ } ->
      let ty = type_of st value.id in
      let place, temporary = scrutinee st value in
      let matched = block st.b in
      test_pattern st pattern place ty ~matched ~failed:no;
      start st.b matched;
      bind_pattern st pattern place ty ~owned:temporary;
      finish st.b (Goto yes)
  | _ ->
      let value = operand st e in
      finish st.b (Switch { value; cases = [ (Z.one, yes) ]; default = Some no })

(* Patterns *)

(* A constant's static data, as a place. *)
and static_constant st path : Lir.place =
  match demand st.context Environment.constant_type path with
  | Some ty -> { root = Static { key = Constant path; ty = ground st ty }; projections = [] }
  | None -> bug "no type for the constant %s" (Path.show path)

(* A [String] or [StringSlice] of a literal's text, in a new local. *)
and string_place st ty text =
  let place = new_local st ty in
  (match ty with
  | Named { path = Top { name = "String"; _ }; _ } ->
      let field, storage_ty, storage = string_value st ty text in
      let built = new_local st storage_ty in
      emit st.b (Assign (built, storage));
      emit st.b (Assign (place, Build { ty; variant = None; fields = [ (field, Move built) ] }))
  | _ -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Record [ (field, Typed view) ] ->
          let bytes = new_local st view in
          emit st.b
            (Assign
               ( bytes,
                 Build
                   {
                     ty = view;
                     variant = None;
                     fields =
                       [
                         ("elements", Constant (Bytes text)); ("length", usize (String.length text));
                       ];
                   } ));
          emit st.b
            (Assign (place, Build { ty; variant = None; fields = [ (field, Lir.Copy bytes) ] }))
      | _ -> bug "a string pattern on %s" (Ground.to_string ty)));
  place

(* Branches to [matched] if the value at [place] of type [ty] matches the
   pattern, and to [failed] otherwise, binding nothing. *)
and test_pattern st (pattern : S.pattern) place ty ~matched ~failed =
  let check rvalue =
    let ok = local st.b (Raw Bool) in
    emit st.b (Assign (at ok, rvalue));
    finish st.b
      (Switch { value = Copy (at ok); cases = [ (Z.one, matched) ]; default = Some failed })
  in
  (* A value matches a constant or a string when it is equal to it. *)
  let equal_to other =
    let ok = new_local st st.context.bool in
    trait_call st ~trait:(core "Equal") ~name:"equal" ~receiver:Read ~self:ty
      ~arguments:[ (Read, ty, place); (Read, ty, other) ]
      ~destination:ok;
    check (Use (Copy ok))
  in
  let constant () =
    match st.frame.code.checked.patterns.(pattern.id) with
    | Some (Constant_pattern path) -> equal_to (static_constant st path)
    | _ -> bug "a constant pattern with no constant"
  in
  match pattern.kind with
  | Wildcard -> finish st.b (Goto matched)
  | Binding_or_constant _ -> (
      match st.frame.code.checked.patterns.(pattern.id) with
      | Some (Constant_pattern _) -> constant ()
      | _ -> finish st.b (Goto matched))
  | Qualified_constant _ -> constant ()
  | Literal (Literal_integer _) ->
      check (Binary (Equal, Copy place, constant_of st ty (literal st pattern.id)))
  | Literal Literal_true -> check (Use (Copy place))
  | Literal Literal_false -> check (Unary (Not, Copy place))
  | Literal (Literal_string _) when st.frame.code.checked.literals.(pattern.id) <> None ->
      check (Binary (Equal, Copy place, constant_of st ty (literal st pattern.id)))
  | Literal (Literal_string literal) -> equal_to (string_place st ty literal.first.value)
  | Pattern_range { start; stop; inclusive } ->
      let bound (e : S.range_end) =
        match e.kind with
        | End_literal (Literal_integer value) -> constant_int (integer_of st ty) value
        | End_literal (Literal_string _) -> constant_of st ty (literal st e.id)
        | End_constant _ | End_name _ -> (
            match st.frame.code.checked.patterns.(e.id) with
            | Some (Constant_pattern path) -> Copy (static_constant st path)
            | _ -> bug "a range end with no constant")
        | End_literal _ -> bug "a range end that is not a number"
      in
      let low = local st.b (Raw Bool) and high = local st.b (Raw Bool) in
      emit st.b (Assign (at low, Binary (Greater_equal, Copy place, bound start)));
      emit st.b
        (Assign (at high, Binary ((if inclusive then Less_equal else Less), Copy place, bound stop)));
      check (Binary (Bit_and, Copy (at low), Copy (at high)))
  | Alternatives alternatives ->
      List.iteri
        (fun i alternative ->
          let next = if i = List.length alternatives - 1 then failed else block st.b in
          test_pattern st alternative place ty ~matched ~failed:next;
          if next <> failed then start st.b next)
        alternatives
  | Variant { name; fields } ->
      let variant = name.last.text in
      let inside = block st.b in
      let is = local st.b (Raw Bool) in
      emit st.b (Assign (at is, Is_variant (place, variant)));
      finish st.b
        (Switch { value = Copy (at is); cases = [ (Z.one, inside) ]; default = Some failed });
      start st.b inside;
      test_fields st (Option.value fields ~default:[]) place ty (Some variant) ~matched ~failed
  | Record fields -> test_fields st fields place ty None ~matched ~failed
  | Pattern_error -> bug "a pattern that did not parse"

and field_patterns st (fields : S.pattern_field list) ty variant =
  let names = constructor_fields st ty variant in
  let shape_fields =
    match (Monomorphic.shape st.context.monomorphic ty, variant) with
    | Record fields, None -> fields
    | Sum variants, Some name ->
        (List.find (fun (v : Memory_layout.variant_shape) -> v.name = name) variants).fields
    | _ -> []
  in
  List.filter_map
    (fun (field : S.pattern_field) ->
      match field.kind with
      | Named_field (name, pattern) -> Some (name.text, pattern)
      | Field ({ kind = Binding_or_constant name; _ } as pattern) when List.mem name.text names ->
          Some (name.text, pattern)
      | Field pattern -> (
          match names with
          | [ only ] -> Some (only, pattern)
          | _ -> bug "a bare pattern for a field")
      | Rest -> None)
    fields
  |> List.map (fun (name, pattern) ->
      let field_ty =
        match List.assoc_opt name shape_fields with
        | Some (Memory_layout.Typed ty) -> ty
        | _ -> bug "no field %s" name
      in
      (name, pattern, field_ty))

and field_place place variant name =
  match variant with
  | None -> place / Lir.Field name
  | Some variant -> place / Lir.Variant_field { variant; field = name }

and test_fields st fields place ty variant ~matched ~failed =
  let parts = field_patterns st fields ty variant in
  let rec go = function
    | [] -> finish st.b (Goto matched)
    | (name, pattern, field_ty) :: rest ->
        let next = block st.b in
        test_pattern st pattern (field_place place variant name) field_ty ~matched:next ~failed;
        start st.b next;
        go rest
  in
  go parts

(* Binds the names a pattern binds to the parts of the value at [place],
   once it is known to match: views of the parts, or the parts moved out
   when the value is owned. Plain parts are copied. *)
and bind_pattern st (pattern : S.pattern) place ty ~owned =
  match pattern.kind with
  | Binding_or_constant name -> (
      match st.frame.code.checked.patterns.(pattern.id) with
      | Some (Constant_pattern _) -> ()
      | _ ->
          if owned || trivial st ty then begin
            let local = at (local st.b ~name:name.text (Value ty)) in
            emit st.b
              (Assign (local, Use (if owned then owned_operand st place ty else Copy place)));
            Hashtbl.replace st.frame.bindings name.id local;
            if not (trivial st ty) then own_in_scope st local
          end
          else Hashtbl.replace st.frame.bindings name.id place)
  | Wildcard | Literal _ | Pattern_range _ | Qualified_constant _ -> ()
  | Alternatives (first :: _) -> bind_pattern st first place ty ~owned
  | Alternatives [] -> ()
  | Variant { name; fields } ->
      List.iter
        (fun (field, pattern, field_ty) ->
          bind_pattern st pattern (field_place place (Some name.last.text) field) field_ty ~owned)
        (field_patterns st (Option.value fields ~default:[]) ty (Some name.last.text))
  | Record fields ->
      List.iter
        (fun (field, pattern, field_ty) ->
          bind_pattern st pattern (field_place place None field) field_ty ~owned)
        (field_patterns st fields ty None)
  | Pattern_error -> bug "a pattern that did not parse"

and owned_operand st place ty = owned st place ty

and match_ st ~scrutinees ~arms destination =
  let values =
    List.map
      (fun e ->
        let place, temporary = scrutinee st e in
        (place, type_of st e.S.id, temporary))
      scrutinees
  in
  let after = block st.b in
  List.iter
    (fun (arm : S.arm) ->
      let next = block st.b in
      let rec test patterns values =
        match (patterns, values) with
        | [], [] -> ()
        | pattern :: patterns, (place, ty, _) :: values ->
            let matched = block st.b in
            test_pattern st pattern place ty ~matched ~failed:next;
            start st.b matched;
            test patterns values
        | _ -> bug "a match arm with the wrong number of patterns"
      in
      test arm.patterns values;
      let bind ~owned =
        List.iter2
          (fun pattern (place, ty, temporary) ->
            bind_pattern st pattern place ty ~owned:(owned && temporary))
          arm.patterns values
      in
      in_scope st (fun () ->
          (match arm.guard with
          | Some guard ->
              (* The guard sees views of what the arm binds, so a guard that
                 fails leaves the values whole for the next arm; the body
                 then owns the parts. *)
              bind ~owned:false;
              let body = block st.b and failed = block st.b in
              branch st guard ~yes:body ~no:failed;
              start st.b failed;
              drop_scope st (List.hd st.scopes);
              finish st.b (Goto next);
              start st.b body;
              bind ~owned:true
          | None -> bind ~owned:true);
          match (arm.body.kind, destination) with
          | Expression e, Some d -> into st e d
          | _, _ -> statement st arm.body);
      finish st.b (Goto after);
      start st.b next)
    arms;
  finish st.b Unreachable;
  start st.b after

(* Instances *)

(* Constants *)

(* Wraps an integer to a type's width, as a shift may need. *)
let wrap st ty value =
  let integer = integer_of st ty in
  let bytes = Memory_layout.integer_size (Memory_layout.target st.context.env) integer in
  let bits = 8 * bytes in
  let modulus = Z.shift_left Z.one bits in
  let low = Z.erem value modulus in
  match integer with
  | Int8 | Int16 | Int32 | Int64 | ISize ->
      if Z.geq low (Z.shift_left Z.one (bits - 1)) then Z.sub low modulus else low
  | _ -> low

(* A constant expression's value, worked out exactly: literals, arithmetic
   on numbers, other constants, and records, variants, strings, lists, and
   arrays built from constant parts. *)
let rec static_of st (e : S.expression) : Lir.static_value =
  let ty = type_of st e.id in
  let number value : Lir.static_value =
    Static_scalar (match operand_constant st ty value with c -> c)
  in
  match e.kind with
  | Parenthesized inner -> static_of st inner
  | Integer _ | Float _ -> number (literal st e.id)
  | Prefix (Negate, ({ kind = Integer _; _ } as inner))
    when st.frame.code.checked.calls.(e.id) = None -> (
      match literal st inner.id with
      | Integer_value v -> number (Integer_value (Z.neg v))
      | Float_value v -> number (Float_value (Float.neg v)))
  | True -> Static_scalar (Bool true)
  | False -> Static_scalar (Bool false)
  | String _ when st.frame.code.checked.literals.(e.id) <> None -> number (literal st e.id)
  | String literal when literal.rest = [] && literal.tag = None -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Record [ (field, Typed _) ] ->
          let bytes =
            List.init (String.length literal.first.value) (fun i ->
                Lir.Static_scalar (Integer (UInt8, Z.of_int (Char.code literal.first.value.[i]))))
          in
          Static_record
            [
              ( field,
                Static_storage
                  { element = Monomorphic.builtin UInt8; elements = bytes; owned = false } );
            ]
      | _ -> bug "a string constant of %s" (Ground.to_string ty))
  | List elements -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Array _ -> Static_array (List.map (static_of st) elements)
      | Record [ (field, Typed storage) ] -> (
          match Monomorphic.kind st.context.monomorphic storage with
          | Storage element ->
              Static_record
                [
                  ( field,
                    Static_storage
                      { element; elements = List.map (static_of st) elements; owned = true } );
                ]
          | _ -> bug "a list constant of %s" (Ground.to_string ty))
      | _ -> bug "a collection constant of %s, which is not built yet" (Ground.to_string ty))
  | Name _ | Member _ -> (
      match st.frame.code.checked.meanings.(e.id) with
      | Some (Global { path; _ }) -> (constant_data st.context path).value
      | Some (Variant_value { variant; _ }) -> Static_variant (variant, [])
      | _ -> bug "a constant that names something else: %s" (source st e.span))
  | Call (_, arguments) -> (
      match st.frame.code.checked.calls.(e.id) with
      | Some { callee = Constructor { variant; _ }; arguments = checked; _ } -> (
          let names = constructor_fields st ty variant in
          let fields =
            List.map
              (fun (argument : C.argument) ->
                let value =
                  (List.find (fun (a : S.argument) -> a.value.id = argument.expression) arguments)
                    .value
                in
                (List.nth names argument.parameter, static_of st value))
              checked
          in
          match variant with Some v -> Static_variant (v, fields) | None -> Static_record fields)
      | _ -> bug "a call in a constant: %s" (source st e.span))
  | Binary { operator; left; right; _ } ->
      fold st ty ~operator:(Some operator) [ static_of st left; static_of st right ]
  | Prefix (Negate, inner) -> fold st ty ~operator:None [ static_of st inner ]
  | _ -> bug "this is not a constant expression: %s" (source st e.span)

and operand_constant st ty literal =
  match constant_of st ty literal with
  | Constant c -> c
  | _ -> bug "a literal that is not a constant"

(* Arithmetic on constant numbers, exact for integers, which the type
   checker has shown do not overflow, and IEEE for floats. *)
and fold st ty ~operator values : Lir.static_value =
  let integer = function
    | Lir.Static_scalar (Integer (_, v)) -> v
    | _ -> bug "an integer constant"
  in
  let real = function
    | Lir.Static_scalar (Float64 bits) -> Int64.float_of_bits bits
    | Static_scalar (Float32 bits) -> Int32.float_of_bits bits
    | _ -> bug "a float constant"
  in
  match scalar_of st ty with
  | Integer kind -> (
      let v op = Lir.Static_scalar (Integer (kind, wrap st ty op)) in
      match (operator, List.map integer values) with
      | None, [ a ] -> v (Z.neg a)
      | Some Add, [ a; b ] -> v (Z.add a b)
      | Some Subtract, [ a; b ] -> v (Z.sub a b)
      | Some Multiply, [ a; b ] -> v (Z.mul a b)
      | Some Divide, [ a; b ] -> v (Z.div a b)
      | Some Remainder, [ a; b ] -> v (Z.rem a b)
      | Some Bit_and, [ a; b ] -> v (Z.logand a b)
      | Some Bit_or, [ a; b ] -> v (Z.logor a b)
      | Some Bit_xor, [ a; b ] -> v (Z.logxor a b)
      | Some Shift_left, [ a; b ] -> v (Z.shift_left a (Z.to_int b))
      | Some Shift_right, [ a; b ] -> v (Z.shift_right a (Z.to_int b))
      | _ -> bug "an operation in a constant that is not folded")
  | (Float32 | Float64) as scalar -> (
      let v x =
        Lir.Static_scalar
          (if scalar = Float32 then Float32 (Int32.bits_of_float x)
           else Float64 (Int64.bits_of_float x))
      in
      match (operator, List.map real values) with
      | None, [ a ] -> v (Float.neg a)
      | Some Add, [ a; b ] -> v (a +. b)
      | Some Subtract, [ a; b ] -> v (a -. b)
      | Some Multiply, [ a; b ] -> v (a *. b)
      | Some Divide, [ a; b ] -> v (a /. b)
      | _ -> bug "an operation in a constant that is not folded")
  | _ -> bug "arithmetic in a constant on %s" (Ground.to_string ty)

(* A constant's static data. *)
and constant_data context path : Lir.data =
  let key = key_of context path in
  let value =
    match demand context Names.definition key with
    | Some { kind = Constant { value; _ }; _ } -> value
    | _ -> bug "%s is not a constant" (Path.show path)
  in
  let ty =
    match demand context Environment.constant_type path with
    | Some ty -> Monomorphic.ground context.monomorphic [] ty
    | None -> bug "%s has no type" (Path.show path)
  in
  let code =
    {
      definition_key = key;
      anchor = path;
      text = text_of context key;
      checked = checked_of context key;
      parameters = [];
      body = { statements = []; span = S.Span.make 0 0; id = 0 };
      result = Returns T.unit;
      parameter_types = [];
      substitution = [];
      uses = [];
      has_defaults = false;
    }
  in
  let st =
    {
      context;
      frame =
        {
          code;
          bindings = Hashtbl.create 1;
          self_place = None;
          on_yield = None;
          inlined = [];
          exit = None;
        };
      b = Lir_builder.create ();
      scopes = [ { owned = [] } ];
      loops = [];
      temporaries = [];
      return_ = None;
      result_local = None;
      nested = ref [];
      evidence = [];
      pulling = false;
    }
  in
  { data_key = Constant path; ty; value = static_of st value }

let constant context path = constant_data context path

(* Derived implementations *)

(* The fields of a variant, or of a record, with their ground types. *)
let shape_fields st ty variant =
  match (Monomorphic.shape st.context.monomorphic ty, variant) with
  | Record fields, None -> fields
  | Sum variants, Some name ->
      (List.find (fun (v : Memory_layout.variant_shape) -> v.name = name) variants).fields
  | _ -> []

let typed_fields fields =
  List.filter_map
    (function name, Memory_layout.Typed ty -> Some (name, ty) | _, Raw _ -> None)
    fields

let variants st ty =
  match Monomorphic.shape st.context.monomorphic ty with
  | Sum variants -> Some (List.map (fun (v : Memory_layout.variant_shape) -> v.name) variants)
  | _ -> None

(* Branches on the variant a value holds, running [f] with each variant's
   name and index, or runs [f] once for a record. *)
let each_variant st ty place f =
  match variants st ty with
  | None -> f None 0
  | Some names ->
      let after = block st.b in
      let cases =
        List.mapi
          (fun index name ->
            let case = block st.b in
            aside st.b case (fun () ->
                f (Some name) index;
                finish st.b (Goto after));
            (name, case))
          names
      in
      finish st.b (Switch_variant { place; cases; default = None });
      start st.b after

let derived context ~(key : Instance.key) ~type_path ~trait ~name ~type_arguments : Lir.t =
  let ty = Ground.Named { path = type_path; arguments = type_arguments } in
  let path = match key with Code { path; _ } -> path | _ -> bug "a derived method's key" in
  let signature = signature_of context path in
  let code =
    {
      definition_key = key_of context type_path;
      anchor = type_path;
      text = "";
      checked = Checked.create 0;
      parameters = [];
      body = { statements = []; span = S.Span.make 0 0; id = 0 };
      result = signature.output;
      parameter_types = [];
      substitution = bind signature.generics type_arguments;
      uses = [];
      has_defaults = false;
    }
  in
  let b = Lir_builder.create () in
  let st =
    {
      context;
      frame =
        {
          code;
          bindings = Hashtbl.create 1;
          self_place = None;
          on_yield = None;
          inlined = [];
          exit = None;
        };
      b;
      scopes = [ { owned = [] } ];
      loops = [];
      temporaries = [];
      return_ = None;
      result_local = None;
      nested = ref [];
      evidence = [];
      pulling = false;
    }
  in
  let lir_signature, result =
    lir_signature context code.substitution ~parameters:(interface_parameters signature)
      ~has_defaults:false signature.output
  in
  let result_pointer =
    match result with Through_pointer pointer -> Some (local b ~name:"result" pointer) | _ -> None
  in
  let parameter (mode : T.mode) ty =
    match Convention.parameter context.env (Monomorphic.mode mode) ty with
    | Some (Pointer _ as pointer) ->
        let local = local b pointer in
        (Some local, { Lir.root = Local local; projections = [ Deref ] })
    | Some lir_ty ->
        let local = local b lir_ty in
        (Some local, at local)
    | None -> (None, new_local st ty)
  in
  let ground_parameters =
    List.map
      (fun (mode, t) -> (mode, Monomorphic.ground context.monomorphic code.substitution t))
      (interface_parameters signature)
  in
  let locals_and_places = List.map (fun (mode, t) -> parameter mode t) ground_parameters in
  let places = List.map snd locals_and_places in
  let result_ty =
    match signature.output with
    | Returns t -> Monomorphic.ground context.monomorphic code.substitution t
    | _ -> bug "a derived method that yields"
  in
  let result_place =
    match result_pointer with
    | Some pointer -> { Lir.root = Local pointer; projections = [ Deref ] }
    | None -> new_local st result_ty
  in
  start b (block b);
  let field_place place variant field =
    match variant with
    | None -> place / Lir.Field field
    | Some variant -> place / Lir.Variant_field { variant; field }
  in
  let trait_name = Ground.path_name trait in
  (match (trait_name, name, places) with
  | "Equal", "equal", [ self; other ] ->
      let bool = context.bool in
      emit b (Assign (result_place, Use (Constant (Bool true))));
      each_variant st ty self (fun variant _ ->
          let same = local b (Raw Bool) in
          emit b
            (Assign
               ( at same,
                 match variant with
                 | Some v -> Is_variant (other, v)
                 | None -> Use (Constant (Bool true)) ));
          let different = local b (Raw Bool) in
          emit b (Assign (at different, Unary (Not, Copy (at same))));
          when_ b
            (Copy (at different))
            (fun () -> emit b (Assign (result_place, Use (Constant (Bool false)))));
          when_ b
            (Copy (at same))
            (fun () ->
              List.iter
                (fun (field, field_ty) ->
                  let equal = new_local st bool in
                  trait_call st ~trait:(core "Equal") ~name:"equal" ~receiver:Read ~self:field_ty
                    ~arguments:
                      [
                        (Read, field_ty, field_place self variant field);
                        (Read, field_ty, field_place other variant field);
                      ]
                    ~destination:equal;
                  emit b (Assign (result_place, Binary (Bit_and, Copy result_place, Copy equal))))
                (typed_fields (shape_fields st ty variant))))
  | "Hash", "hash", [ self; hasher ] ->
      let hasher_ty = match List.nth ground_parameters 1 with _, t -> t in
      let hasher_path = match hasher_ty with Named { path; _ } -> path | _ -> bug "a hasher" in
      let write value =
        let path = Path.Method { owner = hasher_path; name = "write"; receiver = Mut } in
        let signature = signature_of context path in
        let word = new_local st (Monomorphic.builtin UInt64) in
        emit b (Assign (word, Use value));
        call_instance st
          (Code { path; type_arguments = [] })
          ~signature ~substitution:[]
          ~arguments:[ (Mut, hasher_ty, hasher); (Read, Monomorphic.builtin UInt64, word) ]
          ~mask:0
          ~destination:(new_local st (Monomorphic.builtin Unit))
      in
      each_variant st ty self (fun variant index ->
          if variant <> None then write (constant_int UInt64 (Z.of_int index));
          List.iter
            (fun (field, field_ty) ->
              trait_call st ~trait:(core "Hash") ~name:"hash" ~receiver:Read ~self:field_ty
                ~arguments:
                  [ (Read, field_ty, field_place self variant field); (Mut, hasher_ty, hasher) ]
                ~destination:(new_local st (Monomorphic.builtin Unit)))
            (typed_fields (shape_fields st ty variant)))
  | "Ordered", "compare", [ self; other ] ->
      let ordering = result_ty in
      let set name =
        emit b (Assign (result_place, Build { ty = ordering; variant = Some name; fields = [] }))
      in
      set "Equal";
      (* By variant, in declaration order, then by fields in declaration
         order. *)
      let index_of place =
        let index = local b (Raw (Integer UInt32)) in
        each_variant st ty place (fun _ i ->
            emit b (Assign (at index, Use (constant_int UInt32 (Z.of_int i)))));
        index
      in
      let mine = index_of self and theirs = index_of other in
      let less = local b (Raw Bool) and greater = local b (Raw Bool) in
      emit b (Assign (at less, Binary (Less, Copy (at mine), Copy (at theirs))));
      emit b (Assign (at greater, Binary (Greater, Copy (at mine), Copy (at theirs))));
      let done_ = block b in
      when_ b (Copy (at less)) (fun () -> set "Less");
      when_ b (Copy (at greater)) (fun () -> set "Greater");
      let differ = local b (Raw Bool) in
      emit b (Assign (at differ, Binary (Bit_or, Copy (at less), Copy (at greater))));
      let same = block b in
      finish b
        (Switch { value = Copy (at differ); cases = [ (Z.one, done_) ]; default = Some same });
      start b same;
      each_variant st ty self (fun variant _ ->
          List.iter
            (fun (field, field_ty) ->
              let undecided = local b (Raw Bool) in
              emit b (Assign (at undecided, Is_variant (result_place, "Equal")));
              when_ b
                (Copy (at undecided))
                (fun () ->
                  trait_call st ~trait:(core "Ordered") ~name:"compare" ~receiver:Read
                    ~self:field_ty
                    ~arguments:
                      [
                        (Read, field_ty, field_place self variant field);
                        (Read, field_ty, field_place other variant field);
                      ]
                    ~destination:result_place))
            (typed_fields (shape_fields st ty variant)));
      finish b (Goto done_);
      start b done_
  | "Default", "default", [] -> (
      match variants st ty with
      | Some _ -> bug "Default is derived only for records"
      | None ->
          let fields =
            List.map
              (fun (field, field_ty) ->
                let value = new_local st field_ty in
                trait_call st ~trait:(core "Default") ~name:"default" ~receiver:Static
                  ~self:field_ty ~arguments:[] ~destination:value;
                (field, Lir.Move value))
              (typed_fields (shape_fields st ty None))
          in
          emit b (Assign (result_place, Build { ty; variant = None; fields })))
  | _ -> bug "%s cannot be derived" (Path.show path));
  finish b (Return (match result with Returned _ -> Some (Lir.Move result_place) | _ -> None));
  ignore lir_signature;
  let main =
    Lir_builder.build b ?written_result:result_pointer
      ~parameters:(Option.to_list result_pointer @ List.filter_map fst locals_and_places)
      ~result:(match result with Returned t -> Some t | _ -> None)
  in
  { key; main; nested = [||] }

(* Capabilities: entries, tables, and the real implementations *)

(* A state for generated code, with no source of its own. *)
let generated_state context ~anchor ~substitution =
  let code =
    {
      definition_key =
        { Names.module_ = { package = ""; modules = [] }; path = anchor; ordinal = 0 };
      anchor;
      text = "";
      checked = Checked.create 0;
      parameters = [];
      body = { statements = []; span = S.Span.make 0 0; id = 0 };
      result = Returns T.unit;
      parameter_types = [];
      substitution;
      uses = [];
      has_defaults = false;
    }
  in
  {
    context;
    frame =
      {
        code;
        bindings = Hashtbl.create 1;
        self_place = None;
        on_yield = None;
        inlined = [];
        exit = None;
      };
    b = Lir_builder.create ();
    scopes = [ { owned = [] } ];
    loops = [];
    temporaries = [];
    return_ = None;
    result_local = None;
    nested = ref [];
    evidence = [];
    pulling = false;
  }

(* The capability an [impl] implements, and the capabilities its own
   methods use, in path order, which its evidence captures. *)
let impl_capability context impl =
  let interface = impl_interface context impl in
  (interface, interface.implements.trait, evidence_for [] interface.impl_uses)

(* An entry: unpacks the implementation and the evidence it captured from
   the evidence it is called with, and calls the [impl]'s method. *)
let entry context (key : Instance.key) (method_key : Instance.key) : Lir.t =
  let path, type_arguments =
    match method_key with
    | Code { path; type_arguments } -> (path, type_arguments)
    | _ -> bug "an entry's method"
  in
  let impl, name, receiver =
    match path with
    | Method { owner; name; receiver } -> (owner, name, receiver)
    | _ -> bug "an entry for a function"
  in
  let interface, capability, captured = impl_capability context impl in
  let _, capability_signature = capability_method context capability name in
  let entry_lir, result = entry_signature context capability_signature in
  let method_signature = signature_of context path in
  let substitution = bind method_signature.generics type_arguments in
  let st = generated_state context ~anchor:impl ~substitution in
  let b = st.b in
  let evidence = local b ~name:"evidence" Convention.evidence in
  let result_pointer =
    match result with Through_pointer pointer -> Some (local b ~name:"result" pointer) | _ -> None
  in
  let parameters =
    List.map
      (fun (info : T.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        match Convention.parameter context.env (Monomorphic.mode info.mode) ty with
        | Some (Pointer _ as pointer) ->
            let l = local b pointer in
            (Some l, ({ Lir.root = Local l; projections = [ Deref ] } : Lir.place), info.mode, ty)
        | Some lir_ty ->
            let l = local b lir_ty in
            (Some l, at l, info.mode, ty)
        | None -> (None, new_local st ty, info.mode, ty))
      capability_signature.parameters
  in
  start b (block b);
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let implementation = local b (Pointer { target = Value self_ty; writable = true }) in
  if not (zero_size st self_ty) then
    emit b
      (Call
         {
           target = Intrinsic Evidence_implementation;
           arguments = [ Copy (at evidence) ];
           result = Returned (at implementation);
         });
  st.evidence <-
    List.mapi
      (fun i capability ->
        let outer = local b Convention.evidence in
        emit b
          (Call
             {
               target = Intrinsic Evidence_outer;
               arguments = [ Copy (at evidence); Constant (Integer (Int32, Z.of_int i)) ];
               result = Returned (at outer);
             });
        (capability, Lir.Copy (at outer)))
      captured;
  let self_mode : T.mode = match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read in
  let result_ty =
    match capability_signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> bug "a capability method that yields"
  in
  let destination =
    match result_pointer with
    | Some pointer -> { Lir.root = Local pointer; projections = [ Deref ] }
    | None -> new_local st result_ty
  in
  call_instance st method_key ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lir.root = Local implementation; projections = [ Deref ] })
      :: List.map (fun (_, place, mode, ty) -> (mode, ty, place)) parameters)
    ~mask:0 ~destination;
  finish b (Return (match result with Returned _ -> Some (Lir.Move destination) | _ -> None));
  let main =
    Lir_builder.build b ?written_result:result_pointer
      ~parameters:
        ((evidence :: Option.to_list result_pointer)
        @ List.filter_map (fun (l, _, _, _) -> l) parameters)
      ~result:(match result with Returned ty -> Some ty | _ -> None)
  in
  ignore entry_lir;
  {
    key;
    main = { main with returns = capability_signature.output <> Returns Never };
    nested = [||];
  }

(* A capability [impl]'s table: an entry for each of the capability's
   methods, in the capability's order. *)
let table context (key : Instance.key) : Lir.table =
  match key with
  | Table { impl; type_arguments } ->
      let interface, capability, _ = impl_capability context impl in
      let capability_interface =
        match demand context Environment.trait_interface capability with
        | Some i -> i
        | None -> bug "no interface for %s" (Path.show capability)
      in
      let entries =
        List.map
          (fun (m : T.trait_method) ->
            let receiver =
              match
                List.find_opt (fun (name, _, _) -> name = m.method_name) interface.impl_methods
              with
              | Some (_, receiver, _) -> receiver
              | None -> bug "%s does not write %s" (Path.show impl) m.method_name
            in
            let method_key =
              Instance.Code
                { path = Method { owner = impl; name = m.method_name; receiver }; type_arguments }
            in
            (Instance.Entry method_key, fst (entry_signature context m.method_signature)))
          capability_interface.methods
      in
      { table_key = key; entries }
  | _ -> bug "not a table: %s" (Instance.to_string key)

(* The [impl] of a standard capability by its real implementation: the
   standard library's [System] type for it, such as [SystemConsole]. *)
let real_implementation (capability : Path.t) : Path.t =
  let name = Ground.path_name capability in
  Impl
    {
      module_ = { package = "standard"; modules = [ "capabilities" ] };
      name = Printf.sprintf "%s for System%s" name name;
    }

let real_evidence _context (capability : Path.t) : Lir.evidence =
  {
    evidence_key = Real_evidence capability;
    table = Table { impl = real_implementation capability; type_arguments = [] };
    outer = [];
  }

(* The C [main]'s Truss side: the program's arguments as a [List] of
   [String]s, whose bytes are the arguments' own, so they are never copied
   unless bad UTF-8 in them has to be replaced; evidence for the real
   implementation of each capability [main] uses; and [main]'s [ExitCode]
   as the process's status. *)
let program_main context (key : Instance.key) main_path : Lir.t =
  let st = generated_state context ~anchor:main_path ~substitution:[] in
  let b = st.b in
  let count = local b ~name:"count" (Raw (Integer Int32)) in
  let arguments_pointer = local b ~name:"arguments" (Raw (Pointer Opaque)) in
  start b (block b);
  let signature = signature_of context main_path in
  let list_ty, list_mode =
    match signature.parameters with
    | [ info ] -> (Monomorphic.ground context.monomorphic [] info.type_, info.mode)
    | _ -> bug "main takes its arguments"
  in
  let string_ty, storage_field, storage_ty =
    match Monomorphic.shape context.monomorphic list_ty with
    | Record [ (field, Typed storage) ] -> (
        match Monomorphic.kind context.monomorphic storage with
        | Storage element -> (element, field, storage)
        | _ -> bug "a List that is not storage")
    | _ -> bug "main's arguments are not a List"
  in
  ignore storage_ty;
  let list = new_local st list_ty in
  let lower operation type_arguments arguments destination =
    ignore
      (Intrinsics.lower context.env b context.types operation ~type_arguments arguments ~destination
         ~site:{ definition = main_path; line = 0; column = 1 })
  in
  let wanted = local b (Value context.types.usize) in
  emit b (Assign (at wanted, Convert (Copy (at count), Integer USize)));
  lower Storage_with_capacity [ string_ty ]
    [ Value (Copy (at wanted)) ]
    (Some (list / Field storage_field));
  let index = local b (Raw (Integer Int32)) in
  emit b (Assign (at index, Use (Constant (Integer (Int32, Z.zero)))));
  let test = block b and inside = block b and after = block b in
  finish b (Goto test);
  start b test;
  let going = local b (Raw Bool) in
  emit b (Assign (at going, Binary (Less, Copy (at index), Copy (at count))));
  finish b (Switch { value = Copy (at going); cases = [ (Z.one, inside) ]; default = Some after });
  start b inside;
  let length = local b (Value context.types.usize) and bytes = local b (Raw (Pointer Opaque)) in
  emit b
    (Call
       {
         target = Intrinsic Program_argument;
         arguments =
           [
             Copy (at arguments_pointer);
             Copy (at index);
             Address { place = at length; writable = true };
           ];
         result = Returned (at bytes);
       });
  let text = new_local st string_ty in
  (match Monomorphic.shape context.monomorphic string_ty with
  | Record [ (field, Typed storage) ] ->
      emit b
        (Assign
           ( text / Field field,
             Build
               {
                 ty = storage;
                 variant = None;
                 fields =
                   [
                     ("buffer", Copy (at bytes)); ("length", Copy (at length)); ("capacity", usize 0);
                   ];
               } ))
  | _ -> bug "a String that is not storage");
  lower Storage_push [ string_ty ] [ Place (list / Field storage_field); Value (Move text) ] None;
  emit b (Assign (at index, Binary (Add, Copy (at index), Constant (Integer (Int32, Z.one)))));
  finish b (Goto test);
  start b after;
  st.evidence <-
    List.map
      (fun capability -> (capability, Lir.Constant (Symbol_address (Real_evidence capability))))
      (evidence_for [] signature.uses);
  let exit_ty =
    match signature.output with
    | Returns ty -> Monomorphic.ground context.monomorphic [] ty
    | _ -> bug "main yields"
  in
  let exit = new_local st exit_ty in
  call_instance st
    (Code { path = main_path; type_arguments = [] })
    ~signature ~substitution:[]
    ~arguments:[ (list_mode, list_ty, list) ]
    ~mask:0 ~destination:exit;
  emit b (Drop list);
  let status = local b (Raw (Integer Int32)) in
  (match Monomorphic.shape context.monomorphic exit_ty with
  | Record [ (field, _) ] ->
      emit b (Assign (at status, Convert (Copy (exit / Field field), Integer Int32)))
  | _ -> bug "an ExitCode that is not a record of one field");
  finish b (Return (Some (Copy (at status))));
  {
    key;
    main =
      Lir_builder.build b ~parameters:[ count; arguments_pointer ]
        ~result:(Some (Raw (Integer Int32)));
    nested = [||];
  }

(* A named function as a value of a function type. *)
let adapter context (key : Instance.key) ~(function_ : Instance.key) ~(ty : Ground.function_type) :
    Lir.t =
  let path, type_arguments =
    match function_ with
    | Code { path; type_arguments } -> (path, type_arguments)
    | _ -> bug "an adapter"
  in
  let signature = signature_of context path in
  let substitution = bind signature.generics type_arguments in
  let st = generated_state context ~anchor:path ~substitution in
  let b = st.b in
  let environment = local b ~name:"environment" (Raw (Nullable_pointer Opaque)) in
  let result_ty =
    match ty.result with Returns t -> t | _ -> bug "an adapter for a function that yields"
  in
  let result = Convention.result context.env result_ty in
  let result_pointer =
    match result with Through_pointer pointer -> Some (local b ~name:"result" pointer) | _ -> None
  in
  let parameters =
    List.map
      (fun ((mode : Ground.mode), ty) ->
        let types_mode : T.mode = match mode with Read -> Read | Mut -> Mut | Own -> Own in
        match Convention.parameter context.env mode ty with
        | Some (Pointer _ as pointer) ->
            let l = local b pointer in
            (Some l, (types_mode, ty, ({ Lir.root = Local l; projections = [ Deref ] } : Lir.place)))
        | Some lir_ty ->
            let l = local b lir_ty in
            (Some l, (types_mode, ty, at l))
        | None -> (None, (types_mode, ty, new_local st ty)))
      ty.parameters
  in
  let evidence =
    List.map (fun capability -> (capability, local b ~name:"evidence" Convention.evidence)) ty.uses
  in
  start b (block b);
  st.evidence <- List.map (fun (capability, l) -> (capability, Lir.Copy (at l))) evidence;
  let destination =
    match result_pointer with
    | Some p -> { Lir.root = Local p; projections = [ Deref ] }
    | None -> new_local st result_ty
  in
  call_instance st function_ ~signature ~substitution ~arguments:(List.map snd parameters) ~mask:0
    ~destination;
  finish b (Return (match result with Returned _ -> Some (Lir.Move destination) | _ -> None));
  let main =
    Lir_builder.build b ?written_result:result_pointer
      ~parameters:
        ((environment :: Option.to_list result_pointer)
        @ List.filter_map fst parameters @ List.map snd evidence)
      ~result:(match result with Returned t -> Some t | _ -> None)
  in
  { key; main = { main with returns = result_ty <> Never }; nested = [||] }

(* An entry in an [any] table: the value's pointer as [self], then the
   method's arguments. *)
let any_entry context (key : Instance.key) (method_key : Instance.key) : Lir.t =
  let path, type_arguments =
    match method_key with
    | Code { path; type_arguments } -> (path, type_arguments)
    | _ -> bug "an entry's method"
  in
  let impl, name, receiver =
    match path with
    | Method { owner; name; receiver } -> (owner, name, receiver)
    | _ -> bug "an any entry"
  in
  let interface = impl_interface context impl in
  let trait = interface.implements.trait in
  let _, trait_signature = dynamic_slot context trait name in
  let method_signature = signature_of context path in
  let substitution = bind method_signature.generics type_arguments in
  let _, result = any_entry_signature context trait_signature in
  let st = generated_state context ~anchor:impl ~substitution in
  let b = st.b in
  let value = local b ~name:"value" (Raw (Pointer Opaque)) in
  let result_pointer =
    match result with Through_pointer pointer -> Some (local b ~name:"result" pointer) | _ -> None
  in
  let parameters =
    List.map
      (fun (info : T.parameter_info) ->
        let ty = Monomorphic.ground context.monomorphic substitution info.type_ in
        match Convention.parameter context.env (Monomorphic.mode info.mode) ty with
        | Some (Pointer _ as pointer) ->
            let l = local b pointer in
            (Some l, (info.mode, ty, ({ Lir.root = Local l; projections = [ Deref ] } : Lir.place)))
        | Some lir_ty ->
            let l = local b lir_ty in
            (Some l, (info.mode, ty, at l))
        | None -> (None, (info.mode, ty, new_local st ty)))
      method_signature.parameters
  in
  let evidence =
    List.map
      (fun capability -> (capability, local b ~name:"evidence" Convention.evidence))
      (evidence_for [] trait_signature.uses)
  in
  start b (block b);
  st.evidence <- List.map (fun (capability, l) -> (capability, Lir.Copy (at l))) evidence;
  let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
  let typed = local b (Pointer { target = Value self_ty; writable = true }) in
  if not (zero_size st self_ty) then emit b (Assign (at typed, Use (Copy (at value))));
  let self_mode : T.mode = match receiver with Mut -> Mut | Own -> Own | Read | Static -> Read in
  let result_ty =
    match method_signature.output with
    | Returns t -> Monomorphic.ground context.monomorphic substitution t
    | _ -> bug "an any method that yields"
  in
  let destination =
    match result_pointer with
    | Some p -> { Lir.root = Local p; projections = [ Deref ] }
    | None -> new_local st result_ty
  in
  call_instance st method_key ~signature:method_signature ~substitution
    ~arguments:
      ((self_mode, self_ty, { Lir.root = Local typed; projections = [ Deref ] })
      :: List.map snd parameters)
    ~mask:0 ~destination;
  finish b (Return (match result with Returned _ -> Some (Lir.Move destination) | _ -> None));
  let main =
    Lir_builder.build b ?written_result:result_pointer
      ~parameters:
        ((value :: Option.to_list result_pointer)
        @ List.filter_map fst parameters @ List.map snd evidence)
      ~result:(match result with Returned t -> Some t | _ -> None)
  in
  { key; main = { main with returns = method_signature.output <> Returns Never }; nested = [||] }

(* An [any] table: the type's drop in slot 0, then an entry for each method
   that can be called through [any]. *)
let any_table context (key : Instance.key) : Lir.table =
  match key with
  | Any_table { impl; type_arguments } ->
      let interface = impl_interface context impl in
      let trait = interface.implements.trait in
      let substitution = bind interface.impl_generics type_arguments in
      let self_ty = Monomorphic.ground context.monomorphic substitution interface.for_type in
      let drop_signature : Lir.signature =
        { parameters = [ Raw (Pointer Opaque) ]; result = None; returns = true }
      in
      let entries =
        List.map
          (fun (m : T.trait_method) ->
            let receiver =
              match
                List.find_opt (fun (name, _, _) -> name = m.method_name) interface.impl_methods
              with
              | Some (_, receiver, _) -> receiver
              | None -> m.method_receiver
            in
            let method_key =
              Instance.Code
                { path = Method { owner = impl; name = m.method_name; receiver }; type_arguments }
            in
            (Instance.Any_entry method_key, fst (any_entry_signature context m.method_signature)))
          (any_methods context trait)
      in
      { table_key = key; entries = (Instance.Drop self_ty, drop_signature) :: entries }
  | _ -> bug "not an any table: %s" (Instance.to_string key)

(* Whether a method of a derived [impl] is the trait's own, written in the
   trait, rather than one the derivation writes. *)
let trait_provides context ~trait ~name ~receiver =
  match demand context Names.definition (key_of context trait) with
  | Some { kind = Trait { members; _ }; _ } ->
      List.exists
        (fun (member : S.trait_member S.line) ->
          match member.kind with
          | Trait_method { signature; body = Some _ } ->
              name_of signature = name && receiver_of signature.parameters = receiver
          | _ -> false)
        members
  | _ -> false

(* The pulled version of a yielding method: lowered as the method is, but
   with its own [yield]s left for yield lowering, and its parameters first
   among its locals, which is how a cursor's fields are named. *)
let pulled context (yielding : Ground.yielding) : Lir.function_ * Lir.local list =
  let code = code_of context yielding.method_ yielding.type_arguments in
  let b = Lir_builder.create () in
  let st =
    {
      context;
      frame =
        {
          code;
          bindings = Hashtbl.create 16;
          self_place = None;
          on_yield = None;
          inlined = [ yielding.method_ ];
          exit = None;
        };
      b;
      scopes = [ { owned = [] } ];
      loops = [];
      temporaries = [];
      return_ = None;
      result_local = None;
      nested = ref [];
      evidence = [];
      pulling = true;
    }
  in
  let owned = ref [] in
  let parameters =
    List.filter_map
      (fun (mode, ty, (parameter : S.parameter)) ->
        let ty = Monomorphic.ground context.monomorphic code.substitution ty in
        let place, local =
          match held context mode ty with
          | None -> (new_local st ty, None)
          | Some (Pointer _ as pointer) ->
              let local = local b pointer in
              ({ Lir.root = Local local; projections = [ Deref ] }, Some local)
          | Some lir_ty ->
              let local = local b lir_ty in
              (at local, Some local)
        in
        (match parameter.kind with
        | Self_parameter _ -> st.frame.self_place <- Some place
        | Named_parameter { name; _ } -> Hashtbl.replace st.frame.bindings name.id place
        | Parameter_error -> ());
        if mode = T.Own && not (Glue.trivial context.glue ty) then begin
          own_in_scope st place;
          Option.iter (fun l -> owned := l :: !owned) local
        end;
        local)
      code.parameter_types
  in
  if code.has_defaults then
    bug "%s has defaults, which pulled methods do not take yet" (Path.show yielding.method_);
  let evidence =
    List.map
      (fun capability -> (capability, local b ~name:"evidence" Convention.evidence))
      (evidence_for code.substitution code.uses)
  in
  st.evidence <- List.map (fun (capability, l) -> (capability, Lir.Copy (at l))) evidence;
  start b (block b);
  block_into st code.body None;
  drop_scope st (List.hd st.scopes);
  finish b (Return None);
  ( Lir_builder.build b ~parameters:(parameters @ List.map snd evidence) ~result:None,
    List.rev !owned )

let instance context (key : Instance.key) : Lir.t =
  match key with
  | Entry method_key -> entry context key method_key
  | Any_entry method_key -> any_entry context key method_key
  | Adapter { function_; ty } -> adapter context key ~function_ ~ty
  | Program_main main -> program_main context key main
  | Code
      {
        path = Method { owner = Derived { type_ = type_path; trait }; name; receiver };
        type_arguments;
      }
    when not (trait_provides context ~trait ~name ~receiver) ->
      derived context ~key ~type_path ~trait ~name ~type_arguments
  | Code { path; type_arguments } ->
      let code = code_of context path type_arguments in
      let b = Lir_builder.create () in
      let lir_signature, result =
        lir_signature context code.substitution
          ~parameters:(List.map (fun (mode, ty, _) -> (mode, ty)) code.parameter_types)
          ~has_defaults:code.has_defaults code.result
      in
      ignore lir_signature;
      let return_pointer =
        match result with
        | Through_pointer pointer -> Some (local b ~name:"result" pointer)
        | _ -> None
      in
      let st =
        {
          context;
          frame =
            {
              code;
              bindings = Hashtbl.create 16;
              self_place = None;
              on_yield = None;
              inlined = [ path ];
              exit = None;
            };
          b;
          scopes = [ { owned = [] } ];
          loops = [];
          temporaries = [];
          return_ =
            Option.map
              (fun pointer -> { Lir.root = Local pointer; projections = [ Deref ] })
              return_pointer;
          result_local = None;
          nested = ref [];
          evidence = [];
          pulling = false;
        }
      in
      let parameters =
        List.filter_map
          (fun (mode, ty, (parameter : S.parameter)) ->
            let ty = Monomorphic.ground context.monomorphic code.substitution ty in
            let place, local =
              match Convention.parameter context.env (Monomorphic.mode mode) ty with
              | None -> (new_local st ty, None)
              | Some (Pointer _ as pointer) ->
                  let local = local b pointer in
                  ({ Lir.root = Local local; projections = [ Deref ] }, Some local)
              | Some lir_ty ->
                  let local = local b lir_ty in
                  (at local, Some local)
            in
            (match parameter.kind with
            | Self_parameter _ -> st.frame.self_place <- Some place
            | Named_parameter { name; _ } -> Hashtbl.replace st.frame.bindings name.id place
            | Parameter_error -> ());
            if mode = Own && not (Glue.trivial context.glue ty) then own_in_scope st place;
            local)
          code.parameter_types
      in
      let mask =
        if code.has_defaults then Some (local b ~name:"passed" (Raw (Integer UInt64))) else None
      in
      let evidence =
        List.map
          (fun capability -> (capability, local b ~name:"evidence" Convention.evidence))
          (evidence_for code.substitution code.uses)
      in
      let result_local =
        match result with
        | Returned ty -> Some (local b ~name:"result" ty)
        | Nothing | Through_pointer _ -> None
      in
      let st = { st with result_local } in
      st.evidence <-
        List.map (fun (capability, local) -> (capability, Lir.Copy (at local))) evidence;
      start b (block b);
      (* The function fills in each default the caller left out, from its
         constant, so changing a default compiles only the function again. *)
      (match mask with
      | None -> ()
      | Some mask ->
          let defaulted =
            List.filter_map
              (fun (mode, ty, (parameter : S.parameter)) ->
                match parameter.kind with
                | Named_parameter { name; default = Some default; _ } ->
                    Some (mode, ty, name, default)
                | _ -> None)
              code.parameter_types
          in
          List.iteri
            (fun bit (_, ty, (name : S.name), default) ->
              let ty = Monomorphic.ground context.monomorphic code.substitution ty in
              let passed = local b (Raw (Integer UInt64)) and given = local b (Raw Bool) in
              emit b
                (Assign
                   ( at passed,
                     Binary (Bit_and, Copy (at mask), constant_int UInt64 (Z.shift_left Z.one bit))
                   ));
              emit b
                (Assign (at given, Binary (Not_equal, Copy (at passed), constant_int UInt64 Z.zero)));
              let fill = block b and after = block b in
              finish b
                (Switch { value = Copy (at given); cases = [ (Z.one, after) ]; default = Some fill });
              start b fill;
              (match Hashtbl.find_opt st.frame.bindings name.id with
              | Some ({ projections = [ Deref ]; root = Local pointer } : Lir.place) ->
                  let value = new_local st ty in
                  st.temporaries <- [] :: st.temporaries;
                  into st default value;
                  st.temporaries <- List.tl st.temporaries;
                  emit b (Assign (at pointer, Use (Address { place = value; writable = true })))
              | Some place ->
                  st.temporaries <- [] :: st.temporaries;
                  into st default place;
                  st.temporaries <- List.tl st.temporaries
              | None -> ());
              finish b (Goto after);
              start b after)
            defaulted);
      let destination =
        match (st.return_, result_local) with
        | Some pointer, _ -> Some pointer
        | None, Some local -> Some (at local)
        | None, None -> None
      in
      block_into st code.body destination;
      drop_scope st (List.hd st.scopes);
      finish b
        (match code.result with
        | Returns Never -> Unreachable
        | _ -> Return (Option.map (fun local -> Lir.Move (at local)) result_local));
      let main =
        Lir_builder.build b ?written_result:return_pointer
          ~parameters:
            (Option.to_list return_pointer @ parameters @ Option.to_list mask
           @ List.map snd evidence)
          ~result:(match result with Returned ty -> Some ty | _ -> None)
      in
      {
        key;
        main = { main with returns = code.result <> Returns Never };
        nested =
          Array.of_list
            (List.map
               (function Some f -> f | None -> bug "a lambda left unfinished")
               !(st.nested));
      }
  | _ -> bug "%s is not code from source" (Instance.to_string key)
