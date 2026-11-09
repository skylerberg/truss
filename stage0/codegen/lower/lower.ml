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
}

let standard_text name : Ground.ty =
  Named
    {
      path = Top { module_ = { package = "standard"; modules = [ "text" ] }; name };
      arguments = [];
    }

let context database target =
  let monomorphic : Monomorphic.context =
    {
      type_interface = (fun path -> Query.demand database Environment.type_interface path);
      normalize = Interface.Impls.normalize database ~bounds:(fun _ -> []);
      capabilities = (fun _ -> []);
      cursor_fields = (fun _ -> bug "cursors are not lowered yet");
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
  | Some signature -> signature
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
let lir_signature context substitution ~(parameters : (T.mode * T.ty) list) ~has_defaults
    (result : T.result) : Lir.signature * Convention.result =
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
  let parameters, result =
    match result_ty with
    | Through_pointer pointer -> (pointer :: written, None)
    | Returned ty -> (written, Some ty)
    | Nothing -> (written, None)
  in
  ({ parameters = parameters @ mask; result; returns }, result_ty)

let has_defaults (signature : T.signature) =
  List.exists (fun (p : T.parameter_info) -> p.has_default) signature.parameters

let interface_parameters (signature : T.signature) =
  (match signature.receiver with
    | Some (receiver, ty) ->
        [ ((match receiver with Mut -> T.Mut | Own -> Own | Read | Static -> Read), ty) ]
    | None -> [])
  @ List.map (fun (info : T.parameter_info) -> (info.mode, info.type_)) signature.parameters

(* Lowering one function *)

type scope = { mutable owned : Lir.place list  (** Most recent first *) }

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
  match st.scopes with scope :: _ -> scope.owned <- place :: scope.owned | [] -> bug "no scope"

let drop_scope st (scope : scope) = List.iter (fun place -> emit st.b (Drop place)) scope.owned
let drop_temporaries st temporaries = List.iter (fun place -> emit st.b (Drop place)) temporaries

(* Drops everything owned in the scopes inside the [depth] outermost, and
   every pending temporary, as a [return], [break], or [continue] leaves
   them. *)
let leave_to st depth =
  List.iter (drop_temporaries st) st.temporaries;
  List.iteri
    (fun i scope -> if List.length st.scopes - i > depth then drop_scope st scope)
    st.scopes

let in_scope st f =
  let scope = { owned = [] } in
  st.scopes <- scope :: st.scopes;
  let result = f () in
  drop_scope st scope;
  st.scopes <- List.tl st.scopes;
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
let pass st (mode : T.mode) ty (place : Lir.place) : Lir.operand option =
  match Convention.parameter st.context.env (Monomorphic.mode mode) ty with
  | None -> None
  | Some (Pointer { writable; _ }) -> Some (Address { place; writable })
  | Some _ -> ( match mode with Own -> Some (owned st place ty) | Read | Mut -> Some (Copy place))

(* Calls a function instance with arguments that are places of their
   parameter types, writing the result to [destination]. *)
let call_instance st key ~(signature : T.signature) ~substitution
    ~(arguments : (T.mode * Ground.ty * Lir.place) list) ~mask ~destination =
  let lir_signature, result =
    lir_signature st.context substitution ~parameters:(interface_parameters signature)
      ~has_defaults:(has_defaults signature) signature.output
  in
  let passed = List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments in
  let mask = if has_defaults signature then [ constant_int UInt64 (Z.of_int mask) ] else [] in
  let target = Lir.Direct { function_ = Instance key; signature = lir_signature } in
  (match result with
  | Through_pointer _ ->
      emit st.b
        (Call
           {
             target;
             arguments = Address { place = destination; writable = true } :: (passed @ mask);
             result = None;
           })
  | Returned _ -> emit st.b (Call { target; arguments = passed @ mask; result = Some destination })
  | Nothing -> emit st.b (Call { target; arguments = passed @ mask; result = None }));
  if not lir_signature.returns then unreachable_block st

(* Expressions *)

let literal st (id : S.id) =
  match st.frame.code.checked.literals.(id) with
  | Some literal -> literal
  | None -> bug "no literal for %d" id

let constant_of st ty (literal : C.literal) : Lir.operand =
  match (literal, scalar_of st ty) with
  | Integer_value value, Integer integer -> constant_int integer value
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

let rec expression st (e : S.expression) : Lir.place =
  match e.kind with
  | Parenthesized inner | Mode (_, inner) -> expression st inner
  | Name _ | Member _ | Self_value -> (
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
            if call_.arguments <> [] then call_.arguments
            else
              List.mapi
                (fun i (e : S.expression) ->
                  { C.expression = e.id; parameter = i; mode = Read; conversion = None })
                expressions
          in
          Some (lend st call_ ~expressions ~arguments)
      | None -> None)
  | Call (callee, arguments) -> (
      match st.frame.code.checked.calls.(e.id) with
      | Some ({ callee = Function _ | Trait_method _; _ } as call_) when lends st call_ ->
          let expressions = call_expressions call_ callee arguments in
          Some (lend st call_ ~expressions ~arguments:call_.arguments)
      | _ -> None)
  | _ -> None

(* Whether a call is to a lending method. *)
and lends st (call_ : C.call) =
  match resolve_callee st call_ with
  | Some (path, _) -> (
      match (signature_of st.context path).output with Lends _ -> true | _ -> false)
  | None -> false

(* The instance a call to a function or a trait method reaches. *)
and resolve_callee st (call_ : C.call) =
  match call_.callee with
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

(* The arguments of a call as places, in parameter order. *)
and evaluate_arguments st ~(expressions : S.expression list) ~(arguments : C.argument list) =
  let by_id id = List.find (fun (e : S.expression) -> e.id = id) expressions in
  let evaluate (argument : C.argument) =
    let e = by_id argument.expression in
    let ty = type_of st e.id in
    let place =
      match argument.mode with
      | Mut | Read -> (
          match place_expression st e with Some place -> place | None -> expression st e)
      | Own -> (
          match place_expression st e with
          | Some place ->
              let moved = new_local st ty in
              emit st.b (Assign (moved, Use (owned st place ty)));
              moved
          | None -> expression st e)
    in
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
  | String literal when literal.rest = [] && literal.tag = None ->
      let field, _, storage = string_value st (ty ()) literal.first.value in
      assign (Build { ty = ty (); variant = None; fields = [] });
      emit st.b (Assign (destination / Field field, storage))
  | Name _ | Self_value | Member _ -> (
      match place_expression st e with
      | Some place -> assign (Use (owned st place (ty ())))
      | None -> name_value st e destination)
  | Call (callee, arguments) -> call st e ~callee ~arguments destination
  | Binary { operator = (And | Or) as operator; left; right; _ } ->
      let on_left = operand st left in
      let decide = block st.b and other = block st.b and after = block st.b in
      ignore decide;
      let short_value = match operator with And -> false | _ -> true in
      let short = block st.b in
      finish st.b
        (Switch
           {
             value = on_left;
             cases = [ (Z.one, if operator = And then other else short) ];
             default = Some (if operator = And then short else other);
           });
      start st.b short;
      assign (Use (Constant (Bool short_value)));
      finish st.b (Goto after);
      start st.b other;
      into st right destination;
      finish st.b (Goto after);
      start st.b after
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
  | Is { value; pattern; _ } ->
      let scrutinee = expression st value in
      let yes = block st.b and no = block st.b and after = block st.b in
      test_pattern st pattern scrutinee (type_of st value.id) ~matched:yes ~failed:no;
      start st.b yes;
      assign (Use (Constant (Bool true)));
      finish st.b (Goto after);
      start st.b no;
      assign (Use (Constant (Bool false)));
      finish st.b (Goto after);
      start st.b after
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
  | String _ -> bug "interpolated and tagged strings are not lowered yet"
  | Bracket _ | Try _ | With _ | Any _ | Range _ | Quantified _ | List _ | Map _ | Lambda _
  | Provide _ ->
      bug "this expression is not lowered yet: %s" (source st e.span)
  | Self_type_value -> bug "Self as a value"
  | Expression_error -> bug "an expression that did not parse"

(* A literal negated directly, which the type checker checked as one
   literal. *)
and negated_literal st ty (inner : S.expression) =
  match literal st inner.id with
  | Integer_value value -> constant_of st ty (Integer_value (Z.neg value))
  | Float_value value -> constant_of st ty (Float_value (Float.neg value))

and is_built_in st (e : S.expression) =
  match st.frame.code.checked.calls.(e.id) with
  | Some { callee = Built_in_operator; _ } -> true
  | _ -> false

and echo st place ty span =
  emit st.b (Call { target = Intrinsic Debug_begin; arguments = []; result = None });
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
         result = None;
       });
  let bytes = local st.b (Raw (Pointer Opaque))
  and length = local st.b (Value st.context.types.usize) in
  emit st.b (Call { target = Intrinsic Debug_bytes; arguments = []; result = Some (at bytes) });
  emit st.b (Call { target = Intrinsic Debug_length; arguments = []; result = Some (at length) });
  emit st.b (Echo { text = Copy (at bytes); length = Copy (at length); site = site st span })

(* A name that is not a place: a variant with no fields, or a constant. *)
and name_value st (e : S.expression) destination =
  match st.frame.code.checked.meanings.(e.id) with
  | Some (Variant_value { type_; variant }) ->
      emit st.b
        (Assign (destination, Build { ty = ground st type_; variant = Some variant; fields = [] }))
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
  | Some call_ ->
      let expressions = List.map (fun (a : S.argument) -> a.value) arguments in
      let expressions =
        match (call_.callee, callee.kind) with
        | Trait_method { receiver = Read | Mut | Own; _ }, Member (receiver, _)
        | Function { path = Method { receiver = Read | Mut | Own; _ }; _ }, Member (receiver, _) ->
            receiver :: expressions
        | _ -> expressions
      in
      call_with st call_ ~expressions ~arguments:call_.arguments destination ~span:e.span
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
      (argument.parameter, argument.mode, ty, place)
    in
    let evaluated = List.map evaluate arguments in
    let in_order = List.sort (fun (a, _, _, _) (b, _, _, _) -> Int.compare a b) evaluated in
    let as_arguments = List.map (fun (_, mode, ty, place) -> (mode, ty, place)) in
    match call_.callee with
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
          ~signature ~substitution ~arguments:(as_arguments in_order) ~mask ~destination
    | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
        let key = trait_method_key st ~trait ~name ~receiver ~self_type ~type_arguments ~evidence in
        let path = match key with Code { path; _ } -> path | _ -> bug "a trait method's key" in
        let type_arguments =
          match key with Code { type_arguments; _ } -> type_arguments | _ -> []
        in
        let signature = signature_of st.context path in
        let substitution = bind signature.generics type_arguments in
        call_instance st key ~signature ~substitution ~arguments:(as_arguments in_order)
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
        if call_.defaults_left_out <> [] then
          bug "fields left to their defaults are not lowered yet";
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
    | Function_value -> bug "calls through function values are not lowered yet"
    | Capability_method _ -> bug "capability calls are not lowered yet"
    | Built_in_operator -> bug "a built-in operator called as a function"

and default_mask (signature : T.signature) (call_ : C.call) =
  let defaulted = List.filter (fun (p : T.parameter_info) -> p.has_default) signature.parameters in
  let bits =
    List.mapi
      (fun i (p : T.parameter_info) ->
        if List.mem p.name call_.defaults_left_out then 0 else 1 lsl i)
      defaulted
  in
  List.fold_left ( lor ) 0 bits

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
      let scrutinee = expression st value in
      let matched = block st.b and failed = block st.b in
      test_pattern st pattern scrutinee (type_of st value.id) ~matched ~failed;
      start st.b failed;
      block_into st else_ None;
      unreachable_block st;
      start st.b matched;
      bind_pattern st pattern scrutinee (type_of st value.id) ~owned:(is_temporary st value)
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
      let test = block st.b and inside = block st.b and after = block st.b in
      finish st.b (Goto test);
      start st.b test;
      st.temporaries <- [] :: st.temporaries;
      let value = operand st condition in
      end_statement st;
      finish st.b (Switch { value; cases = [ (Z.one, inside) ]; default = Some after });
      start st.b inside;
      let depth = List.length st.scopes in
      st.loops <-
        { continue_ = test; continue_depth = depth; break_ = after; break_depth = depth }
        :: st.loops;
      block_into st body None;
      st.loops <- List.tl st.loops;
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
          let place =
            match place_expression st value with Some place -> place | None -> expression st value
          in
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
      | None -> bug "a yield outside an inlined method")
  | Statement_error -> bug "a statement that did not parse");
  end_statement st

and is_temporary st (e : S.expression) = place_expression st e = None

and let_ st ~mutable_ (pattern : S.pattern) (value : S.expression) =
  let ty = type_of st value.id in
  match (pattern.kind, place_expression st value) with
  | Binding_or_constant name, Some place when (not mutable_) && not (trivial st ty) ->
      (* A [let] of a place views it. *)
      Hashtbl.replace st.frame.bindings name.id (snapshot st place)
  | Binding_or_constant name, _ ->
      let local = at (local st.b ~name:name.text (Value ty)) in
      into st value local;
      Hashtbl.replace st.frame.bindings name.id local;
      if not (trivial st ty) then own_in_scope st local
  | Wildcard, _ -> ignore (expression st value)
  | _, _ ->
      let scrutinee = expression st value in
      bind_pattern st pattern scrutinee ty ~owned:(is_temporary st value || mutable_)

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
        if call_.arguments <> [] then call_.arguments
        else [ { C.expression = iterable.id; parameter = 0; mode; conversion = None } ]
      in
      match resolve_callee st call_ with
      | Some (path, type_arguments) ->
          let arguments = evaluate_arguments st ~expressions ~arguments in
          let element = match ground st call_.result with ty -> ty in
          ignore element;
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
  | Some (Pulled _) -> bug "loops over cursors are not lowered yet"
  | None -> bug "a for loop with no meaning"

(* The type a yielding method yields, in this instance. *)
and yielded_type st path type_arguments =
  let signature = signature_of st.context path in
  match signature.output with
  | Yields (_, ty) | Lends (_, ty) ->
      Monomorphic.ground st.context.monomorphic (bind signature.generics type_arguments) ty
  | Returns _ -> bug "%s does not yield" (Path.show path)

and if_ st ~condition ~then_ ~else_ destination =
  let value = operand st condition in
  let yes = block st.b and no = block st.b and after = block st.b in
  finish st.b (Switch { value; cases = [ (Z.one, yes) ]; default = Some no });
  start st.b yes;
  block_into st then_ destination;
  finish st.b (Goto after);
  start st.b no;
  (match else_ with
  | None -> ()
  | Some (S.Else block) -> block_into st block destination
  | Some (Else_if e) -> (
      match destination with Some d -> into st e d | None -> ignore (expression st e)));
  finish st.b (Goto after);
  start st.b after

(* Patterns *)

(* Branches to [matched] if the value at [place] of type [ty] matches the
   pattern, and to [failed] otherwise, binding nothing. *)
and test_pattern st (pattern : S.pattern) place ty ~matched ~failed =
  let check rvalue =
    let ok = local st.b (Raw Bool) in
    emit st.b (Assign (at ok, rvalue));
    finish st.b
      (Switch { value = Copy (at ok); cases = [ (Z.one, matched) ]; default = Some failed })
  in
  match pattern.kind with
  | Wildcard -> finish st.b (Goto matched)
  | Binding_or_constant _ -> (
      match st.frame.code.checked.patterns.(pattern.id) with
      | Some (Constant_pattern path) ->
          bug "constant patterns are not lowered yet: %s" (Path.show path)
      | _ -> finish st.b (Goto matched))
  | Literal (Literal_integer _) ->
      check (Binary (Equal, Copy place, constant_of st ty (literal st pattern.id)))
  | Literal Literal_true -> check (Use (Copy place))
  | Literal Literal_false -> check (Unary (Not, Copy place))
  | Literal (Literal_string _) -> bug "string patterns are not lowered yet"
  | Pattern_range { start; stop; inclusive } ->
      let bound (e : S.range_end) =
        match e.kind with
        | End_literal (Literal_integer _) -> constant_of st ty (literal st e.id)
        | _ -> bug "range ends other than literals are not lowered yet"
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
  | Qualified_constant _ -> bug "constant patterns are not lowered yet"
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
    List.map (fun e -> (expression st e, type_of st e.S.id, is_temporary st e)) scrutinees
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
      in_scope st (fun () ->
          List.iter2
            (fun pattern (place, ty, owned) -> bind_pattern st pattern place ty ~owned)
            arm.patterns values;
          (match arm.guard with
          | Some guard ->
              let value = operand st guard in
              let body = block st.b in
              finish st.b (Switch { value; cases = [ (Z.one, body) ]; default = Some next });
              start st.b body
          | None -> ());
          match (arm.body.kind, destination) with
          | Expression e, Some d -> into st e d
          | _, _ -> statement st arm.body);
      finish st.b (Goto after);
      start st.b next)
    arms;
  finish st.b Unreachable;
  start st.b after

(* Instances *)

(* Derived implementations *)

(* Calls a trait's method on a value of a ground type, through the [impl]
   the type has, with arguments that are places. *)
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

let core name : Path.t = Top { module_ = { package = "standard"; modules = [ "core" ] }; name }

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
    Lir_builder.build b
      ~parameters:(Option.to_list result_pointer @ List.filter_map fst locals_and_places)
      ~result:(match result with Returned t -> Some t | _ -> None)
  in
  { key; main; nested = [||] }

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

let instance context (key : Instance.key) : Lir.t =
  match key with
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
      let result_local =
        match result with
        | Returned ty -> Some (local b ~name:"result" ty)
        | Nothing | Through_pointer _ -> None
      in
      let st = { st with result_local } in
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
        Lir_builder.build b
          ~parameters:(Option.to_list return_pointer @ parameters @ Option.to_list mask)
          ~result:(match result with Returned ty -> Some ty | _ -> None)
      in
      { key; main = { main with returns = code.result <> Returns Never }; nested = [||] }
  | _ -> bug "%s is not code from source" (Instance.to_string key)
