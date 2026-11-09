(* A checked body as obligations. See PROVER.md, "Verification conditions".

   The body is executed symbolically, forward, in passive form: every value
   is a term, every fact is guarded by the condition of the path it holds
   on, and where paths join, each local that differs gets a fresh symbol
   that each path defines. So the verification condition grows with the
   body, not with its number of paths, as PROVER.md asks of [Vc].

   Each obligation becomes one query: the facts gathered before it, and its
   goal, guarded by its path. Once made, an obligation is a fact for the
   rest of the body, since its own query proves it.

   Anything this stage cannot translate soundly raises [Unsupported], and
   the definition's obligations are not proven at all: an obligation is
   never assumed because the prover could not read the code around it. *)

open Syntax
module T = Types
module C = Checked
module L = Logic
module Names = Resolve.Names
module Code = Diagnostic.Code
module Ids = Map.Make (Int)

exception Unsupported of span * string

let unsupported span format =
  Printf.ksprintf (fun message -> raise (Unsupported (span, message))) format

type obligation = {
  code : Code.prover;
  span : span;  (** Relative to the definition being proven. *)
  message : string;
  query : L.query;
  values : (string * string) list;  (** Each prover symbol a counterexample shows, with its name. *)
}

type outcome = {
  obligations : obligation list;  (** In the order made. *)
  unproven_clauses : (span * string) list;
      (** Clauses this stage does not prove yet, such as cost bounds, which the rest does not rely
          on. *)
}

(* A definition whose tables are being read: the one proven, or a callee
   whose clauses are translated at a call. *)
type source = { key : Names.key; checked : C.t; resolved : Resolve.resolved; text : string }

type loop_exits = { mutable breaks : frame list; mutable continues : frame list }

(* Where a path is: the value of each local, the values on entry for
   [old], the path's condition, and what [self] and [result] are. *)
and frame = {
  source : source;
  locals : L.term Ids.t;
  old_locals : L.term Ids.t;
  self : L.term option;
  old_self : L.term option;
  result : L.term option;
  condition : L.term;
  checking : bool;  (** Whether obligations are made here; not in a callee's clauses. *)
  bound : string list;  (** Symbols bound by quantifiers around this point. *)
  loop : loop_exits option;
  substitution : T.substitution;
      (** The type arguments of the callee whose clauses are read here, for its generic types. *)
}

type context = {
  database : Query.database;
  current : Path.t;
  terminates : bool;  (** Whether the definition proven has a [time] clause. *)
  measures : expression list;  (** Its [decreases], for its recursive calls. *)
  mutable declarations : L.declaration list;
  declared : (string, unit) Hashtbl.t;
  mutable facts : L.term list;  (** Reversed. *)
  mutable obligations : obligation list;  (** Reversed. *)
  mutable unproven : (span * string) list;
  mutable fresh : int;
  mutable values : (string * string) list;  (** For counterexamples. *)
  mutable returns : (frame * L.term option) list;
  mutable instantiating : Path.t list;  (** Contracts being assumed, to stop at recursion. *)
  fits : (int * T.ty) list;  (** The type checker's [Integer_fits] obligations, by expression. *)
  mutable output : T.ty option;  (** What the function proven returns, for [?]. *)
  graph : Call_graph.t;  (** The package's call graph, for recursion in cycles. *)
}

(* Symbols and facts *)

let declare context declaration =
  let name =
    match declaration with
    | L.Constant (name, _) | L.Function (name, _, _) | L.Datatype (name, _) -> name
  in
  if not (Hashtbl.mem context.declared name) then begin
    Hashtbl.replace context.declared name ();
    context.declarations <- declaration :: context.declarations
  end

let fresh context prefix sort =
  context.fresh <- context.fresh + 1;
  let name = Printf.sprintf "%s.%d" prefix context.fresh in
  declare context (L.Constant (name, sort));
  L.Symbol name

let assume context frame fact =
  if not (L.mentions frame.bound fact) then
    match fact with
    | L.Boolean true -> ()
    | _ -> context.facts <- L.( ==> ) frame.condition fact :: context.facts

(* An obligation is shown by its own query, and is a fact for what comes
   after it. Inside a quantifier there is no path to state it on, so it is
   left to the definition of the quantifier's body, which this stage does
   not check yet. *)
let oblige context frame code span message goal =
  if frame.checking && not (L.mentions frame.bound goal) then begin
    let guarded = L.( ==> ) frame.condition goal in
    context.obligations <-
      {
        code;
        span;
        message;
        query =
          {
            declarations = List.rev context.declarations;
            facts = List.rev context.facts;
            goal = guarded;
          };
        values = context.values;
      }
      :: context.obligations;
    assume context frame goal
  end

(* Source text, for messages. *)
let quote source (span : span) =
  if span.stop <= String.length source.text then
    String.sub source.text span.start (span.stop - span.start)
  else "this expression"

(* Types *)

let builtin ty = T.builtin_of ty

let bounds (ty : T.ty) =
  let power n = Z.shift_left Z.one n in
  let signed n = Some (Z.neg (power (n - 1)), Z.pred (power (n - 1))) in
  let unsigned n = Some (Z.zero, Z.pred (power n)) in
  match builtin ty with
  | Some Int8 -> signed 8
  | Some Int16 -> signed 16
  | Some Int32 -> signed 32
  | Some (Int64 | ISize) -> signed 64
  | Some UInt8 -> unsigned 8
  | Some UInt16 -> unsigned 16
  | Some UInt32 -> unsigned 32
  | Some (UInt64 | USize) -> unsigned 64
  | Some Character -> Some (Z.zero, Z.of_int 0x10FFFF)
  | _ -> None

let width (ty : T.ty) =
  match builtin ty with
  | Some (Int8 | UInt8) -> Some 8
  | Some (Int16 | UInt16) -> Some 16
  | Some (Int32 | UInt32) -> Some 32
  | Some (Int64 | UInt64 | USize | ISize) -> Some 64
  | _ -> None

let is_numeric (ty : T.ty) = match ty with T.Integer -> true | _ -> bounds ty <> None
let is_bool ty = T.is_builtin Bool ty

(* A type's name in the logic, unique across modules, as [T.show] is not. *)
let rec type_key (ty : T.ty) =
  match ty with
  | Named { path; arguments = [] } -> Path.show path
  | Named { path; arguments } ->
      Path.show path ^ "[" ^ String.concat ", " (List.map argument_key arguments) ^ "]"
  | _ -> T.show ty

and argument_key = function T.Type ty -> type_key ty | argument -> T.show_argument argument

let constructor_name ty variant =
  "constructor." ^ type_key ty ^ "." ^ Option.value variant ~default:"record"

let selector_name ty variant field =
  "field." ^ type_key ty ^ "." ^ Option.value variant ~default:"record" ^ "." ^ field

let is_standard_equal (path : Path.t) =
  match path with
  | Top { module_ = { package = "standard"; _ }; name = "Equal" } -> true
  | _ -> false

(* A type's interface, when it is a type whose fields this package sees. *)
let visible_type context (ty : T.ty) =
  match ty with
  | Named { path; arguments } when builtin ty = None -> (
      match Query.demand context.database Interface.Environment.interface path with
      | Some (Interface.Environment.Type_interface interface)
        when (not interface.opaque) || Path.package path = Path.package context.current ->
          let substitution =
            try
              List.combine
                (List.map (fun (generic : T.generic) -> generic.generic) interface.type_generics)
                arguments
            with Invalid_argument _ -> []
          in
          Some (interface, substitution)
      | _ -> None)
  | _ -> None

(* A type's shape in the logic: its constructors, each with its variant's
   name, [None] for a record, and its fields, sorted by name so that
   reordering them changes no query. *)
let constructors context ty =
  match visible_type context ty with
  | Some (interface, substitution) -> (
      let fields (list : T.field list) =
        List.sort compare
          (List.map
             (fun (field : T.field) ->
               (field.field_name, T.substitute substitution field.field_type))
             list)
      in
      match interface.shape with
      | Record list -> Some [ (None, fields list) ]
      | Sum variants ->
          Some
            (List.sort compare
               (List.map
                  (fun (variant : T.variant) ->
                    ( Some variant.variant_name,
                      match variant.fields with Some list -> fields list | None -> [] ))
                  variants))
      | Todo_type | Builtin_type _ | Error_shape -> None)
  | None -> None

(* The fields of one constructor, in the order they are declared, which is
   how a call's arguments are numbered. *)
let declared_fields context ty variant =
  match visible_type context ty with
  | Some (interface, substitution) -> (
      let fields (list : T.field list) =
        List.map
          (fun (field : T.field) -> (field.field_name, T.substitute substitution field.field_type))
          list
      in
      match (interface.shape, variant) with
      | Record list, None -> Some (fields list)
      | Sum variants, Some name -> (
          match List.find_opt (fun (v : T.variant) -> v.variant_name = name) variants with
          | Some { fields = Some list; _ } -> Some (fields list)
          | Some { fields = None; _ } -> Some []
          | None -> None)
      | _ -> None)
  | None -> None

let rec sort_of context (ty : T.ty) : L.sort =
  if is_numeric ty then Int
  else if is_bool ty then Bool
  else begin
    let name = type_key ty in
    (if not (Hashtbl.mem context.declared name) then
       match constructors context ty with
       | Some shape ->
           (* Marked first, so a recursive type's fields find it declared. *)
           Hashtbl.replace context.declared name ();
           let declaration =
             L.Datatype
               ( name,
                 List.map
                   (fun (variant, fields) ->
                     ( constructor_name ty variant,
                       List.map
                         (fun (field, field_type) ->
                           (selector_name ty variant field, sort_of context field_type))
                         fields ))
                   shape )
           in
           context.declarations <- declaration :: context.declarations
       | None -> ());
    Uninterpreted name
  end

(* Whether [==] on a type is the solver's equality: built in with identity
   semantics, or derived from fields that all are. See DESIGN.md,
   "Equality, ordering, and deriving". *)
let rec structural context ?(seen = []) (ty : T.ty) =
  if is_numeric ty || is_bool ty || T.is_builtin Character ty then true
  else if List.exists (T.equal ty) seen then true
  else
    match (visible_type context ty, constructors context ty) with
    | Some (interface, _), Some shape ->
        List.exists is_standard_equal interface.derives
        && List.for_all
             (fun (_, fields) ->
               List.for_all
                 (fun (_, field_type) -> structural context ~seen:(ty :: seen) field_type)
                 fields)
             shape
    | _ -> false

let in_range ty term =
  match bounds ty with
  | Some (low, high) ->
      L.(Apply ("<=", [ Integer low; term ]) &&& Apply ("<=", [ term; Integer high ]))
  | None -> L.Boolean true

(* A value of a type that arrives from outside what is known: a parameter,
   a call's result, a loop's havocked local. *)
let arrive context frame prefix ty =
  let value = fresh context prefix (sort_of context ty) in
  assume context frame (in_range ty value);
  value

let type_of frame (expression : expression) =
  match frame.source.checked.types.(expression.id) with
  | Some ty -> T.substitute frame.substitution ty
  | None -> unsupported expression.span "an expression without a type"

let local_type frame id =
  Option.map (T.substitute frame.substitution) frame.source.checked.local_types.(id)

let substituted frame ty = T.substitute frame.substitution ty

(* Paths *)

let restrict frame condition = { frame with condition = L.( &&& ) frame.condition condition }

(* Joins paths: the condition is that one of them was taken, and each
   local whose values differ gets a fresh symbol each path defines. *)
let join context ?value_type frames =
  match frames with
  | [] -> None
  | [ (frame, value) ] -> Some (frame, value)
  | (first, _) :: _ ->
      let condition = L.disjunction (List.map (fun (frame, _) -> frame.condition) frames) in
      let merged = { first with condition } in
      let define prefix sort pick =
        let values = List.map (fun ((frame : frame), item) -> (frame, pick frame item)) frames in
        match values with
        | (_, Some term) :: rest when List.for_all (fun (_, other) -> other = Some term) rest ->
            Some term
        | _ when List.exists (fun (_, term) -> term = None) values -> None
        | _
          when List.exists
                 (fun ((frame : frame), term) ->
                   L.mentions first.bound frame.condition
                   || match term with Some term -> L.mentions first.bound term | None -> false)
                 values -> (
            (* Inside a quantifier, a fact about a fresh symbol could not
               mention the bound variable, so the value is an [ite]. *)
            match List.rev values with
            | (_, Some last) :: earlier ->
                Some
                  (List.fold_left
                     (fun otherwise ((frame : frame), term) ->
                       match term with
                       | Some term -> L.ite frame.condition term otherwise
                       | None -> otherwise)
                     last earlier)
            | _ -> None)
        | _ ->
            let symbol = fresh context prefix sort in
            List.iter
              (fun ((frame : frame), term) ->
                match term with
                | Some term ->
                    context.facts <-
                      L.( ==> ) frame.condition (L.equal symbol term) :: context.facts
                | None -> ())
              values;
            Some symbol
      in
      let locals =
        Ids.mapi
          (fun id term ->
            let sort =
              match local_type first id with
              | Some ty -> sort_of context ty
              | None -> ( match term with L.Boolean _ -> L.Bool | _ -> L.Int)
            in
            match define "joined" sort (fun frame _ -> Ids.find_opt id frame.locals) with
            | Some joined -> joined
            | None -> term)
          first.locals
      in
      let value =
        match value_type with
        | Some ty -> define "value" (sort_of context ty) (fun _ value -> value)
        | None -> None
      in
      Some ({ merged with locals }, value)

let join_frames context frames =
  Option.map fst (join context (List.map (fun frame -> (frame, None)) frames))

(* Calls: what a callee promises *)

type parameter_binding = Self_binding | Parameter_binding of name

(* One tree's clauses about a callee: its own, or, for a method of an
   [impl], its trait's. *)
type part = {
  callee : source;
  binding : parameter_binding list;  (** In the order a call's arguments are numbered. *)
  defaults : (int * expression) list;
  requires : expression list;
  ensures : expression list;
  decreases : expression list;
}

type contract = {
  parts : part list;  (** The callee's own first. *)
  pure : bool;  (** Pure and terminating, so a function in the logic. *)
  result_kind : [ `Returns | `Lends | `Yields ];
  definition : (part * block) option;  (** A functional body, which is the callee's definition. *)
}

let callee_source database (key : Names.key) =
  match
    ( Query.demand database Resolve.resolved key,
      Infer.clean database key,
      Query.demand database Names.text key )
  with
  | Some resolved, Some checked, Some text -> Some { key; checked; resolved; text }
  | _ -> None

let part_of callee (parameters : parameter list) (clauses : clause list) =
  let named =
    List.filter_map
      (fun (parameter : parameter) ->
        match parameter.kind with
        | Named_parameter { name; default; _ } -> Some (name, default)
        | Self_parameter _ | Parameter_error -> None)
      parameters
  in
  let has_self =
    List.exists
      (fun (parameter : parameter) ->
        match parameter.kind with Self_parameter _ -> true | _ -> false)
      parameters
  in
  let offset = if has_self then 1 else 0 in
  {
    callee;
    binding =
      (if has_self then [ Self_binding ] else [])
      @ List.map (fun (name, _) -> Parameter_binding name) named;
    defaults =
      List.concat
        (List.mapi
           (fun index (_, default) ->
             match default with Some value -> [ (index + offset, value) ] | None -> [])
           named);
    requires =
      List.filter_map
        (fun (clause : clause) -> match clause.kind with Requires value -> Some value | _ -> None)
        clauses;
    ensures =
      List.filter_map
        (fun (clause : clause) -> match clause.kind with Ensures value -> Some value | _ -> None)
        clauses;
    decreases =
      List.concat_map
        (fun (clause : clause) -> match clause.kind with Decreases measures -> measures | _ -> [])
        clauses;
  }

let receiver_of (parameters : parameter list) : Path.receiver =
  match parameters with
  | { kind = Self_parameter None; _ } :: _ -> Read
  | { kind = Self_parameter (Some Mut); _ } :: _ -> Mut
  | { kind = Self_parameter (Some Own); _ } :: _ -> Own
  | _ -> Static

let name_of (signature : signature) =
  match signature.name with Plain_name name | Member_name (_, name) -> name.text

(* Whether a body is functional, so that it can be the function's
   definition: [let], [if], [match], [is], calls, fields, building values,
   [with], operators, and quantifiers, with no [var], assignment, loop,
   [return], or argument passed [mut] or [own]. See DESIGN.md, "What a
   function means to the prover". *)
let rec functional_block (written : block) = List.for_all functional_statement written.statements

and functional_statement (written : statement) =
  match written.kind with
  | Let { mutable_ = false; value; else_ = None; _ } -> functional_expression value
  | Expression value -> functional_expression value
  | _ -> false

and functional_expression (written : expression) =
  match written.kind with
  | Mode _ | Lambda _ | Return _ | Break | Continue | Todo | Echo _ | Provide _ | Unreachable ->
      false
  | _ ->
      let fine = ref true in
      Syntax_walk.expression_parts
        ~expression:(fun inner -> if not (functional_expression inner) then fine := false)
        ~statement:(fun inner -> if not (functional_statement inner) then fine := false)
        written;
      !fine

let make_contract database path ~own ~others ~(result : result option) ~body =
  let pure =
    match Query.demand database Interface.Environment.signature path with
    | Some (signature : T.signature) -> (
        signature.uses = [] && signature.terminates
        && List.for_all (fun (info : T.parameter_info) -> info.mode = T.Read) signature.parameters
        && match signature.receiver with Some ((Mut | Own), _) -> false | _ -> true)
    | None -> false
  in
  let result_kind =
    match result with Some (Lends _) -> `Lends | Some (Yields _) -> `Yields | _ -> `Returns
  in
  let definition =
    match body with
    | Some body when pure && result_kind = `Returns && functional_block body -> Some (own, body)
    | _ -> None
  in
  { parts = own :: others; pure; result_kind; definition }

let function_contract database (path : Path.t) =
  match Interface.Summary.definition database path with
  | Some (key, { kind = Function { signature; body }; _ }) ->
      Option.map
        (fun callee ->
          make_contract database path
            ~own:(part_of callee signature.parameters signature.clauses)
            ~others:[] ~result:signature.result ~body:(Some body))
        (callee_source database key)
  | Some (key, { kind = Theorem { parameters; clauses; _ }; _ }) ->
      Option.map
        (fun callee ->
          make_contract database path
            ~own:(part_of callee parameters clauses)
            ~others:[] ~result:None ~body:None)
        (callee_source database key)
  | _ -> None

(* A trait's method's clauses, from the trait's definition. *)
let trait_part database (trait : Path.t) name receiver =
  match Interface.Summary.definition database trait with
  | Some (key, { kind = Trait { members; _ }; _ }) -> (
      match callee_source database key with
      | Some callee ->
          List.find_map
            (fun (member : trait_member line) ->
              match member.kind with
              | Trait_method { signature; _ }
                when name_of signature = name && receiver_of signature.parameters = receiver ->
                  Some (part_of callee signature.parameters signature.clauses, signature)
              | _ -> None)
            members
      | None -> None)
  | _ -> None

(* A trait method's contract: the [impl]'s own clauses with the trait's,
   when the call is known to reach one [impl], and the trait's alone
   through a bound or [any]. See DESIGN.md, "An [impl] can promise more
   than its trait". *)
let method_contract database (trait : T.trait_reference) name receiver (evidence : C.evidence) =
  let trait_side = trait_part database trait.trait name receiver in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match Interface.Summary.definition database impl with
      | Some (key, { kind = Impl { members; _ }; _ }) -> (
          let own =
            match callee_source database key with
            | Some callee ->
                List.find_map
                  (fun (member : impl_member line) ->
                    match member.kind with
                    | Impl_method { signature; body }
                      when name_of signature = name && receiver_of signature.parameters = receiver
                      ->
                        Some (part_of callee signature.parameters signature.clauses, signature, body)
                    | _ -> None)
                  members
            | None -> None
          in
          match (own, trait_side) with
          | Some (part, signature, body), _ ->
              Some
                (make_contract database path ~own:part
                   ~others:(Option.to_list (Option.map fst trait_side))
                   ~result:signature.result ~body:(Some body))
          | None, Some (part, signature) ->
              (* A provided method the [impl] does not replace. *)
              Some
                (make_contract database
                   (Path.Method { owner = trait.trait; name; receiver })
                   ~own:part ~others:[] ~result:signature.result ~body:None)
          | None, None -> None)
      | _ -> None)
  | Bound _ | Dynamic ->
      Option.map
        (fun (part, (signature : signature)) ->
          make_contract database
            (Path.Method { owner = trait.trait; name; receiver })
            ~own:part ~others:[] ~result:signature.result ~body:None)
        trait_side
  | Built_in -> None

(* Expressions *)

let literal_value frame (expression : expression) =
  match frame.source.checked.literals.(expression.id) with
  | Some (Integer_value value) -> Some (L.Integer value)
  | Some (Float_value _) -> unsupported expression.span "a float"
  | None -> None

let comparison operator =
  match operator with
  | Equal -> Some "="
  | Less -> Some "<"
  | Less_equal -> Some "<="
  | Greater -> Some ">"
  | Greater_equal -> Some ">="
  | _ -> None

let rec expression context frame (written : expression) : (frame * L.term) option =
  let result = expression_kind context frame written in
  (match (result, List.assoc_opt written.id context.fits) with
  | Some (after, value), Some ty ->
      oblige context after Fits written.span
        (Printf.sprintf "`%s` may not fit in `%s`." (quote frame.source written.span) (T.show ty))
        (in_range ty value)
  | _ -> ());
  result

and value context frame written =
  match expression context frame written with
  | Some (frame, term) -> (frame, term)
  | None -> unsupported written.span "an expression that never returns, used as a value"

and expression_kind context frame (written : expression) : (frame * L.term) option =
  let source = frame.source in
  match written.kind with
  | Integer _ -> (
      match literal_value frame written with
      | Some term -> Some (frame, term)
      | None -> unsupported written.span "an integer literal without a value")
  | Prefix (Negate, ({ kind = Integer _; _ } as inner)) -> (
      match literal_value frame written with
      | Some term -> Some (frame, term)
      | None -> (
          match literal_value frame inner with
          | Some (L.Integer value) -> Some (frame, L.Integer (Z.neg value))
          | _ -> unsupported written.span "a negated literal"))
  | True -> Some (frame, L.Boolean true)
  | False -> Some (frame, L.Boolean false)
  | Parenthesized inner | Echo inner -> expression context frame inner
  | Self_value -> (
      match frame.self with
      | Some self -> Some (frame, self)
      | None -> unsupported written.span "`self` outside a method")
  | Name path -> name context frame written path
  | Binary { operator = And; left; right; _ } ->
      let frame, left_value = value context frame left in
      let after, right_value = pure_operand context (restrict frame left_value) right in
      Some ({ after with condition = frame.condition }, L.( &&& ) left_value right_value)
  | Binary { operator = Or; left; right; _ } ->
      let frame, left_value = value context frame left in
      let _, right_value = pure_operand context (restrict frame (L.not_ left_value)) right in
      Some (frame, L.( ||| ) left_value right_value)
  | Binary { operator = Implies; left; right; _ } ->
      let frame, left_value = value context frame left in
      let _, right_value = pure_operand context (restrict frame left_value) right in
      Some (frame, L.( ==> ) left_value right_value)
  | Binary { operator; left; right; _ } -> binary context frame written operator left right
  | Prefix (Not, inner) ->
      let frame, inner_value = value context frame inner in
      Some (frame, L.not_ inner_value)
  | Prefix (Negate, inner) ->
      let frame, inner_value = value context frame inner in
      let ty = type_of frame written in
      let negated = L.Apply ("-", [ inner_value ]) in
      if bounds ty <> None then
        oblige context frame Overflow written.span
          (Printf.sprintf "`%s` may overflow `%s`." (quote source written.span) (T.show ty))
          (in_range ty negated)
      else if ty <> T.Integer then unsupported written.span "negating a value of `%s`" (T.show ty);
      Some (frame, negated)
  | Prefix (Complement, inner) ->
      let frame, inner_value = value context frame inner in
      let ty = type_of frame written in
      Some (frame, opaque_operation context frame ty "complement" [ inner_value ])
  | If { condition; then_; else_ } -> if_ context frame written condition then_ else_
  | Block block_ -> block_value context frame block_
  | Return returned ->
      (match returned with
      | Some returned -> (
          match expression context frame returned with
          | Some (after, term) -> context.returns <- (after, Some term) :: context.returns
          | None -> ())
      | None -> context.returns <- (frame, None) :: context.returns);
      None
  | Unreachable ->
      oblige context frame Unreachable written.span "This `unreachable` may be reached."
        (L.Boolean false);
      None
  | Todo -> Some (frame, arrive context frame "todo" (type_of frame written))
  | Break -> (
      match frame.loop with
      | Some exits ->
          exits.breaks <- frame :: exits.breaks;
          None
      | None -> unsupported written.span "`break` outside a loop")
  | Continue -> (
      match frame.loop with
      | Some exits ->
          exits.continues <- frame :: exits.continues;
          None
      | None -> unsupported written.span "`continue` outside a loop")
  | Quantified { quantifier; binder; body } ->
      quantified context frame written quantifier binder body
  | Call (callee, arguments) -> call context frame written callee arguments
  | Mode (_, inner) -> expression context frame inner
  | Member (base, _) -> member context frame written base
  | Bracket _ -> (
      match source.checked.calls.(written.id) with
      | Some call_ -> resolved_call context frame written call_
      | None -> unsupported written.span "type arguments outside a call")
  | Is { value = tested; pattern; _ } ->
      let frame, term = value context frame tested in
      let condition, frame = pattern_match context frame pattern term (type_of frame tested) in
      Some (frame, condition)
  | Match { scrutinees; arms } -> match_ context frame written scrutinees arms
  | Try inner -> try_ context frame written inner
  | With (base, updates) -> with_ context frame written base updates
  | Lambda _ -> unsupported written.span "a lambda"
  | List _ | Map _ -> unsupported written.span "a collection literal"
  | String _ -> unsupported written.span "a string"
  | Float _ -> unsupported written.span "a float"
  | Range _ -> unsupported written.span "a range outside a `for` loop or a quantifier"
  | Any _ -> unsupported written.span "`any`"
  | Provide _ -> unsupported written.span "`provide`"
  | Self_type_value | Expression_error -> unsupported written.span "this expression"

(* The right side of [&&], [||], or [==>], which runs only on some paths:
   it may make obligations there, but not change a local, since the paths
   would then need joining. *)
and pure_operand context frame written =
  let after, term = value context frame written in
  (* It may bind names, as an [is] does, but not change a local. *)
  if Ids.exists (fun id term -> Ids.find_opt id after.locals <> Some term) frame.locals then
    unsupported written.span "changing a variable on the right of `&&`, `||`, or `==>`";
  (after, term)

and name context frame (written : expression) (path : path) =
  let source = frame.source in
  match source.resolved.names.(path.last.id) with
  | Some Result_value -> (
      match frame.result with
      | Some result -> Some (frame, result)
      | None -> unsupported written.span "`result` here")
  | _ -> (
      match source.checked.meanings.(written.id) with
      | Some (Local_value id) -> (
          match Ids.find_opt id frame.locals with
          | Some term -> Some (frame, term)
          | None -> unsupported written.span "a local the prover did not bind")
      | Some (Generic_value parameter) ->
          let symbol = Printf.sprintf "generic.%s.%s" (Path.show parameter.owner) parameter.name in
          declare context (L.Constant (symbol, Int));
          Some (frame, L.Symbol symbol)
      | Some (Global { path = global; _ }) ->
          Some (frame, constant_value context frame written global)
      | Some (Variant_value { type_; variant }) ->
          let type_ = substituted frame type_ in
          let type_ = substituted frame type_ in
          Some (frame, variant_value context written type_ variant)
      | _ -> unsupported written.span "this name")

(* An operation the solver knows only by the range of its result. *)
and opaque_operation context frame ty name arguments =
  let sorts = List.map (fun _ -> L.Int) arguments in
  let symbol = Printf.sprintf "operation.%s.%s" name (T.show ty) in
  declare context (L.Function (symbol, sorts, sort_of context ty));
  let term = L.Apply (symbol, arguments) in
  assume context frame (in_range ty term);
  term

and binary context frame (written : expression) operator left right =
  let source = frame.source in
  let operand_type = type_of frame left in
  let result_type = type_of frame written in
  let primitive =
    (is_numeric operand_type || is_bool operand_type || T.is_builtin Character operand_type)
    && (is_numeric result_type || is_bool result_type)
  in
  let structural_equality =
    (operator = Equal || operator = Not_equal) && structural context operand_type
  in
  if structural_equality then begin
    let frame, left_value = value context frame left in
    let frame, right_value = value context frame right in
    let equal = L.equal left_value right_value in
    Some (frame, if operator = Equal then equal else L.not_ equal)
  end
  else if not primitive then begin
    (* An operator on another type is a call of its trait's method, known
       here only by its result's type. *)
    let frame, _ = value context frame left in
    let frame, _ = value context frame right in
    Some (frame, arrive context frame "operator" result_type)
  end
  else
    let frame, left_value = value context frame left in
    let frame, right_value = value context frame right in
    match (comparison operator, operator) with
    | Some symbol, _ -> Some (frame, L.Apply (symbol, [ left_value; right_value ]))
    | None, Not_equal -> Some (frame, L.not_ (L.equal left_value right_value))
    | None, (Add | Subtract | Multiply | Divide | Remainder) ->
        Some (frame, arithmetic context frame written result_type operator left_value right_value)
    | None, (Shift_left | Shift_right) ->
        (match width result_type with
        | Some bits ->
            oblige context frame Shift right.span
              (Printf.sprintf "The shift amount `%s` may not be less than %d."
                 (quote source right.span) bits)
              L.(Apply ("<", [ right_value; int bits ]))
        | None -> unsupported written.span "a shift of `%s`" (T.show result_type));
        let name = match operator with Shift_left -> "shift_left" | _ -> "shift_right" in
        Some (frame, opaque_operation context frame result_type name [ left_value; right_value ])
    | None, (Bit_and | Bit_or | Bit_xor) ->
        let name = match operator with Bit_and -> "and" | Bit_or -> "or" | _ -> "xor" in
        let term = opaque_operation context frame result_type name [ left_value; right_value ] in
        (match (operator, bounds result_type) with
        | Bit_and, Some (low, _) when Z.equal low Z.zero ->
            assume context frame
              L.(Apply ("<=", [ term; left_value ]) &&& Apply ("<=", [ term; right_value ]))
        | _ -> ());
        Some (frame, term)
    | None, _ -> unsupported written.span "this operator"

and arithmetic context frame (written : expression) ty operator left right =
  let source = frame.source in
  let exact =
    match operator with
    | Add -> L.Apply ("+", [ left; right ])
    | Subtract -> L.Apply ("-", [ left; right ])
    | Multiply -> L.Apply ("*", [ left; right ])
    | Divide -> L.truncated_divide left right
    | _ -> L.truncated_remainder left right
  in
  (match operator with
  | Divide | Remainder ->
      oblige context frame Division written.span
        (Printf.sprintf "The divisor in `%s` may be zero." (quote source written.span))
        (L.not_ (L.equal right (L.int 0)))
  | _ -> ());
  (match bounds ty with
  | Some (low, _) when operator = Divide || operator = Remainder ->
      if Z.sign low < 0 then
        oblige context frame Overflow written.span
          (Printf.sprintf "`%s` may overflow `%s`: the least value over -1."
             (quote source written.span) (T.show ty))
          (L.not_ L.(equal left (Integer low) &&& equal right (int (-1))))
  | Some _ ->
      oblige context frame Overflow written.span
        (Printf.sprintf "`%s` may overflow `%s`." (quote source written.span) (T.show ty))
        (in_range ty exact)
  | None -> ());
  exact

and if_ context frame (written : expression) condition then_ else_ =
  let frame, test = value context frame condition in
  let then_result = block_value context (restrict frame test) then_ in
  let otherwise = restrict frame (L.not_ test) in
  let else_result =
    match else_ with
    | Some (Else block_) -> block_value context otherwise block_
    | Some (Else_if inner) -> expression context otherwise inner
    | None -> Some (otherwise, L.Boolean true)
  in
  let ty = type_of frame written in
  let carries_value = else_ <> None && not (T.equal ty T.unit) in
  let reached = List.filter_map Fun.id [ then_result; else_result ] in
  if carries_value then
    match
      join context ~value_type:ty (List.map (fun (frame, term) -> (frame, Some term)) reached)
    with
    | Some (frame, Some term) -> Some (frame, term)
    | Some (frame, None) -> Some (frame, L.Boolean true)
    | None -> None
  else
    Option.map (fun frame -> (frame, L.Boolean true)) (join_frames context (List.map fst reached))

and quantified context frame (written : expression) quantifier binder body =
  let make bound_symbol sort premise body_frame =
    let _, body_value = value context { body_frame with checking = false } body in
    let bound = [ (bound_symbol, sort) ] in
    match quantifier with
    | Forall -> Some (frame, L.Forall (bound, L.( ==> ) premise body_value))
    | Exists -> Some (frame, L.Exists (bound, L.( &&& ) premise body_value))
  in
  context.fresh <- context.fresh + 1;
  let symbol = Printf.sprintf "bound.%d" context.fresh in
  let with_bound id ty =
    { frame with locals = Ids.add id (L.Symbol symbol) frame.locals; bound = symbol :: frame.bound }
    |> fun inner -> (inner, ty)
  in
  match binder with
  | Binder_type (name_, _) -> (
      match local_type frame name_.id with
      | Some ty when is_numeric ty || is_bool ty ->
          let inner, ty = with_bound name_.id ty in
          make symbol (sort_of context ty) (in_range ty (L.Symbol symbol)) inner
      | _ -> unsupported written.span "a quantifier over this type")
  | Binder_in
      ( { kind = Binding_or_constant name_; _ },
        { kind = Range { start = Some start; stop = Some stop; inclusive; _ }; _ } ) ->
      let _, low = value context frame start in
      let _, high = value context frame stop in
      let ty = match local_type frame name_.id with Some ty -> ty | None -> T.Integer in
      let inner, _ = with_bound name_.id ty in
      let bound = L.Symbol symbol in
      let premise =
        L.(
          Apply ("<=", [ low; bound ]) &&& Apply ((if inclusive then "<=" else "<"), [ bound; high ]))
      in
      make symbol Int premise inner
  | Binder_in _ -> unsupported written.span "a quantifier over a collection"

(* Calls *)

and call context frame (written : expression) callee_expression arguments =
  let source = frame.source in
  match callee_expression.kind with
  | Name path when source.resolved.names.(path.last.id) = Some Old -> (
      match arguments with
      | [ { value = inner; _ } ] ->
          let entry = { frame with locals = frame.old_locals; self = frame.old_self } in
          let _, term = value context entry inner in
          Some (frame, term)
      | _ -> unsupported written.span "`old` with other than one argument")
  | _ -> (
      match source.checked.calls.(written.id) with
      | None -> unsupported written.span "a call the type checker did not resolve"
      | Some call_ -> resolved_call context frame written call_)

and resolved_call context frame (written : expression) (call_ : C.call) =
  let source = frame.source in
  (* Arguments run in the order written. *)
  let frame, values =
    List.fold_left
      (fun (frame, values) (argument : C.argument) ->
        let expression_ = find_expression written argument.expression in
        let frame, term = value context frame expression_ in
        (match argument.conversion with
        | Some From_integer -> ()
        | Some (From_never | Owned_to_view | Function_widening | To_integer) | None -> ());
        (frame, (argument, expression_, term) :: values))
      (frame, []) call_.arguments
  in
  let values = List.rev values in
  let result_type = substituted frame call_.result in
  let havoc_mut frame =
    List.fold_left
      (fun frame ((argument : C.argument), (expression_ : expression), _) ->
        if argument.mode = T.Mut then
          match place_local frame expression_ with
          | Some (id, ty) ->
              { frame with locals = Ids.add id (arrive context frame "changed" ty) frame.locals }
          | None -> havoc_root context frame expression_
        else frame)
      frame values
  in
  let arguments_of (type_arguments : T.argument list) =
    List.map (T.substitute_argument frame.substitution) type_arguments
  in
  let generics_of path =
    match Query.demand context.database Interface.Environment.signature path with
    | Some (signature : T.signature) ->
        List.map (fun (generic : T.generic) -> generic.generic) signature.generics
    | None -> []
  in
  (* Pairs generic parameters with arguments, leaving out those already
     given, such as an [impl]'s. *)
  let pair parameters arguments ~given =
    let parameters =
      List.filter (fun parameter -> not (List.mem_assoc parameter given)) parameters
    in
    let rec go parameters arguments =
      match (parameters, arguments) with
      | parameter :: parameters, argument :: arguments ->
          (parameter, argument) :: go parameters arguments
      | _ -> []
    in
    given @ go parameters arguments
  in
  let instance_of arguments =
    match arguments with
    | [] -> ""
    | _ -> "[" ^ String.concat ", " (List.map argument_key arguments) ^ "]"
  in
  (* In a function with a [time] clause, every call must end, and an
     [impl] used where a bound needs one must not reach back here. *)
  if context.terminates && frame.checking then begin
    let ends =
      match call_.callee with
      | Function { path; _ } -> signature_terminates context path
      | Trait_method { evidence = Impl { impl; _ }; name; receiver; _ } ->
          signature_terminates context (Path.Method { owner = impl; name; receiver })
      | Trait_method { trait; name; receiver; _ } ->
          signature_terminates context (Path.Method { owner = trait.trait; name; receiver })
      | Capability_method { capability; name } ->
          signature_terminates context (Path.Method { owner = capability; name; receiver = Static })
      | Function_value -> (
          match written.kind with
          | Call (callee, _) -> (
              match frame.source.checked.types.(callee.id) with
              | Some (T.Function function_type) -> T.terminates function_type
              | _ -> false)
          | _ -> false)
      | Constructor _ | Intrinsic _ | Built_in_operator -> true
    in
    if not ends then
      oblige context frame Termination written.span
        "This call may not end, since what it calls has no `time` clause, so neither may this \
         function."
        (L.Boolean false);
    let impls =
      Query.demand context.database Call_graph.package_impls (Path.package context.current)
    in
    List.iter
      (fun impl ->
        let reaches_here =
          List.exists
            (fun method_ -> Call_graph.reaches context.graph ~from:method_ ~target:context.current)
            (Call_graph.targets context.graph (Uses_impl impl))
        in
        if reaches_here then
          oblige context frame Termination written.span
            (Printf.sprintf
               "This call uses `%s` where a bound needs it, and that `impl`'s methods reach back \
                here. Such a use passes no arguments the prover can compare, so the recursion \
                cannot be shown to end: write it as a direct call on a part."
               (Path.show impl))
            (L.Boolean false))
      (Call_graph.impls_used context.database impls call_)
  end;
  let with_contract ?(substitution_of = fun _ -> []) ?(instance = "") path = function
    | Some contract when contract.result_kind <> `Yields ->
        Some
          (contract_call context frame written call_ path contract values ~havoc_mut
             ~substitution_of ~instance)
    | Some _ -> unsupported written.span "a call to a yielding method outside a `for` loop"
    | None ->
        let frame = havoc_mut frame in
        Some (frame, arrive context frame "result" result_type)
  in
  match call_.callee with
  | Function { path; type_arguments } ->
      let arguments = arguments_of type_arguments in
      let substitution = pair (generics_of path) arguments ~given:[] in
      with_contract
        ~substitution_of:(fun _ -> substitution)
        ~instance:(instance_of arguments) path
        (function_contract context.database path)
  | Trait_method { trait; name; receiver; evidence; self_type; type_arguments } ->
      let arguments = arguments_of type_arguments in
      let self_type = substituted frame self_type in
      let trait_path = Path.Method { owner = trait.trait; name; receiver } in
      (* The trait's clauses are about [Self] and the trait's parameters. *)
      let trait_substitution =
        let trait_generics =
          match Query.demand context.database Interface.Environment.interface trait.trait with
          | Some (Interface.Environment.Trait_interface interface) ->
              List.map (fun (generic : T.generic) -> generic.generic) interface.trait_generics
          | _ -> []
        in
        let given =
          ({ T.owner = trait.trait; name = "Self" }, T.Type self_type)
          :: pair trait_generics (arguments_of trait.trait_arguments) ~given:[]
        in
        pair (generics_of trait_path) arguments ~given
      in
      let path, own_substitution =
        match evidence with
        | Impl { impl; arguments = impl_arguments } ->
            let given =
              List.map
                (fun (parameter, argument) ->
                  (parameter, T.substitute_argument frame.substitution argument))
                impl_arguments
            in
            let path = Path.Method { owner = impl; name; receiver } in
            (path, pair (generics_of path) arguments ~given)
        | _ -> (trait_path, trait_substitution)
      in
      let own_key =
        match evidence with
        | Impl { impl; _ } -> Query.demand context.database Interface.Summary.key impl
        | _ -> None
      in
      let substitution_of (part : part) =
        if Some part.callee.key = own_key then own_substitution else trait_substitution
      in
      with_contract ~substitution_of
        ~instance:(instance_of (T.Type self_type :: arguments))
        path
        (method_contract context.database trait name receiver evidence)
  | Constructor { variant; _ } -> Some (construct context frame written call_ variant values)
  | Capability_method _ | Function_value | Intrinsic _ | Built_in_operator ->
      let frame = havoc_mut frame in
      ignore source;
      Some (frame, arrive context frame "result" result_type)

and signature_terminates context path =
  match Query.demand context.database Interface.Environment.signature path with
  | Some (signature : T.signature) -> signature.terminates
  | None -> true

(* Data *)

and member context frame (written : expression) base =
  let source = frame.source in
  match source.checked.meanings.(written.id) with
  | Some (Field_read { type_; field }) ->
      let type_ = substituted frame type_ in
      let frame, term = value context frame base in
      if constructors context type_ = None then
        unsupported written.span "a field of `%s`, whose fields the prover does not see"
          (T.show type_);
      ignore (sort_of context type_);
      let field_type =
        match declared_fields context type_ None with
        | Some fields -> ( match List.assoc_opt field fields with Some ty -> ty | None -> T.Error)
        | None -> T.Error
      in
      Some (frame, field_of context frame type_ None field field_type term)
  | Some (Variant_value { type_; variant }) ->
      let type_ = substituted frame type_ in
      Some (frame, variant_value context written type_ variant)
  | Some (Global { path; _ }) -> Some (frame, constant_value context frame written path)
  | _ -> unsupported written.span "this member"

(* A field of a value, which is in its type's range like every value. *)
and field_of context frame ty variant field field_type term =
  let part = L.Apply (selector_name ty variant field, [ term ]) in
  assume context frame (in_range field_type part);
  part

(* A variant with no fields, such as [None]. *)
and variant_value context (written : expression) type_ variant =
  match declared_fields context type_ (Some variant) with
  | Some [] ->
      ignore (sort_of context type_);
      L.Apply (constructor_name type_ (Some variant), [])
  | Some _ -> unsupported written.span "a variant used as a function"
  | None -> unsupported written.span "a variant of `%s`" (T.show type_)

(* A constant is its value, worked out from its definition, which is made
   of literals, arithmetic, other constants, and values built from them. *)
and constant_value context frame (written : expression) path =
  match Interface.Summary.definition context.database path with
  | Some (key, { kind = Constant { value = defined; _ }; _ }) -> (
      match callee_source context.database key with
      | Some constant_source ->
          let empty =
            {
              frame with
              source = constant_source;
              locals = Ids.empty;
              checking = false;
              self = None;
            }
          in
          snd (value context empty defined)
      | None -> unsupported written.span "a constant with errors")
  | _ -> unsupported written.span "a function used as a value"

(* Building a record or a variant: its constructor, with each field given
   or defaulted. *)
and construct context frame (written : expression) (call_ : C.call) variant values =
  let ty = substituted frame call_.result in
  match (constructors context ty, declared_fields context ty variant) with
  | Some shape, Some declared ->
      ignore (sort_of context ty);
      let given =
        List.map
          (fun ((argument : C.argument), _, term) ->
            (fst (List.nth declared argument.parameter), term))
          values
      in
      let fields = match List.assoc_opt variant shape with Some fields -> fields | None -> [] in
      let field_value (name_, _) =
        match List.assoc_opt name_ given with
        | Some term -> term
        | None -> field_default context frame written ty variant name_
      in
      (frame, L.Apply (constructor_name ty variant, List.map field_value fields))
  | _ ->
      (* A type whose fields are not visible here is known by its range. *)
      (frame, arrive context frame "built" ty)

and field_default context frame (written : expression) ty variant field =
  let path =
    match ty with T.Named { path; _ } -> path | _ -> unsupported written.span "a default"
  in
  match Interface.Summary.definition context.database path with
  | Some (key, { kind = Type_definition { body; _ }; _ }) -> (
      let fields =
        match (body, variant) with
        | Fields fields, None -> fields
        | Variants variants, Some name -> (
            match List.find_opt (fun (v : variant) -> v.name.text = name) variants with
            | Some { fields = Some fields; _ } -> fields
            | _ -> [])
        | _ -> []
      in
      match
        List.find_map
          (fun (written_field : field) ->
            match written_field.kind with
            | Field_declaration { name = name_; default = Some default; _ } when name_.text = field
              ->
                Some default
            | _ -> None)
          fields
      with
      | Some default -> (
          match callee_source context.database key with
          | Some type_source ->
              snd
                (value context
                   { frame with source = type_source; locals = Ids.empty; checking = false }
                   default)
          | None -> unsupported written.span "a default of a type with errors")
      | None -> unsupported written.span "a field left out without a default")
  | _ -> unsupported written.span "a default"

(* Whether a value matches a pattern, and the names it binds: the
   condition, and the frame with the names bound. A name bound is the part
   of the value it names, which means something only where the condition
   holds, and is used only there. *)
and pattern_match context frame (written : pattern) term ty : L.term * frame =
  let source = frame.source in
  match written.kind with
  | Wildcard -> (L.Boolean true, frame)
  | Binding_or_constant name_ -> (
      match source.resolved.names.(name_.id) with
      | Some Binding -> (L.Boolean true, { frame with locals = Ids.add name_.id term frame.locals })
      | Some (Definition path) ->
          ( L.equal term
              (constant_value context frame
                 { kind = True; span = written.span; id = written.id }
                 path),
            frame )
      | _ -> unsupported written.span "this name in a pattern")
  | Qualified_constant _ -> (
      match source.checked.patterns.(written.id) with
      | Some (Constant_pattern path) ->
          ( L.equal term
              (constant_value context frame
                 { kind = True; span = written.span; id = written.id }
                 path),
            frame )
      | _ -> unsupported written.span "this constant in a pattern")
  | Literal literal -> (literal_condition written literal term, frame)
  | Pattern_range { start; stop; inclusive } ->
      let end_ (range_end : range_end) =
        match range_end.kind with
        | End_literal (Literal_integer value) -> L.Integer value
        | _ -> unsupported range_end.span "a range pattern's end that is not a literal"
      in
      ( L.(
          Apply ("<=", [ end_ start; term ])
          &&& Apply ((if inclusive then "<=" else "<"), [ term; end_ stop ])),
        frame )
  | Variant { fields; _ } -> (
      match source.checked.patterns.(written.id) with
      | Some (Variant_pattern { type_; variant }) ->
          let type_ = substituted frame type_ in
          ignore (sort_of context type_);
          if constructors context type_ = None then
            unsupported written.span "a variant of `%s`, which the prover does not see"
              (T.show type_);
          let test = L.Apply (L.tester (constructor_name type_ (Some variant)), [ term ]) in
          let condition, frame =
            fields_match context frame written type_ (Some variant) term
              (Option.value fields ~default:[])
          in
          (L.( &&& ) test condition, frame)
      | _ -> unsupported written.span "this variant pattern")
  | Record fields -> (
      match source.checked.patterns.(written.id) with
      | Some (Record_pattern { type_ }) ->
          let type_ = substituted frame type_ in
          ignore (sort_of context type_);
          if constructors context type_ = None then
            unsupported written.span "the fields of `%s`, which the prover does not see"
              (T.show type_);
          fields_match context frame written type_ None term fields
      | _ -> unsupported written.span "this record pattern")
  | Alternatives alternatives ->
      let conditions =
        List.map
          (fun alternative ->
            let condition, after = pattern_match context frame alternative term ty in
            if not (Ids.equal ( = ) after.locals frame.locals) then
              unsupported written.span "alternatives that bind names";
            condition)
          alternatives
      in
      (L.disjunction conditions, frame)
  | Pattern_error -> unsupported written.span "this pattern"

and literal_condition (written : pattern) literal term =
  match literal with
  | Literal_integer value -> L.equal term (L.Integer value)
  | Literal_true -> term
  | Literal_false -> L.not_ term
  | Literal_string _ -> unsupported written.span "a string pattern"

and fields_match context frame (written : pattern) type_ variant term fields =
  let declared =
    match declared_fields context type_ variant with Some declared -> declared | None -> []
  in
  List.fold_left
    (fun (condition, frame) (field : pattern_field) ->
      let named name_ subpattern =
        match List.assoc_opt name_ declared with
        | Some field_type ->
            let part = field_of context frame type_ variant name_ field_type term in
            let inner, frame = pattern_match context frame subpattern part field_type in
            (L.( &&& ) condition inner, frame)
        | None -> unsupported field.span "the field `%s`" name_
      in
      match field.kind with
      | Rest -> (condition, frame)
      | Named_field (name_, subpattern) -> named name_.text subpattern
      | Field subpattern -> (
          match (declared, subpattern.kind) with
          | [ (only, _) ], _ -> named only subpattern
          | _, Binding_or_constant name_ -> named name_.text subpattern
          | _ -> unsupported written.span "a field pattern"))
    (L.Boolean true, frame) fields

and match_ context frame (written : expression) scrutinees arms =
  let frame, scrutinee_values =
    List.fold_left
      (fun (frame, values) scrutinee ->
        let frame, term = value context frame scrutinee in
        (frame, (term, type_of frame scrutinee) :: values))
      (frame, []) scrutinees
  in
  let scrutinee_values = List.rev scrutinee_values in
  let result_type = type_of frame written in
  let carries_value = not (T.equal result_type T.unit || result_type = T.Never) in
  let remaining = ref (L.Boolean true) in
  let reached =
    List.filter_map
      (fun (arm_ : arm) ->
        if List.length arm_.patterns <> List.length scrutinee_values then
          unsupported arm_.span "an arm with a different number of patterns";
        let condition, bound =
          List.fold_left2
            (fun (condition, frame) pattern (term, ty) ->
              let inner, frame = pattern_match context frame pattern term ty in
              (L.( &&& ) condition inner, frame))
            (L.Boolean true, frame) arm_.patterns scrutinee_values
        in
        let entered = restrict bound (L.( &&& ) !remaining condition) in
        let taken, entered =
          match arm_.guard with
          | Some guard ->
              let after, test = pure_operand context entered guard in
              (L.( &&& ) condition test, restrict after test)
          | None -> (condition, entered)
        in
        remaining := L.( &&& ) !remaining (L.not_ taken);
        match arm_.body.kind with
        | Expression body -> expression context entered body
        | _ ->
            Option.map (fun after -> (after, L.Boolean true)) (statement context entered arm_.body))
      arms
  in
  let scoped (joined : frame) =
    { joined with locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) joined.locals }
  in
  if carries_value then
    match join context ~value_type:result_type (List.map (fun (f, t) -> (f, Some t)) reached) with
    | Some (joined, Some term) -> Some (scoped joined, term)
    | Some (joined, None) -> Some (scoped joined, L.Boolean true)
    | None -> None
  else
    Option.map
      (fun joined -> (scoped joined, L.Boolean true))
      (join_frames context (List.map fst reached))

(* [?]: the value inside an [Ok] or a [Some] goes on, and an [Err] or a
   [None] returns, unchanged. *)
and try_ context frame (written : expression) inner =
  let frame, term = value context frame inner in
  let ty = type_of frame inner in
  let shape =
    match constructors context ty with
    | Some shape -> shape
    | None -> unsupported written.span "`?` on `%s`" (T.show ty)
  in
  ignore (sort_of context ty);
  let has variant = List.mem_assoc (Some variant) shape in
  let success, failure =
    if has "Ok" then ("Ok", "Err")
    else if has "Some" then ("Some", "None")
    else unsupported written.span "`?` on `%s`" (T.show ty)
  in
  let succeeded = L.Apply (L.tester (constructor_name ty (Some success)), [ term ]) in
  let output =
    match context.output with
    | Some output -> output
    | None -> unsupported written.span "`?` outside a function"
  in
  ignore (sort_of context output);
  let returned =
    match List.assoc_opt (Some failure) shape with
    | Some [ (field, _) ] ->
        L.Apply
          ( constructor_name output (Some failure),
            [ L.Apply (selector_name ty (Some failure) field, [ term ]) ] )
    | Some [] -> L.Apply (constructor_name output (Some failure), [])
    | _ -> unsupported written.span "`?` on `%s`" (T.show ty)
  in
  context.returns <- (restrict frame (L.not_ succeeded), Some returned) :: context.returns;
  let payload =
    match List.assoc_opt (Some success) shape with
    | Some [ (field, field_type) ] -> field_of context frame ty (Some success) field field_type term
    | _ -> unsupported written.span "`?` on `%s`" (T.show ty)
  in
  Some (restrict frame succeeded, payload)

(* [with]: a record with some fields replaced, each update a path of
   fields. *)
and with_ context frame (written : expression) base updates =
  let source = frame.source in
  let frame, base_term = value context frame base in
  let ty = type_of frame written in
  let rec replace ty term path replacement =
    match (path, constructors context ty) with
    | [], _ -> replacement
    | field :: rest, Some [ (None, fields) ] ->
        ignore (sort_of context ty);
        L.Apply
          ( constructor_name ty None,
            List.map
              (fun (name_, field_type) ->
                let current = L.Apply (selector_name ty None name_, [ term ]) in
                if name_ = field then replace field_type current rest replacement else current)
              fields )
    | _ -> unsupported written.span "`with` on `%s`" (T.show ty)
  in
  let frame, term =
    List.fold_left
      (fun (frame, term) (update_ : update) ->
        match update_.kind with
        | Update { field; path; value = updated } ->
            let frame, replacement =
              match updated with
              | Some updated -> value context frame updated
              | None -> (
                  match source.resolved.names.(field.id) with
                  | Some (Local id) -> (frame, Ids.find id frame.locals)
                  | _ -> unsupported update_.span "this update")
            in
            ( frame,
              replace ty term (field.text :: List.map (fun (n : name) -> n.text) path) replacement
            )
        | Update_error -> unsupported update_.span "this update")
      (frame, base_term) updates
  in
  Some (frame, term)

and find_expression (written : expression) id =
  let found = ref None in
  let rec visit (expression_ : expression) =
    if expression_.id = id then found := Some expression_
    else if !found = None then
      Syntax_walk.expression_parts ~expression:visit ~statement:(fun _ -> ()) expression_
  in
  visit written;
  match !found with
  | Some expression_ -> expression_
  | None -> unsupported written.span "an argument"

(* The local a [mut] argument names, when it is a whole local. *)
and place_local frame (expression_ : expression) =
  match expression_.kind with
  | Mode (_, inner) | Parenthesized inner -> place_local frame inner
  | Name _ -> (
      match frame.source.checked.meanings.(expression_.id) with
      | Some (Local_value id) -> (
          match local_type frame id with Some ty -> Some (id, ty) | None -> None)
      | _ -> None)
  | _ -> None

(* A call to a function whose contract the prover reads: its [requires]
   must hold, its [ensures] holds after, and a recursive call decreases. *)
and contract_call context frame (written : expression) (call_ : C.call) path contract values
    ~havoc_mut ~substitution_of ~instance =
  let caller = frame.source in
  let argument_at index =
    List.find_map
      (fun ((argument : C.argument), _, term) ->
        if argument.parameter = index then Some term else None)
      values
  in
  (* Each part binds its own parameters to the call's arguments, or to its
     defaults. *)
  let bindings (part : part) =
    List.mapi
      (fun index binding ->
        let term =
          match argument_at index with
          | Some term -> Some term
          | None -> (
              match List.assoc_opt index part.defaults with
              | Some default ->
                  let empty =
                    {
                      frame with
                      source = part.callee;
                      locals = Ids.empty;
                      checking = false;
                      substitution = substitution_of part;
                    }
                  in
                  Some (snd (value context empty default))
              | None -> None)
        in
        (binding, term))
      part.binding
  in
  let bind bindings =
    List.fold_left
      (fun (locals, self) (binding, term) ->
        match (binding, term) with
        | Self_binding, Some term -> (locals, Some term)
        | Parameter_binding name_, Some term -> (Ids.add name_.id term locals, self)
        | _, None -> (locals, self))
      (Ids.empty, None) bindings
  in
  let entry_frame (part : part) =
    let locals, self = bind (bindings part) in
    {
      frame with
      source = part.callee;
      locals;
      old_locals = locals;
      self;
      old_self = self;
      result = None;
      checking = false;
      loop = None;
      substitution = substitution_of part;
    }
  in
  let own = List.hd contract.parts in
  (* A call in a cycle of the call graph must decrease: the callee's
     measure, at the call's arguments, is below the caller's on entry. *)
  if
    context.terminates && frame.checking
    && Call_graph.reaches context.graph ~from:path ~target:context.current
  then
    begin match (context.measures, own.decreases) with
    | [], _ | _, [] ->
        oblige context frame Termination written.span
          (Printf.sprintf
             "This call to `%s` may not end: it calls back here, and both need a `decreases` \
              clause for the prover to show that the recursion ends."
             (Path.show path))
          (L.Boolean false)
    | measures, callee_measures ->
        let current_frame =
          { frame with checking = false; locals = frame.old_locals; self = frame.old_self }
        in
        let callee_entry = entry_frame own in
        let rec prefix before after =
          match (before, after) with
          | b :: before, a :: after ->
              let rest_before, rest_after = prefix before after in
              (b :: rest_before, a :: rest_after)
          | _ -> ([], [])
        in
        let before = List.map (fun measure -> snd (value context current_frame measure)) measures in
        let after =
          List.map (fun measure -> snd (value context callee_entry measure)) callee_measures
        in
        let before, after = prefix before after in
        oblige context frame Termination written.span
          (Printf.sprintf "This call may not decrease `%s`."
             (String.concat ", " (List.map (fun (m : expression) -> quote caller m.span) measures)))
          (smaller before after)
    end;
  (* The callee's [requires]: its own when it states any, and otherwise
     its trait's. *)
  let requiring =
    match contract.parts with
    | own :: others -> if own.requires <> [] || others = [] then [ own ] else others
    | [] -> []
  in
  let required =
    List.concat_map
      (fun (part : part) ->
        let entry = entry_frame part in
        List.map
          (fun (clause : expression) ->
            let _, term = value context entry clause in
            oblige context frame Requires written.span
              (Printf.sprintf "`%s` may not hold for this call to `%s`."
                 (quote part.callee clause.span) (Path.show path))
              term;
            term)
          part.requires)
      requiring
  in
  let required = L.conjunction required in
  let after = havoc_mut frame in
  (* What each [mut] argument holds after the call: a local's new value,
     or, for a part of a value, a fresh one, since the prover does not yet
     write it back into the value it is part of. *)
  let changed =
    List.filter_map
      (fun ((argument : C.argument), (expression_ : expression), _) ->
        if argument.mode = T.Mut then
          match place_local after expression_ with
          | Some (id, _) ->
              Option.map (fun term -> (argument.parameter, term)) (Ids.find_opt id after.locals)
          | None ->
              Some (argument.parameter, arrive context after "changed" (type_of frame expression_))
        else None)
      values
  in
  let own_arguments = List.filter_map snd (bindings own) in
  let result =
    if contract.pure && List.length own_arguments = List.length values then begin
      let symbol = "function." ^ Path.show path ^ instance in
      declare context
        (L.Function
           ( symbol,
             List.map
               (fun ((_ : C.argument), (expression_ : expression), _) ->
                 sort_of context (type_of frame expression_))
               values,
             sort_of context (substituted frame call_.result) ));
      let term = L.Apply (symbol, own_arguments) in
      assume context after (in_range (substituted frame call_.result) term);
      term
    end
    else arrive context after "result" (substituted frame call_.result)
  in
  if not (List.exists (Path.equal path) context.instantiating) then begin
    context.instantiating <- path :: context.instantiating;
    (* The definition, unfolded once, where the [requires] holds. A body
       the prover cannot read is simply not unfolded. *)
    (match contract.definition with
    | Some (part, body) when not (List.exists (L.mentions after.bound) own_arguments) -> (
        let unfolding = { (entry_frame part) with condition = after.condition } in
        try
          match block_value context unfolding body with
          | Some (_, defined) -> assume context after (L.( ==> ) required (L.equal result defined))
          | None -> ()
        with Unsupported _ -> ())
    | _ -> ());
    (* The [ensures], after, where the [requires] held: [mut] parameters
       have their new values, and [old] the ones they had. *)
    List.iter
      (fun (part : part) ->
        let entry = bindings part in
        let exit_bindings =
          List.mapi
            (fun index (binding, term) ->
              ( binding,
                match List.assoc_opt index changed with Some term -> Some term | None -> term ))
            entry
        in
        let entry_locals, entry_self = bind entry in
        let exit_locals, exit_self = bind exit_bindings in
        let ensures_frame =
          {
            frame with
            source = part.callee;
            condition = after.condition;
            locals = exit_locals;
            old_locals = entry_locals;
            self = exit_self;
            old_self = entry_self;
            result = Some result;
            checking = false;
            loop = None;
            substitution = substitution_of part;
          }
        in
        List.iter
          (fun (clause : expression) ->
            match value context ensures_frame clause with
            | _, term -> assume context after (L.( ==> ) required term))
          part.ensures)
      contract.parts;
    context.instantiating <- List.tl context.instantiating
  end;
  (after, result)

and smaller before after =
  match (before, after) with
  | [ b ], [ a ] -> L.(Apply ("<=", [ int 0; b ]) &&& Apply ("<", [ a; b ]))
  | b :: before, a :: after ->
      L.(
        Apply ("<=", [ int 0; b ])
        &&& (Apply ("<", [ a; b ]) ||| (equal a b &&& smaller before after)))
  | _ -> L.Boolean true

(* Statements and blocks *)

and block_value context frame (written : block) =
  let rec go frame = function
    | [] -> Some (frame, L.Boolean true)
    | [ ({ kind = Expression last; _ } : statement) ] -> expression context frame last
    | statement_ :: rest -> (
        match statement context frame statement_ with Some frame -> go frame rest | None -> None)
  in
  match go frame written.statements with
  | Some (after, term) ->
      (* Locals declared inside the block end with it. *)
      let locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) after.locals in
      Some ({ after with locals }, term)
  | None -> None

and statement context frame (written : statement) : frame option =
  match written.kind with
  | Expression value_ -> Option.map fst (expression context frame value_)
  | Let { pattern; value = initial; else_ = None; _ } -> (
      match expression context frame initial with
      | None -> None
      | Some (frame, term) ->
          (* A [let]'s pattern cannot fail, so only its names matter. *)
          let _, frame = pattern_match context frame pattern term (type_of frame initial) in
          Some frame)
  | Let { else_ = Some _; _ } -> unsupported written.span "`let ... else`"
  | Assignment { target; operator; value = assigned } ->
      assignment context frame written target operator assigned
  | While { condition; clauses; body } -> while_ context frame written condition clauses body
  | For { parallel = _; pattern; iterable; clauses; body } ->
      for_ context frame written pattern iterable clauses body
  | Assert asserted ->
      let frame, term = value context frame asserted in
      if is_test context then assume context frame term
      else
        oblige context frame Assertion asserted.span
          (Printf.sprintf "`%s` may not hold." (quote frame.source asserted.span))
          term;
      Some frame
  | Proof block_ -> (
      match block_value context frame block_ with
      | Some (after, _) -> Some { frame with locals = after.locals }
      | None -> None)
  | Parallel block_ ->
      (* Branches are disjoint, so they can run in order. *)
      List.fold_left
        (fun frame branch ->
          match frame with Some frame -> statement context frame branch | None -> None)
        (Some frame) block_.statements
  | Yield _ -> unsupported written.span "`yield`"
  | Statement_error -> unsupported written.span "this statement"

and is_test context = match context.current with Path.Test _ -> true | _ -> false

(* The local or [self] a place is part of, which takes a fresh value when
   a part of it changes in a way the prover does not follow. *)
and havoc_root context frame (place : expression) =
  match place.kind with
  | Mode (_, inner) | Parenthesized inner | Member (inner, _) | Bracket (inner, _) ->
      havoc_root context frame inner
  | Self_value -> { frame with self = Some (arrive context frame "changed" (type_of frame place)) }
  | Name _ -> (
      match place_local frame place with
      | Some (id, ty) ->
          { frame with locals = Ids.add id (arrive context frame "changed" ty) frame.locals }
      | None -> unsupported place.span "changing this place")
  | _ -> unsupported place.span "changing this place"

(* Stores a value into a place: a local, a field of a place, or [self]. An
   element of a collection changes its collection in a way the prover does
   not follow yet, so the collection's root takes a fresh value. *)
and store context frame (place : expression) new_value =
  let source = frame.source in
  match place.kind with
  | Mode (_, inner) | Parenthesized inner -> store context frame inner new_value
  | Self_value -> { frame with self = Some new_value }
  | Name _ -> (
      match place_local frame place with
      | Some (id, _) -> { frame with locals = Ids.add id new_value frame.locals }
      | None -> unsupported place.span "assigning to this place")
  | Member (base, _) -> (
      match source.checked.meanings.(place.id) with
      | Some (Field_read { type_; field }) -> (
          let type_ = substituted frame type_ in
          let frame, base_value = value context frame base in
          match constructors context type_ with
          | Some [ (None, fields) ] ->
              let rebuilt =
                L.Apply
                  ( constructor_name type_ None,
                    List.map
                      (fun (name_, _) ->
                        if name_ = field then new_value
                        else L.Apply (selector_name type_ None name_, [ base_value ]))
                      fields )
              in
              store context frame base rebuilt
          | _ -> unsupported place.span "assigning to a field of `%s`" (T.show type_))
      | _ -> unsupported place.span "assigning to this place")
  | Bracket _ -> havoc_root context frame place
  | _ -> unsupported place.span "assigning to this place"

and assignment context frame (written : statement) target operator assigned =
  let source = frame.source in
  let ty = type_of frame target in
  let frame, new_value =
    match operator with
    | Assign -> value context frame assigned
    | _ ->
        let frame, right = value context frame assigned in
        let frame, current = value context frame target in
        let binary_operator : binary =
          match operator with
          | Add_assign -> Add
          | Subtract_assign -> Subtract
          | Multiply_assign -> Multiply
          | Divide_assign -> Divide
          | Remainder_assign -> Remainder
          | Bit_and_assign -> Bit_and
          | Bit_or_assign -> Bit_or
          | Bit_xor_assign -> Bit_xor
          | Shift_left_assign -> Shift_left
          | _ -> Shift_right
        in
        if not (is_numeric ty) then (
          ignore source;
          (frame, arrive context frame "operator" ty))
        else
          begin match binary_operator with
          | Add | Subtract | Multiply | Divide | Remainder ->
              ( frame,
                arithmetic context frame
                  { target with span = written.span }
                  ty binary_operator current right )
          | _ -> (frame, opaque_operation context frame ty "assignment" [ current; right ])
          end
  in
  (* An index is checked once, when the place is read or written. *)
  let frame =
    match (operator, target.kind) with
    | Assign, Bracket _ -> fst (value context frame target)
    | _ -> frame
  in
  Some (store context frame target new_value)

(* The locals a loop's body may change, which are havocked at its head. *)
and changed_locals frame (body : block) =
  let changed = ref [] in
  let rec visit_statement (statement_ : statement) =
    (match statement_.kind with
    | Assignment { target; _ } -> (
        match place_local frame target with Some (id, _) -> changed := id :: !changed | None -> ())
    | _ -> ());
    Syntax_walk.statement_parts ~expression:visit_expression ~statement:visit_statement statement_
  and visit_expression (expression_ : expression) =
    (match expression_.kind with
    | Mode (Mut, inner) -> (
        match place_local frame inner with Some (id, _) -> changed := id :: !changed | None -> ())
    | _ -> ());
    Syntax_walk.expression_parts ~expression:visit_expression ~statement:visit_statement expression_
  in
  List.iter visit_statement body.statements;
  List.sort_uniq compare (List.filter (fun id -> Ids.mem id frame.locals) !changed)

and havoc context frame ids =
  List.fold_left
    (fun frame id ->
      let ty = match local_type frame id with Some ty -> ty | None -> T.Integer in
      { frame with locals = Ids.add id (arrive context frame "loop" ty) frame.locals })
    frame ids

and invariants (clauses : loop_clause list) =
  List.filter_map
    (fun (clause : loop_clause) ->
      match clause.kind with Invariant value -> Some value | _ -> None)
    clauses

and check_invariants context frame clauses ~when_ =
  List.iter
    (fun (invariant : expression) ->
      let _, term = value context frame invariant in
      oblige context frame Invariant invariant.span
        (Printf.sprintf "The loop invariant `%s` may not hold %s."
           (quote frame.source invariant.span)
           when_)
        term)
    (invariants clauses)

and assume_invariants context frame clauses =
  List.iter
    (fun (invariant : expression) ->
      let _, term = value context { frame with checking = false } invariant in
      assume context frame term)
    (invariants clauses)

and unproven_costs context (clauses : loop_clause list) =
  List.iter
    (fun (clause : loop_clause) ->
      match clause.kind with
      | Loop_cost _ ->
          context.unproven <- (clause.span, "a loop's `cost` clause") :: context.unproven
      | _ -> ())
    clauses

and while_ context frame (written : statement) condition clauses body =
  unproven_costs context clauses;
  check_invariants context frame clauses ~when_:"on entry to the loop";
  let changed = changed_locals frame body in
  let head = havoc context frame changed in
  assume_invariants context head clauses;
  let head, test = value context head condition in
  let exits = { breaks = []; continues = [] } in
  let inside = { (restrict head test) with loop = Some exits } in
  let measures =
    match
      List.find_map
        (fun (clause : loop_clause) ->
          match clause.kind with Loop_decreases measures -> Some measures | _ -> None)
        clauses
    with
    | Some measures -> `Written measures
    | None -> (
        match condition.kind with
        | Binary { operator = Less | Less_equal | Greater | Greater_equal; left; right; _ } ->
            `Guessed (left, right, condition)
        | _ -> `None)
  in
  let measure_terms (at : frame) =
    match measures with
    | `Written measures ->
        Some
          (List.map
             (fun measure -> snd (value context { at with checking = false } measure))
             measures)
    | `Guessed (left, right, (condition : expression)) -> (
        let _, l = value context { at with checking = false } left in
        let _, r = value context { at with checking = false } right in
        match condition.kind with
        | Binary { operator = Less; _ } -> Some [ L.Apply ("-", [ r; l ]) ]
        | Binary { operator = Less_equal; _ } ->
            Some [ L.Apply ("+", [ L.Apply ("-", [ r; l ]); L.int 1 ]) ]
        | Binary { operator = Greater; _ } -> Some [ L.Apply ("-", [ l; r ]) ]
        | _ -> Some [ L.Apply ("+", [ L.Apply ("-", [ l; r ]); L.int 1 ]) ])
    | `None -> None
  in
  let start_measures = if context.terminates then measure_terms inside else None in
  if context.terminates && start_measures = None then
    oblige context inside Termination written.span
      "This loop may not end: give it a `decreases` clause." (L.Boolean false);
  let finished = block_value context inside body in
  let ends = (match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues in
  List.iter
    (fun (end_ : frame) ->
      let end_ = { end_ with loop = frame.loop } in
      check_invariants context end_ clauses ~when_:"after an iteration";
      match (start_measures, measure_terms end_) with
      | Some before, Some after ->
          let rec smaller before after =
            match (before, after) with
            | [ b ], [ a ] -> L.(Apply ("<=", [ int 0; b ]) &&& Apply ("<", [ a; b ]))
            | b :: before, a :: after ->
                L.(
                  Apply ("<=", [ int 0; b ])
                  &&& (Apply ("<", [ a; b ]) ||| (equal a b &&& smaller before after)))
            | _ -> L.Boolean true
          in
          oblige context end_ Termination written.span "This loop's measure may not decrease."
            (smaller before after)
      | _ -> ())
    ends;
  let exit_ = { (restrict head (L.not_ test)) with loop = frame.loop } in
  join_frames context
    (exit_ :: List.map (fun (frame' : frame) -> { frame' with loop = frame.loop }) exits.breaks)
  |> Option.map (fun (joined : frame) ->
      { joined with locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) joined.locals })

and for_ context frame (written : statement) pattern iterable clauses body =
  unproven_costs context clauses;
  match (frame.source.checked.loops.(written.id), iterable.kind, pattern.kind) with
  | ( Some (Integer_range { element; inclusive }),
      Range { start = Some start; stop = Some stop; _ },
      (Binding_or_constant _ | Wildcard) ) ->
      let frame, low = value context frame start in
      let frame, high = value context frame stop in
      check_invariants context frame clauses ~when_:"on entry to the loop";
      let changed = changed_locals frame body in
      let head = havoc context frame changed in
      assume_invariants context head clauses;
      let index = arrive context head "index" element in
      let in_range =
        L.(
          Apply ("<=", [ low; index ]) &&& Apply ((if inclusive then "<=" else "<"), [ index; high ]))
      in
      let exits = { breaks = []; continues = [] } in
      let inside = { (restrict head in_range) with loop = Some exits } in
      let inside =
        match pattern.kind with
        | Binding_or_constant name_ -> { inside with locals = Ids.add name_.id index inside.locals }
        | _ -> inside
      in
      let finished = block_value context inside body in
      let ends =
        (match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues
      in
      List.iter
        (fun (end_ : frame) ->
          check_invariants context { end_ with loop = frame.loop } clauses
            ~when_:"after an iteration")
        ends;
      join_frames context
        ({ head with loop = frame.loop }
        :: List.map (fun (f : frame) -> { f with loop = frame.loop }) exits.breaks)
      |> Option.map (fun (joined : frame) ->
          { joined with locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) joined.locals })
  | Some (Yielding { call = driven; mode }), _, _ ->
      each_loop context frame written pattern iterable clauses body driven mode
  | _ -> unsupported written.span "a `for` loop over a cursor"

(* A [for] loop over a yielding method: each element is a fresh value of
   its type, since the method's contract for each [yield] is not read
   yet, and the loop ends when the method has a [time] clause. *)
and each_loop context frame (written : statement) pattern iterable clauses body (driven : C.call)
    mode =
  let source = frame.source in
  let frame =
    List.fold_left
      (fun frame (argument : C.argument) ->
        fst (value context frame (find_expression iterable argument.expression)))
      frame driven.arguments
  in
  let terminates =
    match driven.callee with
    | Function { path; _ } -> (
        match Query.demand context.database Interface.Environment.signature path with
        | Some signature -> signature.terminates
        | None -> false)
    | _ -> false
  in
  if context.terminates && not terminates then
    oblige context frame Termination written.span
      "This loop may not end: the method it loops over has no `time` clause." (L.Boolean false);
  check_invariants context frame clauses ~when_:"on entry to the loop";
  let changed = changed_locals frame body in
  let head = havoc context frame changed in
  let head = if mode = T.Mut then havoc_root context head iterable else head in
  assume_invariants context head clauses;
  let element_type =
    match Option.map (substituted frame) source.checked.pattern_types.(pattern.id) with
    | Some ty -> ty
    | None -> unsupported pattern.span "a loop variable without a type"
  in
  let element = arrive context head "element" element_type in
  let exits = { breaks = []; continues = [] } in
  let _, inside =
    pattern_match context { head with loop = Some exits } pattern element element_type
  in
  let finished = block_value context inside body in
  let ends = (match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues in
  List.iter
    (fun (end_ : frame) ->
      check_invariants context { end_ with loop = frame.loop } clauses ~when_:"after an iteration")
    ends;
  join_frames context
    ({ head with loop = frame.loop }
    :: List.map (fun (f : frame) -> { f with loop = frame.loop }) exits.breaks)
  |> Option.map (fun (joined : frame) ->
      { joined with locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) joined.locals })

(* Definitions *)

let new_context database ~current ~terminates ~measures checked =
  {
    graph = Query.demand database Call_graph.graph (Path.package current);
    database;
    current;
    terminates;
    measures;
    declarations = [];
    declared = Hashtbl.create 64;
    facts = [];
    obligations = [];
    unproven = [];
    fresh = 0;
    values = [];
    returns = [];
    instantiating = [];
    output = None;
    fits =
      List.filter_map
        (function C.Integer_fits { expression; type_ } -> Some (expression, type_) | _ -> None)
        checked.C.obligations;
  }

let outcome context =
  { obligations = List.rev context.obligations; unproven_clauses = List.rev context.unproven }

let reject_checker_obligations (source : source) =
  List.iter
    (function
      | C.Integer_fits _ -> ()
      | C.Disjoint { first; _ } ->
          raise (Unsupported (Span.make 0 0, Printf.sprintf "disjoint indexes (at node %d)" first))
      | C.Costs_imply _ -> raise (Unsupported (Span.make 0 0, "a function value's costs"))
      | C.Guards_cover _ -> raise (Unsupported (Span.make 0 0, "a `match` with guards")))
    source.checked.obligations

let costs_unproven context (clauses : clause list) =
  List.iter
    (fun (clause : clause) ->
      match clause.kind with
      | Cost { resource = Time; bound = Finite; _ } -> ()
      | Cost _ -> context.unproven <- (clause.span, "a `cost` bound") :: context.unproven
      | _ -> ())
    clauses

(* A function, method, or theorem: its parameters arrive, its [requires]
   are assumed, its body runs, and its [ensures] are shown at each way it
   returns. *)
let function_ ?(proof = false) database (source : source) ~path (signature : signature)
    (body : block) =
  reject_checker_obligations source;
  (match signature.result with
  | Some (Yields _ | Lends _) -> unsupported body.span "a lending or yielding method"
  | _ -> ());
  let terminates =
    proof
    || List.exists
         (fun (clause : clause) ->
           match clause.kind with Cost { resource = Time; _ } -> true | _ -> false)
         signature.clauses
  in
  let measures =
    List.concat_map
      (fun (clause : clause) -> match clause.kind with Decreases measures -> measures | _ -> [])
      signature.clauses
  in
  let context = new_context database ~current:path ~terminates ~measures source.checked in
  costs_unproven context signature.clauses;
  (match Query.demand database Interface.Environment.signature path with
  | Some { output = Returns ty; _ } -> context.output <- Some ty
  | _ -> ());
  let start =
    {
      source;
      locals = Ids.empty;
      old_locals = Ids.empty;
      self = None;
      old_self = None;
      result = None;
      condition = L.Boolean true;
      checking = true;
      bound = [];
      loop = None;
      substitution = [];
    }
  in
  let start =
    List.fold_left
      (fun frame (parameter : parameter) ->
        match parameter.kind with
        | Named_parameter { name = name_; _ } -> (
            match local_type frame name_.id with
            | Some ty ->
                let term = arrive context frame ("parameter." ^ name_.text) ty in
                (match term with
                | L.Symbol symbol -> context.values <- (symbol, name_.text) :: context.values
                | _ -> ());
                { frame with locals = Ids.add name_.id term frame.locals }
            | None -> unsupported parameter.span "a parameter without a type")
        | Self_parameter _ ->
            let self_type =
              match Query.demand database Interface.Environment.signature path with
              | Some { receiver = Some (_, ty); _ } -> ty
              | _ -> unsupported parameter.span "`self` without a type"
            in
            { frame with self = Some (arrive context frame "self" self_type) }
        | Parameter_error -> unsupported parameter.span "a parameter that did not parse")
      start signature.parameters
  in
  let start = { start with old_locals = start.locals; old_self = start.self } in
  let start =
    List.fold_left
      (fun frame (clause : clause) ->
        match clause.kind with
        | Requires value_ ->
            let frame, term = value context frame value_ in
            assume context frame term;
            frame
        | _ -> frame)
      start signature.clauses
  in
  let finished = block_value context start body in
  let returns =
    (match finished with Some (frame, term) -> [ (frame, Some term) ] | None -> [])
    @ List.rev context.returns
  in
  List.iter
    (fun ((frame : frame), returned) ->
      let frame = { frame with result = returned } in
      List.iter
        (fun (clause : clause) ->
          match clause.kind with
          | Ensures ensured ->
              let _, term = value context frame ensured in
              oblige context frame Ensures ensured.span
                (Printf.sprintf "`%s` may not hold when the function returns."
                   (quote source ensured.span))
                term
          | _ -> ())
        signature.clauses)
    returns;
  outcome context

let test database (source : source) ~path (body : block) =
  reject_checker_obligations source;
  let context = new_context database ~current:path ~terminates:false ~measures:[] source.checked in
  let start =
    {
      source;
      locals = Ids.empty;
      old_locals = Ids.empty;
      self = None;
      old_self = None;
      result = None;
      condition = L.Boolean true;
      checking = true;
      bound = [];
      loop = None;
      substitution = [];
    }
  in
  ignore (block_value context start body);
  outcome context

let theorem database source ~path ~parameters ~clauses body =
  function_ ~proof:true database source ~path
    {
      name = Plain_name { text = ""; span = Span.make 0 0; id = -1 };
      generics = [];
      parameters;
      result = None;
      clauses;
    }
    body
