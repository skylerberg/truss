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

(* Something the prover cannot read in another definition's tree, such as
   a callee's contract, whose span means nothing in this one. The nearest
   expression of the definition being proven reports it, with its own
   span. *)
exception Foreign_unsupported of string

let unsupported span format =
  Printf.ksprintf (fun message -> raise (Unsupported (span, message))) format

(* A clause that running compiled code can decide: one of a tag's
   [from_template]'s, by its position, for a template of these literal
   texts. See PROVER.md, "Running code while proving". *)
type evaluation = { from_template : Path.t; texts : string list; clause : int }

(* A call whose arguments are all known, of a function that is compiled and
   not generic: its term in the logic, which running it can give a value.
   A [Bool] is 0 or 1, in its arguments and its result. *)
type known_call = { function_ : Path.t; arguments : Z.t list; term : L.term; result_is_bool : bool }

type obligation = {
  code : Code.prover;
  span : span;  (** Relative to the definition being proven. *)
  message : string;
  query : L.query;
  values : (string * string) list;  (** Each prover symbol a counterexample shows, with its name. *)
  constants : Costs.constants list;
      (** The constants of each [O(...)] bound the query mentions, which each try pins. *)
  evaluation : evaluation option;  (** Running code that decides it, where there is any. *)
  known_calls : known_call list;  (** The calls its query mentions that running code can give. *)
}

type outcome = {
  obligations : obligation list;  (** In the order made. *)
  holes : (Names.key * span) list;
      (** Each [todo] in a proof, in the definition whose tree it is in. *)
}

(* A definition whose tables are being read: the one proven, or a callee
   whose clauses are translated at a call. *)
type source = { key : Names.key; checked : C.t; resolved : Resolve.resolved; text : string }
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
  costs : (cost * span) list;  (** Its cost clauses, but [cost time finite]. *)
}

type contract = {
  parts : part list;  (** The callee's own first. *)
  pure : bool;  (** Pure and terminating, so a function in the logic. *)
  result_kind : [ `Returns | `Lends | `Yields ];
  definition : (part * block) option;  (** A functional body, which is the callee's definition. *)
}

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
  self_type : T.ty option;  (** The type of [self], whose fields an invariant names directly. *)
  yielded : L.term option;
      (** What [yielded] names here: the parts a lending or yielding callee handed out, or the
          values a [for] loop's earlier iterations received. *)
  finished : L.term option;  (** What [finished] names here. *)
  handed_out : L.term option;
      (** In a lending or yielding method's own body, the parts it has handed out so far. *)
  spent : (string * L.term) list;
      (** Each counter's value here, by its key: what the code proven has spent since it began. *)
}

(* What a loop's body may change. *)
type changed = { changed_locals : C.local list; changes_self : bool }

(* How a loop bounds a counter: by its [cost] clause about it, or by its
   iterations times a bound on one, and, where the values it changes hold
   potential, also with that potential, from what it held on entry. *)
type loop_rule =
  | Clause_bound of loop_clause * cost * Costs.constants option
  | Per_iteration of { per : L.term; per_held : (L.term * L.term) option }

type loop_cost = {
  counter : Costs.counter;
  key : string;
  entry : L.term;  (** The counter on entry to the loop. *)
  rule : loop_rule;
  held : (frame -> L.term) option;  (** The potential of what the loop changes. *)
}

(* Which elements an index or a range reaches: one, or the run from a start
   to before a stop. *)
type place_value = One of L.term | Run of L.term * L.term

(* Where a cursor came from: a call to a yielding method, whose clauses
   each pull meets, read in [method_frame] with the call's arguments. *)
type cursor = { method_frame : frame; own : part; element : T.ty }

(* What one iteration of a loop that receives parts receives: whether
   there is another part, the part, the parts received through it, and how
   the loop's own state moves on, as a cursor does when pulled. *)
type received = { another : L.term; element : L.term; through : L.term; advance : frame -> frame }

type context = {
  database : Query.context;
  current : Path.t;
  mutable terminates : bool;
      (** Whether the code being proven must end: the definition's [time] clause, or, in a lambda,
          its function type's. *)
  mutable parameters : parameter list;  (** The definition's, for its callbacks' [requires]. *)
  measures : expression list;  (** Its [decreases], for its recursive calls. *)
  mutable declarations : L.declaration list;
  declared : (string, unit) Hashtbl.t;
  mutable facts : L.term list;  (** Reversed. *)
  mutable obligations : obligation list;  (** Reversed. *)
  mutable fresh : int;
  mutable values : (string * string) list;  (** For counterexamples. *)
  mutable returns : (frame * L.term option) list;
  mutable instantiating : Path.t list;  (** Contracts being assumed, to stop at recursion. *)
  fits : (int * T.ty) list;  (** The type checker's [Integer_fits] obligations, by expression. *)
  disjoint : (int * int) list;
      (** The ownership check's pairs of indexes, by expression, that must differ. *)
  mutable indexes : (int * (place_value * span)) list;
      (** The value of each such index or range, once read. *)
  mutable output : T.ty option;  (** What the function proven returns, for [?]. *)
  mutable hands_out : (T.ty * [ `Lends | `Yields ]) option;
      (** In a lending or yielding method's body, the type of the parts it hands out. *)
  mutable handing : (expression list * expression list) option;
      (** Its [ensures]: the clauses for each [yield], which mention [result], and the others. *)
  graph : Call_graph.t;  (** The package's call graph, for recursion in cycles. *)
  home : Names.key;  (** The definition being proven, whose tree spans and obligations are in. *)
  mutable laws_assumed : string list;  (** Each trait and type whose laws are facts already. *)
  mutable counters : Costs.counter list;  (** What the code proven counts, for its cost clauses. *)
  mutable own_constants : (string * Costs.constants) list;
      (** By counter, the constants of the definition's own [O(...)] bounds, which a call back into
          it assumes. *)
  mutable groups : Costs.constants list;  (** Every bound's constants, made so far. *)
  fresh_order : (string, int) Hashtbl.t;
      (** Each fresh symbol's number, to tell what a loop made. *)
  mutable logs : (L.term * bool) list;  (** Each term [log] is applied to, and whether halved. *)
  mutable powers : (L.term * L.term) list;  (** Each base and exponent [power] is applied to. *)
  mutable lambda_times : (L.term * (L.term * obligation list)) list;
      (** A lambda's bound on the time of one call, and the obligations that show it, made only once
          the bound is used. *)
  mutable lambda_captures : (L.term * C.local list) list;  (** What each lambda captures. *)
  mutable potentials : L.term list;  (** Each value's potential whose definition is a fact. *)
  mutable equalities : L.term list;  (** Each derived [==] whose definition is a fact. *)
  mutable known_calls : known_call list;  (** Each call running code can give a value. *)
  mutable cursors : (L.term * cursor) list;  (** Where each cursor value came from. *)
  mutable proving : bool;
      (** In a theorem, a [proof] block, or a law's proof, where a [todo] is a hole. *)
  mutable holes : (Names.key * span) list;  (** Reversed. *)
  mutable call_targets : (L.term * C.local) list;
      (** Each function-typed parameter a [calls] clause counts, with its local. *)
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
  Hashtbl.replace context.fresh_order name context.fresh;
  L.Symbol name

(* Whether a term mentions a fresh symbol made after [mark]: a value a
   loop changes, or one made inside it. *)
let made_since context mark term =
  let rec walk = function
    | L.Symbol name -> (
        match Hashtbl.find_opt context.fresh_order name with Some n -> n > mark | None -> false)
    | L.Integer _ | L.Boolean _ | L.Bits _ -> false
    | L.Apply (_, arguments) -> List.exists walk arguments
    | L.Forall (_, body) | L.Exists (_, body) -> walk body
  in
  walk term

(* A fact of mathematics, true on every path. *)
let fact context frame term =
  if not (L.mentions frame.bound term) then context.facts <- term :: context.facts

(* A fact is guarded by its path's condition. Inside a quantifier, either
   may mention a bound variable, and such a fact has no place outside the
   quantifier, so it is left out, which is always sound. *)
let assume context frame fact =
  if not (L.mentions frame.bound fact || L.mentions frame.bound frame.condition) then
    match fact with
    | L.Boolean true -> ()
    | _ -> context.facts <- L.( ==> ) frame.condition fact :: context.facts

(* An obligation is shown by its own query, and is a fact for what comes
   after it. Inside a quantifier there is no path to state it on, so it is
   left to the definition of the quantifier's body, which this stage does
   not check yet. *)
let rec oblige ?evaluation context frame code span message goal =
  if frame.checking && not (L.mentions frame.bound goal || L.mentions frame.bound frame.condition)
  then begin
    context.obligations <-
      make_obligation ?evaluation context frame code span message goal :: context.obligations;
    assume context frame goal
  end

(* An obligation made but not yet added, for one that is needed only if
   what it shows is used. *)
and obligation_at context frame code span message goal =
  if frame.checking && not (L.mentions frame.bound goal || L.mentions frame.bound frame.condition)
  then Some (make_obligation context frame code span message goal)
  else None

and make_obligation ?evaluation context frame code span message goal =
  let query =
    L.prune
      {
        declarations = List.rev context.declarations;
        facts = List.rev context.facts;
        goal = L.( ==> ) frame.condition goal;
      }
  in
  let constants =
    List.filter
      (fun (group : Costs.constants) ->
        let names = [ group.factor; group.addend ] in
        L.mentions names query.goal || List.exists (L.mentions names) query.facts)
      context.groups
  in
  let known_calls =
    List.filter
      (fun (known : known_call) ->
        let mentioned term = occurs known.term term in
        mentioned query.goal || List.exists mentioned query.facts)
      context.known_calls
  in
  { code; span; message; query; values = context.values; constants; evaluation; known_calls }

(* Whether a term holds another. *)
and occurs part term =
  term = part
  ||
  match term with
  | L.Apply (_, arguments) -> List.exists (occurs part) arguments
  | L.Forall (_, body) | L.Exists (_, body) -> occurs part body
  | L.Symbol _ | L.Integer _ | L.Boolean _ | L.Bits _ -> false

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

(* A float type's widths in the solver's floating-point theory: its
   exponent's, and its significand's, with the hidden bit. *)
let float_format (ty : T.ty) =
  match builtin ty with Some Float32 -> Some (8, 24) | Some Float64 -> Some (11, 53) | _ -> None

(* A float literal, bit for bit. *)
let float_literal (exponent, significand) value =
  let bits =
    if exponent = 8 then Z.extract (Z.of_int32 (Int32.bits_of_float value)) 0 32
    else Z.extract (Z.of_int64 (Int64.bits_of_float value)) 0 64
  in
  let fraction = significand - 1 in
  L.Apply
    ( "fp",
      [
        L.Bits (1, Z.extract bits (exponent + fraction) 1);
        L.Bits (exponent, Z.extract bits fraction exponent);
        L.Bits (fraction, Z.extract bits 0 fraction);
      ] )

(* IEEE 754 arithmetic, rounding to nearest with ties to even, and the
   lawful [==] and ordering DESIGN.md gives floats: every NaN is equal to
   every other and ordered after every number, and otherwise IEEE's, so
   [-0.0 == 0.0]. See DESIGN.md, "Equality, ordering, and deriving". *)
let float_operation name left right = L.Apply (name, [ L.Apply ("RNE", []); left; right ])
let is_nan value = L.Apply ("fp.isNaN", [ value ])
let float_equal left right = L.(Apply ("fp.eq", [ left; right ]) ||| (is_nan left &&& is_nan right))

let float_less left right =
  L.(not_ (is_nan left) &&& is_nan right ||| Apply ("fp.lt", [ left; right ]))

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
  else
    match (ty, float_format ty) with
    | _, Some (exponent, significand) -> Float (exponent, significand)
    | Function function_type, _ ->
        (* One sort for each number of inputs, whatever the clauses, so a
           value keeps its sort where a function type is widened. *)
        Uninterpreted (Printf.sprintf "function/%d" (List.length function_type.inputs))
    | _ -> begin
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
      (* A counter where paths join is what the path taken spent: a fresh
         symbol defined as a choice between them, which a loop's bound on
         one iteration can see through. *)
      let spent =
        List.map
          (fun (key, term) ->
            let values =
              List.map
                (fun ((frame : frame), _) ->
                  ( frame.condition,
                    match List.assoc_opt key frame.spent with Some t -> t | None -> term ))
                frames
            in
            match values with
            | (_, first_value) :: rest when List.for_all (fun (_, v) -> v = first_value) rest ->
                (key, first_value)
            | _ ->
                let choice =
                  match List.rev values with
                  | (_, last) :: earlier ->
                      List.fold_left
                        (fun otherwise (condition, value) -> L.ite condition value otherwise)
                        last earlier
                  | [] -> term
                in
                if L.mentions first.bound choice then (key, choice)
                else
                  let symbol = fresh context "spent" L.Int in
                  context.facts <- L.equal symbol choice :: context.facts;
                  (key, symbol))
          first.spent
      in
      let value =
        match value_type with
        | Some ty -> define "value" (sort_of context ty) (fun _ value -> value)
        | None -> None
      in
      (* [self] and what a lending or yielding method has handed out change
         along paths too, like locals. *)
      let self =
        match first.self_type with
        | Some ty -> (
            match define "self" (sort_of context ty) (fun frame _ -> frame.self) with
            | Some joined -> Some joined
            | None -> first.self)
        | None -> first.self
      in
      let handed_out =
        match context.hands_out with
        | Some (part, _) -> (
            match
              define "parts"
                (sort_of context
                   (T.Named
                      {
                        path =
                          Top
                            {
                              module_ = { package = "standard"; modules = [ "specification" ] };
                              name = "Sequence";
                            };
                        arguments = [ T.Type part ];
                      }))
                (fun frame _ -> frame.handed_out)
            with
            | Some joined -> Some joined
            | None -> first.handed_out)
        | None -> first.handed_out
      in
      Some ({ merged with locals; spent; self; handed_out }, value)

let join_frames context frames =
  Option.map fst (join context (List.map (fun frame -> (frame, None)) frames))

(* Calls: what a callee promises *)

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
    costs =
      List.filter_map
        (fun (clause : clause) ->
          match clause.kind with
          | Cost { resource = Time; bound = Finite; _ } -> None
          | Cost cost -> Some (cost, clause.span)
          | _ -> None)
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
        (* A function of its arguments: it may take them [own], but
           changes none of the caller's. *)
        signature.uses = []
        && signature.terminates
        && List.for_all (fun (info : T.parameter_info) -> info.mode <> T.Mut) signature.parameters
        && match signature.receiver with Some (Mut, _) -> false | _ -> true)
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

(* A capability's method's clauses, from the capability's definition. *)
let capability_part database (capability : Path.t) name =
  match Interface.Summary.definition database capability with
  | Some (key, { kind = Capability { members; _ }; _ }) -> (
      match callee_source database key with
      | Some callee ->
          List.find_map
            (fun (member : capability_member line) ->
              match member.kind with
              | Capability_method signature when name_of signature = name ->
                  Some (part_of callee signature.parameters signature.clauses, signature)
              | _ -> None)
            members
      | None -> None)
  | _ -> None

(* A capability's method's contract. Its calls are never a function in the
   logic: two calls may give different results, since the prover never
   models an implementation's state. See PROVER.md, "Values are values". *)
let capability_contract database (capability : Path.t) name =
  Option.map
    (fun (part, (signature : signature)) ->
      {
        (make_contract database
           (Path.Method { owner = capability; name; receiver = Static })
           ~own:part ~others:[] ~result:signature.result ~body:None)
        with
        pure = false;
      })
    (capability_part database capability name)

(* A trait method's body, when it provides one. *)
let provided_body database (trait : Path.t) name receiver =
  match Interface.Summary.definition database trait with
  | Some (_, { kind = Trait { members; _ }; _ }) ->
      List.find_map
        (fun (member : trait_member line) ->
          match member.kind with
          | Trait_method { signature; body = Some body }
            when name_of signature = name && receiver_of signature.parameters = receiver ->
              Some body
          | _ -> None)
        members
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

let distinct_counters counters =
  List.fold_left
    (fun found counter ->
      if List.exists (fun other -> Costs.key other = Costs.key counter) found then found
      else found @ [ counter ])
    [] counters

let resource_of (cost : cost) ~target_of : Costs.resource option =
  match cost.resource with
  | Time -> Some Time
  | Allocations -> Some Allocations
  | Allocated_bytes -> Some Allocated_bytes
  | Calls written -> Option.map (fun target -> Costs.Calls target) (target_of written)

(* Expressions *)

let literal_value frame (expression : expression) =
  match frame.source.checked.literals.(expression.id) with
  | Some (Integer_value value) -> Some (L.Integer value)
  | Some (Float_value value) -> (
      match Option.bind frame.source.checked.types.(expression.id) float_format with
      | Some format -> Some (float_literal format value)
      | None -> unsupported expression.span "a float literal without a float type")
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
  let home = frame.source.key = context.home in
  let result =
    if home then
      try expression_kind context frame written
      with Foreign_unsupported message -> raise (Unsupported (written.span, message))
    else
      try expression_kind context frame written
      with Unsupported (_, message) ->
        raise
          (Foreign_unsupported
             (Printf.sprintf "%s, in `%s`" message (Names.show_key frame.source.key)))
  in
  (match (result, if home then List.assoc_opt written.id context.fits else None) with
  | Some (after, value), Some ty ->
      oblige context after Fits written.span
        (Printf.sprintf "`%s` may not fit in `%s`." (quote frame.source written.span) (T.show ty))
        (in_range ty value)
  | _ -> ());
  (match result with
  | Some (after, value) when home -> disjoint_index context after written value
  | _ -> ());
  result

(* Two indexes of one collection that are lent together, or used by two
   branches of [parallel], must differ, which the ownership check left to
   the prover. Each is read as it is evaluated, and the pair is shown once
   both are. *)
and disjoint_index context frame (written : expression) value =
  note_place context frame written (One value)

(* An index or a range read, which the ownership check may have paired
   with another: the two must reach different elements. *)
and note_place context frame (written : expression) place =
  if List.exists (fun (first, second) -> first = written.id || second = written.id) context.disjoint
  then begin
    context.indexes <- (written.id, (place, written.span)) :: context.indexes;
    let outside index start stop =
      L.(Apply ("<", [ index; start ]) ||| Apply ("<=", [ stop; index ]))
    in
    List.iter
      (fun (first, second) ->
        if first = written.id || second = written.id then
          match (List.assoc_opt first context.indexes, List.assoc_opt second context.indexes) with
          | Some (a, first_span), Some (b, second_span) ->
              let apart =
                match (a, b) with
                | One a, One b -> L.not_ (L.equal a b)
                | One index, Run (start, stop) | Run (start, stop), One index ->
                    outside index start stop
                | Run (start, stop), Run (other_start, other_stop) ->
                    L.disjunction
                      [
                        L.Apply ("<=", [ stop; other_start ]);
                        L.Apply ("<=", [ other_stop; start ]);
                        L.Apply ("<=", [ stop; start ]);
                        L.Apply ("<=", [ other_stop; other_start ]);
                      ]
              in
              oblige context frame Disjoint written.span
                (Printf.sprintf
                   "`%s` and `%s` may reach the same elements, which are used together."
                   (quote frame.source first_span) (quote frame.source second_span))
                apart
          | _ -> ())
      context.disjoint
  end

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
      let negated =
        if float_format ty <> None then L.Apply ("fp.neg", [ inner_value ])
        else L.Apply ("-", [ inner_value ])
      in
      if float_format ty <> None then ()
      else if bounds ty <> None then
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
  | Todo when context.proving ->
      (* A hole in a proof: what follows it on this path is not shown, and
         a build refuses what can reach it. See PROVER.md, "Holes". *)
      context.holes <- (source.key, written.span) :: context.holes;
      Some
        ( { frame with condition = L.Boolean false },
          arrive context frame "todo" (type_of frame written) )
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
  | Bracket (base, [ Item ({ kind = Range _; _ } as range) ])
    when source.checked.calls.(written.id) = None ->
      Some (slice context frame written base range)
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
  | Lambda { parameters; body } ->
      Some (lambda context frame written parameters body ~facts:(fun _ -> []))
  | List items -> Some (list_literal context frame written items)
  | Map entries -> Some (map_literal context frame written entries)
  | String literal -> Some (string_literal context frame written literal)
  | Float _ -> (
      match literal_value frame written with
      | Some term -> Some (frame, term)
      | None -> unsupported written.span "a float literal without a value")
  | Range _ -> unsupported written.span "a range outside a `for` loop or a quantifier"
  | Any inner ->
      (* A value of [any Trait], known through the trait's contracts: one
         allocation, of the block that holds the value. *)
      let frame, _ = value context frame inner in
      let frame =
        spend context frame (fun (counter : Costs.counter) ->
            match (counter.resource, counter.counting) with
            | Allocations, _ -> L.int 1
            | Allocated_bytes, Units -> L.int 1
            | Allocated_bytes, (At_most | Exactly) -> unknown_amount context frame counter
            | (Time | Calls _), _ -> Costs.zero)
      in
      Some (frame, arrive context frame "any" (type_of frame written))
  | Provide { implementations; body } ->
      (* The body runs with the implementations, which the prover never
         models, so a capability call in it gives a fresh value by its
         contract. Each one handed over [mut] holds a fresh value of its
         type afterward, which meets its type's invariants. *)
      let frame =
        List.fold_left
          (fun frame (implementation : expression) -> fst (value context frame implementation))
          frame implementations
      in
      Option.map
        (fun ((after : frame), result) ->
          let after =
            List.fold_left
              (fun after (implementation : expression) ->
                match implementation.kind with
                | Mode (Mut, place) ->
                    let after = havoc_root context after place in
                    let (root : expression) = root_of place in
                    (match (root.kind, place_local after root) with
                    | Self_value, _ -> (
                        match (after.self, after.self_type) with
                        | Some self, Some ty -> assume_valid context after ty self
                        | _ -> ())
                    | _, Some (id, ty) -> (
                        match Ids.find_opt id after.locals with
                        | Some term -> assume_valid context after ty term
                        | None -> ())
                    | _ -> ());
                    after
                | _ -> after)
              after implementations
          in
          (after, result))
        (block_value context frame body)
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
  | Some Yielded -> (
      (* What the nearest loop or method hands out: a loop's own parts, or
         else, in a lending or yielding method's body, the method's. *)
      match (frame.yielded, frame.handed_out) with
      | Some yielded, _ -> Some (frame, yielded)
      | None, Some handed_out when source.key = context.home -> Some (frame, handed_out)
      | _ -> unsupported written.span "`yielded` here")
  | Some Finished -> (
      match frame.finished with
      | Some finished -> Some (frame, finished)
      | None -> unsupported written.span "`finished` here")
  | _ -> (
      match source.checked.meanings.(written.id) with
      | Some (Local_value id) -> (
          match Ids.find_opt id frame.locals with
          | Some term -> Some (frame, term)
          | None -> unsupported written.span "a local the prover did not bind")
      | _ when match source.resolved.names.(path.last.id) with Some (Field _) -> true | _ -> false
        -> (
          (* A record's field, named directly in its type's invariant. *)
          match (source.resolved.names.(path.last.id), frame.self, frame.self_type) with
          | Some (Field field), Some self, Some self_type ->
              let field_type =
                match declared_fields context self_type None with
                | Some fields -> (
                    match List.assoc_opt field fields with Some ty -> ty | None -> T.Error)
                | None -> T.Error
              in
              Some (frame, field_of context frame self_type None field field_type self)
          | _ -> unsupported written.span "a field outside its type's invariant")
      | Some (Generic_value parameter) ->
          let symbol = Printf.sprintf "generic.%s.%s" (Path.show parameter.owner) parameter.name in
          declare context (L.Constant (symbol, Int));
          Some (frame, L.Symbol symbol)
      | Some (Global { path = global; type_arguments }) ->
          Some (frame, global_value context frame written global type_arguments)
      | Some (Variant_value { type_; variant }) ->
          let type_ = substituted frame type_ in
          let type_ = substituted frame type_ in
          Some (frame, variant_value context written type_ variant)
      | _ -> unsupported written.span "this name")

(* [a == b] on a type: the solver's equality where it is structural, the
   lawful equality of floats, and otherwise the type's [Equal] as a
   function of the two, which a derived [Equal] defines field by field
   with each field's own [==], unfolded once for each two it compares.
   See PROVER.md, "Equality". *)
and equal_of context frame (ty : T.ty) a b =
  if structural context ty then L.equal a b
  else if float_format ty <> None then float_equal a b
  else
    let sort = sort_of context ty in
    let symbol = "equal." ^ type_key ty in
    declare context (L.Function (symbol, [ sort; sort ], L.Bool));
    let equal = L.Apply (symbol, [ a; b ]) in
    (match (visible_type context ty, constructors context ty) with
    | Some (interface, _), Some shape
      when List.exists is_standard_equal interface.derives
           && (not (List.mem equal context.equalities))
           && not (L.mentions frame.bound equal) ->
        context.equalities <- equal :: context.equalities;
        let fields_equal (variant, fields) =
          L.conjunction
            (List.map
               (fun (field, field_type) ->
                 let selector = selector_name ty variant field in
                 let a = L.Apply (selector, [ a ]) and b = L.Apply (selector, [ b ]) in
                 if structural context field_type then L.equal a b
                 else if float_format field_type <> None then float_equal a b
                 else
                   (* Unfolded only when it is compared itself. *)
                   let symbol = "equal." ^ type_key field_type in
                   declare context
                     (L.Function
                        (symbol, [ sort_of context field_type; sort_of context field_type ], L.Bool));
                   L.Apply (symbol, [ a; b ]))
               fields)
        in
        let defined =
          match shape with
          | [ ((None, _) as record) ] -> fields_equal record
          | variants ->
              L.disjunction
                (List.map
                   (fun ((variant, _) as one) ->
                     let is_variant term =
                       L.Apply (L.tester (constructor_name ty variant), [ term ])
                     in
                     L.(is_variant a &&& is_variant b &&& fields_equal one))
                   variants)
        in
        fact context frame (L.equal equal defined)
    | _ -> ());
    equal

(* An operator on two floats, as IEEE 754 and DESIGN.md's lawful [==] and
   ordering give it. A remainder, which IEEE defines differently from
   Truss, is known only by its type. *)
and float_binary context frame (written : expression) operator left right =
  let frame, a = value context frame left in
  let frame, b = value context frame right in
  let result =
    match operator with
    | Equal -> float_equal a b
    | Not_equal -> L.not_ (float_equal a b)
    | Less -> float_less a b
    | Less_equal -> L.( ||| ) (float_less a b) (float_equal a b)
    | Greater -> float_less b a
    | Greater_equal -> L.( ||| ) (float_less b a) (float_equal a b)
    | Add -> float_operation "fp.add" a b
    | Subtract -> float_operation "fp.sub" a b
    | Multiply -> float_operation "fp.mul" a b
    | Divide -> float_operation "fp.div" a b
    | _ -> arrive context frame "operator" (type_of frame written)
  in
  Some (frame, result)

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
  if float_format operand_type <> None && float_format (type_of frame right) <> None then
    float_binary context frame written operator left right
  else
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
    else if not primitive then
      (* An operator on another type is a call of its trait's method:
       [compare] for an ordering, whose result is tested, [equal] for
       [==], and the arithmetic traits' methods. *)
      begin match (operator, source.checked.calls.(written.id)) with
      | (Equal | Not_equal | Less | Less_equal | Greater | Greater_equal), Some call_ ->
          (* [==] and the orderings are functions of their operands in the
           logic, whatever the [impl]: [Equal] and [Ordered] use no
           capabilities, so a call that returns always gives the same
           answer, which is what their laws state. *)
          let frame, left_value = value context frame left in
          let frame, right_value = value context frame right in
          if operator = Equal || operator = Not_equal then begin
            let equal = equal_of context frame operand_type left_value right_value in
            Some (frame, if operator = Equal then equal else L.not_ equal)
          end
          else begin
            let sort = sort_of context operand_type in
            let ordering = substituted frame call_.result in
            ignore (sort_of context ordering);
            let symbol = "compare." ^ type_key operand_type in
            declare context (L.Function (symbol, [ sort; sort ], sort_of context ordering));
            let compared = L.Apply (symbol, [ left_value; right_value ]) in
            let is variant =
              L.Apply (L.tester (constructor_name ordering (Some variant)), [ compared ])
            in
            if constructors context ordering = None then
              Some (frame, arrive context frame "operator" result_type)
            else
              Some
                ( frame,
                  match operator with
                  | Less -> is "Less"
                  | Less_equal -> L.not_ (is "Greater")
                  | Greater -> is "Greater"
                  | _ -> L.not_ (is "Less") )
          end
      | _, None ->
          let frame, _ = value context frame left in
          let frame, _ = value context frame right in
          Some (frame, arrive context frame "operator" result_type)
      | _, Some call_ ->
          (* Arithmetic on another type: its trait's method, by its contract. *)
          resolved_call context frame written call_
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
  let make ?count bound_symbol sort premise body_frame =
    let mark = context.fresh in
    let after, body_value = value context { body_frame with checking = false } body in
    let bound = [ (bound_symbol, sort) ] in
    (* In code, a quantifier over a range runs its body once for each value
       in it, which costs that many times what the body spends, when that
       is the same for every value. *)
    let frame =
      match count with
      | Some count when frame.checking ->
          spend context frame (fun counter ->
              let key = Costs.key counter in
              let spent =
                match (List.assoc_opt key body_frame.spent, List.assoc_opt key after.spent) with
                | Some start, Some total -> Costs.since ~start total
                | _ -> Costs.zero
              in
              if made_since context mark spent || L.mentions [ bound_symbol ] spent then
                unknown_amount context frame counter
              else
                match counter.counting with
                | Units ->
                    Costs.plus
                      (Costs.times (Costs.at_least_zero count) (Costs.plus spent (L.int 1)))
                      (L.int 1)
                | At_most | Exactly ->
                    if spent = Costs.zero then Costs.zero else unknown_amount context frame counter)
      | _ -> frame
    in
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
      (* Over every value of a type: each in its range, and meeting its
         type's invariants. *)
      match local_type frame name_.id with
      | Some ty ->
          let inner, ty = with_bound name_.id ty in
          let each = L.Symbol symbol in
          make symbol (sort_of context ty)
            (L.( &&& ) (in_range ty each) (validity context inner ~assuming:true ty each))
            inner
      | None -> unsupported written.span "a quantifier over a value without a type")
  | Binder_in
      ( ({ kind = Binding_or_constant _ | Wildcard; _ } as binding),
        { kind = Range { start = Some start; stop = Some stop; inclusive; _ }; _ } ) ->
      let _, low = value context frame start in
      let _, high = value context frame stop in
      let inner =
        match binding.kind with
        | Binding_or_constant name_ ->
            let ty = match local_type frame name_.id with Some ty -> ty | None -> T.Integer in
            fst (with_bound name_.id ty)
        | _ -> { frame with bound = symbol :: frame.bound }
      in
      let bound = L.Symbol symbol in
      let premise =
        L.(
          Apply ("<=", [ low; bound ]) &&& Apply ((if inclusive then "<=" else "<"), [ bound; high ]))
      in
      let count =
        if inclusive then Costs.plus (Costs.minus high low) (L.int 1) else Costs.minus high low
      in
      make ~count symbol Int premise inner
  | Binder_in (binding, collection) -> (
      (* Over a collection's elements: by index into its sequence, or each
         value its set contains, each matched against the binding's pattern,
         which names its parts and leaves out what it does not match. *)
      let collection_type = type_of frame collection in
      let _, collected = value context frame collection in
      let element =
        match Option.map (substituted frame) frame.source.checked.pattern_types.(binding.id) with
        | Some ty -> ty
        | None -> unsupported written.span "a quantifier over a value without a type"
      in
      let set_path : Path.t =
        Top { module_ = { package = "standard"; modules = [ "set" ] }; name = "Set" }
      in
      let bound_to term =
        let matched, inner =
          pattern_match context { frame with bound = symbol :: frame.bound } binding term element
        in
        (matched, inner)
      in
      match collection_type with
      | Named { path; _ } when Path.equal path set_path || Path.equal path finite_set_path ->
          let finite = T.Named { path = finite_set_path; arguments = [ T.Type element ] } in
          let model =
            if Path.equal path finite_set_path then Some collected
            else model_as context collection_type collected ~model:finite
          in
          let model =
            match model with
            | Some model -> model
            | None -> unsupported collection.span "a quantifier over `%s`" (T.show collection_type)
          in
          let each = L.Symbol symbol in
          let matched, inner = bound_to each in
          make symbol (sort_of context element)
            (L.( &&& )
               (finite_function context finite "contains" L.Bool
                  [ (each, sort_of context element) ]
                  model)
               matched)
            inner
      | _ -> (
          let sequence =
            match collection_type with
            | Named { path; _ } when Path.equal path sequence_path -> Some collected
            | _ -> model_of context collection_type collected ~element
          in
          match sequence with
          | Some sequence -> (
              let index = L.Symbol symbol in
              match sequence_at context element sequence index with
              | Some at ->
                  let length = sequence_length context element sequence in
                  let matched, inner = bound_to at in
                  make ~count:length symbol Int
                    L.(
                      Apply ("<=", [ int 0; index ]) &&& Apply ("<", [ index; length ]) &&& matched)
                    inner
              | None ->
                  unsupported collection.span "a quantifier over `%s`" (T.show collection_type))
          | None -> unsupported collection.span "a quantifier over `%s`" (T.show collection_type)))

(* Calls *)

and call context frame (written : expression) callee_expression arguments =
  let source = frame.source in
  match callee_expression.kind with
  | Name path when source.resolved.names.(path.last.id) = Some Identical -> (
      (* Identity, for every type: the solver's equality. *)
      match arguments with
      | [ { value = first; _ }; { value = second; _ } ] ->
          let frame, first_value = value context frame first in
          let frame, second_value = value context frame second in
          extensional context frame (type_of frame first) first_value second_value;
          Some (frame, L.equal first_value second_value)
      | _ -> unsupported written.span "`identical` with other than two arguments")
  | Name path
    when match source.resolved.names.(path.last.id) with
         | Some (Cost_function _) -> true
         | _ -> false -> (
      match source.resolved.names.(path.last.id) with
      | Some (Cost_function kind) -> cost_function context frame written kind arguments
      | _ -> None)
  | Name path when source.resolved.names.(path.last.id) = Some Old -> (
      match arguments with
      | [ { value = inner; _ } ] ->
          let entry = { frame with locals = frame.old_locals; self = frame.old_self } in
          let _, term = value context entry inner in
          Some (frame, term)
      | _ -> unsupported written.span "`old` with other than one argument")
  | _ -> (
      match source.checked.calls.(written.id) with
      | None ->
          unsupported written.span "a call the type checker did not resolve, `%s`"
            (quote source written.span)
      | Some call_ -> resolved_call context frame written call_)

and resolved_call ?lent_final context frame (written : expression) (call_ : C.call) =
  let source = frame.source in
  (* Arguments run in the order written, except lambdas, which are proven
     last, as the type checker checks them, so that what the callee
     promises to pass them can mention the other arguments. *)
  let is_lambda (argument : C.argument) =
    let (argument_expression : expression) = find_expression written argument.expression in
    match argument_expression.kind with Lambda _ -> true | _ -> false
  in
  let frame, evaluated =
    List.fold_left
      (fun (frame, values) (argument : C.argument) ->
        if is_lambda argument then (frame, values)
        else
          let expression_ = find_expression written argument.expression in
          let frame, term = value context frame expression_ in
          let term =
            match argument.conversion with
            | Some Owned_to_view -> view_of context frame (type_of frame expression_) term
            | _ -> term
          in
          (frame, (argument.parameter, term) :: values))
      (frame, []) call_.arguments
  in
  let values =
    List.map
      (fun (argument : C.argument) ->
        let (expression_ : expression) = find_expression written argument.expression in
        match (List.assoc_opt argument.parameter evaluated, expression_.kind) with
        | Some term, _ -> (argument, expression_, term)
        | None, Lambda { parameters; body } ->
            let facts = callback_facts context frame call_ argument.parameter evaluated in
            (argument, expression_, lambda context frame expression_ parameters body ~facts |> snd)
        | None, _ -> unsupported expression_.span "an argument")
      call_.arguments
  in
  List.iter
    (fun ((argument : C.argument), (expression_ : expression), _) ->
      match named_function_of context frame expression_ with
      | Some (path, contract) ->
          check_named_callback context frame call_ argument expression_ path contract evaluated
      | None -> ())
    values;
  let result_type = substituted frame call_.result in
  (match call_.callee with
  | Constructor _ | Built_in_operator | Intrinsic _ -> ()
  | _ ->
      let exempt = updating_helper context call_ in
      List.iter
        (fun ((argument : C.argument), (expression_ : expression), term) ->
          if not (exempt && argument.parameter = 0) then
            check_valid context frame expression_.span
              (argument_type frame argument expression_)
              term ~deep:true ~when_:"when it is passed to this call")
        values);
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
    | Some contract ->
        (* A yielding method called outside a [for] loop makes a cursor. *)
        Some
          (contract_call ~lent_final context frame written call_ path contract values ~havoc_mut
             ~substitution_of ~instance)
    | None ->
        let frame = havoc_mut frame in
        let frame = spend context frame (step_amount context frame call_ values) in
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
  | Trait_method { trait; name = "next"; self_type = T.Cursor _ as cursor_type; _ }
    when Path.equal trait.trait cursor_trait
         && List.assoc_opt (argument_at_index values 0) context.cursors <> None ->
      (* A pull of a cursor whose method the prover knows. *)
      let cursor = argument_at_index values 0 in
      let made = List.assoc cursor context.cursors in
      let pulled, later =
        pull context frame made cursor ~cursor_type:(substituted frame cursor_type)
      in
      let receiver =
        List.find_map
          (fun ((argument : C.argument), (expression_ : expression), _) ->
            if argument.parameter = 0 then Some expression_ else None)
          values
      in
      let frame =
        match receiver with Some place -> store context frame place later | None -> frame
      in
      Some (spend context frame one_step, pulled)
  | Trait_method { trait; name; receiver; evidence; self_type; type_arguments } ->
      let arguments = arguments_of type_arguments in
      let self_type = substituted frame self_type in
      (* A bound on [Self], read where [Self] is a known type, as in a law
         proven for one [impl], reaches that type's [impl]. *)
      let evidence =
        match evidence with
        | Bound _ -> (
            match concrete_impl context trait.trait self_type with
            | Some impl -> C.Impl { impl; arguments = [] }
            | None -> evidence)
        | _ -> evidence
      in
      assume_laws context frame trait.trait self_type;
      (match evidence with
      | (Bound _ | Dynamic) when name = "from_template" && Path.equal trait.trait template_trait ->
          oblige context frame Requires written.span
            "A call of `from_template` through a bound or `any` cannot see what the tag requires \
             of its template: build the value with a template, where the tag is known."
            (L.Boolean false)
      | _ -> ());
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
  | Constructor { variant; _ } ->
      let frame, built = construct context frame written call_ variant values in
      Some (spend context frame (step_amount context frame call_ values), built)
  | Function_value ->
      check_callback_requires context frame written values;
      let frame = havoc_mut frame in
      let frame =
        match written.kind with
        | Call (callee, _) when context.counters <> [] -> (
            let _, callee_term = value context frame callee in
            match type_of frame callee with
            | T.Function function_type ->
                spend context frame (function_value_amount context frame function_type callee_term)
            | _ -> spend context frame (unknown_amount context frame))
        | _ -> frame
      in
      Some (frame, arrive context frame "result" result_type)
  | Capability_method { capability; name } ->
      with_contract
        (Path.Method { owner = capability; name; receiver = Static })
        (capability_contract context.database capability name)
  | Intrinsic _ | Built_in_operator ->
      let frame = havoc_mut frame in
      ignore source;
      let frame = spend context frame (step_amount context frame call_ values) in
      Some (frame, arrive context frame "result" result_type)

(* Lambdas and callbacks *)

(* A lambda is proven where it is written, with fresh arguments of its
   function type and what the callee promises to pass it; it ends exactly
   when its function type has a [time] clause; and it is a value about
   which nothing more is known. *)
and lambda context frame (written : expression) (parameters : pattern list) body ~facts =
  let ty = type_of frame written in
  let function_type =
    match ty with
    | T.Function function_type -> function_type
    | _ -> unsupported written.span "a lambda"
  in
  if List.length parameters <> List.length function_type.inputs then
    unsupported written.span "a lambda with a different number of parameters";
  let inside = { frame with result = None; loop = None } in
  let arguments, inside =
    List.fold_left2
      (fun (arguments, inside) (pattern : pattern) (_, input) ->
        let input = substituted frame input in
        let argument = arrive context inside "argument" input in
        assume_valid context inside input argument;
        let _, inside = pattern_match context inside pattern argument input in
        (argument :: arguments, inside))
      ([], inside) parameters function_type.inputs
  in
  let arguments = List.rev arguments in
  List.iter (assume context inside) (facts arguments);
  (* A lambda counts on its own: what its type's cost clauses promise, and,
     where the code around it counts time, its time, to bound [time(f)]
     for it. *)
  let promised =
    List.filter_map
      (fun (cost : T.cost) ->
        let counting : Costs.counting option =
          match cost.bound with
          | Order_of -> Some Units
          | No_more_than (Some _) -> Some At_most
          | Exactly_cost (Some _) -> Some Exactly
          | Finite_cost | No_more_than None | Exactly_cost None -> None
        in
        let resource : Costs.resource option =
          match cost.resource with
          | "time" -> Some Time
          | "allocations" -> Some Allocations
          | "allocated_bytes" -> Some Allocated_bytes
          | _ -> None
        in
        match (resource, counting) with
        | Some resource, Some counting ->
            let counter = { Costs.resource; counting } in
            let constants =
              if counting = Units then begin
                let constants =
                  Costs.constants (Printf.sprintf "lambda.%d.%s" written.id (Costs.key counter))
                in
                context.groups <- constants :: context.groups;
                declare context (L.Constant (constants.factor, L.Int));
                declare context (L.Constant (constants.addend, L.Int));
                Some constants
              end
              else None
            in
            Some (counter, cost.bound, constants)
        | _ -> None)
      function_type.costs
  in
  let time_units = { Costs.resource = Time; counting = Units } in
  let counts_time =
    List.exists (fun counter -> Costs.key counter = Costs.key time_units) context.counters
  in
  let times_by_type = List.exists (fun (counter, _, _) -> counter = time_units) promised in
  (* A call back into the definition around it still assumes its bound
     with the definition's constants, which are kept. *)
  let saved_counters = context.counters in
  context.counters <-
    distinct_counters
      ((if counts_time then [ time_units ] else [])
      @ List.map (fun (counter, _, _) -> counter) promised
      @ loop_counters frame.source inside.locals body);
  let inside =
    {
      inside with
      spent = List.map (fun counter -> (Costs.key counter, Costs.zero)) context.counters;
    }
  in
  let mark = context.fresh and facts_mark = List.length context.facts in
  let saved_returns = context.returns
  and saved_output = context.output
  and saved_terminates = context.terminates in
  context.returns <- [];
  context.output <- (match function_type.output with Returns output -> Some output | _ -> None);
  context.terminates <- T.terminates function_type;
  let pending =
    Fun.protect
      ~finally:(fun () ->
        context.returns <- saved_returns;
        context.output <- saved_output;
        context.terminates <- saved_terminates;
        context.counters <- saved_counters)
      (fun () ->
        let finished = block_value context inside body in
        let exits =
          (match finished with Some (frame, _) -> [ frame ] | None -> [])
          @ List.map fst context.returns
        in
        let spent_of (exit_ : frame) counter =
          match List.assoc_opt (Costs.key counter) exit_.spent with
          | Some term -> term
          | None -> Costs.zero
        in
        List.iter
          (fun (exit_ : frame) ->
            List.iter
              (fun (counter, (bound : T.cost_bound), constants) ->
                let spent = spent_of exit_ counter in
                let goal =
                  match (bound, constants) with
                  | Order_of, Some constants ->
                      Costs.at_most spent (Costs.bound constants (L.int 1))
                  | No_more_than (Some k), _ -> Costs.at_most spent (L.Integer k)
                  | Exactly_cost (Some k), _ -> L.equal spent (L.Integer k)
                  | _ -> L.Boolean true
                in
                oblige context exit_ Cost written.span
                  (Printf.sprintf "This lambda may spend more than its type, `%s`, allows."
                     (T.show ty))
                  goal)
              promised)
          exits;
        (* A bound on the time of one call, from what the lambda does not
           change, shown only once a cost uses it. *)
        if counts_time && not times_by_type then
          let spent = List.map (fun exit_ -> spent_of exit_ time_units) exits in
          let most =
            match spent with
            | [] -> Costs.zero
            | first :: rest -> List.fold_left Costs.larger first rest
          in
          match
            Costs.bound_on ~varies:(made_since context mark)
              ~facts:
                (facts_since context facts_mark
                @ List.map (fun (exit_ : frame) -> exit_.condition) exits)
              most
          with
          | Some bound ->
              Some
                ( bound,
                  List.filter_map
                    (fun ((exit_ : frame), spent) ->
                      obligation_at context exit_ Cost written.span
                        "The prover cannot show that a call of this lambda takes no more time than \
                         the bound it found for every call, which a cost here relies on."
                        (Costs.at_most spent bound))
                    (List.combine exits spent) )
          | None -> None
        else None)
  in
  let term = arrive context frame "lambda" ty in
  (match frame.source.checked.captures.(written.id) with
  | Some captured -> context.lambda_captures <- (term, captured) :: context.lambda_captures
  | None -> ());
  (match pending with
  | Some found -> context.lambda_times <- (term, found) :: context.lambda_times
  | None -> ());
  (frame, term)

(* The [requires] on the type of a function-typed parameter, with the
   names of its inputs, in the definition that declares it. *)
and callback_requires (parameters : parameter list) index =
  let named =
    List.filter_map
      (fun (parameter : parameter) ->
        match parameter.kind with Named_parameter { type_; _ } -> Some type_ | _ -> None)
      parameters
  in
  let has_self =
    List.exists
      (fun (p : parameter) -> match p.kind with Self_parameter _ -> true | _ -> false)
      parameters
  in
  match List.nth_opt named (if has_self then index - 1 else index) with
  | Some { kind = Function_type { input_names; clauses; _ }; _ } when input_names <> [] ->
      Some
        ( input_names,
          List.filter_map
            (fun (clause : clause) ->
              match clause.kind with Requires value -> Some value | _ -> None)
            clauses )
  | _ -> None

(* What a callee promises the lambda it is passed for one parameter: that
   parameter's [requires], read in the callee with the call's other
   arguments, and the lambda's arguments for the inputs it names. *)
and callback_facts context frame (call_ : C.call) index evaluated arguments =
  match call_.callee with
  | Function { path; type_arguments } -> (
      match Interface.Summary.definition context.database path with
      | Some (key, { kind = Function { signature; _ }; _ }) -> (
          match
            (callback_requires signature.parameters index, callee_source context.database key)
          with
          | Some (input_names, requires), Some callee ->
              let part = part_of callee signature.parameters signature.clauses in
              let locals, self =
                List.fold_left
                  (fun (locals, self) (position, binding) ->
                    match (binding, List.assoc_opt position evaluated) with
                    | Self_binding, Some term -> (locals, Some term)
                    | Parameter_binding name_, Some term -> (Ids.add name_.id term locals, self)
                    | _ -> (locals, self))
                  (Ids.empty, None)
                  (List.mapi (fun position binding -> (position, binding)) part.binding)
              in
              if List.length input_names <> List.length arguments then []
              else
                let locals =
                  List.fold_left2
                    (fun locals (name_ : name) term -> Ids.add name_.id term locals)
                    locals input_names arguments
                in
                let substitution =
                  match Query.demand context.database Interface.Environment.signature path with
                  | Some (signature : T.signature) ->
                      let rec pair generics arguments =
                        match (generics, arguments) with
                        | (generic : T.generic) :: generics, argument :: arguments ->
                            (generic.generic, T.substitute_argument frame.substitution argument)
                            :: pair generics arguments
                        | _ -> []
                      in
                      pair signature.generics type_arguments
                  | None -> []
                in
                let inside =
                  {
                    frame with
                    source = callee;
                    locals;
                    old_locals = locals;
                    self;
                    old_self = self;
                    checking = false;
                    loop = None;
                    substitution;
                    result = None;
                  }
                in
                List.map (fun clause -> snd (value context inside clause)) requires
          | _ -> [])
      | _ -> [])
  | _ -> []

(* A call through a function-typed parameter whose type has a [requires]
   must meet it. *)
and check_callback_requires context frame (written : expression) values =
  match written.kind with
  | Call (({ kind = Name _; _ } as callee), _) -> (
      match frame.source.checked.meanings.(callee.id) with
      | Some (Local_value id) -> (
          let index =
            let rec find position = function
              | [] -> None
              | (parameter : parameter) :: rest -> (
                  match parameter.kind with
                  | Named_parameter { name = name_; _ } when name_.id = id -> Some position
                  | Self_parameter _ | Named_parameter _ -> find (position + 1) rest
                  | Parameter_error -> find (position + 1) rest)
            in
            find 0 context.parameters
          in
          match index with
          | Some index -> (
              match callback_requires context.parameters index with
              | Some (input_names, requires) when List.length input_names = List.length values ->
                  let locals =
                    List.fold_left2
                      (fun locals (name_ : name) (_, _, term) -> Ids.add name_.id term locals)
                      frame.locals input_names values
                  in
                  let inside = { frame with locals; checking = false } in
                  List.iter
                    (fun (clause : expression) ->
                      oblige context frame Requires written.span
                        (Printf.sprintf "`%s` may not hold for this call through `%s`."
                           (quote frame.source clause.span) (quote frame.source callee.span))
                        (snd (value context inside clause)))
                    requires
              | _ -> ())
          | None -> ())
      | _ -> ())
  | _ -> ()

(* Whether a call is to a private method that takes [mut self], which is a
   step of an update: its receiver's invariant is neither shown at the call
   nor assumed after. See DESIGN.md, "Type invariants". *)
and updating_helper context (call_ : C.call) =
  match call_.callee with
  | Function { path = Method { receiver = Mut; _ } as path; _ } -> is_updating_helper context path
  | _ -> false

and is_updating_helper context path =
  match Interface.Summary.definition context.database path with
  | Some
      ( _,
        { visibility = Private; kind = Function { signature = { name = Member_name _; _ }; _ }; _ }
      ) ->
      true
  | _ -> false

(* The [impl] of a trait for a known type, when it has no generic
   parameters of its own, from the type's package or this one. *)
and concrete_impl context trait (ty : T.ty) =
  match ty with
  | Named { path; _ } ->
      let packages = List.sort_uniq compare [ Path.package context.current; Path.package path ] in
      List.find_map
        (fun package ->
          List.find_map
            (fun impl ->
              match Query.demand context.database Interface.Environment.interface impl with
              | Some (Interface.Environment.Impl_interface { impl_generics = []; _ }) -> Some impl
              | _ -> None)
            (Call_graph.impls_for
               (Query.demand context.database Call_graph.package_impls package)
               [ trait ] ty))
        packages
  | _ -> None

(* A trait's laws, and those of the traits it requires, as facts about a
   type, each quantified over its parameters. A law is shown for each
   [impl] written by hand, by the [impl], so it is a fact wherever the
   trait's methods are used. See PROVER.md, "Proofs". *)
and assume_laws context frame trait (ty : T.ty) =
  let key = Path.show trait ^ " for " ^ type_key ty in
  if not (List.mem key context.laws_assumed) then begin
    context.laws_assumed <- key :: context.laws_assumed;
    List.iter
      (fun trait ->
        List.iter
          (fun (source, (law : law)) ->
            match law_fact context frame source trait ty law with
            | Some fact -> assume context frame fact
            | None -> ())
          (laws_of context trait))
      (Call_graph.traits_with_required context.database trait)
  end

and laws_of context trait =
  match Interface.Summary.definition context.database trait with
  | Some (key, { kind = Trait { members; _ }; _ }) -> (
      match callee_source context.database key with
      | Some source ->
          List.filter_map
            (fun (member : trait_member line) ->
              match member.kind with Law law -> Some (source, law) | _ -> None)
            members
      | None -> [])
  | _ -> []

(* A law's frame: its parameters as the given terms, with [Self] the type. *)
and law_frame frame source trait ty (law : law) terms =
  let locals =
    List.fold_left2
      (fun locals (parameter : parameter) term ->
        match parameter.kind with
        | Named_parameter { name = name_; _ } -> Ids.add name_.id term locals
        | _ -> locals)
      Ids.empty law.parameters terms
  in
  {
    frame with
    source;
    locals;
    old_locals = locals;
    self = None;
    old_self = None;
    result = None;
    checking = false;
    loop = None;
    substitution = [ ({ T.owner = trait; name = "Self" }, T.Type ty) ];
    self_type = None;
  }

and law_parameter_types frame source trait ty (law : law) =
  List.map
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name = name_; _ } -> (
          match source.checked.local_types.(name_.id) with
          | Some declared ->
              T.substitute [ ({ T.owner = trait; name = "Self" }, T.Type ty) ] declared
          | None -> T.Error)
      | _ -> T.Error)
    law.parameters
  |> fun types ->
  ignore frame;
  types

and law_fact context frame source trait ty (law : law) =
  let types = law_parameter_types frame source trait ty law in
  if List.exists (fun ty -> ty = T.Error) types then None
  else begin
    context.fresh <- context.fresh + 1;
    let symbols = List.mapi (fun index _ -> Printf.sprintf "law.%d.%d" context.fresh index) types in
    let inside =
      law_frame
        { frame with bound = symbols @ frame.bound }
        source trait ty law
        (List.map (fun s -> L.Symbol s) symbols)
    in
    try
      let premise =
        L.conjunction (List.map (fun clause -> snd (value context inside clause)) law.requires)
      in
      let range =
        L.conjunction (List.map2 (fun symbol ty -> in_range ty (L.Symbol symbol)) symbols types)
      in
      match block_value context inside law.body with
      | Some (_, holds) ->
          Some
            (L.Forall
               ( List.map2 (fun symbol ty -> (symbol, sort_of context ty)) symbols types,
                 L.( ==> ) (L.( &&& ) range premise) holds ))
      | None -> None
    with Unsupported _ | Foreign_unsupported _ -> None
  end

(* Sequences of handed-out parts, through the same functions in the
   logic that the contracts of [standard::specification] are about. *)
and sequence_path : Path.t =
  Top { module_ = { package = "standard"; modules = [ "specification" ] }; name = "Sequence" }

and sequence_type element = T.Named { path = sequence_path; arguments = [ T.Type element ] }

and sequence_length context element term =
  let path = Path.Method { owner = sequence_path; name = "length"; receiver = Read } in
  let symbol = "function." ^ Path.show path ^ "[" ^ type_key element ^ "]" in
  declare context (L.Function (symbol, [ sort_of context (sequence_type element) ], L.Int));
  L.Apply (symbol, [ term ])

and sequence_at context element term index =
  let sequence = sequence_type element in
  let index_trait : Path.t =
    Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Index" }
  in
  match
    Call_graph.impls_for
      (Query.demand context.database Call_graph.package_impls "standard")
      [ index_trait ] sequence
  with
  | impl :: _ ->
      let path = Path.Method { owner = impl; name = "at"; receiver = Read } in
      let symbol = "function." ^ Path.show path ^ "[" ^ type_key sequence ^ "]" in
      declare context
        (L.Function (symbol, [ sort_of context sequence; L.Int ], sort_of context element));
      Some (L.Apply (symbol, [ term; index ]))
  | [] -> None

(* Two sequences with the same length and the same elements are identical:
   the one fact about sequences their contracts cannot state, since a
   contract describes a result. It is stated for each two that are
   compared, which keeps the solver from comparing every two it knows. *)
and extensional context frame (ty : T.ty) a b =
  match ty with
  | Named { path; arguments = [ T.Type element ] } when Path.equal path sequence_path -> (
      context.fresh <- context.fresh + 1;
      let index = Printf.sprintf "index.%d" context.fresh in
      match
        ( sequence_at context element a (L.Symbol index),
          sequence_at context element b (L.Symbol index) )
      with
      | Some at_a, Some at_b ->
          let length = sequence_length context element in
          fact context frame
            L.(
              equal (length a) (length b)
              &&& Forall
                    ( [ (index, Int) ],
                      Apply ("<=", [ int 0; Symbol index ])
                      &&& Apply ("<", [ Symbol index; length a ])
                      ==> equal at_a at_b )
              ==> equal a b)
      | _ -> ())
  | Named { path; arguments }
    when Path.equal path finite_set_path || Path.equal path finite_map_path -> (
      (* A set by what it contains, and a map by its keys and their values. *)
      let finite_map = Path.equal path finite_map_path in
      match arguments with
      | T.Type key :: rest ->
          context.fresh <- context.fresh + 1;
          let each = Printf.sprintf "key.%d" context.fresh in
          let function_ name output inputs = finite_function context ty name output inputs in
          let key_sort = sort_of context key in
          let has =
            function_
              (if finite_map then "contains_key" else "contains")
              L.Bool
              [ (L.Symbol each, key_sort) ]
          in
          let same =
            if finite_map then
              match rest with
              | [ T.Type value_type ] ->
                  let get =
                    function_ "get" (sort_of context value_type) [ (L.Symbol each, key_sort) ]
                  in
                  L.(equal (has a) (has b) &&& (has a ==> equal (get a) (get b)))
              | _ -> L.equal (has a) (has b)
            else L.equal (has a) (has b)
          in
          fact context frame
            L.(Forall ([ (each, key_sort) ], in_range key (Symbol each) ==> same) ==> equal a b)
      | _ -> ())
  | _ -> ()

(* A method of a [FiniteSet] or a [FiniteMap], as a function in the logic,
   applied to a value of it and the inputs given with their sorts. *)
and finite_function context (ty : T.ty) name output inputs =
  match ty with
  | Named { path; arguments } ->
      let symbol =
        "function."
        ^ Path.show (Path.Method { owner = path; name; receiver = Read })
        ^ "["
        ^ String.concat ", " (List.map argument_key arguments)
        ^ "]"
      in
      declare context (L.Function (symbol, sort_of context ty :: List.map snd inputs, output));
      fun term -> L.Apply (symbol, term :: List.map fst inputs)
  | _ -> fun term -> term

and finite_set_path : Path.t =
  Top { module_ = { package = "standard"; modules = [ "specification" ] }; name = "FiniteSet" }

and finite_map_path : Path.t =
  Top { module_ = { package = "standard"; modules = [ "specification" ] }; name = "FiniteMap" }

(* A [List] or a [Sequence] written out: a value whose sequence, the list's
   model or the sequence itself, has the elements in order. A non-empty
   list is one allocation. *)
and list_literal context frame (written : expression) items =
  let ty = type_of frame written in
  let frame, values =
    List.fold_left
      (fun (frame, values) item ->
        let frame, term = value context frame item in
        (frame, values @ [ term ]))
      (frame, []) items
  in
  let element =
    match ty with
    | Named { arguments = T.Type element :: _; _ } -> element
    | _ -> unsupported written.span "a literal of `%s`" (T.show ty)
  in
  let literal =
    match sequence_of context frame ty ~element values with
    | Some literal -> literal
    | None -> (
        match set_of context frame ty ~element values with
        | Some literal -> literal
        | None -> unsupported written.span "a literal of `%s`" (T.show ty))
  in
  let allocates =
    items <> []
    && match ty with Named { path; _ } -> not (Path.equal path sequence_path) | _ -> false
  in
  let frame =
    spend context frame (fun (counter : Costs.counter) ->
        match (counter.resource, counter.counting) with
        | Allocations, _ when allocates -> L.int 1
        | Allocated_bytes, Units when allocates -> L.int 1
        | Allocated_bytes, (At_most | Exactly) when allocates ->
            unknown_amount context frame counter
        | _ -> Costs.zero)
  in
  (frame, literal)

(* A slice, [items[a..b]]: a view of the elements from [a] to before [b],
   which must be within the collection, whose model is that run of the
   collection's model. *)
and slice context frame (written : expression) base (range : expression) =
  let base_type = type_of frame base in
  let element =
    match base_type with
    | Named { arguments = T.Type element :: _; _ } -> element
    | _ -> unsupported written.span "a slice of `%s`" (T.show base_type)
  in
  let frame, collection = value context frame base in
  let model =
    match model_of context base_type collection ~element with
    | Some model -> model
    | None -> unsupported written.span "a slice of `%s`" (T.show base_type)
  in
  let length = sequence_length context element model in
  match range.kind with
  | Range { start; stop; inclusive; _ } ->
      let frame, low =
        match start with Some start -> value context frame start | None -> (frame, L.int 0)
      in
      let frame, high =
        match stop with
        | Some stop ->
            let frame, high = value context frame stop in
            (frame, if inclusive then Costs.plus high (L.int 1) else high)
        | None -> (frame, length)
      in
      oblige context frame Requires range.span
        (Printf.sprintf "`%s` may not be within `%s`." (quote frame.source range.span)
           (quote frame.source base.span))
        L.(
          Apply ("<=", [ int 0; low ])
          &&& Apply ("<=", [ low; high ])
          &&& Apply ("<=", [ high; length ]));
      note_place context frame range (Run (low, high));
      let slice_type = type_of frame written in
      let viewed = arrive context frame "slice" slice_type in
      (match model_of context slice_type viewed ~element with
      | Some viewed_model -> (
          let count = Costs.minus high low in
          assume context frame (L.equal (sequence_length context element viewed_model) count);
          context.fresh <- context.fresh + 1;
          let position = Printf.sprintf "index.%d" context.fresh in
          match
            ( sequence_at context element viewed_model (L.Symbol position),
              sequence_at context element model (Costs.plus low (L.Symbol position)) )
          with
          | Some inside, Some outside ->
              assume context frame
                (L.Forall
                   ( [ (position, L.Int) ],
                     L.(
                       Apply ("<=", [ int 0; Symbol position ])
                       &&& Apply ("<", [ Symbol position; count ])
                       ==> equal inside outside) ))
          | _ -> ())
      | None -> ());
      (frame, viewed)
  | _ -> unsupported range.span "this slice"

(* An argument's type as the callee gets it: a view's, where an owned
   value is passed as one. *)
and argument_type frame (argument : C.argument) (expression_ : expression) =
  let ty = type_of frame expression_ in
  match argument.conversion with
  | Some Owned_to_view -> Option.value (viewed_type ty) ~default:ty
  | _ -> ty

and viewed_type (owned : T.ty) =
  let standard modules name : Path.t = Top { module_ = { package = "standard"; modules }; name } in
  match owned with
  | Named { path; arguments } when Path.equal path (standard [ "list" ] "List") ->
      Some (T.Named { path = standard [ "list" ] "Slice"; arguments })
  | Named { path; arguments } when Path.equal path (standard [ "text" ] "String") ->
      Some (T.Named { path = standard [ "text" ] "StringSlice"; arguments })
  | _ -> None

(* A [List] passed as a [Slice], or a [String] as a [StringSlice]: a view
   of the value, with the same model. See DESIGN.md, "Views". *)
and view_of context frame (owned : T.ty) term =
  match viewed_type owned with
  | Some view_type -> (
      let element =
        match owned with
        | Named { arguments = T.Type element :: _; _ } -> element
        | _ -> T.builtin UInt8
      in
      let view = arrive context frame "view" view_type in
      match (model_of context owned term ~element, model_of context view_type view ~element) with
      | Some owned_model, Some view_model ->
          assume context frame (L.equal view_model owned_model);
          view
      | _ -> view)
  | None -> term

(* A string literal. Plain text is a [String] in static memory, which costs
   nothing to make, whose model is its UTF-8 bytes. Text with
   interpolations is a new [String], about which nothing more is known,
   since each part is written out by its [Display]. *)
and string_literal context frame (written : expression) (literal : string_literal) =
  let ty = type_of frame written in
  match (literal.tag, literal.rest) with
  | None, [] -> (frame, text_value context frame ty literal.first.value)
  | None, _ ->
      let frame =
        List.fold_left (fun frame (part, _) -> fst (value context frame part)) frame literal.rest
      in
      let frame = spend context frame (unknown_amount context frame) in
      (frame, arrive context frame "string" ty)
  | Some _, _ -> tagged_template context frame written literal ty

(* Whether a clause reads its template parameter only as
   [template.literals], so that a template's parts cannot change it. *)
and reads_only_literals (source : source) (parameter : name) (clause : expression) =
  let names_parameter (expression_ : expression) =
    match (expression_.kind, source.checked.meanings.(expression_.id)) with
    | Name _, Some (Local_value id) -> id = parameter.id
    | _ -> false
  in
  let fine = ref true in
  let rec visit (expression_ : expression) =
    match expression_.kind with
    | Member (base, { text = "literals"; _ }) when names_parameter base -> ()
    | _ ->
        if names_parameter expression_ then fine := false;
        Syntax_walk.expression_parts ~expression:visit
          ~statement:(fun _ -> fine := false)
          expression_
  in
  visit clause;
  !fine

and template_trait : Path.t =
  Top { module_ = { package = "standard"; modules = [ "text" ] }; name = "FromTemplate" }

(* A tagged template is a call of its tag's [from_template], with the
   template: its literal texts, each a [Literal] whose model is its bytes,
   and its parts, each turned into the tag's [Part] by its [From]. The
   call's [requires], such as that the text is one character, is shown of
   that template. See DESIGN.md, "Tagged templates". *)
and tagged_template context frame (written : expression) (literal : string_literal) tag_type =
  let template =
    match frame.source.checked.templates.(literal.id) with
    | Some template -> template
    | None -> unsupported written.span "a tagged template without a checked form"
  in
  match template.from_template with
  | Some
      ({
         callee = Trait_method { trait; name; receiver; evidence = Impl { impl; _ } as evidence; _ };
         _;
       } as call_) -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match
        ( method_contract context.database trait name receiver evidence,
          Query.demand context.database Interface.Environment.signature path )
      with
      | Some contract, Some { parameters = [ { type_ = template_type; _ } ]; _ } ->
          let part_type =
            match template_type with
            | Named { arguments = [ T.Type part ]; _ } -> part
            | _ -> unsupported written.span "a template of `%s`" (T.show template_type)
          in
          let text name : Path.t =
            Top { module_ = { package = "standard"; modules = [ "text" ] }; name }
          in
          let list_of element =
            T.Named
              {
                path =
                  Top { module_ = { package = "standard"; modules = [ "list" ] }; name = "List" };
                arguments = [ T.Type element ];
              }
          in
          let literal_type = T.Named { path = text "Literal"; arguments = [] } in
          let texts =
            literal.first.value :: List.map (fun (_, (text : text)) -> text.value) literal.rest
          in
          let literals = List.map (text_value context frame literal_type) texts in
          let frame, parts =
            List.fold_left2
              (fun (frame, parts) ((part : expression), _) conversion ->
                let frame, term =
                  match conversion with
                  | Some converting -> (
                      match resolved_call context frame part converting with
                      | Some converted -> converted
                      | None -> unsupported part.span "a part that never returns")
                  | None -> value context frame part
                in
                (frame, parts @ [ term ]))
              (frame, []) literal.rest template.part_conversions
          in
          let made list element items =
            match sequence_of context frame list ~element items with
            | Some made -> made
            | None -> unsupported written.span "a template of `%s`" (T.show template_type)
          in
          ignore (sort_of context template_type);
          let value_ =
            L.Apply
              ( constructor_name template_type None,
                [
                  made (list_of literal_type) literal_type literals;
                  made (list_of part_type) part_type parts;
                ] )
          in
          let own = List.hd contract.parts in
          let entry = part_frame frame own ~arguments:[ (0, value_) ] ~substitution:[] in
          (* A clause that reads only the template's literal texts, of a tag
             whose [impl] is not generic, can be decided by running it. *)
          let evaluable (clause : expression) =
            match (evidence, own.binding) with
            | Impl { arguments = []; _ }, [ Parameter_binding parameter ] ->
                reads_only_literals own.callee parameter clause
            | _ -> false
          in
          List.iteri
            (fun index (clause : expression) ->
              let evaluation =
                if evaluable clause then Some { from_template = path; texts; clause = index }
                else None
              in
              oblige ?evaluation context frame Requires written.span
                (Printf.sprintf "This template may not meet `%s`, which its tag requires."
                   (quote own.callee clause.span))
                (snd (value context entry clause)))
            own.requires;
          let result = arrive context frame "tagged" tag_type in
          assume_valid context frame tag_type result;
          List.iter
            (fun (clause : expression) ->
              assume context frame (snd (value context { entry with result = Some result } clause)))
            own.ensures;
          let frame =
            spend context frame
              (callee_amount context frame ~path ~parts:contract.parts
                 ~bound_frame:(fun part ->
                   {
                     (part_frame frame part ~arguments:[ (0, value_) ] ~substitution:[]) with
                     result = Some result;
                   })
                 ~call_ ~values:[] ~change:None)
          in
          (frame, result)
      | _ -> unsupported written.span "a tagged template whose tag the prover cannot read")
  | _ -> unsupported written.span "a tagged template whose tag the prover cannot read"

(* A [List] or a [Sequence] of these elements, in order: a value whose
   sequence, the list's model or the sequence itself, has them. *)
and sequence_of context frame (ty : T.ty) ~element values =
  let made = arrive context frame "literal" ty in
  let sequence =
    match ty with
    | Named { path; _ } when Path.equal path sequence_path -> Some made
    | Named
        {
          path = Top { module_ = { package = "standard"; modules = [ "list" ] }; name = "List" };
          _;
        } ->
        model_of context ty made ~element
    | _ -> None
  in
  Option.map
    (fun sequence ->
      assume_valid context frame ty made;
      assume context frame
        (L.equal (sequence_length context element sequence) (L.int (List.length values)));
      List.iteri
        (fun index item ->
          match sequence_at context element sequence (L.int index) with
          | Some at -> assume context frame (L.equal at item)
          | None -> ())
        values;
      made)
    sequence

(* A [Set] or a [FiniteSet] of these elements: one that contains each of
   them and nothing else, so no more of them than were written. *)
and set_of context frame (ty : T.ty) ~element values =
  let set_path : Path.t =
    Top { module_ = { package = "standard"; modules = [ "set" ] }; name = "Set" }
  in
  let finite = T.Named { path = finite_set_path; arguments = [ T.Type element ] } in
  let made = arrive context frame "literal" ty in
  let model =
    match ty with
    | Named { path; _ } when Path.equal path finite_set_path -> Some made
    | Named { path; _ } when Path.equal path set_path -> model_as context ty made ~model:finite
    | _ -> None
  in
  Option.map
    (fun model ->
      assume_valid context frame ty made;
      let element_sort = sort_of context element in
      let contains value =
        finite_function context finite "contains" L.Bool [ (value, element_sort) ] model
      in
      List.iter (fun value -> assume context frame (contains value)) values;
      context.fresh <- context.fresh + 1;
      let each = Printf.sprintf "value.%d" context.fresh in
      assume context frame
        (L.Forall
           ( [ (each, element_sort) ],
             L.( ==> ) (contains (L.Symbol each))
               (L.disjunction (List.map (L.equal (L.Symbol each)) values)) ));
      let size = finite_function context finite "size" L.Int [] model in
      assume context frame (Costs.at_most size (L.int (List.length values)));
      made)
    model

(* A [Map] or a [FiniteMap] written out: each key with its value, and no
   other keys. Its keys must be distinct. A non-empty map is one
   allocation. See PROVER.md, "Obligations". *)
and map_literal context frame (written : expression) entries =
  let ty = type_of frame written in
  let map_path : Path.t =
    Top { module_ = { package = "standard"; modules = [ "map" ] }; name = "Map" }
  in
  let key_type, value_type =
    match ty with
    | Named { arguments = [ T.Type key; T.Type value_type ]; _ } -> (key, value_type)
    | _ -> unsupported written.span "a literal of `%s`" (T.show ty)
  in
  let frame, terms =
    List.fold_left
      (fun (frame, terms) ((key : expression), (entry : expression)) ->
        let frame, key_term = value context frame key in
        let frame, value_term = value context frame entry in
        (frame, terms @ [ (key, key_term, value_term) ]))
      (frame, []) entries
  in
  List.iteri
    (fun index (_, key_term, _) ->
      List.iteri
        (fun other ((other_key : expression), other_term, _) ->
          if other > index then
            oblige context frame Disjoint other_key.span
              (Printf.sprintf "The key `%s` may equal an earlier key of this map."
                 (quote frame.source other_key.span))
              (L.not_ (equal_of context frame key_type key_term other_term)))
        terms)
    terms;
  let finite =
    T.Named { path = finite_map_path; arguments = [ T.Type key_type; T.Type value_type ] }
  in
  let made = arrive context frame "literal" ty in
  let model =
    match ty with
    | Named { path; _ } when Path.equal path finite_map_path -> made
    | Named { path; _ } when Path.equal path map_path -> (
        match model_as context ty made ~model:finite with
        | Some model -> model
        | None -> unsupported written.span "a literal of `%s`" (T.show ty))
    | _ -> unsupported written.span "a literal of `%s`" (T.show ty)
  in
  assume_valid context frame ty made;
  let key_sort = sort_of context key_type in
  let has key = finite_function context finite "contains_key" L.Bool [ (key, key_sort) ] model in
  let get key =
    finite_function context finite "get" (sort_of context value_type) [ (key, key_sort) ] model
  in
  List.iter
    (fun (_, key, entry) -> assume context frame L.(has key &&& equal (get key) entry))
    terms;
  context.fresh <- context.fresh + 1;
  let each = Printf.sprintf "key.%d" context.fresh in
  assume context frame
    (L.Forall
       ( [ (each, key_sort) ],
         L.( ==> ) (has (L.Symbol each))
           (L.disjunction (List.map (fun (_, key, _) -> L.equal (L.Symbol each) key) terms)) ));
  assume context frame
    (L.equal (finite_function context finite "size" L.Int [] model) (L.int (List.length terms)));
  let frame =
    spend context frame (fun (counter : Costs.counter) ->
        match (counter.resource, counter.counting) with
        | Allocations, _ when entries <> [] -> L.int 1
        | Allocated_bytes, Units when entries <> [] -> L.int 1
        | Allocated_bytes, (At_most | Exactly) when entries <> [] ->
            unknown_amount context frame counter
        | _ -> Costs.zero)
  in
  (frame, made)

(* Text as a value whose model is its UTF-8 bytes. *)
and text_value context frame (ty : T.ty) text =
  let made = arrive context frame "string" ty in
  let byte = T.builtin UInt8 in
  (match model_of context ty made ~element:byte with
  | Some model ->
      assume context frame
        (L.equal (sequence_length context byte model) (L.int (String.length text)));
      String.iteri
        (fun index character ->
          match sequence_at context byte model (L.int index) with
          | Some at -> assume context frame (L.equal at (L.int (Char.code character)))
          | None -> ())
        text
  | None -> ());
  made

(* A callee part's frame, for reading its clauses, with its parameters
   bound to the given terms by position. *)
and part_frame frame (part : part) ~arguments ~substitution =
  let locals, self =
    List.fold_left
      (fun (locals, self) (position, binding) ->
        match (binding, List.assoc_opt position arguments) with
        | Self_binding, Some term -> (locals, Some term)
        | Parameter_binding name_, Some term -> (Ids.add name_.id term locals, self)
        | _ -> (locals, self))
      (Ids.empty, None)
      (List.mapi (fun position binding -> (position, binding)) part.binding)
  in
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
    substitution;
  }

(* A value's model, by the standard library's [impl] of [Model] for its
   type, as a call of [model()] would read it. *)
and model_of context (ty : T.ty) term ~element =
  model_as context ty term ~model:(sequence_type element)

(* A value's model of the given type, by the standard library's [impl] of
   [Model] for its type, as a call of [model()] would read it. *)
and model_as context (ty : T.ty) term ~(model : T.ty) =
  let model_trait : Path.t =
    Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Model" }
  in
  match
    Call_graph.impls_for
      (Query.demand context.database Call_graph.package_impls "standard")
      [ model_trait ] ty
  with
  | impl :: _ ->
      let path = Path.Method { owner = impl; name = "model"; receiver = Read } in
      let symbol = "function." ^ Path.show path ^ "[" ^ type_key ty ^ "]" in
      declare context (L.Function (symbol, [ sort_of context ty ], sort_of context model));
      Some (L.Apply (symbol, [ term ]))
  | [] -> None

(* Cursors. A cursor carries what it has handed out and whether it has
   ended as ghost parts of its value. See PROVER.md, "Lending and yielding
   methods". *)
and cursor_trait : Path.t =
  Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Cursor" }

and cursor_yielded context cursor_type element cursor =
  let sort = sort_of context cursor_type in
  let symbol = "cursor.yielded." ^ type_key cursor_type in
  declare context (L.Function (symbol, [ sort ], sort_of context (sequence_type element)));
  L.Apply (symbol, [ cursor ])

and cursor_ended context cursor_type cursor =
  let symbol = "cursor.ended." ^ type_key cursor_type in
  declare context (L.Function (symbol, [ sort_of context cursor_type ], L.Bool));
  L.Apply (symbol, [ cursor ])

(* A pull: [Some] of a part that meets the method's clauses for each part,
   after which the cursor has handed it out too and the method's other
   clauses hold, as where it may stop; or [None], once the method has
   ended, after which its other clauses hold with [finished] true. The
   cursor that is left is a new value, from the same call. *)
and pull context frame (made : cursor) cursor ~cursor_type =
  let element = made.element in
  let option_type = T.Named { path = option_path; arguments = [ T.Type element ] } in
  ignore (sort_of context option_type);
  let later = arrive context frame "cursor" cursor_type in
  context.cursors <- (later, made) :: context.cursors;
  let pulled = arrive context frame "pulled" option_type in
  let some = L.Apply (L.tester (constructor_name option_type (Some "Some")), [ pulled ]) in
  let part = L.Apply (selector_name option_type (Some "Some") "value", [ pulled ]) in
  let before = cursor_yielded context cursor_type element cursor in
  let clauses (at : frame) ~each ~result ~yielded ~finished =
    let inside =
      {
        made.method_frame with
        condition = at.condition;
        bound = at.bound;
        result;
        yielded = Some yielded;
        finished;
      }
    in
    List.iter
      (fun (clause : expression) ->
        if mentions_result made.own.callee clause = each then
          assume context at (snd (value context inside clause)))
      made.own.ensures
  in
  assume context frame (L.( ==> ) (cursor_ended context cursor_type cursor) (L.not_ some));
  let handed = restrict frame some in
  assume_valid context handed element part;
  clauses handed ~each:true ~result:(Some part) ~yielded:before ~finished:None;
  let through = appended context handed element before part in
  assume context handed
    L.(
      equal (cursor_yielded context cursor_type element later) through
      &&& not_ (cursor_ended context cursor_type later));
  clauses handed ~each:false ~result:None ~yielded:through ~finished:(Some (L.Boolean false));
  let none = restrict frame (L.not_ some) in
  assume context none
    L.(
      equal (cursor_yielded context cursor_type element later) before
      &&& cursor_ended context cursor_type later);
  clauses none ~each:false ~result:None ~yielded:before ~finished:(Some (L.Boolean true));
  (pulled, later)

and option_path : Path.t =
  Top { module_ = { package = "standard"; modules = [ "option" ] }; name = "Option" }

(* A sequence of parts with nothing in it. *)
and empty_parts context frame element =
  let parts = fresh context "parts" (sort_of context (sequence_type element)) in
  assume context frame (L.equal (sequence_length context element parts) (L.int 0));
  parts

(* A sequence of parts about which only its length is known. *)
and some_parts context frame element =
  let parts = fresh context "parts" (sort_of context (sequence_type element)) in
  assume context frame L.(Apply (">=", [ sequence_length context element parts; int 0 ]));
  parts

(* The parts, with one more after them. *)
and appended context frame element parts part =
  let longer = fresh context "parts" (sort_of context (sequence_type element)) in
  let length = sequence_length context element parts in
  assume context frame
    L.(
      Apply (">=", [ length; int 0 ])
      &&& equal (sequence_length context element longer) (Apply ("+", [ length; int 1 ])));
  (match (sequence_at context element longer length, frame.bound) with
  | Some last, _ -> assume context frame (L.equal last part)
  | None, _ -> ());
  context.fresh <- context.fresh + 1;
  let index = Printf.sprintf "index.%d" context.fresh in
  (match
     ( sequence_at context element longer (L.Symbol index),
       sequence_at context element parts (L.Symbol index) )
   with
  | Some after, Some before ->
      assume context frame
        (L.Forall
           ( [ (index, L.Int) ],
             L.(
               Apply ("<=", [ int 0; Symbol index ])
               &&& Apply ("<", [ Symbol index; length ])
               ==> equal after before) ))
  | _ -> ());
  longer

(* Whether a clause mentions [result], so that it holds at each [yield]
   of a lending or yielding method, rather than where the method ends. *)
and mentions_result source (clause : expression) =
  let found = ref false in
  let rec visit (expression : expression) =
    (match expression.kind with
    | Name path when source.resolved.names.(path.last.id) = Some Result_value -> found := true
    | _ -> ());
    Syntax_walk.expression_parts ~expression:visit ~statement:(fun _ -> ()) expression
  in
  visit clause;
  !found

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
  | Some (Global { path; type_arguments }) ->
      Some (frame, global_value context frame written path type_arguments)
  | _ -> unsupported written.span "this member"

(* A field of a value, which is in its type's range like every value. *)
and field_of context frame ty variant field field_type term =
  let part = L.Apply (selector_name ty variant field, [ term ]) in
  assume context frame (in_range field_type part);
  (* A part of a value is below it, which is how structural recursion is
     shown to end. *)
  if constructors context field_type <> None then begin
    let below = rank context field_type part in
    assume context frame
      L.(Apply ("<=", [ int 0; below ]) &&& Apply ("<", [ below; rank context ty term ]))
  end;
  part

(* A value's place in the order of parts, as Dafny's datatypes have one:
   any field is below the value it is in. *)
and rank context ty term =
  let symbol = "rank." ^ type_key ty in
  declare context (L.Function (symbol, [ sort_of context ty ], L.Int));
  L.Apply (symbol, [ term ])

(* A variant with no fields, such as [None]. *)
and variant_value context (written : expression) type_ variant =
  match declared_fields context type_ (Some variant) with
  | Some [] ->
      ignore (sort_of context type_);
      L.Apply (constructor_name type_ (Some variant), [])
  | Some _ -> unsupported written.span "a variant used as a function"
  | None -> unsupported written.span "a variant of `%s`" (T.show type_)

(* A global used as a value: a constant's value, or a function named as a
   value. *)
and global_value context frame (written : expression) path type_arguments =
  match function_contract context.database path with
  | Some contract -> named_function context frame written path type_arguments contract
  | None -> constant_value context frame written path

(* A function named as a value is a value of its type known by what it
   promises of its calls: one unit of time per call when its [time] is a
   constant. Naming it is an edge of the call graph that passes no
   arguments, so in a function that must end, it must not reach back.
   See PROVER.md, "Termination". *)
and named_function context frame (written : expression) path type_arguments contract =
  if
    context.terminates && frame.checking
    && Call_graph.reaches context.graph ~from:path ~target:context.current
  then
    oblige context frame Termination written.span
      (Printf.sprintf
         "Naming `%s` as a value reaches back here, and such a use passes no arguments the prover \
          can compare, so the recursion cannot be shown to end: write it as a direct call on a \
          part."
         (Path.show path))
      (L.Boolean false);
  let ty = type_of frame written in
  let instance =
    match List.map (T.substitute_argument frame.substitution) type_arguments with
    | [] -> ""
    | arguments -> "[" ^ String.concat ", " (List.map argument_key arguments) ^ "]"
  in
  let symbol = "named." ^ Path.show path ^ instance in
  declare context (L.Constant (symbol, sort_of context ty));
  let term = L.Symbol symbol in
  let constant_time =
    List.exists
      (fun (part : part) ->
        List.exists
          (fun ((cost : cost), _) ->
            match cost with
            | { resource = Time; bound = Big_o { kind = Integer _; _ }; amortized = false } -> true
            | _ -> false)
          part.costs)
      contract.parts
  in
  (if constant_time then
     let time = time_of context frame ty term in
     fact context frame (L.equal time (L.int 1)));
  term

(* The function a value names, if it names one by its path. *)
and named_function_of context frame (expression_ : expression) =
  match expression_.kind with
  | Mode (_, inner) | Parenthesized inner -> named_function_of context frame inner
  | Name _ | Member _ -> (
      match frame.source.checked.meanings.(expression_.id) with
      | Some (Global { path; _ }) -> (
          match function_contract context.database path with
          | Some contract -> Some (path, contract)
          | None -> None)
      | _ -> None)
  | _ -> None

(* A function named as a value and passed for a function-typed parameter
   must accept every argument the parameter's type promises it, and keep
   the cost clauses the type asks of what is passed. See PROVER.md,
   "Obligations". *)
and check_named_callback context frame (call_ : C.call) (argument : C.argument)
    (passed : expression) path (contract : contract) evaluated =
  let own = List.hd contract.parts in
  match parameter_type context frame call_ argument.parameter with
  | Some (T.Function expected) ->
      let inputs =
        List.map
          (fun (_, input) ->
            let input = substituted frame input in
            let term = arrive context frame "argument" input in
            assume_valid context frame input term;
            term)
          expected.inputs
      in
      let promised =
        L.conjunction (callback_facts context frame call_ argument.parameter evaluated inputs)
      in
      let at = restrict frame promised in
      (if List.length own.binding = List.length inputs then
         let locals, self =
           List.fold_left2
             (fun (locals, self) binding term ->
               match binding with
               | Self_binding -> (locals, Some term)
               | Parameter_binding name_ -> (Ids.add name_.id term locals, self))
             (Ids.empty, None) own.binding inputs
         in
         let inside =
           {
             frame with
             source = own.callee;
             locals;
             old_locals = locals;
             self;
             old_self = self;
             checking = false;
             loop = None;
             result = None;
             substitution = [];
           }
         in
         List.iter
           (fun (clause : expression) ->
             oblige context at Requires passed.span
               (Printf.sprintf
                  "`%s` may not accept every argument this parameter's type promises it: its `%s` \
                   may not hold."
                  (Path.show path) (quote own.callee clause.span))
               (snd (value context inside clause)))
           own.requires);
      List.iter
        (fun (cost : T.cost) ->
          if not (keeps_cost context path contract cost) then
            oblige context frame Cost passed.span
              (Printf.sprintf
                 "`%s` does not promise what this parameter's type, `%s`, asks of a function \
                  passed for it."
                 (Path.show path) (T.show (T.Function expected)))
              (L.Boolean false))
        expected.costs
  | _ ->
      if own.requires <> [] || own.costs <> [] then
        unsupported passed.span
          "a function passed for a parameter whose type the prover cannot read"

(* The type of a callee's parameter, by its position, with the call's type
   arguments. *)
and parameter_type context frame (call_ : C.call) index =
  match call_.callee with
  | Function { path; type_arguments } -> (
      match Query.demand context.database Interface.Environment.signature path with
      | Some (signature : T.signature) ->
          let types =
            (match signature.receiver with
              | Some ((Read | Mut | Own), ty) -> [ ty ]
              | Some (Static, _) | None -> [])
            @ List.map (fun (info : T.parameter_info) -> info.type_) signature.parameters
          in
          let rec pair (generics : T.generic list) arguments =
            match (generics, arguments) with
            | generic :: generics, argument :: arguments ->
                (generic.generic, T.substitute_argument frame.substitution argument)
                :: pair generics arguments
            | _ -> []
          in
          Option.map
            (T.substitute (pair signature.generics type_arguments))
            (List.nth_opt types index)
      | None -> None)
  | _ -> None

(* Whether a named function's cost clauses imply one a function type asks
   for, which can only be a constant: a constant [O(...)], or a number of
   at most, or exactly, what is asked. *)
and keeps_cost context path (contract : contract) (asked : T.cost) =
  let resource : resource option =
    match asked.resource with
    | "time" -> Some Time
    | "allocations" -> Some Allocations
    | "allocated_bytes" -> Some Allocated_bytes
    | _ -> None
  in
  let constant (value : expression) = match value.kind with Integer k -> Some k | _ -> None in
  match (resource, asked.bound) with
  | Some Time, Finite_cost -> signature_terminates context path
  | Some resource, _ -> (
      match
        List.find_map
          (fun (part : part) ->
            List.find_map
              (fun ((cost : cost), _) -> if cost.resource = resource then Some cost else None)
              part.costs)
          contract.parts
      with
      | Some cost -> (
          match (asked.bound, cost.bound) with
          | Order_of, (Big_o value | At_most value | Exactly value) -> constant value <> None
          | No_more_than (Some most), (At_most value | Exactly value) -> (
              match constant value with Some k -> Z.leq k most | None -> false)
          | Exactly_cost (Some exact), Exactly value -> constant value = Some exact
          | _ -> false)
      | None -> false)
  | None, _ -> false

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
      let built = L.Apply (constructor_name ty variant, List.map field_value fields) in
      check_built context frame written ty built;
      (frame, built)
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
      | Some (Local id) ->
          (* A later alternative's name for the binding the first one made. *)
          (L.Boolean true, { frame with locals = Ids.add id term frame.locals })
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
  | Literal literal -> (literal_condition context written literal term ty, frame)
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
      (* Each alternative binds the same names, each the part of the value
         the first alternative that matches names. *)
      let matched =
        List.map (fun alternative -> pattern_match context frame alternative term ty) alternatives
      in
      let bound =
        match matched with
        | [] -> frame.locals
        | (_, first) :: _ ->
            Ids.mapi
              (fun id _ ->
                match List.rev matched with
                | (_, last) :: earlier ->
                    List.fold_left
                      (fun otherwise (condition, (after : frame)) ->
                        match Ids.find_opt id after.locals with
                        | Some part -> L.ite condition part otherwise
                        | None -> otherwise)
                      (Ids.find id last.locals) earlier
                | [] -> Ids.find id first.locals)
              (Ids.filter
                 (fun id _ ->
                   List.for_all (fun (_, (after : frame)) -> Ids.mem id after.locals) matched)
                 first.locals)
      in
      (L.disjunction (List.map fst matched), { frame with locals = bound })
  | Pattern_error -> unsupported written.span "this pattern"

and literal_condition context (written : pattern) literal term ty =
  match literal with
  | Literal_integer value -> L.equal term (L.Integer value)
  | Literal_true -> term
  | Literal_false -> L.not_ term
  | Literal_string { tag = None; first; rest = []; _ } -> (
      (* Text matches when its bytes are the pattern's. *)
      let byte = T.builtin UInt8 in
      match model_of context ty term ~element:byte with
      | Some model ->
          L.conjunction
            (L.equal (sequence_length context byte model) (L.int (String.length first.value))
            :: List.init (String.length first.value) (fun index ->
                match sequence_at context byte model (L.int index) with
                | Some at -> L.equal at (L.int (Char.code first.value.[index]))
                | None -> L.Boolean false))
      | None -> unsupported written.span "a string pattern on `%s`" (T.show ty))
  | Literal_string _ -> unsupported written.span "a string pattern with a tag or interpolations"

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
  check_built context frame written ty term;
  Some (frame, term)

(* Type invariants. See PROVER.md, "Type invariants". *)

(* A type's invariants, and the definition to read them in. *)
and invariants_of context (ty : T.ty) =
  match ty with
  | Named { path; _ } -> (
      match Interface.Summary.definition context.database path with
      | Some (key, { kind = Type_definition { clauses; _ }; _ }) -> (
          let written =
            List.filter_map
              (fun (clause : type_clause) ->
                match clause.kind with Type_invariant value -> Some value | _ -> None)
              clauses
          in
          match written with
          | [] -> None
          | _ -> Option.map (fun source -> (source, written)) (callee_source context.database key))
      | _ -> None)
  | _ -> None

(* Whether a value meets its type's invariants, and with [deep] its
   fields' too, each read with [self] as the value. An invariant the prover
   cannot read, as one about another package's opaque fields, is no fact
   when assumed, and stops the definition when it must be shown. *)
and validity context frame ~assuming ?(deep = true) ?(seen = []) ty term =
  if List.exists (T.equal ty) seen then L.Boolean true
  else
    let own =
      match invariants_of context ty with
      | Some (source, written) -> (
          let substitution = match visible_type context ty with Some (_, s) -> s | None -> [] in
          let inner =
            {
              frame with
              source;
              locals = Ids.empty;
              old_locals = Ids.empty;
              self = Some term;
              old_self = Some term;
              self_type = Some ty;
              result = None;
              checking = false;
              loop = None;
              substitution;
            }
          in
          try
            L.conjunction (List.map (fun invariant -> snd (value context inner invariant)) written)
          with Unsupported _ | Foreign_unsupported _ when assuming -> L.Boolean true)
      | None -> L.Boolean true
    in
    let fields =
      if not deep then L.Boolean true
      else
        match constructors context ty with
        | Some shape ->
            L.conjunction
              (List.concat_map
                 (fun (variant, fields) ->
                   List.map
                     (fun (field, field_type) ->
                       let part =
                         validity context frame ~assuming ~deep ~seen:(ty :: seen) field_type
                           (L.Apply (selector_name ty variant field, [ term ]))
                       in
                       match (variant, part) with
                       | _, L.Boolean true -> part
                       | Some name_, _ ->
                           L.( ==> )
                             (L.Apply (L.tester (constructor_name ty (Some name_)), [ term ]))
                             part
                       | None, _ -> part)
                     fields)
                 shape)
        | None -> L.Boolean true
    in
    L.( &&& ) own fields

and assume_valid context frame ty term =
  assume context frame (validity context frame ~assuming:true ty term)

and check_valid context frame span ty term ~deep ~when_ =
  match validity context frame ~assuming:false ~deep ty term with
  | L.Boolean true -> ()
  | valid ->
      oblige context frame Invariant span
        (Printf.sprintf "The invariant of `%s` may not hold %s." (T.show ty) when_)
        valid

and check_built context frame (written : expression) ty term =
  check_valid context frame written.span ty term ~deep:false ~when_:"for the value built here"

and find_expression_opt (written : expression) id =
  let found = ref None in
  let rec visit (expression_ : expression) =
    if expression_.id = id then found := Some expression_
    else if !found = None then
      Syntax_walk.expression_parts ~expression:visit ~statement:(fun _ -> ()) expression_
  in
  visit written;
  !found

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
    ~lent_final ~havoc_mut ~substitution_of ~instance =
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
    | [], [] when Path.equal path context.current && structural_parameters frame own <> [] ->
        (* With no [decreases], a call on parts of the parameters ends:
           their ranks decrease, compared in the parameters' order. *)
        let pairs = structural_parameters frame own in
        let before = List.map (fun (ty, entry, _) -> rank context ty entry) pairs in
        let after =
          List.map (fun (ty, _, index) -> rank context ty (argument_at_index values index)) pairs
        in
        oblige context frame Termination written.span
          "This recursive call may not be on a part of its parameters: give the function a \
           `decreases` clause."
          L.(
            conjunction (List.map (fun b -> Apply ("<=", [ int 0; b ])) before)
            &&& smaller before after)
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
          match (place_local after expression_, is_self expression_) with
          | Some (id, _), _ ->
              Option.map (fun term -> (argument.parameter, term)) (Ids.find_opt id after.locals)
          | None, true -> Option.map (fun term -> (argument.parameter, term)) after.self
          | None, false ->
              Some
                ( argument.parameter,
                  arrive context after "changed" (argument_type frame argument expression_) )
        else None)
      values
  in
  let own_arguments = List.filter_map snd (bindings own) in
  let result =
    if
      contract.pure && contract.result_kind <> `Yields
      && List.length own_arguments = List.length values
    then begin
      let symbol = "function." ^ Path.show path ^ instance in
      declare context
        (L.Function
           ( symbol,
             List.map
               (fun ((argument : C.argument), (expression_ : expression), _) ->
                 sort_of context (argument_type frame argument expression_))
               values,
             sort_of context (substituted frame call_.result) ));
      let term = L.Apply (symbol, own_arguments) in
      assume context after (in_range (substituted frame call_.result) term);
      note_known_call context call_ path term own_arguments;
      term
    end
    else if contract.result_kind = `Yields then
      (* A cursor, of the call's own type. *)
      arrive context after "cursor" (type_of frame written)
    else arrive context after "result" (substituted frame call_.result)
  in
  if contract.result_kind <> `Yields then
    assume_valid context after (substituted frame call_.result) result;
  let helper = updating_helper context call_ in
  List.iter
    (fun ((argument : C.argument), (expression_ : expression), _) ->
      if argument.mode = T.Mut && not (helper && argument.parameter = 0) then
        match List.assoc_opt argument.parameter changed with
        | Some term -> assume_valid context after (argument_type frame argument expression_) term
        | None -> ())
    values;
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
        with Unsupported _ | Foreign_unsupported _ -> ())
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
        let ensures_frame =
          match contract.result_kind with
          | `Lends ->
              (* The part as lent, and the parts handed out: the one part, as
                 the caller's statement left it. *)
              let part_type = substituted frame call_.result in
              let left = match lent_final with Some term -> term | None -> result in
              let none = empty_parts context after part_type in
              {
                ensures_frame with
                yielded = Some (appended context after part_type none left);
                finished = Some (L.Boolean true);
              }
          | `Returns | `Yields -> ensures_frame
        in
        List.iter
          (fun (clause : expression) ->
            let frame_for_clause =
              if contract.result_kind = `Lends && mentions_result part.callee clause then
                { ensures_frame with locals = entry_locals; self = entry_self; yielded = None }
              else ensures_frame
            in
            match value context frame_for_clause clause with
            | _, term -> assume context after (L.( ==> ) required term))
          part.ensures)
      (* A yielding method's clauses are about each part it hands out and
         how it ends, which each pull of the cursor it makes meets. *)
      (if contract.result_kind = `Yields then [] else contract.parts);
    context.instantiating <- List.tl context.instantiating
  end;
  (if contract.result_kind = `Yields then
     match type_of frame written with
     | T.Cursor _ as cursor_type -> (
         match Query.demand context.database Interface.Environment.signature path with
         | Some { output = Yields (_, element); _ } ->
             let element = T.substitute (substitution_of own) element in
             let made = { method_frame = entry_frame own; own; element } in
             context.cursors <- (result, made) :: context.cursors;
             assume context after
               L.(
                 equal
                   (sequence_length context element
                      (cursor_yielded context cursor_type element result))
                   (int 0)
                 &&& not_ (cursor_ended context cursor_type result))
         | _ -> ())
     | _ -> ());
  (* What the call spends, by the callee's cost clauses, read with the
     arguments as passed and [result]. *)
  (* How much the potential of what the call changed grew: what it returns
     and leaves in [mut] arguments, less what it was given to change or to
     keep. *)
  let change () =
    List.fold_left
      (fun total ((argument : C.argument), (expression_ : expression), before) ->
        let ty = argument_type frame argument expression_ in
        match argument.mode with
        | T.Mut -> (
            match List.assoc_opt argument.parameter changed with
            | Some later ->
                Costs.plus total
                  (Costs.minus
                     (potential context after ty later)
                     (potential context frame ty before))
            | None -> total)
        | T.Own -> Costs.minus total (potential context frame ty before)
        | T.Read -> total)
      (if contract.result_kind = `Yields then Costs.zero
       else potential context after (substituted frame call_.result) result)
      values
  in
  let after =
    spend context after (fun counter ->
        match (call_.callee, counter.resource) with
        | Capability_method _, Calls _ ->
            (* A call of a capability's method is one of its calls. *)
            step_amount context after call_ values counter
        | _ ->
            callee_amount context after ~path ~parts:contract.parts
              ~bound_frame:(fun part ->
                { (entry_frame part) with result = Some result; condition = after.condition })
              ~call_ ~values ~change:(Some change) counter)
  in
  (after, result)

(* A call that running code could give a value: a function that is
   compiled and not generic, reached directly, with every argument an
   integer or [Bool] literal and a result of one of those. See PROVER.md,
   "Running code while proving". *)
and note_known_call context (call_ : C.call) path term arguments =
  let direct =
    match call_.callee with
    | Function { type_arguments = []; _ } -> true
    | Trait_method { evidence = Impl { arguments = []; _ }; type_arguments = []; _ } -> true
    | _ -> false
  in
  let literal = function
    | L.Integer value -> Some value
    | L.Boolean value -> Some (if value then Z.one else Z.zero)
    | _ -> None
  in
  let values = List.filter_map literal arguments in
  match Query.demand context.database Interface.Environment.signature path with
  | Some ({ specification_only = false; generics = []; output = Returns result; _ } : T.signature)
    when direct
         && List.length values = List.length arguments
         && (is_numeric result || is_bool result)
         && not (T.equal result T.Integer) ->
      if not (List.exists (fun (known : known_call) -> known.term = term) context.known_calls) then
        context.known_calls <-
          { function_ = path; arguments = values; term; result_is_bool = is_bool result }
          :: context.known_calls
  | _ -> ()

(* The parameters of the definition proven whose types are datatypes,
   with their values on entry and their arguments' positions. *)
and structural_parameters frame (own : part) =
  List.concat
    (List.mapi
       (fun index binding ->
         match binding with
         | Self_binding -> (
             match (frame.old_self, frame.self_type) with
             | Some entry, Some ty when is_datatype frame ty -> [ (ty, entry, index) ]
             | _ -> [])
         | Parameter_binding name_ -> (
             match (Ids.find_opt name_.id frame.old_locals, local_type frame name_.id) with
             | Some entry, Some ty when is_datatype frame ty -> [ (ty, entry, index) ]
             | _ -> []))
       own.binding)

and is_datatype frame ty =
  ignore frame;
  match ty with T.Named _ -> builtin ty = None | _ -> false

and argument_at_index values index =
  match
    List.find_map
      (fun ((argument : C.argument), _, term) ->
        if argument.parameter = index then Some term else None)
      values
  with
  | Some term -> term
  | None -> L.Boolean false

and smaller before after =
  match (before, after) with
  | [ b ], [ a ] -> L.(Apply ("<=", [ int 0; b ]) &&& Apply ("<", [ a; b ]))
  | b :: before, a :: after ->
      L.(
        Apply ("<=", [ int 0; b ])
        &&& (Apply ("<", [ a; b ]) ||| (equal a b &&& smaller before after)))
  | _ -> L.Boolean true

(* Costs: what each step spends. See PROVER.md, "Costs". *)

(* The counters a body's loops' [cost] clauses count, outside lambdas,
   which count on their own. *)
and loop_counters (source : source) locals (body : block) =
  let found = ref [] in
  let rec visit_statement (statement_ : statement) =
    (match statement_.kind with
    | While { clauses; _ } | For { clauses; _ } ->
        List.iter
          (fun (clause : loop_clause) ->
            match clause.kind with
            | Loop_cost cost -> (
                match resource_of cost ~target_of:(target_in source locals) with
                | Some resource ->
                    found := { Costs.resource; counting = counting_of cost } :: !found
                | None -> unsupported clause.span "this `calls` target")
            | _ -> ())
          clauses
    | _ -> ());
    Syntax_walk.statement_parts ~expression:visit_expression ~statement:visit_statement statement_
  and visit_expression (expression_ : expression) =
    match expression_.kind with
    | Lambda _ -> ()
    | _ ->
        Syntax_walk.expression_parts ~expression:visit_expression ~statement:visit_statement
          expression_
  in
  List.iter visit_statement body.statements;
  List.rev !found

(* Each counter, increased by what one step spends of it. *)
and spend context frame (amount : Costs.counter -> L.term) =
  if context.counters = [] then frame
  else
    {
      frame with
      spent =
        List.map
          (fun (key, term) ->
            match List.find_opt (fun counter -> Costs.key counter = key) context.counters with
            | Some counter -> (key, Costs.plus term (amount counter))
            | None -> (key, term))
          frame.spent;
    }

(* An amount nothing bounds: at least zero, or one for a call's time. *)
and unknown_amount context frame (counter : Costs.counter) =
  let amount = fresh context "spent" L.Int in
  let least = match counter.resource with Time -> 1 | _ -> 0 in
  assume context frame (L.Apply ("<=", [ L.int least; amount ]));
  amount

(* An amount from zero to [bound], for a counter that counts exactly. *)
and bounded_amount context frame bound =
  let amount = fresh context "spent" L.Int in
  assume context frame L.(Apply ("<=", [ int 0; amount ]) &&& Apply ("<=", [ amount; bound ]));
  amount

(* Whether a cost clause is about a counter's resource. A [calls] clause's
   target is read in the clause's own definition, through [target_of]. *)
and same_resource (cost : cost) ~target_of (counter : Costs.counter) =
  match (cost.resource, counter.resource) with
  | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
  | Calls written, Calls counted -> (
      match target_of written with
      | Some target -> Costs.covers ~clause:target ~counter:counted
      | None -> false)
  | _ -> false

(* What a [calls] clause counts, read in [source] with its parameters as
   [locals]. *)
and target_in (source : source) locals (written : call_target) : Costs.target option =
  match written with
  | Call_parameter name_ -> (
      match source.resolved.names.(name_.id) with
      | Some (Local id) -> Option.map (fun term -> Costs.Through term) (Ids.find_opt id locals)
      | _ -> None)
  | Call_capability path_type -> (
      match source.resolved.names.(path_type.path.last.id) with
      | Some (Definition path) -> Some (Costs.Capability path)
      | _ -> None)
  | Call_method (path_type, method_) -> (
      match source.resolved.names.(path_type.path.last.id) with
      | Some (Definition path) -> Some (Costs.Capability_method (path, method_.text))
      | _ -> None)

(* What a clause promises of a counter, in the counter's way of counting:
   [assumed] is the bound to assume for a call back into the definition
   proven, which is the induction hypothesis, and [change] is how much the
   potential of what an amortized clause's call changed grew, which it
   paid for out of its bound. *)
and promised_amount context frame (counter : Costs.counter) (bound : bound) ~evaluate ~assumed
    ~exact_target ~change =
  match (bound, counter.counting) with
  | Big_o g, Units ->
      let g = evaluate g in
      let amount =
        match assumed with
        | Some constants ->
            let hypothesis = Costs.at_least_zero (Costs.bound constants g) in
            if counter.resource = Time then Costs.plus hypothesis (L.int 1) else hypothesis
        | None -> Costs.units g
      in
      Costs.minus amount change
  | (At_most g | Exactly g), Units -> Costs.at_least_zero (Costs.minus (evaluate g) change)
  | At_most g, (At_most | Exactly) -> bounded_amount context frame (Costs.minus (evaluate g) change)
  | Exactly g, (At_most | Exactly) ->
      let g = Costs.minus (evaluate g) change in
      if exact_target then g else bounded_amount context frame g
  | (Big_o _ | Finite), _ -> unknown_amount context frame counter

(* What a call to a callee whose clauses are read spends of a counter: its
   clause about the counter's resource, from its first part that has one.
   A call back into the definition proven, through a cycle, assumes its
   [O(...)] bound with the definition's own constants; every function of a
   cycle is then proven with the first pair, so that each assumes of the
   others what they show. *)
and callee_amount context after ~path ~(parts : part list) ~(bound_frame : part -> frame)
    ~(call_ : C.call) ~values ~change (counter : Costs.counter) =
  let assumed =
    if
      counter.counting = Units
      && Call_graph.reaches context.graph ~from:path ~target:context.current
    then
      match List.assoc_opt (Costs.key counter) context.own_constants with
      | Some constants ->
          if not (Path.equal path context.current) then constants.pairs <- [ List.hd Costs.pairs ];
          Some constants
      | None -> None
    else None
  in
  let clauses_of (part : part) =
    let frame = bound_frame part in
    let target_of = target_in part.callee frame.locals in
    List.filter_map
      (fun ((cost : cost), _) ->
        if same_resource cost ~target_of counter then Some (part, frame, cost) else None)
      part.costs
  in
  let amount (_, (frame : frame), (cost : cost)) =
    let exact_target =
      match (cost.resource, counter.resource) with
      | Calls (Call_capability _), Calls (Capability_method _) -> false
      | _ -> true
    in
    match (cost.amortized, change) with
    | true, None -> unknown_amount context after counter
    | _ ->
        promised_amount context after counter cost.bound
          ~evaluate:(fun g -> snd (value context frame g))
          ~assumed ~exact_target
          ~change:
            (match (cost.amortized, change) with true, Some change -> change () | _ -> Costs.zero)
  in
  let first_clauses () =
    List.find_map (fun part -> match clauses_of part with [] -> None | found -> Some found) parts
  in
  match counter.resource with
  | Calls target when not (call_reaches context call_ values target) -> Costs.zero
  | Calls (Through term) -> (
      (* Each parameter the function value is passed for must have a
         clause about it. *)
      let receiving =
        List.filter_map
          (fun ((argument : C.argument), _, argument_term) ->
            if argument_term = term then Some argument.parameter else None)
          values
      in
      let captured =
        List.exists
          (fun (_, _, argument_term) -> lambda_captures_target context argument_term term)
          values
      in
      match first_clauses () with
      | Some found
        when (not captured) && List.length found >= List.length receiving && receiving <> [] ->
          List.fold_left (fun total clause -> Costs.plus total (amount clause)) Costs.zero found
      | _ -> unknown_amount context after counter)
  | _ -> (
      match first_clauses () with
      | Some (clause :: _) -> amount clause
      | _ -> unknown_amount context after counter)

(* Whether a call can reach a [calls] clause's target: a function value
   passed to it, or captured by a lambda passed to it, or a capability it
   uses. *)
and call_reaches context (call_ : C.call) values (target : Costs.target) =
  match target with
  | Through term ->
      List.exists
        (fun (_, _, argument_term) ->
          argument_term = term || lambda_captures_target context argument_term term)
        values
  | Capability path | Capability_method (path, _) ->
      List.exists
        (function
          | T.Capability used -> Path.equal used path
          | T.Capability_parameter parameter -> (
              match List.assoc_opt parameter call_.capability_arguments with
              | Some given -> List.mem (T.Capability path) given
              | None -> true))
        call_.uses

and lambda_captures_target context lambda target =
  match
    (List.assoc_opt lambda context.lambda_captures, List.assoc_opt target context.call_targets)
  with
  | Some captured, Some local -> List.mem local captured
  | _ -> false

(* What a call through a function value spends: its [time], which is one
   unit for a function type with an [O(...)] bound, and its type's clauses
   for other resources. *)
and function_value_amount context frame (function_type : T.function_type) callee_term
    (counter : Costs.counter) =
  let clause resource =
    List.find_opt (fun (cost : T.cost) -> cost.resource = resource) function_type.costs
  in
  let by_clause resource =
    match (clause resource, counter.counting) with
    | Some { bound = Order_of; _ }, Units -> L.int 1
    | Some { bound = No_more_than (Some k) | Exactly_cost (Some k); _ }, Units -> L.Integer k
    | Some { bound = No_more_than (Some k); _ }, (At_most | Exactly) ->
        bounded_amount context frame (L.Integer k)
    | Some { bound = Exactly_cost (Some k); _ }, (At_most | Exactly) -> L.Integer k
    | _ -> unknown_amount context frame counter
  in
  match counter.resource with
  | Time -> time_of context frame (T.Function function_type) callee_term
  | Allocations -> by_clause "allocations"
  | Allocated_bytes -> by_clause "allocated_bytes"
  | Calls (Through term) ->
      if callee_term = term then L.int 1
      else if lambda_captures_target context callee_term term then
        unknown_amount context frame counter
      else Costs.zero
  | Calls (Capability path | Capability_method (path, _)) ->
      if
        List.exists
          (function T.Capability used -> Path.equal used path | T.Capability_parameter _ -> true)
          function_type.uses
      then unknown_amount context frame counter
      else Costs.zero

(* [time(f)], the time one call through a function value takes: one unit
   when its type has an [O(...)] bound, at least one otherwise, and for a
   lambda whose calls the prover could bound, that bound. *)
and time_of context frame (ty : T.ty) term =
  let sort = sort_of context ty in
  let symbol = "time." ^ match sort with L.Uninterpreted name -> name | _ -> "value" in
  declare context (L.Function (symbol, [ sort ], L.Int));
  let time = L.Apply (symbol, [ term ]) in
  fact context frame (L.Apply ("<=", [ L.int 1; time ]));
  (match ty with
  | T.Function { costs; _ }
    when List.exists (fun (cost : T.cost) -> cost.resource = "time" && cost.bound = Order_of) costs
    ->
      fact context frame (L.equal time (L.int 1))
  | _ -> ());
  (match List.assoc_opt term context.lambda_times with
  | Some (bound, showing) ->
      (* The bound is used, so the obligations that show it are made. *)
      context.lambda_times <- List.remove_assoc term context.lambda_times;
      context.obligations <- List.rev_append showing context.obligations;
      fact context frame (L.equal time (Costs.larger (L.int 1) bound))
  | None -> ());
  time

(* What a step that is not a call to a definition spends. *)
and step_amount context frame (call_ : C.call) values (counter : Costs.counter) =
  match call_.callee with
  | Constructor { variant; _ } -> (
      let ty = substituted frame call_.result in
      match counter.resource with
      | (Allocations | Allocated_bytes) when not (indirect context ty variant) -> Costs.zero
      | Allocations -> L.int 1
      | Allocated_bytes when counter.counting = Units -> L.int 1
      | Allocated_bytes ->
          (* The size of the variant's block, which is fixed and not known
             here. *)
          let symbol = "bytes." ^ type_key ty ^ "." ^ Option.value variant ~default:"record" in
          declare context (L.Constant (symbol, L.Int));
          fact context frame (L.Apply ("<=", [ L.int 1; L.Symbol symbol ]));
          L.Symbol symbol
      | Time | Calls _ -> Costs.zero)
  | Intrinsic { operation; _ } -> (
      let cost = Intrinsic_signatures.cost operation in
      match counter.resource with
      | Time -> if cost.constant_time then Costs.zero else unknown_amount context frame counter
      | Allocations | Allocated_bytes ->
          if cost.allocation_free then Costs.zero else unknown_amount context frame counter
      | Calls _ -> Costs.zero)
  | Built_in_operator -> Costs.zero
  | Capability_method { capability; name } -> (
      let direct =
        match counter.resource with
        | Calls (Capability path) when Path.equal path capability -> L.int 1
        | Calls (Capability_method (path, method_))
          when Path.equal path capability && method_ = name ->
            L.int 1
        | _ -> Costs.zero
      in
      match counter.resource with
      | Calls _ -> direct
      | _ -> (
          match capability_part context.database capability name with
          | Some (part, _) ->
              let inside =
                part_frame frame part
                  ~arguments:
                    (List.map
                       (fun ((argument : C.argument), _, term) -> (argument.parameter, term))
                       values)
                  ~substitution:[]
              in
              callee_amount context frame
                ~path:(Path.Method { owner = capability; name; receiver = Static })
                ~parts:[ part ]
                ~bound_frame:(fun _ -> inside)
                ~call_ ~values ~change:None counter
          | None -> unknown_amount context frame counter))
  | Function _ | Trait_method _ | Function_value -> (
      (* A call whose contract is not read. *)
      match counter.resource with
      | Calls target when not (call_reaches context call_ values target) -> Costs.zero
      | _ -> unknown_amount context frame counter)

and indirect context (ty : T.ty) variant =
  match (ty, variant) with
  | Named { path; _ }, Some variant -> (
      match Query.demand context.database Interface.Environment.interface path with
      | Some (Interface.Environment.Type_interface { shape = Sum variants; _ }) ->
          List.exists
            (fun (written : T.variant) -> written.variant_name = variant && written.indirect)
            variants
      | _ -> false)
  | _ -> false

(* [log(n)], [power(b, e)], and [time(f)] in a cost bound. *)
and cost_function context frame (written : expression) kind (arguments : argument list) =
  let argument_values =
    List.map (fun (argument : argument) -> snd (value context frame argument.value)) arguments
  in
  match (kind, argument_values, arguments) with
  | Resolve.Log, [ n ], _ -> Some (frame, log_of context frame n)
  | Power, [ base; exponent ], _ -> Some (frame, power_of context frame base exponent)
  | Time, [ f ], [ { value = function_value; _ } ] ->
      Some (frame, time_of context frame (type_of frame function_value) f)
  | _ -> unsupported written.span "this cost function"

and log_of context frame n =
  declare context (L.Function (Costs.log_symbol, [ L.Int ], L.Int));
  let rec add n ~halving =
    match List.assoc_opt n context.logs with
    | Some true -> ()
    | Some false when not halving -> ()
    | seen ->
        if seen = None then
          List.iter (fun (other, _) -> fact context frame (Costs.log_order n other)) context.logs;
        context.logs <- (n, halving) :: List.remove_assoc n context.logs;
        let facts, half = Costs.log_facts n ~halving in
        List.iter (fact context frame) facts;
        Option.iter (fun half -> add half ~halving:false) half
  in
  if not (L.mentions frame.bound n) then add n ~halving:true;
  L.Apply (Costs.log_symbol, [ n ])

and power_of context frame base exponent =
  declare context (L.Function (Costs.power_symbol, [ L.Int; L.Int ], L.Int));
  let add exponent =
    if not (List.mem (base, exponent) context.powers) then begin
      List.iter
        (fun (other_base, other) ->
          if other_base = base then fact context frame (Costs.power_order base exponent other))
        context.powers;
      context.powers <- (base, exponent) :: context.powers;
      let facts, step = Costs.power_facts base exponent in
      List.iter (fact context frame) facts;
      Some step
    end
    else None
  in
  (if not (L.mentions frame.bound base || L.mentions frame.bound exponent) then
     match add exponent with
     | Some (step, previous) ->
         fact context frame step;
         ignore (add previous)
     | None -> ());
  L.Apply (Costs.power_symbol, [ base; exponent ])

(* Loops' costs. A loop with a [cost] clause about a counter is bounded by
   it: what the loop has spent so far is within the clause at its head, on
   entry and after each iteration, and after the loop, the loop counts as
   the clause, as a call with that bound would. Any other counter is
   bounded by the loop's iterations so far times a bound on one iteration,
   [per], which is worked out from what the body spends and then shown of
   each iteration.

   Where the values a loop changes hold potential, which amortized callees
   spend and save, a second bound, [per_held], is about what the loop has
   spent plus the potential it holds, which is what telescopes when each
   iteration spends potential earlier ones saved. Both are assumed at the
   head, and are sound to assume even unbounded, since each run of the loop
   has a largest iteration; only the one that what an iteration spends
   calls for is worked out and shown. [held] is the potential of the values
   the loop changes, in a frame. *)
and loop_costs context frame (clauses : loop_clause list) ~held =
  List.map
    (fun (counter : Costs.counter) ->
      let key = Costs.key counter in
      let entry =
        match List.assoc_opt key frame.spent with Some term -> term | None -> Costs.zero
      in
      let written =
        List.find_map
          (fun (clause : loop_clause) ->
            match clause.kind with
            | Loop_cost cost
              when same_resource cost ~target_of:(target_in frame.source frame.locals) counter
                   && counting_of cost = counter.counting ->
                Some (clause, cost)
            | _ -> None)
          clauses
      in
      let rule =
        match written with
        | Some (clause, cost) ->
            let constants =
              match counter.counting with
              | Units ->
                  let constants = Costs.constants (Printf.sprintf "loop.%d" clause.id) in
                  context.groups <- constants :: context.groups;
                  declare context (L.Constant (constants.factor, L.Int));
                  declare context (L.Constant (constants.addend, L.Int));
                  Some constants
              | At_most | Exactly -> None
            in
            Clause_bound (clause, cost, constants)
        | None ->
            Per_iteration
              {
                per = fresh context "per" L.Int;
                per_held = Option.map (fun held -> (fresh context "per" L.Int, held frame)) held;
              }
      in
      { counter; key; entry; rule; held })
    context.counters

and counting_of (cost : cost) : Costs.counting =
  match cost.bound with Big_o _ | Finite -> Units | At_most _ -> At_most | Exactly _ -> Exactly

(* A loop's [cost] clause, about what the loop has spent so far, at [at]. *)
and loop_clause_holds context (at : frame) (counter : Costs.counter) (cost : cost) constants ~since
    =
  let g =
    match cost.bound with
    | Big_o g | At_most g | Exactly g -> snd (value context { at with checking = false } g)
    | Finite -> Costs.zero
  in
  match (counter.counting, constants) with
  | Units, Some constants -> Costs.at_most since (Costs.bound constants g)
  | Exactly, _ -> L.equal since g
  | _ -> Costs.at_most since g

and spent_at (frame : frame) key =
  match List.assoc_opt key frame.spent with Some t -> t | None -> Costs.zero

(* What a counter is bounded by at the head and where the loop is left:
   its value, plus the potential the loop holds there, for [per_held]. *)
and counted_with ~(counter : Costs.counter) ~at ~bound =
  if counter.counting = Exactly then L.equal at bound else Costs.at_most at bound

(* The head of a loop: each counter takes a fresh value, within its
   clause, or within its iterations so far times its bounds on one. *)
and loop_head context head costs ~iterations =
  let iterations = Option.value iterations ~default:Costs.zero in
  let head =
    { head with spent = List.map (fun cost -> (cost.key, fresh context "spent" L.Int)) costs }
  in
  List.iter
    (fun cost ->
      let at_head = spent_at head cost.key in
      match cost.rule with
      | Clause_bound (_, written, constants) ->
          assume context head
            (loop_clause_holds context head cost.counter written constants
               ~since:(Costs.minus at_head cost.entry))
      | Per_iteration { per; per_held } -> (
          assume context head
            (counted_with ~counter:cost.counter ~at:at_head
               ~bound:(Costs.plus cost.entry (Costs.times iterations per)));
          match (per_held, cost.held) with
          | Some (per_held, on_entry), Some held ->
              assume context head
                (counted_with ~counter:cost.counter
                   ~at:(Costs.plus at_head (held head))
                   ~bound:
                     (Costs.plus (Costs.plus cost.entry on_entry) (Costs.times iterations per_held)))
          | _ -> ()))
    costs;
  head

(* Each [cost] clause on entry to the loop, when nothing is spent yet. *)
and loop_entry context frame costs =
  List.iter
    (fun cost ->
      match cost.rule with
      | Clause_bound ((clause : loop_clause), written, constants) ->
          oblige context frame Cost clause.span
            (Printf.sprintf "The loop's `%s` may not hold on entry to the loop."
               (quote frame.source clause.span))
            (loop_clause_holds context frame cost.counter written constants ~since:Costs.zero)
      | Per_iteration _ -> ())
    costs

(* Whether a term mentions what a value's potential is. *)
and mentions_potential term =
  let rec walk = function
    | L.Apply (name, arguments) ->
        String.starts_with ~prefix:"potential." name || List.exists walk arguments
    | L.Forall (_, body) | L.Exists (_, body) -> walk body
    | L.Symbol _ | L.Integer _ | L.Boolean _ | L.Bits _ -> false
  in
  walk term

(* After the body: each bound on one iteration is worked out from what the
   iterations that ended spent, and every iteration, ended or left by
   [break], is shown to be within its counter's bound. An iteration that
   spends or saves potential is bounded with the potential the loop
   holds. *)
and loop_iterations context (written : statement) head costs ~mark ~facts ~ends ~breaks =
  List.iter
    (fun cost ->
      match cost.rule with
      | Clause_bound ((clause : loop_clause), written_cost, constants) ->
          List.iter
            (fun (frame, when_) ->
              oblige context frame Cost clause.span
                (Printf.sprintf "The loop's `%s` may not hold %s." (quote frame.source clause.span)
                   when_)
                (loop_clause_holds context frame cost.counter written_cost constants
                   ~since:(Costs.minus (spent_at frame cost.key) cost.entry)))
            (List.map (fun f -> (f, "after an iteration")) ends
            @ List.map (fun f -> (f, "where the loop is left")) breaks)
      | Per_iteration { per; per_held } -> (
          let frames = ends @ breaks in
          let plain (frame : frame) =
            Costs.since ~start:(spent_at head cost.key) (spent_at frame cost.key)
          in
          let per, spent_in =
            match (per_held, cost.held) with
            | Some (per_held, _), Some held
              when List.exists (fun f -> mentions_potential (plain f)) frames ->
                ( per_held,
                  fun (frame : frame) ->
                    Costs.normalize
                      (Costs.plus (plain frame) (Costs.minus (held frame) (held head))) )
            | _ -> (per, plain)
          in
          let spent = List.map spent_in frames in
          let most =
            match spent with
            | [] -> Costs.zero
            | first :: rest -> List.fold_left Costs.larger first rest
          in
          let facts = facts @ List.map (fun (frame : frame) -> frame.condition) frames in
          match Costs.bound_on ~varies:(made_since context mark) ~facts most with
          | Some bound ->
              fact context head (L.equal per bound);
              List.iter2
                (fun (frame : frame) spent ->
                  oblige context frame Cost written.span
                    "The prover cannot show that this iteration of the loop spends no more than \
                     the bound it found for every iteration from what the loop does not change: \
                     give the loop a `cost` clause."
                    (counted_with ~counter:cost.counter ~at:spent ~bound:per))
                frames spent
          | None ->
              oblige context head Cost written.span
                "The prover cannot bound what one iteration of this loop spends by what the loop \
                 does not change, so it cannot count the loop's cost: give the loop a `cost` \
                 clause."
                (L.Boolean false)))
    costs

(* Where the loop is left: a counter bounded by a clause counts as the
   clause, and one bounded by its iterations is also bounded by each upper
   bound [most] on them, which is arithmetic, so assumed. *)
and loop_exit context (exit_ : frame) costs ~iterations ~most =
  let iterations = Option.value iterations ~default:Costs.zero in
  let spent =
    List.map
      (fun cost ->
        let at = spent_at exit_ cost.key in
        match cost.rule with
        | Clause_bound (_, (written : cost), _) ->
            let g =
              match written.bound with
              | Big_o g | At_most g | Exactly g ->
                  snd (value context { exit_ with checking = false } g)
              | Finite -> Costs.zero
            in
            let counted =
              match cost.counter.counting with
              | Units -> Costs.units g
              | At_most -> bounded_amount context exit_ g
              | Exactly -> g
            in
            (cost.key, Costs.plus cost.entry counted)
        | Per_iteration { per; per_held } ->
            let bounded ~at ~start per =
              if cost.counter.counting <> Exactly then
                List.iter
                  (fun most ->
                    fact context exit_
                      L.(
                        conjunction
                          [
                            Costs.at_most at (Costs.plus start (Costs.times iterations per));
                            Apply ("<=", [ int 0; iterations ]);
                            Apply ("<=", [ iterations; most ]);
                            Apply ("<=", [ int 0; per ]);
                          ]
                        ==> Costs.at_most at (Costs.plus start (Costs.times most per))))
                  most
            in
            bounded ~at ~start:cost.entry per;
            (match (per_held, cost.held) with
            | Some (per_held, on_entry), Some held ->
                bounded
                  ~at:(Costs.plus at (held exit_))
                  ~start:(Costs.plus cost.entry on_entry) per_held
            | _ -> ());
            (cost.key, at))
      costs
  in
  { exit_ with spent }

(* The potential held by the values of some locals, in a frame, or nothing
   when none of their types can hold any. *)
and held_by context (frame : frame) (changed : changed) =
  let typed =
    List.filter_map
      (fun id -> Option.map (fun ty -> (`Local id, ty)) (local_type frame id))
      changed.changed_locals
    @
    match (changed.changes_self, frame.self_type) with
    | true, Some ty -> [ (`Self, ty) ]
    | _ -> []
  in
  if not (List.exists (fun (_, ty) -> has_potential context ty) typed) then None
  else
    Some
      (fun (frame : frame) ->
        List.fold_left
          (fun total (place, ty) ->
            match (place, frame.self) with
            | `Local id, _ -> (
                match Ids.find_opt id frame.locals with
                | Some term -> Costs.plus total (potential context frame ty term)
                | None -> total)
            | `Self, Some self -> Costs.plus total (potential context frame ty self)
            | `Self, None -> total)
          Costs.zero typed)

(* Potentials. See PROVER.md, "Amortized bounds". *)

(* A type's own [cost potential], from its definition. *)
and potential_clause context (ty : T.ty) =
  match ty with
  | Named { path; _ } -> (
      match Interface.Summary.definition context.database path with
      | Some (key, { kind = Type_definition { clauses; _ }; _ }) -> (
          match
            List.find_map
              (fun (clause : type_clause) ->
                match clause.kind with Potential value -> Some value | _ -> None)
              clauses
          with
          | Some value ->
              Option.map (fun source -> (source, value)) (callee_source context.database key)
          | None -> None)
      | _ -> None)
  | _ -> None

(* Whether a value of a type can hold potential: its type declares one, or
   a part of it can, whether or not this package sees its fields. A type
   parameter may stand for such a type. The elements of a built-in
   collection holding potential is not read yet. *)
and has_potential context ?(seen = []) (ty : T.ty) =
  if List.exists (T.equal ty) seen then false
  else
    match ty with
    | Parameter _ -> true
    | Named { path; arguments } when builtin ty = None -> (
        potential_clause context ty <> None
        ||
        match Query.demand context.database Interface.Environment.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            let substitution =
              try
                List.combine
                  (List.map (fun (generic : T.generic) -> generic.generic) interface.type_generics)
                  arguments
              with Invalid_argument _ -> []
            in
            let fields =
              match interface.shape with
              | Record fields -> fields
              | Sum variants ->
                  List.concat_map
                    (fun (variant : T.variant) -> Option.value variant.fields ~default:[])
                    variants
              | Todo_type | Builtin_type _ | Error_shape -> []
            in
            List.exists
              (fun (field : T.field) ->
                has_potential context ~seen:(ty :: seen)
                  (T.substitute substitution field.field_type))
              fields
        | _ -> false)
    | Named { arguments; _ } ->
        if
          List.exists
            (function
              | T.Type element -> has_potential context ~seen:(ty :: seen) element | _ -> false)
            arguments
        then raise (Foreign_unsupported "the potential of a collection's elements")
        else false
    | _ -> false

(* The potential a value holds: a function of it in the logic, at least
   zero for a valid value, as each type with a potential shows, and its
   type's own potential plus its parts', unfolded once for each value it is
   asked of. *)
and potential context frame (ty : T.ty) term =
  if not (has_potential context ty) then Costs.zero
  else begin
    let held = held_symbol context ty term in
    if (not (List.mem held context.potentials)) && not (L.mentions frame.bound term) then begin
      context.potentials <- held :: context.potentials;
      fact context frame
        L.(validity context frame ~assuming:true ty term ==> Apply ("<=", [ int 0; held ]));
      match (potential_clause context ty, constructors context ty) with
      | Some (source, written), Some shape -> (
          let substitution = match visible_type context ty with Some (_, s) -> s | None -> [] in
          let inner =
            {
              frame with
              source;
              locals = Ids.empty;
              old_locals = Ids.empty;
              self = Some term;
              old_self = Some term;
              self_type = Some ty;
              result = None;
              checking = false;
              loop = None;
              substitution;
            }
          in
          try
            let own = snd (value context inner written) in
            let parts (variant, fields) =
              List.fold_left
                (fun total (field, field_type) ->
                  if has_potential context field_type then
                    Costs.plus total
                      (held_symbol context field_type
                         (L.Apply (selector_name ty variant field, [ term ])))
                  else total)
                Costs.zero fields
            in
            let parts =
              match shape with
              | [ (None, fields) ] -> parts (None, fields)
              | variants -> (
                  match List.rev variants with
                  | last :: earlier ->
                      List.fold_left
                        (fun otherwise ((variant, _) as one) ->
                          L.ite
                            (L.Apply (L.tester (constructor_name ty variant), [ term ]))
                            (parts one) otherwise)
                        (parts last) earlier
                  | [] -> Costs.zero)
            in
            fact context frame (L.equal held (Costs.plus own parts))
          with Unsupported _ | Foreign_unsupported _ -> ())
      | _ -> ()
    end;
    held
  end

and held_symbol context ty term =
  let symbol = "potential." ^ type_key ty in
  declare context (L.Function (symbol, [ sort_of context ty ], L.Int));
  L.Apply (symbol, [ term ])

(* The facts since a mark in the list, which is kept reversed. *)
and facts_since context count =
  let rec take n list =
    if n <= 0 then [] else match list with [] -> [] | x :: rest -> x :: take (n - 1) rest
  in
  take (List.length context.facts - count) context.facts

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
  if frame.source.key = context.home then
    try statement_kind context frame written
    with Foreign_unsupported message -> raise (Unsupported (written.span, message))
  else statement_kind context frame written

and statement_kind context frame (written : statement) : frame option =
  match written.kind with
  | Expression value_ -> Option.map fst (expression context frame value_)
  | Let { pattern; value = initial; else_ = None; _ } -> (
      match expression context frame initial with
      | None -> None
      | Some (frame, term) ->
          (* A [let]'s pattern cannot fail, so only its names matter. *)
          let _, frame = pattern_match context frame pattern term (type_of frame initial) in
          Some frame)
  | Let { pattern; value = initial; else_ = Some otherwise; _ } -> (
      (* The pattern may fail, and the [else] block, which must leave the
         path, runs where it does. *)
      match expression context frame initial with
      | None -> None
      | Some (frame, term) -> (
          let matched, bound = pattern_match context frame pattern term (type_of frame initial) in
          match block_value context (restrict frame (L.not_ matched)) otherwise with
          | Some (fallen, _) ->
              oblige context fallen Unreachable otherwise.span
                "This `else` block may finish, but it must leave the path, since the pattern did \
                 not match."
                (L.Boolean false);
              Some (restrict bound matched)
          | None -> Some (restrict bound matched)))
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
      let proving = context.proving in
      context.proving <- true;
      let after = block_value context frame block_ in
      context.proving <- proving;
      match after with
      | Some (after, _) -> Some { frame with locals = after.locals; condition = after.condition }
      | None -> None)
  | Parallel block_ ->
      (* Branches are disjoint, so they can run in order. *)
      List.fold_left
        (fun frame branch ->
          match frame with Some frame -> statement context frame branch | None -> None)
        (Some frame) block_.statements
  | Yield handed -> handing_out context frame written handed
  | Statement_error -> unsupported written.span "this statement"

and is_test context = match context.current with Path.Test _ -> true | _ -> false

(* A [yield] in a lending or yielding method's own body: the part meets
   the clauses about each part; a [mut] part comes back as the caller left
   it, which is any value of its type; and a yielding method may end here,
   if a loop stops it, so its other clauses and [self]'s invariant hold. *)
and handing_out context frame (written : statement) handed =
  match (context.hands_out, context.handing, frame.handed_out) with
  | Some (part_type, kind), Some (each, at_end), Some before ->
      let frame, part = value context frame handed in
      let show clauses ~at ~result ~yielded ~finished ~when_ =
        List.iter
          (fun (clause : expression) ->
            let _, term =
              value context
                { at with result; yielded = Some yielded; finished; checking = false }
                clause
            in
            oblige context at Ensures clause.span
              (Printf.sprintf "`%s` may not hold %s." (quote at.source clause.span) when_)
              term)
          clauses
      in
      show each ~at:frame ~result:(Some part) ~yielded:before ~finished:None
        ~when_:"for the part handed out here";
      let frame, part_after =
        match handed.kind with
        | Mode (Mut, place) ->
            let frame = havoc_root context frame place in
            value context frame place
        | _ -> (frame, part)
      in
      let after = appended context frame part_type before part_after in
      let frame = { frame with handed_out = Some after } in
      if kind = `Yields then begin
        show at_end ~at:frame ~result:None ~yielded:after ~finished:(Some (L.Boolean false))
          ~when_:"at this `yield`, where a loop may stop the method";
        match (frame.self, frame.self_type) with
        | Some self, Some self_type ->
            check_valid context frame written.span self_type self ~deep:true
              ~when_:"for `self` at this `yield`, where a loop may stop the method"
        | _ -> ()
      end;
      Some frame
  | _ -> unsupported written.span "`yield` outside a lending or yielding method's body"

(* The local or [self] a place is part of. *)
and root_of (place : expression) =
  match place.kind with
  | Mode (_, inner) | Parenthesized inner | Member (inner, _) | Bracket (inner, _) -> root_of inner
  | _ -> place

and is_self (expression_ : expression) =
  match expression_.kind with
  | Mode (_, inner) | Parenthesized inner -> is_self inner
  | Self_value -> true
  | _ -> false

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
  | Bracket _ -> (
      (* An element is stored through the collection's [lends mut] index,
         whose contract says how the collection takes the element back. *)
      match source.checked.calls.(place.id) with
      | Some ({ callee = Trait_method method_; arguments = receiver :: rest; _ } as recorded) -> (
          let lend_mut =
            {
              recorded with
              callee = Trait_method { method_ with receiver = Mut };
              arguments = { receiver with mode = T.Mut } :: rest;
            }
          in
          match resolved_call ~lent_final:new_value context frame place lend_mut with
          | Some (after, _) -> after
          | None -> havoc_root context frame place)
      | _ -> havoc_root context frame place)
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
        if float_format ty <> None then
          let combined =
            match binary_operator with
            | Add -> float_operation "fp.add" current right
            | Subtract -> float_operation "fp.sub" current right
            | Multiply -> float_operation "fp.mul" current right
            | Divide -> float_operation "fp.div" current right
            | _ -> arrive context frame "operator" ty
          in
          (frame, combined)
        else if not (is_numeric ty) then (
          ignore source;
          (frame, arrive context frame "operator" ty))
        else
          begin match binary_operator with
          | Add | Subtract | Multiply | Divide | Remainder ->
              ( frame,
                arithmetic context frame
                  { target with span = written.span }
                  ty binary_operator current right )
          | Bit_and -> (frame, opaque_operation context frame ty "and" [ current; right ])
          | Bit_or -> (frame, opaque_operation context frame ty "or" [ current; right ])
          | Bit_xor -> (frame, opaque_operation context frame ty "xor" [ current; right ])
          | Shift_left | Shift_right ->
              (match width ty with
              | Some bits ->
                  oblige context frame Shift assigned.span
                    (Printf.sprintf "The shift amount `%s` may not be less than %d."
                       (quote source assigned.span) bits)
                    L.(Apply ("<", [ right; int bits ]))
              | None -> unsupported written.span "a shift of `%s`" (T.show ty));
              ( frame,
                opaque_operation context frame ty
                  (if binary_operator = Shift_left then "shift_left" else "shift_right")
                  [ current; right ] )
          | _ -> (frame, opaque_operation context frame ty "assignment" [ current; right ])
          end
  in
  (* Storing into an element checks its index, through the [lends mut]
     call. *)
  Some (store context frame target new_value)

(* What a loop's body may change, which is havocked at its head: the local
   or [self] that each place it assigns to, passes [mut], or loops over
   [mut] is part of. A call passes a place [mut] however it is written,
   [f(mut items)] or [mut items.push(value)], as the type checker recorded
   its arguments. *)
and changed_places frame (body : block) : changed =
  let locals = ref [] and self = ref false in
  let source = frame.source in
  let note (place : expression) =
    let root = root_of place in
    match root.kind with
    | Self_value -> self := true
    | _ -> (
        match place_local frame root with Some (id, _) -> locals := id :: !locals | None -> ())
  in
  let rec visit_statement (statement_ : statement) =
    (match statement_.kind with
    | Assignment { target; _ } -> note target
    | For { iterable; _ } -> (
        match source.checked.loops.(statement_.id) with
        | Some (Yielding { mode = T.Mut; _ }) -> note iterable
        | _ -> ())
    | _ -> ());
    Syntax_walk.statement_parts ~expression:visit_expression ~statement:visit_statement statement_
  and visit_expression (expression_ : expression) =
    (match expression_.kind with Mode (Mut, inner) -> note inner | _ -> ());
    (match source.checked.calls.(expression_.id) with
    | Some call_ ->
        List.iter
          (fun (argument : C.argument) ->
            if argument.mode = T.Mut then
              match find_expression_opt expression_ argument.expression with
              | Some passed -> note passed
              | None -> ())
          call_.arguments
    | None -> ());
    Syntax_walk.expression_parts ~expression:visit_expression ~statement:visit_statement expression_
  in
  List.iter visit_statement body.statements;
  {
    changed_locals =
      List.sort_uniq compare (List.filter (fun id -> Ids.mem id frame.locals) !locals);
    changes_self = !self && frame.self <> None;
  }

and havoc context frame (changed : changed) =
  let frame =
    List.fold_left
      (fun frame id ->
        let ty = match local_type frame id with Some ty -> ty | None -> T.Integer in
        { frame with locals = Ids.add id (arrive context frame "loop" ty) frame.locals })
      frame changed.changed_locals
  in
  match (changed.changes_self, frame.self_type) with
  | true, Some ty -> { frame with self = Some (arrive context frame "loop" ty) }
  | _ -> frame

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

and while_ context frame (written : statement) condition clauses body =
  check_invariants context frame clauses ~when_:"on entry to the loop";
  let changed = changed_places frame body in
  let costs = loop_costs context frame clauses ~held:(held_by context frame changed) in
  loop_entry context frame costs;
  let mark = context.fresh and facts_mark = List.length context.facts in
  let head = havoc context frame changed in
  let head =
    if contains_yield body then { head with handed_out = havoc_parts context head } else head
  in
  let iterations = iterations_so_far context head costs in
  let head = loop_head context head costs ~iterations in
  assume_invariants context head clauses;
  let head, test = value context head condition in
  let exits = { breaks = []; continues = [] } in
  let inside = { (restrict head test) with loop = Some exits } in
  let inside = spend context inside one_step in
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
  (* With one measure, which every iteration shows to start at or above
     zero and to decrease, the loop runs at most one more time than the
     measure on entry. A ghost [last] is the measure at the start of the
     latest iteration. *)
  let most =
    match (start_measures, measure_terms frame, iterations) with
    | Some [ at_head ], Some [ on_entry ], Some iterations ->
        let last = fresh context "last" L.Int in
        assume context head
          L.(
            equal iterations (int 0)
            ==> Apply ("<=", [ at_head; on_entry ])
            &&& (Apply (">=", [ iterations; int 1 ])
                ==> (Apply ("<=", [ int 0; last ])
                    &&& Apply
                          ( "<=",
                            [ Apply ("+", [ Apply ("-", [ iterations; int 1 ]); last ]); on_entry ]
                          )
                    &&& Apply ("<", [ at_head; last ]))));
        [ Costs.at_least_zero (Costs.plus on_entry (L.int 1)) ]
    | _ -> []
  in
  let finished = block_value context inside body in
  let ends = (match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues in
  loop_iterations context written head costs ~mark
    ~facts:(facts_since context facts_mark @ [ inside.condition ])
    ~ends ~breaks:exits.breaks;
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
  let exit_ =
    loop_exit context
      { (restrict head (L.not_ test)) with loop = frame.loop }
      costs ~iterations ~most
  in
  let left =
    List.map
      (fun (frame' : frame) ->
        loop_exit context { frame' with loop = frame.loop } costs
          ~iterations:(Option.map (fun n -> Costs.plus n (L.int 1)) iterations)
          ~most)
      exits.breaks
  in
  join_frames context (exit_ :: left)
  |> Option.map (fun (joined : frame) ->
      { joined with locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) joined.locals })

(* A ghost count of a loop's iterations so far, when the loop counts a
   cost by them. *)
and iterations_so_far context head costs =
  if
    List.exists
      (fun (cost : loop_cost) ->
        match cost.rule with Per_iteration _ -> true | Clause_bound _ -> false)
      costs
  then begin
    let iterations = fresh context "iterations" L.Int in
    assume context head (L.Apply ("<=", [ L.int 0; iterations ]));
    Some iterations
  end
  else None

and one_step (counter : Costs.counter) =
  match counter.resource with Time -> L.int 1 | _ -> Costs.zero

and for_ context frame (written : statement) pattern iterable clauses body =
  match (frame.source.checked.loops.(written.id), iterable.kind, pattern.kind) with
  | ( Some (Integer_range { element; inclusive }),
      Range { start = Some start; stop = Some stop; _ },
      (Binding_or_constant _ | Wildcard) ) ->
      let element = substituted frame element in
      let frame, low = value context frame start in
      let frame, high = value context frame stop in
      let outer_yielded = frame.yielded in
      check_invariants context
        { frame with yielded = Some (empty_parts context frame element) }
        clauses ~when_:"on entry to the loop";
      let changed = changed_places frame body in
      let costs = loop_costs context frame clauses ~held:(held_by context frame changed) in
      loop_entry context frame costs;
      let mark = context.fresh and facts_mark = List.length context.facts in
      let head = havoc context frame changed in
      let head =
        if contains_yield body then { head with handed_out = havoc_parts context head } else head
      in
      (* The [n]th iteration, from 0, has the index [low + n]. *)
      let count =
        Costs.normalize
          (if inclusive then Costs.plus (Costs.minus high low) (L.int 1) else Costs.minus high low)
      in
      let iterations = fresh context "iterations" L.Int in
      assume context head
        L.(
          Apply ("<=", [ int 0; iterations ])
          &&& Apply ("<=", [ iterations; Costs.at_least_zero count ]));
      (* [yielded] is the indexes so far, from [low] up. *)
      let before = some_parts context head element in
      assume context head (L.equal (sequence_length context element before) iterations);
      (context.fresh <- context.fresh + 1;
       let position = Printf.sprintf "index.%d" context.fresh in
       match sequence_at context element before (L.Symbol position) with
       | Some at ->
           assume context head
             (L.Forall
                ( [ (position, L.Int) ],
                  L.(
                    Apply ("<=", [ int 0; Symbol position ])
                    &&& Apply ("<", [ Symbol position; iterations ])
                    ==> equal at (Apply ("+", [ low; Symbol position ]))) ))
       | None -> ());
      let head =
        loop_head context { head with yielded = Some before } costs ~iterations:(Some iterations)
      in
      assume_invariants context head clauses;
      let index = Costs.plus low iterations in
      let exits = { breaks = []; continues = [] } in
      let inside =
        { (restrict head (L.Apply ("<", [ iterations; count ]))) with loop = Some exits }
      in
      let through = appended context inside element before index in
      let inside = { inside with yielded = outer_yielded } in
      let inside = spend context inside one_step in
      let inside =
        match pattern.kind with
        | Binding_or_constant name_ -> { inside with locals = Ids.add name_.id index inside.locals }
        | _ -> inside
      in
      let finished = block_value context inside body in
      let ends =
        (match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues
      in
      let with_through (f : frame) = { f with loop = frame.loop; yielded = Some through } in
      loop_iterations context written head costs ~mark
        ~facts:(facts_since context facts_mark @ [ inside.condition ])
        ~ends:(List.map with_through ends)
        ~breaks:(List.map with_through exits.breaks);
      List.iter
        (fun (end_ : frame) ->
          check_invariants context (with_through end_) clauses ~when_:"after an iteration")
        ends;
      let most = [ Costs.at_least_zero count ] in
      let exit_ =
        loop_exit context
          { (restrict head (L.Apply (">=", [ iterations; count ]))) with loop = frame.loop }
          costs ~iterations:(Some iterations) ~most
      in
      let left =
        List.map
          (fun (f : frame) ->
            loop_exit context (with_through f) costs
              ~iterations:(Some (Costs.plus iterations (L.int 1)))
              ~most)
          exits.breaks
      in
      join_frames context
        (List.map (fun (f : frame) -> { f with yielded = outer_yielded }) (exit_ :: left))
      |> Option.map (fun (joined : frame) ->
          { joined with locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) joined.locals })
  | Some (Yielding { call = driven; mode }), _, _ ->
      each_loop context frame written pattern iterable clauses body driven mode
  | Some (Pulled { cursor = T.Cursor { method_; _ } as cursor_type }), _, _ ->
      pulled_loop context frame written pattern iterable clauses body
        ~cursor_type:(substituted frame cursor_type) ~method_
  | Some (Pulled { cursor = cursor_type }), _, _ ->
      own_cursor_loop context frame written pattern iterable clauses body
        ~cursor_type:(substituted frame cursor_type)
  | _ -> unsupported written.span "this `for` loop"

(* A [for] loop over a yielding method: each element is a fresh value
   that meets the method's clauses for each part, and the loop ends when
   the method has a [time] clause. *)
and each_loop context frame (written : statement) pattern iterable clauses body (driven : C.call)
    mode =
  let source = frame.source in
  let frame, arguments =
    List.fold_left
      (fun (frame, arguments) (argument : C.argument) ->
        let frame, term = value context frame (find_expression iterable argument.expression) in
        (frame, (argument.parameter, term) :: arguments))
      (frame, []) driven.arguments
  in
  (* An implicit [each] takes the loop's collection as its receiver. *)
  let frame, arguments =
    if List.mem_assoc 0 arguments then (frame, arguments)
    else
      let frame, receiver = value context frame iterable in
      (frame, (0, receiver) :: arguments)
  in
  let path, terminates, contract, substitution =
    match driven.callee with
    | Function { path; type_arguments } -> (
        let substitution =
          match Query.demand context.database Interface.Environment.signature path with
          | Some (signature : T.signature) ->
              let rec pair generics arguments =
                match (generics, arguments) with
                | (generic : T.generic) :: generics, argument :: arguments ->
                    (generic.generic, T.substitute_argument frame.substitution argument)
                    :: pair generics arguments
                | _ -> []
              in
              pair signature.generics type_arguments
          | None -> []
        in
        match Query.demand context.database Interface.Environment.signature path with
        | Some signature ->
            (Some path, signature.terminates, function_contract context.database path, substitution)
        | None -> (Some path, false, None, substitution))
    | _ -> (None, false, None, [])
  in
  if context.terminates && not terminates then
    oblige context frame Termination written.span
      "This loop may not end: the method it loops over has no `time` clause." (L.Boolean false);
  let element_type =
    match Option.map (substituted frame) source.checked.pattern_types.(pattern.id) with
    | Some ty -> ty
    | None -> unsupported pattern.span "a loop variable without a type"
  in
  (* The method's frame, with the loop's arguments. *)
  let method_frame (at : frame) (own : part) = part_frame at own ~arguments ~substitution in
  (* The method's clauses, read with the loop's arguments, the part handed
     out, and the parts before it. *)
  let method_clauses (at : frame) ~each ~result ~yielded ~finished =
    match contract with
    | Some { parts = (own : part) :: _; _ } ->
        let inside = { (method_frame at own) with result; yielded = Some yielded; finished } in
        List.iter
          (fun (clause : expression) ->
            if mentions_result own.callee clause = each then
              assume context at (snd (value context inside clause)))
          own.ensures
    | _ -> ()
  in
  (* The method's own work, by its cost clauses, once for the loop. *)
  let frame =
    match (contract, path) with
    | Some contract, Some path ->
        let values =
          List.map
            (fun (position, term) ->
              ( ({ expression = iterable.id; parameter = position; mode = T.Read; conversion = None }
                  : C.argument),
                iterable,
                term ))
            arguments
        in
        spend context frame
          (callee_amount context frame ~path ~parts:contract.parts
             ~bound_frame:(fun part -> method_frame frame part)
             ~call_:driven ~values ~change:None)
    | _ -> spend context frame (unknown_amount context frame)
  in
  (* A loop over a collection [mut] changes the collection too. *)
  let changed =
    let in_body = changed_places frame body in
    if mode = T.Mut then
      let root = root_of iterable in
      match (root.kind, place_local frame root) with
      | Self_value, _ -> { in_body with changes_self = frame.self <> None }
      | _, Some (id, _) ->
          { in_body with changed_locals = List.sort_uniq compare (id :: in_body.changed_locals) }
      | _, None -> unsupported iterable.span "looping over this place `mut`"
    else in_body
  in
  receiving_loop context frame written pattern clauses body ~element_type ~changed
    ~start:(fun head -> some_parts context head element_type)
    ~receive:(fun head before ->
      (* Each time round, the method either hands out another part or ends. *)
      let another = fresh context "another" L.Bool in
      let element = arrive context head "element" element_type in
      let inside = restrict head another in
      assume_valid context inside element_type element;
      method_clauses inside ~each:true ~result:(Some element) ~yielded:before ~finished:None;
      let through = appended context inside element_type before element in
      method_clauses inside ~each:false ~result:None ~yielded:through
        ~finished:(Some (L.Boolean false));
      method_clauses
        (restrict head (L.not_ another))
        ~each:false ~result:None ~yielded:before ~finished:(Some (L.Boolean true));
      { another; element; through; advance = Fun.id })

(* A [for] loop over a cursor pulls it until it ends, putting the cursor
   that is left back where it was. Its [yielded] is everything the cursor
   has handed out, before the loop too. *)
and pulled_loop context frame (written : statement) pattern iterable clauses body ~cursor_type
    ~method_ =
  let frame, cursor = value context frame iterable in
  let made =
    match List.assoc_opt cursor context.cursors with
    | Some made -> made
    | None -> unsupported iterable.span "a loop over a cursor whose method the prover does not know"
  in
  let id =
    match place_local frame (root_of iterable) with
    | Some (id, _) -> id
    | None -> unsupported iterable.span "a loop over a cursor that is not in a local"
  in
  if context.terminates && not (signature_terminates context method_) then
    oblige context frame Termination written.span
      "This loop may not end: the method its cursor comes from has no `time` clause."
      (L.Boolean false);
  let in_body = changed_places frame body in
  let changed =
    { in_body with changed_locals = List.sort_uniq compare (id :: in_body.changed_locals) }
  in
  let at_head = ref cursor in
  receiving_loop context frame written pattern clauses body ~element_type:made.element ~changed
    ~start:(fun head ->
      let cursor = Ids.find id head.locals in
      context.cursors <- (cursor, made) :: context.cursors;
      at_head := cursor;
      cursor_yielded context cursor_type made.element cursor)
    ~receive:(fun head _ ->
      let pulled, later = pull context head made !at_head ~cursor_type in
      let option_type = T.Named { path = option_path; arguments = [ T.Type made.element ] } in
      {
        another = L.Apply (L.tester (constructor_name option_type (Some "Some")), [ pulled ]);
        element = L.Apply (selector_name option_type (Some "Some") "value", [ pulled ]);
        through = cursor_yielded context cursor_type made.element later;
        advance = (fun (frame : frame) -> { frame with locals = Ids.add id later frame.locals });
      })

(* A [for] loop over a value of a type's own [Cursor]: each iteration
   calls its [next] by the [impl]'s contract, and the loop ends at [None].
   Such a cursor promises no end, so in a function that must end, the loop
   needs a [decreases] clause, which each iteration decreases. *)
and own_cursor_loop context frame (written : statement) pattern iterable clauses body ~cursor_type =
  let frame, _ = value context frame iterable in
  let id =
    match place_local frame (root_of iterable) with
    | Some (id, _) -> id
    | None -> unsupported iterable.span "a loop over a cursor that is not in a local"
  in
  let element_type =
    match Option.map (substituted frame) frame.source.checked.pattern_types.(pattern.id) with
    | Some ty -> ty
    | None -> unsupported pattern.span "a loop variable without a type"
  in
  let impl =
    match concrete_impl context cursor_trait cursor_type with
    | Some impl -> impl
    | None ->
        unsupported iterable.span "a loop over `%s`, whose `Cursor` the prover cannot find"
          (T.show cursor_type)
  in
  let evidence = C.Impl { impl; arguments = [] } in
  let trait : T.trait_reference =
    { trait = cursor_trait; trait_arguments = []; associated = [ ("Element", element_type) ] }
  in
  let contract =
    match method_contract context.database trait "next" Mut evidence with
    | Some contract -> contract
    | None ->
        unsupported iterable.span "a loop over `%s`, whose `next` the prover cannot read"
          (T.show cursor_type)
  in
  let path = Path.Method { owner = impl; name = "next"; receiver = Mut } in
  let option_type = T.Named { path = option_path; arguments = [ T.Type element_type ] } in
  let argument : C.argument =
    { expression = iterable.id; parameter = 0; mode = T.Mut; conversion = None }
  in
  let call_ : C.call =
    {
      callee =
        Trait_method
          {
            trait;
            name = "next";
            receiver = Mut;
            self_type = cursor_type;
            type_arguments = [];
            evidence;
          };
      arguments = [ argument ];
      defaults_left_out = [];
      uses = [];
      capability_arguments = [];
      result = option_type;
    }
  in
  let measures =
    List.find_map
      (fun (clause : loop_clause) ->
        match clause.kind with Loop_decreases measures -> Some measures | _ -> None)
      clauses
  in
  if context.terminates && not (signature_terminates context path) then
    oblige context frame Termination written.span
      (Printf.sprintf "This loop may not end: `%s`'s `next` has no `time` clause."
         (T.show cursor_type))
      (L.Boolean false);
  if context.terminates && measures = None then
    oblige context frame Termination written.span
      "This loop may not end: a cursor of a type's own promises no end, so give the loop a \
       `decreases` clause."
      (L.Boolean false);
  let measured (at : frame) =
    Option.map
      (List.map (fun measure -> snd (value context { at with checking = false } measure)))
      measures
  in
  let in_body = changed_places frame body in
  let changed =
    { in_body with changed_locals = List.sort_uniq compare (id :: in_body.changed_locals) }
  in
  receiving_loop context frame written pattern clauses body ~element_type ~changed
    ~each_iteration:(fun ~head ~ends ->
      (* The pull is part of the iteration, so the measure is compared from
         the head, before it. *)
      if context.terminates then
        match measured head with
        | Some before ->
            List.iter
              (fun (end_ : frame) ->
                match measured end_ with
                | Some after ->
                    oblige context end_ Termination written.span
                      "This loop's measure may not decrease." (smaller before after)
                | None -> ())
              ends
        | None -> ())
    ~start:(fun head -> some_parts context head element_type)
    ~receive:(fun head before ->
      let cursor = Ids.find id head.locals in
      let havoc_mut (frame : frame) =
        { frame with locals = Ids.add id (arrive context frame "changed" cursor_type) frame.locals }
      in
      let after, pulled =
        contract_call ~lent_final:None context head iterable call_ path contract
          [ (argument, iterable, cursor) ]
          ~havoc_mut
          ~substitution_of:(fun _ ->
            [ ({ T.owner = cursor_trait; name = "Self" }, T.Type cursor_type) ])
          ~instance:("[" ^ type_key cursor_type ^ "]")
      in
      let another = L.Apply (L.tester (constructor_name option_type (Some "Some")), [ pulled ]) in
      let element = L.Apply (selector_name option_type (Some "Some") "value", [ pulled ]) in
      let inside = restrict after another in
      assume_valid context inside element_type element;
      {
        another;
        element;
        through = appended context inside element_type before element;
        advance =
          (fun (frame : frame) ->
            {
              frame with
              locals = Ids.add id (Ids.find id after.locals) frame.locals;
              spent = after.spent;
            });
      })

(* A [for] loop that receives parts one at a time: from a yielding method
   it calls, or from a cursor it pulls. [start] is what was received before
   an iteration, at the head, and [receive] is what an iteration receives,
   having assumed what the method says of it. *)
and receiving_loop ?(each_iteration = fun ~head:_ ~ends:_ -> ()) context frame (written : statement)
    pattern clauses body ~element_type ~changed ~start ~receive =
  let entry = { frame with yielded = Some (empty_parts context frame element_type) } in
  check_invariants context entry clauses ~when_:"on entry to the loop";
  let costs = loop_costs context frame clauses ~held:(held_by context frame changed) in
  loop_entry context entry costs;
  let mark = context.fresh and facts_mark = List.length context.facts in
  let head = havoc context frame changed in
  let head =
    if contains_yield body then { head with handed_out = havoc_parts context head } else head
  in
  let before = start head in
  let iterations = sequence_length context element_type before in
  let head =
    loop_head context { head with yielded = Some before } costs ~iterations:(Some iterations)
  in
  assume_invariants context head clauses;
  let ended_mark = List.length context.facts in
  let received = receive head before in
  let through = received.through in
  let inside = received.advance (restrict head received.another) in
  let exits = { breaks = []; continues = [] } in
  let inside = spend context inside one_step in
  let _, inside =
    pattern_match context
      { inside with loop = Some exits; yielded = frame.yielded }
      pattern received.element element_type
  in
  let finished = block_value context inside body in
  let ends = (match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues in
  each_iteration ~head ~ends;
  let with_through (f : frame) = { f with loop = frame.loop; yielded = Some through } in
  loop_iterations context written head costs ~mark
    ~facts:(facts_since context facts_mark @ [ inside.condition ])
    ~ends:(List.map with_through ends)
    ~breaks:(List.map with_through exits.breaks);
  List.iter
    (fun (end_ : frame) ->
      check_invariants context (with_through end_) clauses ~when_:"after an iteration")
    ends;
  let ended = received.advance (restrict head (L.not_ received.another)) in
  let varies = made_since context mark in
  let ended_facts = facts_since context ended_mark @ facts_since context facts_mark in
  let exit_ =
    loop_exit context
      { ended with loop = frame.loop; yielded = Some before }
      costs ~iterations:(Some iterations)
      ~most:(Costs.upper_bounds ~varies ~facts:ended_facts iterations)
  in
  let left =
    List.map
      (fun (f : frame) ->
        loop_exit context (with_through f) costs
          ~iterations:(Some (Costs.plus iterations (L.int 1)))
          ~most:
            (Costs.upper_bounds ~varies ~facts:ended_facts
               (sequence_length context element_type through)))
      exits.breaks
  in
  join_frames context
    (List.map (fun (f : frame) -> { f with yielded = frame.yielded }) (exit_ :: left))
  |> Option.map (fun (joined : frame) ->
      { joined with locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) joined.locals })

(* Whether a loop's body hands out parts of the method it is in. *)
and contains_yield (body : block) =
  let found = ref false in
  let rec visit_statement (statement_ : statement) =
    (match statement_.kind with Yield _ -> found := true | _ -> ());
    Syntax_walk.statement_parts ~expression:visit_expression ~statement:visit_statement statement_
  and visit_expression expression_ =
    Syntax_walk.expression_parts ~expression:visit_expression ~statement:visit_statement expression_
  in
  List.iter visit_statement body.statements;
  !found

and havoc_parts context frame =
  match context.hands_out with
  | Some (part, _) -> Some (some_parts context frame part)
  | None -> frame.handed_out

(* Definitions *)

let new_context database ~home ~current ~terminates ~measures checked =
  {
    home;
    graph = Query.demand database Call_graph.graph (Path.package current);
    laws_assumed = [];
    database;
    current;
    terminates;
    measures;
    declarations = [];
    declared = Hashtbl.create 64;
    facts = [];
    obligations = [];
    fresh = 0;
    values = [];
    returns = [];
    instantiating = [];
    output = None;
    hands_out = None;
    handing = None;
    parameters = [];
    counters = [];
    own_constants = [];
    groups = [];
    fresh_order = Hashtbl.create 64;
    logs = [];
    powers = [];
    lambda_times = [];
    lambda_captures = [];
    potentials = [];
    equalities = [];
    known_calls = [];
    cursors = [];
    proving = false;
    holes = [];
    call_targets = [];
    fits =
      List.filter_map
        (function C.Integer_fits { expression; type_ } -> Some (expression, type_) | _ -> None)
        checked.C.obligations;
    disjoint =
      List.filter_map
        (function C.Disjoint { first; second } -> Some (first, second) | _ -> None)
        (checked.C.obligations
        @
        match Query.demand database Ownership.ownership home with
        | Some ownership -> ownership.obligations
        | None -> []);
    indexes = [];
  }

let outcome context = { obligations = List.rev context.obligations; holes = List.rev context.holes }

let reject_checker_obligations (source : source) =
  List.iter
    (function
      | C.Integer_fits _ -> ()
      | C.Disjoint _ ->
          (* Shown where both indexes are read. *)
          ()
      | C.Costs_imply _ -> raise (Unsupported (Span.make 0 0, "a function value's costs"))
      | C.Guards_cover _ ->
          (* Shown by the [_ => unreachable] arm it is about, which is an
             obligation of its own. *)
          ())
    source.checked.obligations

(* A cost clause, as a promise about one counter, shown at each way its
   definition returns. A trait's clause, which an [impl]'s method keeps, is
   read in the trait's tree. *)
type promise = {
  counter : Costs.counter;
  clause : cost;
  constants : Costs.constants option;
  span : span;
  written_in : source;
  inherited : bool;
}

let promises context (source : source) locals (clauses : clause list) ~inherited =
  List.filter_map
    (fun (clause : clause) ->
      match clause.kind with
      | Cost { resource = Time; bound = Finite; _ } -> None
      | Cost cost -> (
          match resource_of cost ~target_of:(target_in source locals) with
          | None -> unsupported clause.span "this `calls` target"
          | Some resource ->
              let counter = { Costs.resource; counting = counting_of cost } in
              let key = Costs.key counter in
              (match cost.resource with
              | Calls (Call_parameter name_) -> (
                  match (source.resolved.names.(name_.id), resource) with
                  | Some (Local id), Calls (Through term) ->
                      context.call_targets <- (term, id) :: context.call_targets
                  | _ -> ())
              | _ -> ());
              let constants =
                match counter.counting with
                | Units ->
                    let constants = Costs.constants (key ^ if inherited then ".trait" else "") in
                    context.groups <- constants :: context.groups;
                    declare context (L.Constant (constants.factor, L.Int));
                    declare context (L.Constant (constants.addend, L.Int));
                    if not (List.mem_assoc key context.own_constants) then
                      context.own_constants <- (key, constants) :: context.own_constants;
                    Some constants
                | At_most | Exactly -> None
              in
              Some
                {
                  counter;
                  clause = cost;
                  constants;
                  span = clause.span;
                  written_in = source;
                  inherited;
                })
      | _ -> None)
    clauses

(* A promise shown where its definition returns: what was spent within
   its bound, read with the parameters as they were on entry. *)
let keep_promise context (frame : frame) (promise : promise) ~(at : frame) ~span ~change =
  let spent =
    match List.assoc_opt (Costs.key promise.counter) frame.spent with
    | Some term -> term
    | None -> Costs.zero
  in
  (* An amortized bound is on what is spent plus the growth of the
     potential of what the definition returns and changes. *)
  let spent = if promise.clause.amortized then Costs.plus spent (change ()) else spent in
  let g =
    match promise.clause.bound with
    | Big_o g | At_most g | Exactly g -> snd (value context { at with checking = false } g)
    | Finite -> Costs.zero
  in
  let goal =
    match (promise.counter.counting, promise.constants) with
    | Units, Some constants -> Costs.at_most spent (Costs.bound constants g)
    | Exactly, _ -> L.equal spent g
    | _ -> Costs.at_most spent g
  in
  oblige context frame Cost span
    (if promise.inherited then
       Printf.sprintf "This method may spend more than its trait's `%s` allows."
         (quote promise.written_in promise.span)
     else
       Printf.sprintf "This may spend more than `%s` allows."
         (quote promise.written_in promise.span))
    goal

(* A function, method, or theorem: its parameters arrive, its [requires]
   are assumed, its body runs, and its [ensures] and cost clauses are
   shown at each way it returns. *)
let function_ ?(proof = false) ?(updating_helper = false) ?inherited database (source : source)
    ~path (signature : signature) (body : block) =
  reject_checker_obligations source;
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
  let context =
    new_context database ~home:source.key ~current:path ~terminates ~measures source.checked
  in
  context.proving <- proof;
  context.parameters <- signature.parameters;
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
      self_type = None;
      yielded = None;
      finished = None;
      handed_out = None;
      spent = [];
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
                assume_valid context frame ty term;
                { frame with locals = Ids.add name_.id term frame.locals }
            | None -> unsupported parameter.span "a parameter without a type")
        | Self_parameter _ ->
            let self_type =
              match Query.demand database Interface.Environment.signature path with
              | Some { receiver = Some (_, ty); _ } -> ty
              | _ -> unsupported parameter.span "`self` without a type"
            in
            let self = arrive context frame "self" self_type in
            (* A step of an update may be given a value in the middle of
               one. *)
            if not updating_helper then assume_valid context frame self_type self;
            { frame with self = Some self; self_type = Some self_type }
        | Parameter_error -> unsupported parameter.span "a parameter that did not parse")
      start signature.parameters
  in
  let start = { start with old_locals = start.locals; old_self = start.self } in
  (* A lending or yielding method hands out parts: its [ensures] that
     mention [result] hold at each [yield], and its others where it ends. *)
  let start =
    match (signature.result, Query.demand database Interface.Environment.signature path) with
    | Some (Yields _ | Lends _), Some { output = (Yields (_, part) | Lends (_, part)) as output; _ }
      ->
        let kind = match output with Lends _ -> `Lends | _ -> `Yields in
        context.hands_out <- Some (part, kind);
        let ensures =
          List.filter_map
            (fun (clause : clause) ->
              match clause.kind with Ensures value_ -> Some value_ | _ -> None)
            signature.clauses
        in
        context.handing <-
          Some
            ( List.filter (mentions_result source) ensures,
              List.filter (fun clause -> not (mentions_result source clause)) ensures );
        { start with handed_out = Some (empty_parts context start part) }
    | _ -> start
  in
  (* An [impl]'s method also keeps its trait's contract: the trait's
     [requires] is what callers through a bound show, so it is assumed,
     and implies the method's own; the trait's [ensures] is what they
     assume, so it is shown. See DESIGN.md, "An [impl] can promise more
     than its trait". *)
  let own_terms =
    (match start.self with Some self -> [ self ] | None -> [])
    @ List.filter_map
        (fun (parameter : parameter) ->
          match parameter.kind with
          | Named_parameter { name = name_; _ } -> Ids.find_opt name_.id start.locals
          | _ -> None)
        signature.parameters
  in
  let trait_frame (at : frame) ~result =
    match inherited with
    | Some ((part : part), substitution, _) ->
        let locals, self, old_locals =
          List.fold_left2
            (fun (locals, self, old_locals) binding (entry, exit_) ->
              match binding with
              | Self_binding -> (locals, Some exit_, old_locals)
              | Parameter_binding name_ ->
                  (Ids.add name_.id exit_ locals, self, Ids.add name_.id entry old_locals))
            (Ids.empty, None, Ids.empty) part.binding
            (List.combine own_terms
               ((match at.self with Some self -> [ self ] | None -> [])
               @ List.filter_map
                   (fun (parameter : parameter) ->
                     match parameter.kind with
                     | Named_parameter { name = name_; _ } -> Ids.find_opt name_.id at.locals
                     | _ -> None)
                   signature.parameters))
        in
        Some
          ( part,
            {
              at with
              source = part.callee;
              locals;
              old_locals;
              self;
              old_self = start.self;
              result;
              checking = false;
              loop = None;
              substitution;
            } )
    | None -> None
  in
  let own_requires =
    List.filter_map
      (fun (clause : clause) -> match clause.kind with Requires value_ -> Some value_ | _ -> None)
      signature.clauses
  in
  (* Its cost clauses, and its trait's, each count from zero. *)
  let promised =
    promises context source start.locals signature.clauses ~inherited:false
    @
    match (inherited, trait_frame start ~result:None) with
    | Some ((part : part), _, _), Some (_, inside) ->
        promises context part.callee inside.locals
          (List.map (fun (cost, span) : clause -> { kind = Cost cost; span; id = -1 }) part.costs)
          ~inherited:true
    | _ -> []
  in
  context.counters <-
    distinct_counters
      (List.map (fun promise -> promise.counter) promised @ loop_counters source start.locals body);
  let start =
    {
      start with
      spent = List.map (fun counter -> (Costs.key counter, Costs.zero)) context.counters;
    }
  in
  let start =
    match trait_frame start ~result:None with
    | Some (part, inside)
      when List.length part.binding = List.length own_terms
           (* A tag's [from_template] may require more than its trait, since
              only a template calls it, where the tag is known; a call through
              a bound is an error, which keeps that sound. See DESIGN.md,
              "Tagged templates". *)
           && not (Path.equal part.callee.key.path template_trait) ->
        List.iter
          (fun (clause : expression) -> assume context start (snd (value context inside clause)))
          part.requires;
        List.fold_left
          (fun frame (clause : expression) ->
            let frame, term = value context frame clause in
            oblige context frame Requires clause.span
              (Printf.sprintf
                 "`%s` may not follow from the trait's `requires`, which callers through the trait \
                  show, and an `impl`'s `requires` must."
                 (quote source clause.span))
              term;
            frame)
          start own_requires
    | _ ->
        List.fold_left
          (fun frame (clause : expression) ->
            let frame, term = value context frame clause in
            assume context frame term;
            frame)
          start own_requires
  in
  let finished = block_value context start body in
  let returns =
    (match finished with Some (frame, term) -> [ (frame, Some term) ] | None -> [])
    @ List.rev context.returns
  in
  let mut_parameters =
    List.filter_map
      (fun (parameter : parameter) ->
        match parameter.kind with
        | Named_parameter { name = name_; mode = Some Mut; _ } -> Some name_
        | _ -> None)
      signature.parameters
  in
  let mut_self =
    List.exists
      (fun (parameter : parameter) ->
        match parameter.kind with Self_parameter (Some Mut) -> true | _ -> false)
      signature.parameters
  in
  List.iter
    (fun ((frame : frame), returned) ->
      let frame = { frame with result = returned } in
      (* What other code sees again: the result, each [mut] parameter, and
         [mut self], unless this is a step of an update. *)
      (match (returned, context.output) with
      | Some term, Some output ->
          check_valid context frame body.span output term ~deep:true ~when_:"for the value returned"
      | _ -> ());
      List.iter
        (fun (name_ : name) ->
          match (Ids.find_opt name_.id frame.locals, local_type frame name_.id) with
          | Some term, Some ty ->
              check_valid context frame name_.span ty term ~deep:true
                ~when_:(Printf.sprintf "for `%s` when the function returns" name_.text)
          | _ -> ())
        mut_parameters;
      (match (mut_self, updating_helper, frame.self, frame.self_type) with
      | true, false, Some self, Some self_type ->
          check_valid context frame body.span self_type self ~deep:true
            ~when_:"for `self` when the method returns"
      | _ -> ());
      (match (context.handing, frame.handed_out) with
      | Some (_, at_end), Some handed_out ->
          (* The clauses about how a lending or yielding method ends, with
             everything it handed out, having run to its end. *)
          List.iter
            (fun (ensured : expression) ->
              let _, term =
                value context
                  {
                    frame with
                    yielded = Some handed_out;
                    finished = Some (L.Boolean true);
                    checking = false;
                  }
                  ensured
              in
              oblige context frame Ensures ensured.span
                (Printf.sprintf "`%s` may not hold when the method ends."
                   (quote source ensured.span))
                term)
            at_end
      | _ ->
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
            signature.clauses);
      (* How much the potential of what the definition returns and changes
         grew, less what it was given to keep, for an amortized bound. *)
      let change () =
        let given =
          List.fold_left
            (fun total (parameter : parameter) ->
              match parameter.kind with
              | Named_parameter { name = name_; mode = Some ((Mut | Own) as mode); _ } -> (
                  match
                    ( Ids.find_opt name_.id start.locals,
                      Ids.find_opt name_.id frame.locals,
                      local_type frame name_.id )
                  with
                  | Some entry, later, Some ty ->
                      let kept =
                        match (mode, later) with
                        | Mut, Some later -> potential context frame ty later
                        | _ -> Costs.zero
                      in
                      Costs.plus total (Costs.minus kept (potential context frame ty entry))
                  | _ -> total)
              | Self_parameter (Some ((Mut | Own) as mode)) -> (
                  match (start.self, frame.self, frame.self_type) with
                  | Some entry, later, Some ty ->
                      let kept =
                        match (mode, later) with
                        | Mut, Some later -> potential context frame ty later
                        | _ -> Costs.zero
                      in
                      Costs.plus total (Costs.minus kept (potential context frame ty entry))
                  | _ -> total)
              | _ -> total)
            Costs.zero signature.parameters
        in
        match (returned, context.output) with
        | Some term, Some output -> Costs.plus given (potential context frame output term)
        | _ -> given
      in
      List.iter
        (fun promise ->
          if promise.inherited then
            match trait_frame frame ~result:returned with
            | Some (_, inside) ->
                keep_promise context frame promise
                  ~at:{ inside with locals = inside.old_locals; self = inside.old_self }
                  ~span:body.span ~change
            | None -> ()
          else
            keep_promise context frame promise
              ~at:{ frame with locals = frame.old_locals; self = frame.old_self; result = returned }
              ~span:promise.span ~change)
        promised;
      match trait_frame frame ~result:returned with
      | Some (part, inside) when List.length part.binding = List.length own_terms ->
          List.iter
            (fun (clause : expression) ->
              let _, term = value context inside clause in
              oblige context frame Ensures body.span
                (Printf.sprintf "The trait's `%s` may not hold when this method returns."
                   (quote part.callee clause.span))
                term)
            part.ensures;
          (* A method that replaces a provided one gives the result the
             provided body gives, which is its definition. *)
          begin match (inherited, returned) with
          | Some (_, _, Some provided), Some returned ->
              if functional_block provided then
                begin match block_value context inside provided with
                | Some (_, defined) ->
                    oblige context frame Ensures body.span
                      "This method replaces one its trait provides, so it must give the result the \
                       provided body gives, and it may not."
                      (L.equal returned defined)
                | None -> ()
                end
              else
                oblige context frame Ensures body.span
                  "This method replaces one its trait provides, whose body is not functional, so \
                   it is no definition this one could be shown to agree with."
                  (L.Boolean false)
          | _ -> ()
          end
      | _ -> ())
    returns;
  outcome context

(* The laws of a trait an [impl] writes by hand, each shown for fresh
   values of its parameters, after the bodies of the [proof]s written for
   it. *)
let laws database (source : source) ~impl ~trait ~for_type ~proofs ~at =
  let context =
    new_context database ~home:source.key ~current:impl ~terminates:false ~measures:[]
      source.checked
  in
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
      self_type = None;
      yielded = None;
      finished = None;
      handed_out = None;
      spent = [];
    }
  in
  List.iter
    (fun (law_source, (law : law)) ->
      let types = law_parameter_types start law_source trait for_type law in
      if not (List.exists (fun ty -> ty = T.Error) types) then begin
        (* The other laws are facts here, and this one is not. *)
        context.laws_assumed <-
          (Path.show trait ^ " for " ^ type_key for_type) :: context.laws_assumed;
        let terms =
          List.map
            (fun ty ->
              let term = arrive context start "law" ty in
              assume_valid context start ty term;
              term)
            types
        in
        let frame = ref start in
        (* A [proof]'s statements are hints: its calls' [ensures] are facts
           where their [requires] hold, which is all a proof needs. *)
        List.iter
          (fun ((proof_source : source), (body : block)) ->
            context.proving <- true;
            let after =
              block_value context { start with source = proof_source; checking = false } body
            in
            context.proving <- false;
            match after with
            | Some (after, _) -> frame := { start with condition = after.condition }
            | None -> ())
          (List.filter_map
             (fun (name_, proof) -> if name_ = law.name.text then Some proof else None)
             proofs);
        let inside = law_frame !frame law_source trait for_type law terms in
        List.iter
          (fun clause -> assume context !frame (snd (value context inside clause)))
          law.requires;
        match block_value context inside law.body with
        | Some (_, holds) ->
            oblige context !frame Law at
              (Printf.sprintf "The law `%s` may not hold for `%s`." law.name.text (T.show for_type))
              holds
        | None -> ()
      end)
    (let context0 = context in
     laws_of context0 trait);
  outcome context

(* A type's [cost potential] is never below zero for a value that meets
   its invariants, which is what makes each potential a fact about every
   valid value. See PROVER.md, "Amortized bounds". *)
let type_potential database (source : source) ~path ~(written : expression) =
  let context =
    new_context database ~home:source.key ~current:path ~terminates:false ~measures:[]
      source.checked
  in
  let ty =
    match Query.demand database Interface.Environment.interface path with
    | Some (Interface.Environment.Type_interface interface) ->
        T.Named
          { path; arguments = Interface.Environment.generic_arguments interface.type_generics }
    | _ -> T.Named { path; arguments = [] }
  in
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
      self_type = Some ty;
      yielded = None;
      finished = None;
      handed_out = None;
      spent = [];
    }
  in
  let value_ = arrive context start "value" ty in
  assume_valid context start ty value_;
  let at = { start with self = Some value_; old_self = Some value_ } in
  let _, own = value context { at with checking = false } written in
  oblige context at Cost written.span
    (Printf.sprintf "The potential of `%s` may be below zero for a value that meets its invariants."
       (T.show ty))
    (L.Apply ("<=", [ L.int 0; own ]));
  outcome context

let test database (source : source) ~path (body : block) =
  reject_checker_obligations source;
  let context =
    new_context database ~home:source.key ~current:path ~terminates:false ~measures:[]
      source.checked
  in
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
      self_type = None;
      yielded = None;
      finished = None;
      handed_out = None;
      spent = [];
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
