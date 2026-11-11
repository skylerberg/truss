(* A checked body as obligations.

   The body is executed symbolically, forward, in passive form: every value
   is a term, every fact is guarded by the condition of the path it holds
   on, and where paths join, each local that differs gets a fresh symbol
   that each path defines. So the verification condition grows with the
   body, not with its number of paths.

   Each obligation becomes one query: the facts gathered before it, and its
   goal, guarded by its path. Once made, an obligation is a fact for the
   rest of the body, since its own query proves it.

   Anything this stage cannot translate soundly raises [Unsupported], and
   the definition's obligations are not proven at all: an obligation is
   never assumed because the prover could not read the code around it. *)

open Core
module T = Types
module L = Logic
module Names = Resolve.Names
module Code = Diagnostic.Code
module Span = Syntax.Span

type span = Syntax.span

module Locals = Map.Make (struct
  type t = Core.local

  let compare = compare
end)

exception Unsupported of span * string

(* Something the prover cannot read in another definition's form, such as
   a callee's contract, whose span means nothing in this one. The nearest
   node of the definition being proven reports it, with its own span. *)
exception Foreign_unsupported of string

let unsupported span format =
  Printf.ksprintf (fun message -> raise (Unsupported (span, message))) format

(* A clause that running compiled code can decide: one of a tag's
   [from_template]'s, by its position, for a template of these literal
   texts. *)
type evaluation = { from_template : Path.t; texts : string list; clause : int }

(* A call whose arguments are all known, of a function that is compiled and
   not generic: its term in the logic, which running it can give a value.
   A [Bool] is 0 or 1, in its arguments and its result. *)
type known_call = { function_ : Path.t; arguments : Z.t list; term : L.term; result_is_bool : bool }

type obligation = {
  code : Code.prover;
  span : span;  (** Relative to the definition being proven. *)
  message : string;
  cited : (Names.key * span) option;
      (** The clause it comes from, in the definition that states it, where that is not the one
          being proven: a callee's [requires]. *)
  query : L.query;
  contracts_alone : L.query option;
      (** The query without what unfolding callees' definitions gave, where it has any: asked when
          the query runs out of steps, since a callee's contract can be enough where its definition
          is too much for the solver. *)
  values : (string * string) list;  (** Each prover symbol a counterexample shows, with its name. *)
  locals : (string * string) list;
      (** The locals whose values are symbols where the obligation is made, with their names: asked
          for only once the query has a counterexample, so the query's key stays its own. *)
  constants : Costs.constants list;
      (** The constants of each [O(...)] bound the query mentions, which each try pins. *)
  evaluation : evaluation option;  (** Running code that decides it, where there is any. *)
  known_calls : known_call list;  (** The calls its query mentions that running code can give. *)
  hidden : (string * bool) list;
      (** The callees its query mentions whose bodies would define them but are not visible in this
          package, each with whether it can be marked [transparent], as a method of an [impl]
          cannot. *)
}

type outcome = {
  obligations : obligation list;  (** In the order made. *)
  holes : (Names.key * span) list;  (** Each [todo] in a proof, in the definition proven. *)
}

(* A definition whose form is being read: the one proven, or a callee
   whose clauses are translated at a call. A derived method's form was
   written by no one, so it has no key and no text. *)
type source = {
  key : Names.key option;
  name : string;  (** For messages. *)
  core : Core.t;
  spans : span array Lazy.t;
      (** By a node's origin, read only to report something, so a caller's proof depends on a
          callee's text only where it says something about it. *)
  text : string Lazy.t;
}

(* One form's clauses about a callee: its own, or, for a method of an
   [impl], its trait's. Its parameters are in the order a call's arguments
   are, a method's receiver first. *)
type part = {
  callee : source;
  parameters : Core.parameter list;
  requires : expression list;
  ensures : expression list;
  decreases : expression list;
  costs : Core.cost list;  (** Its cost clauses, but [cost time finite]. *)
  inherited : bool;  (** The trait's, which an [impl]'s method keeps. *)
}

type contract = {
  parts : part list;  (** The callee's own first. *)
  pure : bool;  (** Pure and terminating, so a function in the logic. *)
  result_kind : [ `Returns | `Lends | `Yields ];
  definition : (part * block) option;  (** A functional body, which is the callee's definition. *)
}

type loop_exits = { mutable breaks : frame list; mutable continues : frame list }

(* An early exit from [concurrent] code, which takes effect only where the
   tasks it leaves end: the tasks, innermost first, where it was, and what
   it does then. *)
and leaving = { tasks : Core.task list; at : frame; exit : exit_ }
and exit_ = Returning of L.term option | Breaking | Continuing

(* Where a path is: the value of each local, the values on entry for
   [old], the path's condition, and what [self] and [result] are. *)
and frame = {
  source : source;
  locals : L.term Locals.t;
  types : T.ty Locals.t;  (** Each local's type, as it was bound. *)
  old_locals : L.term Locals.t;
  self : L.term option;
  old_self : L.term option;
  result : L.term option;
  condition : L.term;
  checking : bool;  (** Whether obligations are made here; not in a callee's clauses. *)
  bound : string list;  (** Symbols bound by quantifiers around this point. *)
  binders : (string * L.sort * L.term) list;
      (** The quantifiers around this point, innermost first: each bound symbol, its sort, and the
          premise it ranges over. *)
  loop : loop_exits option;
  substitution : T.substitution;
      (** The type arguments of the callee whose clauses are read here, for its generic types. *)
  self_type : T.ty option;  (** The type of [self], whose fields an invariant names. *)
  yielded : L.term option;
      (** What [yielded] names here: the parts a lending or yielding callee handed out, or the
          values a [for] loop's earlier iterations received. *)
  finished : L.term option;  (** What [finished] names here. *)
  handed_out : L.term option;
      (** In a lending or yielding method's own body, the parts it has handed out so far. *)
  updating : L.term option;  (** What the target of an update holds before it. *)
  spent : (string * L.term) list;
      (** Each counter's value here, by its key: what the code proven has spent since it began. *)
}

(* What a loop's body may change. *)
type changed = { changed_locals : Core.local list; changes_self : bool }

(* How a loop bounds a counter: by its [cost] clause about it, or by its
   iterations times a bound on one, and, where the values it changes hold
   potential, also with that potential, from what it held on entry. *)
type loop_rule =
  | Clause_bound of Core.cost * Costs.constants option
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

(* An argument of a call, as the callee is given it: its position, its
   mode, what was written for it, if anything, its type, and its value. *)
type passed = {
  position : int;
  mode : T.mode;
  operand : operand option;  (** [None] for a default. *)
  type_ : T.ty;
  term : L.term;
  run : (L.term * L.term) option;
      (** A slice argument's bounds, as the argument was evaluated, for writing back what a [mut]
          callee changes. *)
}

type context = {
  database : Query.context;
  current : Path.t;
  mutable terminates : bool;
      (** Whether the code being proven must end: the definition's [time] clause, or, in a lambda,
          its function type's. *)
  mutable parameters : Core.parameter list;  (** The definition's, for its callbacks' [requires]. *)
  measures : expression list;  (** Its [decreases], for its recursive calls. *)
  mutable declarations : L.declaration list;
  declared : (string, unit) Hashtbl.t;
  mutable facts : L.term list;  (** Reversed. *)
  unfolded : (L.term, unit) Hashtbl.t;
      (** The facts that come from unfolding a callee's definition, which a query that runs out of
          steps is asked again without. *)
  mutable obligations : obligation list;  (** Reversed. *)
  mutable fresh : int;
  mutable values : (string * string) list;  (** For counterexamples. *)
  local_names : (Core.local, string) Hashtbl.t;  (** Each local's name, as its pattern binds it. *)
  mutable returns : (frame * L.term option) list;
  mutable leaving : leaving list;  (** The early exits of the [concurrent] code being read. *)
  mutable lent_back : (T.ty * L.term * L.term) list;
      (** Each part a lending method lends [mut]: its type, as it was lent, and as it came back. *)
  mutable instantiating : Path.t list;  (** Contracts being assumed, to stop at recursion. *)
  disjoint : (int * int) list;
      (** The ownership check's pairs of indexes, by the origin of each, that must differ. *)
  mutable indexes : (int * (place_value * span)) list;
      (** The value of each such index or range, once read. *)
  mutable hands_out : (T.ty * [ `Lends | `Yields ]) option;
      (** In a lending or yielding method's body, the type of the parts it hands out. *)
  mutable handing : (expression list * expression list) option;
      (** Its [ensures]: the clauses for each [yield], which mention [result], and the others. *)
  home : Names.key;  (** The definition being proven, whose spans and obligations are in it. *)
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
  mutable lambda_captures : (L.term * Core.local list) list;  (** What each lambda captures. *)
  mutable potentials : L.term list;  (** Each value's potential whose definition is a fact. *)
  models : (string, (L.term -> L.term) option) Hashtbl.t;
      (** Each type's model function, by the types' keys, which reading it takes the standard
          library's impls to find, and which is asked at every potential. *)
  holds_potential : (string, bool) Hashtbl.t;  (** Whether each type can hold potential. *)
  buffers : (string, (T.ty * (L.term -> L.term)) option) Hashtbl.t;
      (** Each type's elements and model as a buffer's, where it is one. *)
  mutable equalities : L.term list;  (** Each derived [==] whose definition is a fact. *)
  mutable known_calls : known_call list;  (** Each call running code can give a value. *)
  mutable hidden_bodies : (string * (string * bool)) list;
      (** Each callee in another package whose body would define it but is not [transparent]: its
          symbol, with its name and whether it can be marked so. *)
  mutable cursors : (L.term * cursor) list;  (** Where each cursor value came from. *)
  mutable proving : bool;
      (** In a theorem, a [proof] block, or a law's proof, where a [todo] is a hole. *)
  mutable holes : (Names.key * span) list;  (** Reversed. *)
  mutable unfinished : L.term list;
      (** The condition of each path a [todo] ends in the [proof] block being read. *)
  mutable call_targets : (L.term * Core.local) list;
      (** Each function-typed parameter a [calls] clause counts, with its local. *)
  mutable passed_values : int list;
      (** Each named function passed straight to a parameter, which the call checks against what the
          parameter promises. *)
  mutable reading_callback : bool;
      (** Reading a function-typed parameter to call it or pass it, where its [requires] is checked,
          not lost. *)
  ranking : bool;
      (** Whether the definition proven may show a recursive call ends by being on a part of its
          parameters, the one use of the order of parts, which is stated only then. *)
  mutable validating : T.ty list;
      (** The types whose invariants are being read, around this point. A type is valid inside the
          reading of its own invariant, as it is inside its own fields, so a type that holds itself
          through another's invariant is read once. *)
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

(* A symbol for a value made at this point. Inside quantifiers it is a
   function of their bound symbols, since the value can differ for each of
   theirs. *)
let made_here context frame name sort =
  match List.rev frame.binders with
  | [] ->
      declare context (L.Constant (name, sort));
      L.Symbol name
  | outermost_first ->
      declare context (L.Function (name, List.map (fun (_, sort, _) -> sort) outermost_first, sort));
      L.Apply (name, List.map (fun (bound, _, _) -> L.Symbol bound) outermost_first)

let fresh context frame prefix sort =
  context.fresh <- context.fresh + 1;
  let name = Printf.sprintf "%s.%d" prefix context.fresh in
  Hashtbl.replace context.fresh_order name context.fresh;
  made_here context frame name sort

(* Whether a term mentions a fresh symbol made after [mark]: a value a
   loop changes, or one made inside it. *)
let made_since context mark term =
  let made name =
    match Hashtbl.find_opt context.fresh_order name with Some n -> n > mark | None -> false
  in
  let rec walk = function
    | L.Symbol name -> made name
    | L.Integer _ | L.Boolean _ | L.Bits _ -> false
    | L.Apply (name, arguments) -> made name || List.exists walk arguments
    | L.Forall (_, body) | L.Exists (_, body) -> walk body
  in
  walk term

(* A statement made inside quantifiers, closed over them: true for every
   value of each bound symbol that its premise admits. [None] when it names
   a symbol bound by something other than a quantifier, such as a lambda's
   parameter, where it has no meaning outside. *)
let closed_over_binders frame term =
  let names = List.map (fun (name, _, _) -> name) frame.binders in
  if L.mentions (List.filter (fun name -> not (List.mem name names)) frame.bound) term then None
  else if not (L.mentions names term) then Some term
  else
    let outermost_first = List.rev frame.binders in
    Some
      (L.Forall
         ( List.map (fun (name, sort, _) -> (name, sort)) outermost_first,
           L.( ==> )
             (L.conjunction (List.map (fun (_, _, premise) -> premise) outermost_first))
             term ))

(* A fact of mathematics, true on every path. Inside a quantifier, one that
   names a bound symbol is left out, which is always sound: closed over the
   quantifier it would be true, but a body's calls give many such facts,
   and the solver spends its steps on them. *)
let fact context frame term =
  if not (L.mentions frame.bound term) then context.facts <- term :: context.facts

(* A fact is guarded by its path's condition, and left out where either
   names a bound symbol, as [fact] says. *)
let assume context frame term =
  if not (L.mentions frame.bound term || L.mentions frame.bound frame.condition) then
    match term with
    | L.Boolean true -> ()
    | _ -> context.facts <- L.( ==> ) frame.condition term :: context.facts

(* An obligation is shown by its own query, and is a fact for what comes
   after it. Inside a quantifier it is shown for each value the
   quantifier's premise admits, which is how a quantifier's body is shown
   to be well defined. *)
let rec oblige ?evaluation ?cited context frame code span message goal =
  match obligation_at ?evaluation context frame code span message goal with
  | Some obligation ->
      context.obligations <- { obligation with cited } :: context.obligations;
      assume context frame goal
  | None -> ()

(* An obligation made but not yet added, for one that is needed only if
   what it shows is used. *)
and obligation_at ?evaluation context frame code span message goal =
  if not frame.checking then None
  else if not (L.mentions frame.bound goal || L.mentions frame.bound frame.condition) then
    Some (make_obligation ?evaluation context frame code span message goal)
  else
    match closed_over_binders frame (L.( ==> ) frame.condition goal) with
    | Some closed ->
        Some
          (make_obligation ?evaluation context
             { frame with condition = L.Boolean true }
             code span message closed)
    | None -> None

and make_obligation ?evaluation context frame code span message goal =
  let query =
    L.prune
      {
        declarations = List.rev context.declarations;
        facts = List.rev context.facts;
        goal = L.( ==> ) frame.condition goal;
      }
  in
  let contracts_alone =
    if List.exists (Hashtbl.mem context.unfolded) query.facts then
      Some
        (L.prune
           {
             query with
             facts = List.filter (fun fact -> not (Hashtbl.mem context.unfolded fact)) query.facts;
           })
    else None
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
  let hidden =
    List.sort_uniq compare
      (List.filter_map
         (fun (symbol, name) ->
           if L.mentions [ symbol ] query.goal || List.exists (L.mentions [ symbol ]) query.facts
           then Some name
           else None)
         context.hidden_bodies)
  in
  {
    code;
    span;
    message;
    cited = None;
    hidden;
    query;
    contracts_alone;
    values = context.values;
    locals =
      Locals.fold
        (fun local term shown ->
          match (term, Hashtbl.find_opt context.local_names local) with
          | L.Symbol symbol, Some name
            when not (List.mem_assoc symbol context.values || List.mem_assoc symbol shown) ->
              (symbol, name) :: shown
          | _ -> shown)
        frame.locals
        (match frame.result with
        | Some (L.Symbol symbol) when not (List.mem_assoc symbol context.values) ->
            [ (symbol, "result") ]
        | _ -> []);
    constants;
    evaluation;
    known_calls;
  }

(* Whether a term holds another. *)
and occurs part term =
  term = part
  ||
  match term with
  | L.Apply (_, arguments) -> List.exists (occurs part) arguments
  | L.Forall (_, body) | L.Exists (_, body) -> occurs part body
  | L.Symbol _ | L.Integer _ | L.Boolean _ | L.Bits _ -> false

(* Where a node came from in its form's text, by its origin. *)
let span_of (source : source) origin =
  let spans = Lazy.force source.spans in
  if origin >= 0 && origin < Array.length spans then spans.(origin) else Span.make 0 0

(* A node's source text, for messages. *)
let quote source origin =
  let span = span_of source origin in
  let text = Lazy.force source.text in
  if span.stop > span.start && span.stop <= String.length text then
    String.sub text span.start (span.stop - span.start)
  else "this expression"

(* Where a node of the form read here is. *)
let at frame (node : expression) = span_of frame.source node.origin

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
   lawful [==] and ordering of floats: every NaN is equal to every other
   and ordered after every number, and otherwise IEEE's, so [-0.0 == 0.0]. *)
let float_operation name left right = L.Apply (name, [ L.Apply ("RNE", []); left; right ])
let is_nan value = L.Apply ("fp.isNaN", [ value ])

(* A float cut toward zero, as a real number. *)
let truncated value =
  L.Apply ("fp.to_real", [ L.Apply ("fp.roundToIntegral", [ L.Apply ("RTZ", []); value ]) ])

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

let is_standard_equal = Well_known.is Equal
let equal_trait = Well_known.path Equal

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
      | Todo_type | Builtin_type _ | Error_shape _ -> None)
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
    | _ when T.equal ty T.unit ->
        (* One value, so any two are equal. *)
        if not (Hashtbl.mem context.declared "Unit") then begin
          Hashtbl.replace context.declared "Unit" ();
          context.declarations <- L.Datatype ("Unit", [ ("Unit.unit", []) ]) :: context.declarations
        end;
        Uninterpreted "Unit"
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
   semantics, or derived from fields that all are. *)
let rec structural context ?(seen = []) (ty : T.ty) =
  if is_numeric ty || is_bool ty || T.is_builtin Character ty || T.equal ty T.unit then true
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

(* Whether a term is a value of a type: within its bounds, and for a
   [Character], a Unicode scalar value, so never a surrogate. *)
let in_range ty term =
  match bounds ty with
  | Some (low, high) ->
      let within =
        L.(Apply ("<=", [ Integer low; term ]) &&& Apply ("<=", [ term; Integer high ]))
      in
      if T.is_builtin Character ty then
        L.(
          within &&& not_ (Apply ("<=", [ int 0xD800; term ]) &&& Apply ("<=", [ term; int 0xDFFF ])))
      else within
  | None -> L.Boolean true

(* Runs [make] the first time a key is met in a definition's proof, for a
   fact that is stated once. *)
let once context key make =
  if not (Hashtbl.mem context.declared key) then begin
    Hashtbl.replace context.declared key ();
    make ()
  end

(* A sort's name, as part of a symbol's. *)
let sort_label (sort : L.sort) =
  match sort with
  | Int -> "Int"
  | Bool -> "Bool"
  | Float (exponent, significand) -> Printf.sprintf "Float%d_%d" exponent significand
  | Uninterpreted name -> name

(* A term with its quantifiers' bound names numbered in the order they
   appear, so two terms that differ only in those names are the same. *)
let canonical_binders term =
  let count = ref 0 in
  let rec walk renamed = function
    | L.Symbol name -> (
        match List.assoc_opt name renamed with
        | Some other -> L.Symbol other
        | None -> L.Symbol name)
    | (L.Integer _ | L.Boolean _ | L.Bits _) as term -> term
    | L.Apply (name, arguments) -> L.Apply (name, List.map (walk renamed) arguments)
    | L.Forall (bound, body) ->
        let bound, renamed = rename renamed bound in
        L.Forall (bound, walk renamed body)
    | L.Exists (bound, body) ->
        let bound, renamed = rename renamed bound in
        L.Exists (bound, walk renamed body)
  and rename renamed bound =
    List.fold_right
      (fun (name, sort) (bound, renamed) ->
        incr count;
        let other = Printf.sprintf "binder.%d" !count in
        ((other, sort) :: bound, (name, other) :: renamed))
      bound ([], renamed)
  in
  walk [] term

(* A value of a type that arrives from outside what is known: a parameter,
   a call's result, a loop's havocked local. *)
let arrive context frame prefix ty =
  let value = fresh context frame prefix (sort_of context ty) in
  assume context frame (in_range ty value);
  value

(* A local bound to a value of a type. *)
let bind frame local ty term =
  {
    frame with
    locals = Locals.add local term frame.locals;
    types = Locals.add local ty frame.types;
  }

(* A type in a frame: its generic parameters replaced by what they stand
   for, and each associated type of a known type by what its [impl]
   chooses, so a trait's [Self.Key] read for a [List] is a [USize]. *)
let substituted context frame ty =
  Interface.Impls.normalize context.database
    ~bounds:(fun _ -> [])
    (T.substitute frame.substitution ty)

let type_of context frame (node : expression) = substituted context frame node.type_

(* A local's type in a frame, as it was bound, with what the frame's
   generic parameters stand for. *)
let local_type context frame local =
  Option.map (substituted context frame) (Locals.find_opt local frame.types)

(* Whether a term mentions what a value's potential is: a type's potential,
   or what a growable buffer has saved, which a type that holds one, as a
   [String] does in its own package, unfolds to. *)
let mentions_potential term =
  let rec walk = function
    | L.Apply (name, arguments) ->
        String.starts_with ~prefix:"potential." name
        || String.starts_with ~prefix:"slack." name
        || List.exists walk arguments
    | L.Forall (_, body) | L.Exists (_, body) -> walk body
    | L.Symbol _ | L.Integer _ | L.Boolean _ | L.Bits _ -> false
  in
  walk term

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
      (* The joined condition is named, so that each later fact on the path
         names it rather than repeating every branch's condition, which
         would grow with each join. *)
      let condition =
        match condition with
        | L.Boolean _ | L.Symbol _ -> condition
        | _ when L.mentions first.bound condition -> condition
        | _ ->
            let path = fresh context first "path" L.Bool in
            fact context first (L.equal path condition);
            path
      in
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
            let symbol = fresh context first prefix sort in
            List.iter
              (fun ((frame : frame), term) ->
                match term with
                | Some term -> fact context first (L.( ==> ) frame.condition (L.equal symbol term))
                | None -> ())
              values;
            Some symbol
      in
      let locals =
        Locals.mapi
          (fun id term ->
            let sort =
              match local_type context first id with
              | Some ty -> sort_of context ty
              | None -> ( match term with L.Boolean _ -> L.Bool | _ -> L.Int)
            in
            match define "joined" sort (fun frame _ -> Locals.find_opt id frame.locals) with
            | Some joined -> joined
            | None -> term)
          first.locals
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
      (* What a path spent, in terms of the joined values: on that path each
         is the path's own, so the potential of a value it changed is the
         potential of the joined value, which the other paths name too. *)
      let in_joined (frame : frame) amount =
        let renamed =
          Locals.fold
            (fun id joined renamed ->
              match Locals.find_opt id frame.locals with
              | Some own when own <> joined -> (own, joined) :: renamed
              | _ -> renamed)
            locals []
        in
        let renamed =
          match (frame.self, self) with
          | Some own, Some joined when own <> joined -> (own, joined) :: renamed
          | _ -> renamed
        in
        List.fold_left (fun amount (from, into) -> L.replace ~from ~into amount) amount renamed
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
                    in_joined frame
                      (match List.assoc_opt key frame.spent with Some t -> t | None -> term) ))
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
                (* A choice that names a potential stays a choice, so that a
                   loop sees the potential each path changed, which the
                   potential the loop holds cancels. *)
                if L.mentions first.bound choice || mentions_potential choice then (key, choice)
                else
                  let symbol = fresh context first "spent" L.Int in
                  fact context first (L.equal symbol choice);
                  (key, symbol))
          first.spent
      in
      let value =
        match value_type with
        | Some ty -> define "value" (sort_of context ty) (fun _ value -> value)
        | None -> None
      in
      let handed_out =
        match context.hands_out with
        | Some (part, _) -> (
            match
              define "parts"
                (sort_of context
                   (T.Named { path = Well_known.path Sequence; arguments = [ T.Type part ] }))
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

let source_of database (key : Names.key) core =
  {
    key = Some key;
    name = Names.show_key key;
    core;
    spans = lazy (Option.value (Query.demand database Names.spans key) ~default:[||]);
    text = lazy (Option.value (Query.demand database Names.text key) ~default:"");
  }

(* The form of a definition, by its key, when it has one. *)
let source_at_key database key =
  Option.map (source_of database key) (Query.demand database Infer.core key)

(* Whose form is read for a function or a method: its own, written or
   derived, or, for a method an [impl] leaves to its trait, the trait's. *)
type found = Written | Derived | Provided

(* The form of a function or a method by its path, with the substitution it
   is read under: the [impl]'s, for the form of the trait's method that the
   [impl] leaves to it. A caller reads its callee's specification, whose
   body is there only where the callee is a function in the logic, so
   editing another body proves no caller again; a caller in another
   package, [reader], reads the specification the callee's package
   exports, whose body is there only for a [transparent] function. *)
let source_at ?reader database (path : Path.t) =
  let specification =
    match reader with
    | Some package when package <> Path.package path -> Infer.exported_specification_of_path
    | _ -> Infer.specification_of_path
  in
  match Query.demand database specification path with
  | None -> None
  | Some (core, substitution) -> (
      if Option.is_some (Query.demand database Infer.derived path) then
        Some
          ( { key = None; name = Path.show path; core; spans = lazy [||]; text = lazy "" },
            substitution,
            Derived )
      else
        let own_key =
          Option.bind (Query.demand database Interface.Summary.key path) (fun key ->
              Option.map (fun _ -> key) (Query.demand database Infer.core key))
        in
        match (own_key, path) with
        | Some key, _ -> Some (source_of database key core, substitution, Written)
        | None, Method { owner; name; receiver } ->
            Option.bind (Interface.Impls.impl_interface database owner)
              (fun (impl : T.impl_interface) ->
                Option.map
                  (fun key -> (source_of database key core, substitution, Provided))
                  (Query.demand database Interface.Summary.key
                     (Method { owner = impl.implements.trait; name; receiver })))
        | None, _ -> None)

(* What a trait's clauses and laws are read with for a type: [Self] the
   type, and each of the trait's parameters its argument. *)
let trait_substitution database (trait : T.trait_reference) (ty : T.ty) =
  let generics =
    match Query.demand database Interface.Environment.interface trait.trait with
    | Some (Interface.Environment.Trait_interface interface) ->
        List.map (fun (generic : T.generic) -> generic.generic) interface.trait_generics
    | _ -> []
  in
  let rec pair generics arguments =
    match (generics, arguments) with
    | generic :: generics, argument :: arguments -> (generic, argument) :: pair generics arguments
    | _ -> []
  in
  ({ T.owner = trait.trait; name = "Self" }, T.Type ty) :: pair generics trait.trait_arguments

(* A form's clauses about what it defines. *)
let part_of ?(inherited = false) callee =
  match callee.core.definition with
  | Function { parameters; contract; _ } ->
      Some
        {
          callee;
          parameters;
          requires = List.map (fun (clause : condition) -> clause.value) contract.requires;
          ensures = contract.ensures;
          decreases = contract.decreases;
          costs =
            List.filter
              (fun (cost : Core.cost) ->
                match cost with { resource = Time; bound = Finite; _ } -> false | _ -> true)
              contract.costs;
          inherited;
        }
  | _ -> None

let body_of callee = match callee.core.definition with Function { body; _ } -> body | _ -> None

(* Whether a pattern binds a part of what it matches [mut]. *)
let rec lends_mut (pattern : pattern) =
  match pattern.kind with
  | Bind { mode = T.Mut; _ } -> true
  | Variant { fields; _ } | Record fields -> List.exists (fun (_, inner) -> lends_mut inner) fields
  | Alternatives alternatives -> List.exists lends_mut alternatives
  | Wildcard | Bind _ | Literal _ | Range _ | Equal_to _ -> false

let holds_todo (body : block) =
  let found = ref false in
  Core_walk.block
    (Core_walk.deep
       {
         Core_walk.ignore_all with
         expression =
           (fun (node : Core.expression) -> match node.kind with Todo -> found := true | _ -> ());
       })
    body;
  !found

(* The [proof]s written for a trait's laws on a type, in the package: each
   law's name, with the proof's source, the renaming of the proof's generic
   parameters to the type's arguments, and the proof's parameters and body. *)
let law_proofs database package (trait : T.trait_reference) (for_type : T.ty) =
  let same_argument (left : T.argument) (right : T.argument) =
    match (left, right) with Type left, Type right -> T.equal left right | _ -> left = right
  in
  List.concat_map
    (fun module_ ->
      List.filter_map
        (fun (declaration : Names.declaration) ->
          match
            ( declaration.kind,
              Query.demand database Interface.Environment.interface declaration.path )
          with
          | Law_proof, Some (Interface.Environment.Law_proof_interface proven)
            when Path.equal proven.trait.trait trait.trait -> (
              let variables =
                List.map (fun (generic : T.generic) -> generic.generic) proven.generics
              in
              match Interface.Impls.match_type ~variables [] proven.for_type for_type with
              | Some renaming
                when List.equal same_argument
                       (List.map (T.substitute_argument renaming) proven.trait.trait_arguments)
                       trait.trait_arguments -> (
                  match source_at_key database (Names.key_of declaration) with
                  | Some
                      ({ core = { definition = Law_proof { parameters; body }; _ }; _ } as source)
                    ->
                      Some (proven.law, (source, renaming, parameters, body))
                  | _ -> None)
              | _ -> None)
          | _ -> None)
        (Query.demand database Names.declarations module_))
    (Query.demand database Workspace.modules package)

(* Whether an [impl] writes a method whose body holds a [todo]. Its laws
   are about what its methods return, so they wait, as the methods'
   contracts do. *)
let impl_unfinished database (key : Names.key) =
  List.exists
    (fun (method_ : Names.key) ->
      match source_at_key database method_ with
      | Some { core = { definition = Function { body = Some body; _ }; _ }; _ } -> holds_todo body
      | _ -> false)
    (Query.demand database Names.contained key)

(* Whether an [impl]'s law is not shown: the [impl] is unfinished, so its
   laws wait, or the law's proof holds a [todo]. A proof that assumes it
   has a hole there. *)
let law_unshown database (impl : Path.t) (trait : T.trait_reference) for_type name =
  match Query.demand database Interface.Summary.key impl with
  | Some key ->
      impl_unfinished database key
      || List.exists
           (fun (law, (_, _, _, body)) -> law = name && holds_todo body)
           (law_proofs database (Path.package impl) trait for_type)
  | None -> false

(* Whether a body is functional, so that it can be the function's
   definition: [let], [if], [match], [is], calls, fields, building values,
   [with], operators, and quantifiers, with no [var], assignment, loop,
   [return], or argument lent to change. *)
let functional walk =
  let fine = ref true in
  let rec visit =
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : expression) ->
          match node.kind with
          | Return _ | Break | Continue | Todo | Echo _ | Provide _ | Unreachable -> fine := false
          | Call { arguments; _ } ->
              if
                List.exists
                  (function Passed { mode = T.Mut; _ } -> true | Passed _ | Default -> false)
                  arguments
              then fine := false;
              Core_walk.expression_children visit node
          | _ -> Core_walk.expression_children visit node);
      statement =
        (fun (node : statement) ->
          match node.kind with
          | Let { pattern; else_ = None; _ } when not (binds_variable pattern) ->
              Core_walk.statement_children visit node
          | Evaluate _ -> Core_walk.statement_children visit node
          | _ -> fine := false);
      pattern = (fun node -> Core_walk.pattern_children visit node);
    }
  and binds_variable (pattern : pattern) =
    let found = ref false in
    Core_walk.pattern_children
      {
        Core_walk.ignore_all with
        pattern = (fun inner -> if binds_variable inner then found := true);
      }
      pattern;
    !found || match pattern.kind with Bind { mutable_; _ } -> mutable_ | _ -> false
  in
  walk visit;
  !fine

let functional_block (body : block) = functional (fun visit -> Core_walk.block visit body)

let functional_expression (node : expression) =
  functional (fun visit -> Core_walk.expression visit node)

let make_contract database path ~own ~others ~body =
  let signature = Interface.Impls.signature database path in
  let pure =
    match signature with
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
    match signature with
    | Some { output = Lends _; _ } -> `Lends
    | Some { output = Yields _; _ } -> `Yields
    | _ -> `Returns
  in
  let definition =
    match body with
    | Some body when pure && result_kind = `Returns && functional_block body -> Some (own, body)
    | _ -> None
  in
  { parts = own :: others; pure; result_kind; definition }

(* The contract of a function, a theorem, or a type's own method. *)
let function_contract ~reader database (path : Path.t) =
  Option.bind (source_at ~reader database path) (fun (callee, _, _) ->
      Option.map
        (fun own -> make_contract database path ~own ~others:[] ~body:(body_of callee))
        (part_of callee))

(* A trait's method's clauses. *)
let trait_part database (trait : Path.t) name receiver =
  Option.bind
    (source_at database (Method { owner = trait; name; receiver }))
    (fun (callee, _, _) -> part_of ~inherited:true callee)

(* A capability's method's contract. Its calls are never a function in the
   logic: two calls may give different results, since the prover never
   models an implementation's state. *)
let capability_contract database (capability : Path.t) name =
  let path = Path.Method { owner = capability; name; receiver = Static } in
  Option.bind (source_at database path) (fun (callee, _, _) ->
      Option.map
        (fun own -> { (make_contract database path ~own ~others:[] ~body:None) with pure = false })
        (part_of callee))

let capability_part database (capability : Path.t) name =
  Option.bind
    (source_at database (Method { owner = capability; name; receiver = Static }))
    (fun (callee, _, _) -> part_of callee)

(* A trait method's body, when it provides one. *)
let provided_body database (trait : Path.t) name receiver =
  Option.bind
    (source_at database (Method { owner = trait; name; receiver }))
    (fun (callee, _, _) -> body_of callee)

(* A trait method's contract: the [impl]'s own clauses with the trait's,
   when the call is known to reach one [impl], and the trait's alone
   through a bound or [any]. *)
let method_contract ~reader database (trait : T.trait_reference) name receiver (evidence : evidence)
    =
  let trait_side = trait_part database trait.trait name receiver in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match source_at ~reader database path with
      | Some (callee, _, (Written | Derived)) ->
          Option.map
            (fun own ->
              make_contract database path ~own ~others:(Option.to_list trait_side)
                ~body:(body_of callee))
            (part_of callee)
      | Some (_, _, Provided) | None ->
          (* A method the [impl] leaves to its trait: the trait's clauses,
             with the [impl]'s signature for the method. *)
          Option.map (fun own -> make_contract database path ~own ~others:[] ~body:None) trait_side)
  | Bound | Dynamic ->
      Option.map
        (fun own ->
          make_contract database
            (Path.Method { owner = trait.trait; name; receiver })
            ~own ~others:[] ~body:None)
        trait_side

let distinct_counters counters =
  List.fold_left
    (fun found counter ->
      if List.exists (fun other -> Costs.key other = Costs.key counter) found then found
      else found @ [ counter ])
    [] counters

(* What a cost clause counts, with the locals it is read with, which give
   a [calls] clause's parameter its value. *)
let resource_of (cost : Core.cost) ~locals : Costs.resource option =
  match cost.resource with
  | Time -> Some Time
  | Allocations -> Some Allocations
  | Allocated_bytes -> Some Allocated_bytes
  | Calls (Function_parameter local) ->
      Option.map (fun term -> Costs.Calls (Through term)) (Locals.find_opt local locals)
  | Calls (Capability path) -> Some (Calls (Capability path))
  | Calls (Capability_method (path, name)) -> Some (Calls (Capability_method (path, name)))

(* The type a place holds. *)
let place_type context frame (place : place) =
  substituted context frame (Core_walk.place_type place)

let operand_type context frame = function
  | Place place -> place_type context frame place
  | Value node -> type_of context frame node

(* The local or [self] a place is part of: what an assignment or a lend to
   change it changes. *)
let rec root_of (place : place) =
  match place with
  | Local { local; _ } -> Some local
  | Field { base; _ } -> root_of base
  | Constant _ -> None
  | Lent { kind = Call { arguments = Passed { value = Place receiver; _ } :: _; _ }; _ } ->
      root_of receiver
  | Lent _ | Temporary _ -> None

let is_test context = match context.current with Path.Test _ -> true | _ -> false

(* Whether a function is a private method that takes [mut self] and is
   written as [fn Type.method], which is a step of an update: its
   receiver's invariant is neither shown at a call nor assumed after. *)
let is_updating_helper database (path : Path.t) =
  match path with
  | Method { receiver = Mut; _ } -> (
      match Interface.Summary.definition database path with
      | Some
          ( _,
            {
              visibility = Private;
              kind = Function { signature = { name = Member_name _; _ }; _ };
              _;
            } ) ->
          true
      | _ -> false)
  | _ -> false

(* Expressions *)

let comparison (comparison : comparison) =
  match comparison with
  | Equal -> Some "="
  | Less -> Some "<"
  | Less_equal -> Some "<="
  | Greater -> Some ">"
  | Greater_equal -> Some ">="
  | Not_equal -> None

let rec expression context frame (node : expression) : (frame * L.term) option =
  if frame.source.key = Some context.home then
    try expression_kind context frame node
    with Foreign_unsupported message -> raise (Unsupported (at frame node, message))
  else
    try expression_kind context frame node
    with Unsupported (_, message) ->
      raise (Foreign_unsupported (Printf.sprintf "%s, in `%s`" message frame.source.name))

(* An index or a range read, which the ownership check may have paired
   with another: the two must reach different elements. Two indexes of one
   collection that are lent together, or used by two branches of
   [parallel], must differ, which the ownership check left to the prover.
   Each is read as it is evaluated, and the pair is shown once both are. *)
and note_place context frame (node : expression) place =
  let origin = node.origin in
  if
    frame.source.key = Some context.home
    && List.exists (fun (first, second) -> first = origin || second = origin) context.disjoint
  then begin
    context.indexes <- (origin, (place, at frame node)) :: context.indexes;
    let outside index start stop =
      L.(Apply ("<", [ index; start ]) ||| Apply ("<=", [ stop; index ]))
    in
    List.iter
      (fun (first, second) ->
        if first = origin || second = origin then
          match (List.assoc_opt first context.indexes, List.assoc_opt second context.indexes) with
          | Some (a, (first_span : span)), Some (b, (second_span : span)) ->
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
              let text (span : span) =
                let source_text = Lazy.force frame.source.text in
                if span.stop <= String.length source_text then
                  String.sub source_text span.start (span.stop - span.start)
                else "this expression"
              in
              oblige context frame Disjoint (at frame node)
                (Printf.sprintf
                   "`%s` and `%s` may reach the same elements, which are used together."
                   (text first_span) (text second_span))
                apart
          | _ -> ())
      context.disjoint
  end

and value context frame node =
  match expression context frame node with
  | Some (frame, term) -> (frame, term)
  | None -> unsupported (at frame node) "an expression that never returns, used as a value"

(* The value at a place. *)
and place_value context frame (place : place) =
  match place with
  | Local { local = Self; _ } -> (
      match frame.self with
      | Some self -> (frame, self)
      | None -> raise (Foreign_unsupported "`self` outside a method"))
  | Constant { path; _ } -> (frame, constant_value context frame path)
  | Local { local; _ } -> (
      if frame.checking && not context.reading_callback then escaping_callback context frame local;
      match Locals.find_opt local frame.locals with
      | Some term -> (frame, term)
      | None -> raise (Foreign_unsupported "a local the prover did not bind"))
  | Field { base; field; type_; _ } ->
      let base_type = place_type context frame base in
      let frame, term = place_value context frame base in
      if constructors context base_type = None then
        raise
          (Foreign_unsupported
             (Printf.sprintf "a field of `%s`, whose fields the prover does not see"
                (T.show base_type)));
      ignore (sort_of context base_type);
      (frame, field_of context frame base_type None field (substituted context frame type_) term)
  | Lent node | Temporary node -> value context frame node

and operand_value context frame = function
  | Place place -> place_value context frame place
  | Value node -> value context frame node

(* A function-typed parameter whose type has a [requires], read as a value
   other than to call it or pass it to a parameter: the value's type keeps
   no [requires], so the [requires] must hold for every argument. *)
and escaping_callback context frame local =
  match
    ( List.find_opt (fun (parameter : Core.parameter) -> parameter.local = local) context.parameters,
      local_type context frame local )
  with
  | ( Some { callback_contract = Some { inputs; requires = _ :: _ as requires }; name; _ },
      Some (T.Function function_type) )
    when List.length inputs = List.length function_type.inputs ->
      let arguments =
        List.map
          (fun (_, input) ->
            let input = substituted context frame input in
            let term = arrive context frame "argument" input in
            assume_valid context frame input term;
            term)
          function_type.inputs
      in
      check_callback_contract context frame
        (span_of frame.source (List.hd requires).origin)
        ~name inputs requires arguments ~promised:(L.Boolean true)
        ~why:"is used as a value whose type promises nothing of its arguments"
  | _ -> ()

and reading_callback : 'a. _ -> (unit -> 'a) -> 'a =
 fun context read ->
  let saved = context.reading_callback in
  context.reading_callback <- true;
  Fun.protect ~finally:(fun () -> context.reading_callback <- saved) read

(* A function-typed parameter passed on for another callee's parameter:
   what that parameter promises its arguments must imply this one's
   [requires]. *)
and check_forwarded_callback context frame (node : expression) (call_ : call) (passed : passed)
    local values =
  match
    List.find_opt (fun (parameter : Core.parameter) -> parameter.local = local) context.parameters
  with
  | Some { callback_contract = Some { inputs; requires = _ :: _ as requires }; name; _ } -> (
      match parameter_type context frame call_ passed.position with
      | Some (T.Function expected) when List.length expected.inputs = List.length inputs ->
          let arguments =
            List.map
              (fun (_, input) ->
                let input = substituted context frame input in
                let term = arrive context frame "argument" input in
                assume_valid context frame input term;
                term)
              expected.inputs
          in
          let known = List.map (fun (passed : passed) -> (passed.position, passed.term)) values in
          check_callback_contract context frame (at frame node) ~name inputs requires arguments
            ~promised:
              (L.conjunction (callback_facts context frame call_ passed.position known arguments))
            ~why:"is passed for a parameter that may not promise what it requires"
      | _ -> escaping_callback context frame local)
  | _ -> ()

(* That a function-typed parameter's [requires], read with its parameters
   as they were on entry, holds wherever [promised] does. *)
and check_callback_contract context frame span ~name inputs requires arguments ~promised ~why =
  let locals =
    List.fold_left2
      (fun locals (input, _) term -> Locals.add input term locals)
      frame.old_locals inputs arguments
  in
  let inside = { frame with locals; self = frame.old_self; checking = false } in
  List.iter
    (fun (clause : expression) ->
      oblige context (restrict frame promised) Requires span
        (Printf.sprintf "`%s` %s, so its `%s` may not hold." name why
           (quote frame.source clause.origin))
        (snd (clause_value context inside clause)))
    requires

and expression_kind context frame (node : expression) : (frame * L.term) option =
  let source = frame.source in
  match node.kind with
  | Integer number -> Some (frame, L.Integer number)
  | Float number -> (
      match float_format (type_of context frame node) with
      | Some format -> Some (frame, float_literal format number)
      | None -> unsupported (at frame node) "a float literal without a float type")
  | Boolean value -> Some (frame, L.Boolean value)
  | String text -> Some (frame, text_value context frame (type_of context frame node) text)
  | Template { literals; call = made } -> Some (tagged_template context frame node literals made)
  | Use place -> Some (place_value context frame place)
  | Copy operand ->
      let ty = operand_type context frame operand in
      let frame, term = operand_value context frame operand in
      Some (copied context frame ty term, term)
  | Function_value { path; type_arguments } ->
      Some (frame, global_value context frame node path type_arguments)
  | Value_parameter parameter -> Some (frame, value_term context frame (Value_parameter parameter))
  | Lambda { parameters; body; captures; _ } ->
      Some (lambda context frame node parameters captures body ~facts:(fun _ -> []))
  | Construct { variant; fields } -> Some (construct context frame node variant fields)
  | Collection_literal { elements; _ } -> Some (list_literal context frame node elements)
  | Map_literal { entries; _ } -> Some (map_literal context frame node entries)
  | Record_update { base; updates } -> Some (with_ context frame node base updates)
  | Slice
      {
        base;
        call =
          {
            kind =
              Call
                {
                  arguments =
                    [ _; Passed { value = Value start; _ }; Passed { value = Value stop; _ } ];
                  _;
                };
            _;
          };
      } ->
      Some (slice context frame node base ~start:(Some start) ~stop:(Some stop) ~inclusive:false)
  | Slice _ -> unsupported (at frame node) "a slice whose call is not of `slice_range`"
  | Call call_ -> (
      match resolved_call context frame node call_ with
      | Some _ when T.equal (type_of context frame node) T.Never ->
          (* A call that gives [Never] does not return, so the path ends. *)
          None
      | found -> found)
  | Operator { operation; arguments } -> Some (operator context frame node operation arguments)
  | Compare { comparison = compared; left; right } ->
      let operand_type = type_of context frame left in
      let frame, a = value context frame left in
      let frame, b = value context frame right in
      Some
        ( frame,
          if float_format operand_type <> None then
            match compared with
            | Equal -> float_equal a b
            | Not_equal -> L.not_ (float_equal a b)
            | Less -> float_less a b
            | Less_equal -> L.( ||| ) (float_less a b) (float_equal a b)
            | Greater -> float_less b a
            | Greater_equal -> L.( ||| ) (float_less b a) (float_equal a b)
          else
            match comparison compared with
            | Some symbol when compared = Equal ->
                ignore symbol;
                L.equal a b
            | Some symbol -> L.Apply (symbol, [ a; b ])
            | None -> L.not_ (L.equal a b) )
  | Not inner ->
      let frame, term = value context frame inner in
      Some (frame, L.not_ term)
  | And (left, right) ->
      let frame, left_value = value context frame left in
      short_circuit context frame right ~runs:left_value ~otherwise:(L.Boolean false) ~binds:true
        (L.( &&& ) left_value)
  | Or (left, right) ->
      let frame, left_value = value context frame left in
      short_circuit context frame right ~runs:(L.not_ left_value) ~otherwise:(L.Boolean true)
        ~binds:false (L.( ||| ) left_value)
  | Implies (left, right) ->
      let frame, left_value = value context frame left in
      short_circuit context frame right ~runs:left_value ~otherwise:(L.Boolean true) ~binds:false
        (L.( ==> ) left_value)
  | Matches { value = tested; pattern } ->
      let tested_type = operand_type context frame tested in
      let frame, term = operand_value context frame tested in
      let condition, frame = pattern_match context frame pattern term tested_type in
      Some (frame, condition)
  | Cursor_next place -> (
      (* A pull of a cursor whose method the prover knows. *)
      let cursor_type = place_type context frame place in
      let frame, cursor = place_value context frame place in
      match List.assoc_opt cursor context.cursors with
      | Some made ->
          let pulled, later = pull context frame made cursor ~cursor_type in
          let frame = store context frame place later in
          Some (spend context frame one_step, pulled)
      | None ->
          unsupported (at frame node) "a pull of a cursor whose method the prover does not know")
  | Convert { conversion; value = converted } -> (
      let frame, term = value context frame converted in
      match conversion with
      | Widen ->
          (* A named function's costs are checked where it is passed, and a
             lambda's where it is written. *)
          (match (converted.kind, type_of context frame converted, type_of context frame node) with
          | (Function_value _ | Lambda _), _, _ -> ()
          | _, T.Function given, T.Function expected
            when not (List.for_all (fun cost -> List.mem cost given.costs) expected.costs) ->
              unsupported (at frame node) "a function value's costs"
          | _ -> ());
          Some (frame, term)
      | To_integer -> Some (frame, term)
      | From_integer ->
          let ty = type_of context frame node in
          oblige context frame Fits (at frame node)
            (Printf.sprintf "`%s` may not fit in `%s`." (quote source node.origin) (T.show ty))
            (in_range ty term);
          Some (frame, term))
  | To_any { value = inner; _ } ->
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
      Some (frame, arrive context frame "any" (type_of context frame node))
  | If { condition; then_; else_ } -> if_ context frame node condition then_ else_
  | Match { scrutinees; arms; _ } -> match_ context frame node scrutinees arms
  | Block block_ -> block_value context frame block_
  | Provide { implementations; body } ->
      (* The body runs with the implementations, which the prover never
         models, so a capability call in it gives a fresh value by its
         contract. Each one handed over [mut] holds a fresh value of its
         type afterward, which meets its type's invariants. *)
      let frame =
        List.fold_left
          (fun frame (implementation : implementation) ->
            fst (operand_value context frame implementation.value))
          frame implementations
      in
      Option.map
        (fun ((after : frame), result) ->
          let after =
            List.fold_left
              (fun after (implementation : implementation) ->
                match (implementation.mode, implementation.value) with
                | T.Mut, Place place ->
                    let after = havoc_root context after place in
                    (match root_of place with
                    | Some Self -> (
                        match (after.self, after.self_type) with
                        | Some self, Some ty -> assume_valid context after ty self
                        | _ -> ())
                    | Some local -> (
                        match
                          (Locals.find_opt local after.locals, local_type context after local)
                        with
                        | Some term, Some ty -> assume_valid context after ty term
                        | _ -> ())
                    | None -> ());
                    after
                | _ -> after)
              after implementations
          in
          (after, result))
        (block_value context frame body)
  | Return returned ->
      (match returned with
      | Some returned -> (
          match expression context frame returned with
          | Some (after, term) -> context.returns <- (after, Some term) :: context.returns
          | None -> ())
      | None -> context.returns <- (frame, None) :: context.returns);
      None
  | Unreachable ->
      oblige context frame Unreachable (at frame node) "This `unreachable` may be reached."
        (L.Boolean false);
      None
  | Todo ->
      (* What follows a [todo] on its path is not shown, and a build refuses
         what can reach it. In a proof it is a hole. *)
      if context.proving then begin
        context.holes <- (context.home, at frame node) :: context.holes;
        context.unfinished <- frame.condition :: context.unfinished
      end;
      Some
        ( { frame with condition = L.Boolean false },
          arrive context frame "todo" (type_of context frame node) )
  | Break -> (
      match frame.loop with
      | Some exits ->
          exits.breaks <- frame :: exits.breaks;
          None
      | None -> unsupported (at frame node) "`break` outside a loop")
  | Continue -> (
      match frame.loop with
      | Some exits ->
          exits.continues <- frame :: exits.continues;
          None
      | None -> unsupported (at frame node) "`continue` outside a loop")
  | Echo inner -> expression context frame inner
  | Result -> (
      match frame.result with
      | Some result -> Some (frame, result)
      | None -> unsupported (at frame node) "`result` here")
  | Old inner ->
      let entry = { frame with locals = frame.old_locals; self = frame.old_self } in
      let _, term = value context entry inner in
      Some (frame, term)
  | Current_target -> (
      match frame.updating with
      | Some term -> Some (frame, term)
      | None -> unsupported (at frame node) "an update's target outside an update")
  | Quantified { quantifier; binder; body } -> quantified context frame node quantifier binder body
  | Yielded -> (
      (* What the nearest loop or method hands out: a loop's own parts, or
         else, in a lending or yielding method's body, the method's. *)
      match (frame.yielded, frame.handed_out) with
      | Some yielded, _ -> Some (frame, yielded)
      | None, Some handed_out when source.key = Some context.home -> Some (frame, handed_out)
      | _ -> unsupported (at frame node) "`yielded` here")
  | Finished -> (
      match frame.finished with
      | Some finished -> Some (frame, finished)
      | None -> unsupported (at frame node) "`finished` here")
  | Identical (first, second) ->
      (* Identity, for every type: the solver's equality. *)
      let frame, first_value = value context frame first in
      let frame, second_value = value context frame second in
      extensional context frame (type_of context frame first) first_value second_value;
      Some (frame, L.equal first_value second_value)
  | Specification_function { function_; arguments } ->
      specification_function context frame node function_ arguments
  | Method_time callee -> Some (frame, method_time context frame callee)
  | Task_exit { tasks; exit } -> (
      (* The exit is where the block it leaves ends, after the other
         branches, so here it is only recorded. *)
      match tasks with
      | Iteration _ :: _ ->
          unsupported (at frame node) "an early exit from an iteration of a `concurrent for` loop"
      | _ -> (
          let record at exit_ = context.leaving <- { tasks; at; exit = exit_ } :: context.leaving in
          match exit.kind with
          | Return (Some returned) -> (
              match expression context frame returned with
              | Some (after, term) ->
                  record after (Returning (Some term));
                  None
              | None -> None)
          | Return None ->
              record frame (Returning None);
              None
          | Break ->
              record frame Breaking;
              None
          | Continue ->
              record frame Continuing;
              None
          | _ ->
              unsupported (at frame node)
                "an early exit that is not a `return`, `break`, or `continue`"))

(* The right side of [&&], [||], or [==>], which runs only where [runs]
   holds. One that changes a local, as a call with a [mut] argument does,
   joins its path with the one where it did not run, as an [if] would;
   otherwise the operator is its operands' term, as written, and only
   [&&] keeps what its right side binds, as an [is] does. *)
and short_circuit context frame right ~runs ~otherwise ~binds combine =
  let after, right_value = value context (restrict frame runs) right in
  (* What the right side spends is known only where it ran, so where it
     spends anything the paths where it ran and did not run are joined. *)
  let changed =
    Locals.exists (fun id term -> Locals.find_opt id after.locals <> Some term) frame.locals
    || after.self <> frame.self || after.spent <> frame.spent
  in
  if not changed then
    Some ((if binds then { after with condition = frame.condition } else frame), combine right_value)
  else
    match
      join context ~value_type:T.bool
        [ (after, Some right_value); (restrict frame (L.not_ runs), Some otherwise) ]
    with
    | Some (joined, Some term) -> Some (joined, term)
    | Some (joined, None) -> Some (joined, L.Boolean true)
    | None -> None

and equal_of context frame (ty : T.ty) a b =
  if structural context ty then L.equal a b
  else if float_format ty <> None then float_equal a b
  else
    match written_equal context ty a b with
    | Some equal -> equal
    | None -> derived_equal context frame ty a b

(* [==] on a type whose [impl] of [Equal] is written: the term a call of its
   [equal] is, so that what the [impl]'s contract says of a call holds of
   it. *)
and written_equal context ty a b =
  match concrete_impl context { trait = equal_trait; trait_arguments = []; associated = [] } ty with
  | Some (((Impl _ : Path.t) as impl), arguments) -> (
      let evidence : evidence = Impl { impl; arguments } in
      match
        method_contract ~reader:(Path.package context.current) context.database
          { trait = equal_trait; trait_arguments = []; associated = [] }
          "equal" Read evidence
      with
      | Some contract when contract.pure ->
          let symbol =
            "function."
            ^ Path.show (Path.Method { owner = impl; name = "equal"; receiver = Read })
            ^ "[" ^ type_key ty ^ "]"
          in
          let sort = sort_of context ty in
          declare context (L.Function (symbol, [ sort; sort ], L.Bool));
          Some (L.Apply (symbol, [ a; b ]))
      | _ -> None)
  | _ -> None

and derived_equal context frame (ty : T.ty) a b =
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
                 match written_equal context field_type a b with
                 | Some equal -> equal
                 | None ->
                     (* Unfolded only when it is compared itself. *)
                     let symbol = "equal." ^ type_key field_type in
                     declare context
                       (L.Function
                          ( symbol,
                            [ sort_of context field_type; sort_of context field_type ],
                            L.Bool ));
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

(* An operation the solver knows only by the range of its result. *)
and opaque_operation context frame ty name arguments =
  let sorts = List.map (fun _ -> L.Int) arguments in
  let symbol = Printf.sprintf "operation.%s.%s" name (T.show ty) in
  declare context (L.Function (symbol, sorts, sort_of context ty));
  let term = L.Apply (symbol, arguments) in
  assume context frame (in_range ty term);
  term

(* An arithmetic, bitwise, or shift operation on built-in numbers, or on
   [Integer]s in a specification: IEEE 754's for floats, and otherwise the
   exact result, which must fit its type. *)
and operator context frame (node : expression) (operation : Intrinsic.operation) arguments =
  let frame, operands =
    List.fold_left
      (fun (frame, operands) argument ->
        let frame, term = value context frame argument in
        (frame, operands @ [ term ]))
      (frame, []) arguments
  in
  let ty = type_of context frame node in
  let source = frame.source in
  let span = at frame node in
  if float_format ty <> None then
    let result =
      match (operation, operands) with
      | Add, [ a; b ] -> float_operation "fp.add" a b
      | Subtract, [ a; b ] -> float_operation "fp.sub" a b
      | Multiply, [ a; b ] -> float_operation "fp.mul" a b
      | Divide, [ a; b ] -> float_operation "fp.div" a b
      | Negate, [ a ] -> L.Apply ("fp.neg", [ a ])
      | _ -> arrive context frame "operator" ty
    in
    (frame, result)
  else
    match (operation, operands) with
    | (Add | Subtract | Multiply | Divide | Remainder), [ left; right ] ->
        (frame, arithmetic context frame node ty operation left right)
    | Negate, [ inner ] ->
        let negated = L.Apply ("-", [ inner ]) in
        if bounds ty <> None then
          oblige context frame Overflow span
            (Printf.sprintf "`%s` may overflow `%s`." (quote source node.origin) (T.show ty))
            (in_range ty negated)
        else if ty <> T.Integer then unsupported span "negating a value of `%s`" (T.show ty);
        (frame, negated)
    | Complement, [ inner ] -> (frame, opaque_operation context frame ty "complement" [ inner ])
    | (Shift_left | Shift_right), [ left; right ] ->
        let amount = List.nth arguments 1 in
        (match width ty with
        | Some bits ->
            oblige context frame Shift (at frame amount)
              (Printf.sprintf "The shift amount `%s` may not be less than %d."
                 (quote source amount.origin) bits)
              L.(Apply ("<", [ right; int bits ]))
        | None -> unsupported span "a shift of `%s`" (T.show ty));
        let name = match operation with Shift_left -> "shift_left" | _ -> "shift_right" in
        let shifted = opaque_operation context frame ty name [ left; right ] in
        (* An unsigned shift multiplies or divides by a power of two: to the
           left exactly, where the product fits. *)
        (match bounds ty with
        | Some (low, high) when Z.equal low Z.zero && not (L.mentions frame.bound right) ->
            let scale = power_of context frame (L.int 2) right in
            assume context frame
              (match operation with
              | Shift_left ->
                  L.(
                    Apply ("<=", [ Apply ("*", [ left; scale ]); Integer high ])
                    ==> equal shifted (Apply ("*", [ left; scale ])))
              | _ -> L.equal shifted (L.truncated_divide left scale))
        | _ -> ());
        (frame, shifted)
    | (Bit_and | Bit_or | Bit_xor), [ left; right ] ->
        let name = match operation with Bit_and -> "and" | Bit_or -> "or" | _ -> "xor" in
        let term = opaque_operation context frame ty name [ left; right ] in
        (* Of unsigned values, [and] is at most each operand, [or] at
           least each, and [or] and [xor] at most their sum and below each
           power of two both operands are below. *)
        (match bounds ty with
        | Some (low, _) when Z.equal low Z.zero -> (
            let at_most bound = L.Apply ("<=", [ term; bound ]) in
            match operation with
            | Bit_and -> assume context frame L.(at_most left &&& at_most right)
            | _ ->
                let sum = L.Apply ("+", [ left; right ]) in
                if operation = Bit_or then
                  assume context frame
                    L.(Apply ("<=", [ left; term ]) &&& Apply ("<=", [ right; term ]));
                assume context frame (at_most sum);
                declare context (L.Function (Costs.power_symbol, [ L.Int; L.Int ], L.Int));
                let exponent = L.Symbol "exponent" in
                let below value =
                  L.Apply ("<", [ value; L.Apply (Costs.power_symbol, [ L.int 2; exponent ]) ])
                in
                assume context frame
                  (L.Forall
                     ( [ ("exponent", L.Int) ],
                       L.(
                         Apply ("<=", [ int 0; exponent ])
                         &&& below left &&& below right ==> below term) )))
        | _ -> ());
        (frame, term)
    | _ -> unsupported span "this operator"

and arithmetic context frame (node : expression) ty (operation : Intrinsic.operation) left right =
  let source = frame.source in
  let span = at frame node in
  let exact =
    match operation with
    | Add -> L.Apply ("+", [ left; right ])
    | Subtract -> L.Apply ("-", [ left; right ])
    | Multiply -> L.Apply ("*", [ left; right ])
    | Divide -> L.truncated_divide left right
    | _ -> L.truncated_remainder left right
  in
  (match operation with
  | Divide | Remainder ->
      oblige context frame Division span
        (Printf.sprintf "The divisor in `%s` may be zero." (quote source node.origin))
        (L.not_ (L.equal right (L.int 0)))
  | _ -> ());
  (match bounds ty with
  | Some (low, _) when operation = Divide || operation = Remainder ->
      if Z.sign low < 0 then
        oblige context frame Overflow span
          (Printf.sprintf "`%s` may overflow `%s`: the least value over -1."
             (quote source node.origin) (T.show ty))
          (L.not_ L.(equal left (Integer low) &&& equal right (int (-1))))
  | Some _ ->
      oblige context frame Overflow span
        (Printf.sprintf "`%s` may overflow `%s`." (quote source node.origin) (T.show ty))
        (in_range ty exact)
  | None -> ());
  exact

and if_ context frame (node : expression) condition (then_ : block) (else_ : block option) =
  let frame, test = value context frame condition in
  let then_result = block_value context (restrict frame test) then_ in
  let otherwise = restrict frame (L.not_ test) in
  let else_result =
    match else_ with
    | Some block_ -> block_value context otherwise block_
    | None -> Some (otherwise, L.Boolean true)
  in
  let ty = type_of context frame node in
  let carries_value = else_ <> None && not (T.equal ty T.unit || ty = T.Never) in
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

and quantified context frame (node : expression) (quantifier : Syntax.quantifier) binder body =
  let make ?count bound_symbol sort premise body_frame =
    let mark = context.fresh in
    (* The body runs only for the values the premise admits, which may be
       none, so what it assumes is only for them. *)
    let body_frame =
      restrict
        { body_frame with binders = (bound_symbol, sort, premise) :: body_frame.binders }
        premise
    in
    let after, body_value = value context body_frame body in
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
  let inner = { frame with bound = symbol :: frame.bound } in
  let each = L.Symbol symbol in
  (* Over a collection's elements: by index into its sequence, or each
     value its set contains, each matched against the binding's pattern,
     which names its parts and leaves out what it does not match. *)
  let over_collection (pattern : pattern) (collection_type : T.ty) collected span =
    let element = substituted context frame pattern.type_ in
    let set_path = Well_known.path Set in
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
          | None -> unsupported span "a quantifier over `%s`" (T.show collection_type)
        in
        let matched, inner = pattern_match context inner pattern each element in
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
            match sequence_at context element sequence each with
            | Some found ->
                let length = sequence_length context element sequence in
                let matched, inner = pattern_match context inner pattern found element in
                make ~count:length symbol Int
                  L.(Apply ("<=", [ int 0; each ]) &&& Apply ("<", [ each; length ]) &&& matched)
                  inner
            | None -> unsupported span "a quantifier over `%s`" (T.show collection_type))
        | None -> unsupported span "a quantifier over `%s`" (T.show collection_type))
  in
  match binder with
  | Over_type { local; type_; _ } ->
      (* Over every value of a type: each in its range, and meeting its
         type's invariants. *)
      let ty = substituted context frame type_ in
      let inner = bind inner local ty each in
      make symbol (sort_of context ty)
        (L.( &&& ) (in_range ty each) (validity context inner ~assuming:true ty each))
        inner
  | Over_range { pattern; start; stop; inclusive } ->
      let _, low = value context frame start in
      let _, high = value context frame stop in
      let _, inner =
        pattern_match context inner pattern each (substituted context frame pattern.type_)
      in
      let premise =
        L.(
          Apply ("<=", [ low; each ]) &&& Apply ((if inclusive then "<=" else "<"), [ each; high ]))
      in
      let count =
        if inclusive then Costs.plus (Costs.minus high low) (L.int 1) else Costs.minus high low
      in
      make ~count symbol Int premise inner
  | Over_collection { pattern; collection } ->
      over_collection pattern
        (type_of context frame collection)
        (snd (value context frame collection))
        (at frame collection)
  (* In code that runs, the collection is what the call of [each] is given. *)
  | Over_each
      {
        pattern;
        call = { kind = Call { arguments = [ Passed { value = given; _ } ]; _ }; _ } as call;
      } ->
      over_collection pattern
        (operand_type context frame given)
        (snd (operand_value context frame given))
        (at frame call)
  | Over_each { call; _ } -> unsupported (at frame call) "this quantifier's loop"

(* A [USize] generic argument's value: a number, or what the parameter
   stands for here, or the parameter itself, a constant the solver knows
   nothing more of. *)
and value_term context frame (value : T.value) =
  match value with
  | Value_parameter parameter -> (
      match List.assoc_opt parameter frame.substitution with
      | Some (T.Value given) when given <> Value_parameter parameter ->
          value_term context frame given
      | _ -> substituted_value_term context value)
  | Known _ | Value_variable _ -> substituted_value_term context value

(* A value already substituted: a number, or a generic, which is a [USize]
   on every path. *)
and substituted_value_term context (value : T.value) =
  match value with
  | Known number -> L.Integer number
  | Value_parameter parameter ->
      let symbol = Printf.sprintf "generic.%s.%s" (Path.show parameter.owner) parameter.name in
      once context ("range." ^ symbol) (fun () ->
          declare context (L.Constant (symbol, Int));
          context.facts <- in_range (T.builtin USize) (L.Symbol symbol) :: context.facts);
      L.Symbol symbol
  | Value_variable _ -> raise (Foreign_unsupported "an unsolved size")

(* The value of an intrinsic's [USize] generic argument, by the generic's
   name. *)
and generic_argument context frame (operation : Intrinsic.operation) type_arguments name =
  let generics = (Intrinsic_signatures.signature operation).generics in
  List.find_map
    (fun ((generic : T.generic), argument) ->
      match argument with
      | T.Value value when generic.generic.name = name -> Some (value_term context frame value)
      | _ -> None)
    (try List.combine generics type_arguments with Invalid_argument _ -> [])

(* An array's elements: a sequence as long as its type says. *)
and array_model context frame (ty : T.ty) term =
  match ty with
  | Named { arguments = [ T.Type element; T.Value count ]; _ } -> (
      match model_of context ty term ~element with
      | Some sequence ->
          assume context frame
            (L.equal (sequence_length context element sequence) (value_term context frame count));
          sequence
      | None -> raise (Foreign_unsupported (Printf.sprintf "the elements of `%s`" (T.show ty))))
  | _ -> raise (Foreign_unsupported (Printf.sprintf "the elements of `%s`" (T.show ty)))

(* Calls *)

(* A call's arguments, as its callee is given them, in its order: each
   written one with its value, and none for a default, which the callee's
   own form holds. Lambdas are proven last, as the type checker checks
   them, so that what the callee promises to pass them can mention the
   other arguments. *)
and call_arguments context frame (node : expression) (call_ : call) ~facts_for =
  let indexed = List.mapi (fun position argument -> (position, argument)) call_.arguments in
  let is_lambda = function
    | Passed { value = Value { kind = Lambda _; _ }; _ } -> true
    | Passed _ | Default -> false
  in
  let frame, evaluated =
    List.fold_left
      (fun (frame, evaluated) (position, (argument : argument)) ->
        match argument with
        | Passed { mode; value = operand } when not (is_lambda argument) ->
            let type_ = operand_type context frame operand in
            let frame, term, run =
              match operand with
              | Value
                  ({
                     kind =
                       Slice
                         {
                           base;
                           call =
                             {
                               kind =
                                 Call
                                   {
                                     arguments =
                                       [
                                         _;
                                         Passed { value = Value start; _ };
                                         Passed { value = Value stop; _ };
                                       ];
                                     _;
                                   };
                               _;
                             };
                         };
                     _;
                   } as slice_node) ->
                  let frame, term, low, high =
                    slice_run context frame slice_node base ~start:(Some start) ~stop:(Some stop)
                      ~inclusive:false
                  in
                  (frame, term, Some (low, high))
              | Place (Local _) ->
                  let frame, term =
                    reading_callback context (fun () -> operand_value context frame operand)
                  in
                  (frame, term, None)
              | _ ->
                  let frame, term = operand_value context frame operand in
                  (frame, term, None)
            in
            (frame, evaluated @ [ { position; mode; operand = Some operand; type_; term; run } ])
        | Passed _ | Default -> (frame, evaluated))
      (frame, []) indexed
  in
  let known = List.map (fun (passed : passed) -> (passed.position, passed.term)) evaluated in
  let passed =
    List.filter_map
      (fun (position, (argument : argument)) ->
        match argument with
        | Passed
            {
              mode;
              value = Value ({ kind = Lambda { parameters; captures; body; _ }; _ } as lambda_node);
            } ->
            let _, term =
              lambda context frame lambda_node parameters captures body
                ~facts:(facts_for position known)
            in
            Some
              {
                position;
                mode;
                operand = Some (Value lambda_node);
                type_ = type_of context frame lambda_node;
                term;
                run = None;
              }
        | Passed _ -> List.find_opt (fun (passed : passed) -> passed.position = position) evaluated
        | Default -> None)
      indexed
  in
  ignore node;
  (frame, passed)

and resolved_call ?lent_final context frame (node : expression) (call_ : call) =
  let span = at frame node in
  (* A call through a function value gives the value first. *)
  let frame, through =
    match call_.callee with
    | Indirect callee ->
        let ty = operand_type context frame callee in
        let frame, term = reading_callback context (fun () -> operand_value context frame callee) in
        (frame, Some (ty, term, callee))
    | _ -> (frame, None)
  in
  let rec unwidened (node : expression) =
    match node.kind with
    | Convert { conversion = Widen; value = inner } -> unwidened inner
    | _ -> node
  in
  List.iter
    (function
      | Passed { value = Value given; _ } -> (
          match unwidened given with
          | { kind = Function_value _; id; _ } ->
              context.passed_values <- id :: context.passed_values
          | _ -> ())
      | Passed _ | Default -> ())
    call_.arguments;
  let frame, values =
    call_arguments context frame node call_ ~facts_for:(fun position known arguments ->
        callback_facts context frame call_ position known arguments)
  in
  List.iter
    (fun (passed : passed) ->
      match passed.operand with
      | Some (Value given) -> (
          match unwidened given with
          | { kind = Function_value { path; _ }; _ } as named -> (
              match
                function_contract ~reader:(Path.package context.current) context.database path
              with
              | Some contract ->
                  check_named_callback context frame call_ passed named path contract values
              | None -> ())
          | _ -> ())
      | Some (Place (Local { local; _ })) ->
          check_forwarded_callback context frame node call_ passed local values
      | _ -> ())
    values;
  (* An index read, which the ownership check may have paired with
     another. *)
  (match (call_.lends, values) with
  | Some _, _ :: index :: _ -> note_place context frame node (One index.term)
  | _ -> ());
  let result_type = type_of context frame node in
  (match call_.callee with
  | Intrinsic _ -> ()
  | _ ->
      let exempt = updating_helper context call_ in
      List.iter
        (fun (passed : passed) ->
          if not (exempt && passed.position = 0) then
            check_valid context frame span passed.type_ passed.term ~deep:true
              ~when_:"when it is passed to this call")
        values);
  (* Each [mut] argument takes a fresh value, stored into its place: a
     local, [self], a field, which rebuilds the value it is in, or an
     element, through its collection's [lends mut] index. A place the prover
     cannot store into forgets its root. *)
  let havoc_mut frame =
    List.fold_left
      (fun frame (passed : passed) ->
        match (passed.mode, passed.operand) with
        | T.Mut, Some (Place place) -> (
            let changed = arrive context frame "changed" passed.type_ in
            try store context frame place changed
            with Unsupported _ | Foreign_unsupported _ -> havoc_root context frame place)
        | T.Mut, Some (Value { kind = Slice { base; _ }; _ }) -> (
            (* The callee changes the elements of the run the slice views,
               and nothing else of its owner: the slice read again after the
               call is a view of the new run, which the callee's
               postconditions are about. *)
            match passed.run with
            | Some (start, stop) -> (
                try sliced_owner_changed context frame base ~start ~stop
                with Unsupported _ | Foreign_unsupported _ -> havoc_root context frame base)
            | None -> havoc_root context frame base)
        | _ -> frame)
      frame values
  in
  let arguments_of (type_arguments : T.argument list) =
    List.map (T.substitute_argument frame.substitution) type_arguments
  in
  let generics_of path =
    match Interface.Impls.signature context.database path with
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
      | Indirect _ -> (
          match through with
          | Some (T.Function function_type, _, _) -> T.terminates function_type
          | _ -> false)
      | Intrinsic _ -> true
    in
    if not ends then
      oblige context frame Termination span
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
            (fun method_ ->
              Call_graph.reaches context.database ~package:(Path.package context.current)
                ~from:method_ ~target:context.current)
            (Call_graph.impl_methods context.database impl)
        in
        if reaches_here then
          oblige context frame Termination span
            (Printf.sprintf
               "This call uses `%s` where a bound needs it, and that `impl`'s methods reach back \
                here. Such a use passes no arguments the prover can compare, so the recursion \
                cannot be shown to end: write it as a direct call on a part."
               (Path.show impl))
            (L.Boolean false))
      (Call_graph.impls_used context.database impls call_.callee)
  end;
  let with_contract ?(substitution_of = fun _ -> []) ?(instance = "") path = function
    | Some contract ->
        Some
          (contract_call ~lent_final context frame node call_ path contract values ~havoc_mut
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
        (function_contract ~reader:(Path.package context.current) context.database path)
  | Trait_method { trait; name; receiver; evidence; self_type; type_arguments } -> (
      let arguments = arguments_of type_arguments in
      let self_type = substituted context frame self_type in
      let trait = { trait with trait_arguments = arguments_of trait.trait_arguments } in
      (* A bound on [Self], read where [Self] is a known type, as in a law
         proven for one [impl], reaches that type's [impl]. *)
      let evidence : evidence =
        match evidence with
        | Bound -> (
            match concrete_impl context trait self_type with
            | Some (impl, arguments) -> Impl { impl; arguments }
            | None -> evidence)
        | _ -> evidence
      in
      assume_laws context frame ~at:span trait self_type;
      let operands () = List.map (fun (passed : passed) -> passed.term) values in
      match (name, evidence, operands ()) with
      | "equal", _, [ a; b ] when Path.equal trait.trait equal_trait && structural context self_type
        ->
          (* [==] on a type with identity semantics is the solver's
             equality. *)
          Some (frame, L.equal a b)
      | "equal", Impl { impl = Derived _; _ }, [ a; b ] when Path.equal trait.trait equal_trait ->
          (* A derived [impl] is defined by the rule that derived it. *)
          Some (frame, equal_of context frame self_type a b)
      | _ ->
          (match evidence with
          | (Bound | Dynamic) when name = "from_template" && Path.equal trait.trait template_trait
            ->
              oblige context frame Requires span
                "A call of `from_template` through a bound or `any` cannot see what the tag \
                 requires of its template: build the value with a template, where the tag is \
                 known."
                (L.Boolean false)
          | _ -> ());
          let trait_path = Path.Method { owner = trait.trait; name; receiver } in
          (* The trait's clauses are about [Self] and the trait's parameters. *)
          let trait_substitution =
            pair (generics_of trait_path) arguments
              ~given:(trait_substitution context.database trait self_type)
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
          let substitution_of (part : part) =
            if part.inherited then trait_substitution else own_substitution
          in
          with_contract ~substitution_of
            ~instance:(instance_of (T.Type self_type :: arguments))
            path
            (method_contract ~reader:(Path.package context.current) context.database trait name
               receiver evidence))
  | Indirect _ ->
      check_callback_requires context frame node through values;
      let frame = havoc_mut frame in
      let frame =
        match through with
        | _ when context.counters = [] -> frame
        | Some (T.Function function_type, callee_term, _) ->
            spend context frame (function_value_amount context frame function_type callee_term)
        | _ -> spend context frame (unknown_amount context frame)
      in
      let result =
        match through with
        | Some (T.Function function_type, callee_term, _) when in_the_logic function_type ->
            let term =
              applied context function_type callee_term
                (List.map (fun (passed : passed) -> passed.term) values)
            in
            assume context frame (in_range result_type term);
            term
        | _ -> arrive context frame "result" result_type
      in
      (* A function value meets its type's invariants where it returns, as
         a function does, so its result and what it leaves in a [mut]
         argument are valid. *)
      assume_valid context frame result_type result;
      List.iter
        (fun (passed : passed) ->
          match (passed.mode, passed.operand) with
          | T.Mut, Some operand -> (
              try
                assume_valid context frame passed.type_
                  (snd (operand_value context { frame with checking = false } operand))
              with Unsupported _ | Foreign_unsupported _ -> ())
          | _ -> ())
        values;
      Some (frame, result)
  | Capability_method { capability; name } ->
      with_contract
        (Path.Method { owner = capability; name; receiver = Static })
        (capability_contract context.database capability name)
  | Intrinsic { operation; type_arguments } ->
      (* Lending a part of a storage changes nothing until the lend ends,
         where what the caller left is written back. *)
      let frame =
        match operation with
        | Storage_at_mut | Array_at_mut | View_at_mut -> frame
        | _ -> havoc_mut frame
      in
      let operands = List.map (fun (passed : passed) -> passed.term) values in
      (* What each argument holds after the call: a [mut] one read again. *)
      let changed =
        List.map
          (fun (passed : passed) ->
            match (passed.mode, passed.operand) with
            | T.Mut, Some operand -> (
                try snd (operand_value context { frame with checking = false } operand)
                with Unsupported _ | Foreign_unsupported _ -> passed.term)
            | _ -> passed.term)
          values
      in
      let types =
        List.filter_map
          (function T.Type ty -> Some (substituted context frame ty) | _ -> None)
          type_arguments
      in
      let result =
        match (operation, values) with
        | Array_model, [ array ] -> array_model context frame array.type_ array.term
        | Array_take_view, [ array; part; start ] -> (
            match (array.type_, changed) with
            | Named { arguments = T.Type element :: _; _ }, after :: _ ->
                let before = array_model context frame array.type_ array.term in
                let run = buffer_model context View element part.term in
                oblige context frame Requires (at frame node)
                  (Printf.sprintf "`%s` may not take back a view within the array."
                     (quote frame.source node.origin))
                  L.(
                    Apply
                      ( "<=",
                        [
                          Apply ("+", [ start.term; sequence_length context element run ]);
                          sequence_length context element before;
                        ] ));
                run_replaced context frame element ~before
                  ~after:(array_model context frame array.type_ after)
                  ~start:start.term
                  ~stop:(L.Apply ("+", [ start.term; sequence_length context element run ]))
                  ~run:(Some run);
                arrive context frame "result" result_type
            | _ -> arrive context frame "result" result_type)
        | Array_view, [ array ] -> (
            (* A view of the array's elements. *)
            match array.type_ with
            | Named { arguments = T.Type element :: _; _ } ->
                let view = arrive context frame "view" result_type in
                assume context frame
                  (L.equal
                     (buffer_model context View element view)
                     (array_model context frame array.type_ array.term));
                view
            | _ -> arrive context frame "view" result_type)
        | Array_at_mut, [ array; index ] -> (
            (* The element at [index], lent to change until the lend ends,
               where the array takes back what the borrower left. *)
            match array.type_ with
            | Named { arguments = T.Type element :: _; _ } -> (
                let model = array_model context frame array.type_ array.term in
                oblige context frame Requires (at frame node)
                  (Printf.sprintf "`%s` may not be within the array."
                     (quote frame.source node.origin))
                  L.(
                    Apply ("<=", [ int 0; index.term ])
                    &&& Apply ("<", [ index.term; sequence_length context element model ]));
                match sequence_at context element model index.term with
                | Some part -> part
                | None -> arrive context frame "part" result_type)
            | _ -> arrive context frame "part" result_type)
        | Storage_from_array, [ array ] -> (
            (* The array's elements, moved into storage with room for exactly
               them. *)
            match array.type_ with
            | Named { arguments = [ T.Type element; T.Value count ]; _ } ->
                let storage = arrive context frame "storage" result_type in
                let elements = buffer_model context Storage element storage in
                let count = value_term context frame count in
                assume context frame
                  L.(
                    equal elements (array_model context frame array.type_ array.term)
                    &&& equal (sequence_length context element elements) count
                    &&& equal (buffer_capacity context element storage) count);
                storage
            | _ -> arrive context frame "storage" result_type)
        | Array_from_storage, [ storage ] -> (
            (* The storage's elements, moved into an array, which must be
               exactly as many as the array's count. *)
            match result_type with
            | Named { arguments = [ T.Type element; T.Value count ]; _ } ->
                let elements = buffer_model context Storage element storage.term in
                let count = value_term context frame count in
                oblige context frame Requires (at frame node)
                  (Printf.sprintf "`%s` may not have as many elements as the array's count."
                     (quote frame.source node.origin))
                  (L.equal (sequence_length context element elements) count);
                let array = arrive context frame "array" result_type in
                assume context frame
                  (L.equal (array_model context frame result_type array) elements);
                array
            | _ -> arrive context frame "array" result_type)
        | _ -> intrinsic context frame ~node operation types operands ~changed result_type
      in
      let frame = spend context frame (step_amount context frame call_ values) in
      Some (frame, result)

(* What an intrinsic operation on integers gives, as the compiler declares
   it. Arithmetic that stops the program on overflow or a zero divisor gives
   the exact result when it returns; wrapping arithmetic gives the exact
   result brought into range by a remainder; the overflow tests, the
   comparisons, and [fits] are exact; and [convert] keeps a value that
   fits. Anything else is known by its type alone. *)
and intrinsic context frame ~node (operation : Intrinsic.operation) types operands ~changed
    result_type =
  let known = arrive context frame "result" result_type in
  match (operation, types) with
  | Shared_update, _ ->
      (* What [change] returned, which a function value's result is: valid. *)
      assume_valid context frame result_type known;
      known
  | ( ( Storage_model | View_model | Storage_empty | Storage_with_capacity | Storage_length
      | Storage_capacity | Storage_set_capacity | Storage_lengthen | Storage_shorten | Storage_push
      | Storage_pop | Storage_insert | Storage_remove | Storage_swap | Storage_at | Storage_at_mut
      | Storage_view | View_at_mut | View_swap | Storage_view_mut | Storage_take_view
      | View_take_view | View_length | View_at | View_slice ),
      element :: _ ) ->
      buffer_operation context frame ~node operation element operands ~changed known
  | Compare_bytes, _ ->
      buffer_operation context frame ~node operation (T.builtin UInt8) operands ~changed known
  | Libc function_, _ -> libc_call context frame ~node function_ operands ~changed known
  | Libc_number number, _ -> libc_number context frame number
  | (Ieee_equal | Ieee_less), ty :: _ when float_format ty <> None -> (
      match operands with
      | [ left; right ] ->
          L.Apply ((if operation = Ieee_equal then "fp.eq" else "fp.lt"), [ left; right ])
      | _ -> known)
  | (Square_root | Floor | Ceiling | Truncate | Round_to_even), ty :: _ when float_format ty <> None
    -> (
      (* The rounding the compiled operation does, as IEEE 754 names it. *)
      match operands with
      | [ value ] -> (
          match operation with
          | Square_root -> L.Apply ("fp.sqrt", [ L.Apply ("RNE", []); value ])
          | Floor -> L.Apply ("fp.roundToIntegral", [ L.Apply ("RTN", []); value ])
          | Ceiling -> L.Apply ("fp.roundToIntegral", [ L.Apply ("RTP", []); value ])
          | Truncate -> L.Apply ("fp.roundToIntegral", [ L.Apply ("RTZ", []); value ])
          | _ -> L.Apply ("fp.roundToIntegral", [ L.Apply ("RNE", []); value ]))
      | _ -> known)
  | Fused_multiply_add, ty :: _ when float_format ty <> None -> (
      match operands with
      | [ value; multiplier; addend ] ->
          L.Apply ("fp.fma", [ L.Apply ("RNE", []); value; multiplier; addend ])
      | _ -> known)
  | Is_nan, ty :: _ when float_format ty <> None -> (
      match operands with [ value ] -> is_nan value | _ -> known)
  | From_bits, [ bits; target ] when bounds bits <> None -> (
      match (operands, float_format target, width bits) with
      | [ value ], Some (exponent, significand), Some width ->
          L.Apply
            ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
              [ L.Apply (Printf.sprintf "(_ int2bv %d)" width, [ value ]) ] )
      | _ -> known)
  | To_bits, [ source; bits ] when bounds bits <> None -> (
      (* A float's bits are those that make it again, which every float but
         a NaN has one of. *)
      match (operands, float_format source, width bits) with
      | [ value ], Some (exponent, significand), Some width ->
          assume context frame
            L.(
              not_ (is_nan value)
              ==> equal
                    (Apply
                       ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
                         [ Apply (Printf.sprintf "(_ int2bv %d)" width, [ known ]) ] ))
                    value);
          known
      | _ -> known)
  | Multiply_high, ty :: _ when bounds ty <> None -> (
      (* The product's upper word: the exact product divided by the type's
         size, rounded down, which is its upper word signed or not. *)
      match (operands, width ty) with
      | [ left; right ], Some bits ->
          L.Apply ("div", [ L.Apply ("*", [ left; right ]); L.Integer (Z.shift_left Z.one bits) ])
      | _ -> known)
  | (Rotate_left | Rotate_right | Swap_bytes), ty :: _ when bounds ty <> None ->
      let name =
        match operation with
        | Rotate_left -> "rotate_left"
        | Rotate_right -> "rotate_right"
        | _ -> "swap_bytes"
      in
      opaque_operation context frame ty name operands
  | Convert, [ source; target ] when float_format source <> None && bounds target <> None -> (
      (* A float becomes an integer by being cut toward zero, which must be
         a number in the target's range: the conversion does not check. *)
      match operands with
      | [ value ] ->
          oblige context frame Requires (at frame node)
            (Printf.sprintf
               "`%s` may not fit `%s`: it must be a number that, cut toward zero, is in its range."
               (quote frame.source node.origin) (T.show target))
            (float_fits target value);
          L.Apply ("to_int", [ truncated value ])
      | _ -> known)
  | Convert, [ source; target ] when bounds source <> None && float_format target <> None -> (
      (* An integer becomes the float nearest it, ties to even, as the
         compiled cast rounds: exactly it, where the float can hold it. *)
      match (operands, float_format target) with
      | [ value ], Some (exponent, significand) ->
          L.Apply
            ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
              [ L.Apply ("RNE", []); L.Apply ("to_real", [ value ]) ] )
      | _ -> known)
  | Convert, [ _; target ] when T.is_builtin Character target -> (
      (* A [Character] is made from an integer only when the integer is a
         Unicode scalar value, which the conversion does not check. *)
      match operands with
      | [ value ] ->
          oblige context frame Requires (at frame node)
            (Printf.sprintf "`%s` may not be a Unicode scalar value, which a `Character` must be."
               (quote frame.source node.origin))
            (in_range target value);
          value
      | _ -> known)
  | _ -> integer_intrinsic context frame ~node operation types operands known

(* A function of the C library, by its row of the C library's table. It
   is given only an address into a storage, so each storage it is lent
   keeps its length and its capacity, whatever the function does. Each
   argument it reads or writes through an address names how many elements:
   room after a storage's elements must be there, elements of a view or of
   a storage it changes must be there, and a view it reads up to a zero
   must end with one. A storage passed as room keeps its elements; one
   passed as its elements to change has elements nothing more is known of.
   A result that is not negative is at most the parameter the row names. *)
and libc_call context frame ~(node : expression) (function_ : Libc.function_) operands ~changed
    known =
  let { Libc.parameters; at_most; _ } = Libc.signature function_ in
  let arguments =
    List.concat_map
      (fun (name, (passes : Libc.passes)) ->
        match passes with
        | Value _ | Elements _ | Room _ | Elements_to_change _ -> [ (name, Some passes) ]
        | Written (_, names) -> List.map (fun name -> (name, None)) names
        | Always _ | Fixed _ -> [])
      parameters
  in
  let value_of name =
    List.find_map
      (fun (position, (named, _)) -> if named = name then List.nth_opt operands position else None)
      (List.mapi (fun position argument -> (position, argument)) arguments)
  in
  let count (extent : Libc.extent) =
    match extent with
    | Counted { by; each } ->
        Option.map
          (fun value -> if each = 1 then value else L.Apply ("*", [ L.int each; value ]))
          (value_of by)
    | Exactly elements -> Some (L.int elements)
    | Number number -> Some (libc_number context frame number)
    | Through_zero -> None
  in
  let needs what condition =
    oblige context frame Requires (at frame node)
      (Printf.sprintf "`%s` may not %s." (quote frame.source node.origin) what)
      condition
  in
  let element_of scalar = T.builtin (Intrinsic.libc_builtin scalar) in
  let length element sequence = sequence_length context element sequence in
  List.iteri
    (fun position (_, passes) ->
      match (passes, List.nth_opt operands position, List.nth_opt changed position) with
      | ( Some ((Libc.Room (scalar, extent) | Elements_to_change (scalar, extent)) as passes),
          Some before,
          Some after ) -> (
          let element = element_of scalar in
          let model term = buffer_model context Storage element term in
          let capacity term = buffer_capacity context element term in
          assume context frame
            L.(
              equal (length element (model after)) (length element (model before))
              &&& equal (capacity after) (capacity before));
          match (passes, count extent) with
          | Room _, counted ->
              assume context frame (L.equal (model after) (model before));
              Option.iter
                (fun counted ->
                  needs "have the room it writes into"
                    (L.Apply
                       ( "<=",
                         [
                           L.Apply ("+", [ length element (model before); counted ]);
                           capacity before;
                         ] )))
                counted
          | _, Some counted ->
              needs "have the elements it changes"
                (L.Apply ("<=", [ counted; length element (model before) ]))
          | _, None -> ())
      | Some (Libc.Elements (scalar, extent)), Some view, _ -> (
          let element = element_of scalar in
          let elements = buffer_model context View element view in
          match count extent with
          | Some counted ->
              needs "have the elements it reads"
                (L.Apply ("<=", [ counted; length element elements ]))
          | None ->
              let last = L.Apply ("-", [ length element elements; L.int 1 ]) in
              needs "end with a zero, which it reads up to"
                L.(
                  Apply (">=", [ length element elements; int 1 ])
                  &&&
                  match sequence_at context element elements last with
                  | Some found -> equal found (int 0)
                  | None -> Boolean false))
      | _ -> ())
    arguments;
  (match Option.bind at_most value_of with
  | Some bound ->
      assume context frame L.(Apply (">=", [ known; int 0 ]) ==> Apply ("<=", [ known; bound ]))
  | None -> ());
  known

(* A number of the system that the C library's headers define, such as
   [PATH_MAX]: one constant, whatever call gives it, so the room a caller
   makes for it and the room a function needs are the same term. *)
and libc_number context frame (number : Libc.number) =
  let symbol = "libc.number." ^ Libc.number_name number in
  declare context (L.Constant (symbol, L.Int));
  let term = L.Symbol symbol in
  assume context frame
    (in_range (T.builtin (Intrinsic.libc_builtin (Libc.number_type number))) term);
  term

(* Whether a float is a number that, cut toward zero, is in an integer
   type's range. *)
and float_fits target value =
  match bounds target with
  | Some (low, high) ->
      let cut = truncated value in
      L.(
        not_ (is_nan value)
        &&& not_ (Apply ("fp.isInfinite", [ value ]))
        &&& Apply ("<=", [ Integer low; cut ])
        &&& Apply ("<=", [ cut; Integer high ]))
  | None -> L.Boolean false

and integer_intrinsic context frame ~node (operation : Intrinsic.operation) types operands known =
  let integer = match types with ty :: _ -> bounds ty | [] -> None in
  let exact operation left right =
    match (operation : Intrinsic.operation) with
    | Add | Wrapping_add | Add_overflows -> L.Apply ("+", [ left; right ])
    | Subtract | Wrapping_subtract | Subtract_overflows -> L.Apply ("-", [ left; right ])
    | Divide -> L.truncated_divide left right
    | Remainder -> L.truncated_remainder left right
    | _ -> L.Apply ("*", [ left; right ])
  in
  match (operation, integer, types, operands) with
  (* An integer operation is defined where its operator is, so it has the
     operator's obligations: a call of it, as an [impl] of [Add] makes, shows
     what [+] would. *)
  | (Add | Subtract | Multiply | Divide | Remainder), Some _, ty :: _, [ left; right ] ->
      let result = arithmetic context frame node ty operation left right in
      assume context frame (in_range ty result);
      result
  | Negate, Some _, ty :: _, [ value ] ->
      let result = L.Apply ("-", [ value ]) in
      oblige context frame Overflow (at frame node)
        (Printf.sprintf "`%s` may overflow `%s`." (quote frame.source node.origin) (T.show ty))
        (in_range ty result);
      result
  | (Wrapping_add | Wrapping_subtract | Wrapping_multiply), Some (low, high), _, [ left; right ] ->
      let modulus = Z.succ (Z.sub high low) in
      L.Apply
        ( "+",
          [
            L.Integer low;
            L.Apply
              ( "mod",
                [ L.Apply ("-", [ exact operation left right; L.Integer low ]); L.Integer modulus ]
              );
          ] )
  | (Add_overflows | Subtract_overflows | Multiply_overflows), Some _, ty :: _, [ left; right ] ->
      L.not_ (in_range ty (exact operation left right))
  | Equal, None, ty :: _, [ left; right ] when float_format ty <> None -> float_equal left right
  | Less, None, ty :: _, [ left; right ] when float_format ty <> None -> float_less left right
  | Equal, Some _, _, [ left; right ] -> L.equal left right
  | Less, Some _, _, [ left; right ] -> L.Apply ("<", [ left; right ])
  | Fits, Some _, [ _; target ], [ value ] when bounds target <> None -> in_range target value
  | Fits, None, [ source; target ], [ value ]
    when float_format source <> None && bounds target <> None ->
      float_fits target value
  | Convert, Some _, [ _; target ], [ value ] when bounds target <> None ->
      assume context frame L.(in_range target value ==> equal known value);
      known
  | (Leading_zeros | Trailing_zeros | Count_ones), Some (low, _), ty :: _, [ value ] -> (
      (* Each count of bits is a function of the value, at most the width,
         and for an unsigned value the three are related: a nonzero value
         lies between the powers of two its leading zeros give, has no
         more ones than the bits below its highest one, all of them where
         it is one less than a power of two, and its lowest one below its
         highest; zero has no ones and is all zeros. *)
      match width ty with
      | Some bits ->
          let count name =
            let symbol = Printf.sprintf "bits.%s.%d" name bits in
            declare context (L.Function (symbol, [ L.Int ], L.Int));
            L.Apply (symbol, [ value ])
          in
          let leading = count "leading_zeros"
          and trailing = count "trailing_zeros"
          and ones = count "count_ones" in
          let term =
            match operation with Leading_zeros -> leading | Trailing_zeros -> trailing | _ -> ones
          in
          assume context frame
            L.(Apply ("<=", [ int 0; term ]) &&& Apply ("<=", [ term; int bits ]));
          (if Z.equal low Z.zero && not (L.mentions frame.bound value) then
             let power exponent = power_of context frame (L.int 2) exponent in
             let width = L.int bits in
             let nonzero = L.not_ (L.equal value (L.int 0)) in
             let below_highest = L.Apply ("-", [ width; leading ]) in
             List.iter (assume context frame)
               L.
                 [
                   Apply ("<=", [ int 0; leading ])
                   &&& Apply ("<=", [ leading; width ])
                   &&& Apply ("<=", [ int 0; trailing ])
                   &&& Apply ("<=", [ trailing; width ])
                   &&& Apply ("<=", [ int 0; ones ])
                   &&& Apply ("<=", [ ones; width ]);
                   nonzero
                   ==> (Apply ("<=", [ power (Apply ("-", [ int (bits - 1); leading ])); value ])
                       &&& Apply ("<", [ value; power below_highest ]));
                   equal (equal ones (int 0)) (equal value (int 0));
                   nonzero ==> Apply ("<=", [ ones; below_highest ]);
                   nonzero
                   &&& equal (Apply ("+", [ value; int 1 ])) (power below_highest)
                   ==> equal ones below_highest;
                   nonzero ==> Apply ("<=", [ Apply ("+", [ trailing; leading ]); int (bits - 1) ]);
                   equal value (int 0) ==> (equal trailing width &&& equal leading width);
                 ]);
          term
      | None -> known)
  | _ -> known

(* Lambdas and callbacks *)

(* A lambda is proven where it is written, with fresh arguments of its
   function type and what the callee promises to pass it; it ends exactly
   when its function type has a [time] clause; and it is a value about
   which nothing more is known. *)
and lambda context frame (node : expression) (parameters : pattern list) captures (body : block)
    ~facts =
  let span = at frame node in
  let ty = type_of context frame node in
  let function_type =
    match ty with T.Function function_type -> function_type | _ -> unsupported span "a lambda"
  in
  if List.length parameters <> List.length function_type.inputs then
    unsupported span "a lambda with a different number of parameters";
  (* A lambda's body runs only where it is called, which may be nowhere, so
     what its path assumes is only where it is called: what the body
     assumes of its arguments, or of what it calls, holds of no other path. *)
  let called = fresh context frame "called" L.Bool in
  let inside = { (restrict frame called) with result = None; loop = None; updating = None } in
  let start_fresh = context.fresh
  and start_facts = List.length context.facts
  and start_declarations = List.length context.declarations in
  let arguments, inside =
    List.fold_left2
      (fun (arguments, inside) (pattern : pattern) (_, input) ->
        let input = substituted context frame input in
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
          | Time -> Some Time
          | Allocations -> Some Allocations
          | Allocated_bytes -> Some Allocated_bytes
          | Calls _ -> None
        in
        match (resource, counting) with
        | Some resource, Some counting ->
            let counter = { Costs.resource; counting; amortized = cost.amortized } in
            let constants =
              if counting = Units then begin
                let constants =
                  Costs.constants (Printf.sprintf "lambda.%d.%s" node.id (Costs.key counter))
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
  let time_units = { Costs.resource = Time; counting = Units; amortized = false } in
  let counts_time =
    List.exists
      (fun (counter : Costs.counter) -> counter.resource = Time && counter.counting = Units)
      context.counters
  in
  let times_by_type = List.exists (fun (counter, _, _) -> counter = time_units) promised in
  (* A call back into the definition around it still assumes its bound
     with the definition's constants, which are kept. *)
  let saved_counters = context.counters in
  context.counters <-
    distinct_counters
      ((if counts_time then [ time_units ] else [])
      @ List.map (fun (counter, _, _) -> counter) promised
      @ loop_counters inside.locals body);
  let inside =
    {
      inside with
      spent = List.map (fun counter -> (Costs.key counter, Costs.zero)) context.counters;
    }
  in
  let mark = context.fresh and facts_mark = List.length context.facts in
  let premises =
    List.filteri
      (fun index _ -> index >= List.length context.facts - facts_mark)
      (facts_since context start_facts)
  in
  let ended = ref [] in
  let saved_returns = context.returns and saved_terminates = context.terminates in
  context.returns <- [];
  context.terminates <- T.terminates function_type;
  let pending =
    Fun.protect
      ~finally:(fun () ->
        context.returns <- saved_returns;
        context.terminates <- saved_terminates;
        context.counters <- saved_counters)
      (fun () ->
        let finished = block_value context inside body in
        let exits =
          (match finished with Some (frame, _) -> [ frame ] | None -> [])
          @ List.map fst context.returns
        in
        ended :=
          (match finished with Some (frame, value) -> [ (frame, Some value) ] | None -> [])
          @ context.returns;
        (* Like a function, it meets its type's invariants where it ends:
           a call through it assumes so. *)
        List.iter
          (fun ((exit_ : frame), returned) ->
            (match (returned, function_type.output) with
            | Some term, Returns output ->
                check_valid context exit_ span
                  (substituted context frame output)
                  term ~deep:true ~when_:"for the value this lambda returns"
            | _ -> ());
            List.iter2
              (fun (pattern : pattern) (mode, input) ->
                match (mode, pattern.kind) with
                | T.Mut, Bind { local; _ } -> (
                    match Locals.find_opt local exit_.locals with
                    | Some term ->
                        check_valid context exit_ span (substituted context frame input) term
                          ~deep:true ~when_:"for a `mut` parameter when this lambda ends"
                    | None -> ())
                | _ -> ())
              parameters function_type.inputs)
          !ended;
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
                oblige context exit_ Cost span
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
                      obligation_at context exit_ Cost span
                        "The prover cannot show that a call of this lambda takes no more time than \
                         the bound it found for every call, which a cost here relies on."
                        (Costs.at_most spent bound))
                    (List.combine exits spent) )
          | None -> None
        else None)
  in
  let end_fresh = context.fresh in
  let term =
    match lambda_definition context frame function_type parameters body with
    | Some term -> term
    | None ->
        let term = arrive context frame "lambda" ty in
        if in_the_logic function_type && frame.bound = [] then
          what_a_lambda_does context function_type term ~called ~arguments ~start_fresh ~end_fresh
            ~start_declarations ~premises ~shown:(facts_since context facts_mark) ~ended:!ended;
        term
  in
  context.lambda_captures <-
    (term, List.map (fun (capture : capture) -> capture.local) captures) :: context.lambda_captures;
  (match pending with
  | Some found -> context.lambda_times <- (term, found) :: context.lambda_times
  | None -> ());
  (frame, term)

(* What a lambda whose body is not its definition does, for every argument:
   its body ran on arguments that are arbitrary but for [premises], so what
   it showed, and the value it ended with on each path, hold for each
   argument the premises admit, since its type promises that it ends, and
   so is called wherever it is applied. Over each argument, each value made in the
   body is a function of the arguments, since it can differ for each. A
   nested lambda's symbol, named after what it captures, is not such a
   function, so a body with one gives nothing. *)
and what_a_lambda_does context function_type term ~called ~arguments ~start_fresh ~end_fresh
    ~start_declarations ~premises ~shown ~ended =
  let declared_here =
    List.filteri
      (fun index _ -> index < List.length context.declarations - start_declarations)
      context.declarations
  in
  let nested_lambda =
    List.exists
      (function
        | L.Constant (name, _) ->
            String.starts_with ~prefix:"lambda." name && not (Hashtbl.mem context.fresh_order name)
        | _ -> false)
      declared_here
  in
  if not nested_lambda then begin
    let parameters =
      List.mapi
        (fun index (_, input) -> (Printf.sprintf "lambda.argument.%d" index, sort_of context input))
        function_type.T.inputs
    in
    let variables = List.map (fun (name, _) -> L.Symbol name) parameters in
    let renamed = Hashtbl.create 16 in
    (match called with L.Symbol name -> Hashtbl.replace renamed name (L.Boolean true) | _ -> ());
    List.iter2
      (fun argument variable ->
        match argument with L.Symbol name -> Hashtbl.replace renamed name variable | _ -> ())
      arguments variables;
    List.iter
      (function
        | L.Constant (name, sort) when not (Hashtbl.mem renamed name) -> (
            match Hashtbl.find_opt context.fresh_order name with
            | Some made when made > start_fresh && made <= end_fresh ->
                let over = name ^ ".over" in
                declare context (L.Function (over, List.map snd parameters, sort));
                Hashtbl.replace renamed name (L.Apply (over, variables))
            | _ -> ())
        | _ -> ())
      declared_here;
    let rec over = function
      | L.Symbol name as symbol -> Option.value (Hashtbl.find_opt renamed name) ~default:symbol
      | (L.Integer _ | L.Boolean _ | L.Bits _) as term -> term
      | L.Apply (name, arguments) -> L.Apply (name, List.map over arguments)
      | L.Forall (bound, body) -> L.Forall (bound, over body)
      | L.Exists (bound, body) -> L.Exists (bound, over body)
    in
    let premise = over (L.conjunction premises) in
    let applied_here = applied context function_type term variables in
    let statements =
      List.map over shown
      @ List.filter_map
          (fun ((exit_ : frame), value) ->
            Option.map
              (fun value -> L.( ==> ) (over exit_.condition) (L.equal applied_here (over value)))
              value)
          ended
    in
    List.iter
      (fun statement ->
        context.facts <- L.Forall (parameters, L.( ==> ) premise statement) :: context.facts)
      statements
  end

(* A clause's value: a specification, which never runs, so it spends
   nothing whatever it calls. *)
and clause_value context frame (clause : expression) =
  specification context (fun () -> value context frame clause)

(* Reading what never runs, as a specification, which spends nothing. *)
and specification : 'a. _ -> (unit -> 'a) -> 'a =
 fun context read ->
  let saved = context.counters in
  context.counters <- [];
  Fun.protect ~finally:(fun () -> context.counters <- saved) read

(* A lambda whose body is functional, as a function in the logic: applied,
   it is its body. Lambdas with the same body over the same captured values
   are the same function, so a bound and a loop's bound that both write
   [(row) => row.length()] mean the same sum. A body whose value needs a
   fresh symbol, or that the prover cannot read, gives no definition. *)
and lambda_definition context frame (function_type : T.function_type) parameters (body : block) =
  if not (in_the_logic function_type && functional_block body) then None
  else
    let bound = parameters_of context frame function_type in
    let defined =
      body_over context frame bound body (fun inside ->
          List.fold_left2
            (fun inside (pattern : pattern) ((name, _), (_, input)) ->
              snd
                (pattern_match context inside pattern (L.Symbol name)
                   (substituted context frame input)))
            inside parameters
            (List.combine bound function_type.inputs))
    in
    match defined with
    | Some defined ->
        let defined = canonical_binders defined in
        (* The same body is the same function wherever it is written, so its
           parameters are named by position alone in what names it. *)
        let named_by_position =
          List.fold_left
            (fun term (index, (name, _)) ->
              L.replace ~from:(L.Symbol name)
                ~into:(L.Symbol (Printf.sprintf "parameter.%d" index))
                term)
            defined
            (List.mapi (fun index parameter -> (index, parameter)) bound)
        in
        let symbol =
          "lambda."
          ^ Logic.hash
              (String.concat " " (List.map (fun (_, sort) -> sort_label sort) bound)
              ^ " " ^ L.show_term named_by_position)
        in
        let sort = sort_of context (T.Function function_type) in
        (* A lambda that captures a quantifier's bound symbol is a function
           of it. *)
        let term =
          if L.mentions frame.bound defined then made_here context frame symbol sort
          else made_here context { frame with binders = [] } symbol sort
        in
        let application =
          applied context function_type term (List.map (fun (name, _) -> L.Symbol name) bound)
        in
        fact context frame (L.Forall (bound, L.equal application defined));
        (* Its body's value is in the range of the body's type, which may be
           narrower than the function type's [Integer]. *)
        let rec unconverted (node : expression) =
          match node.kind with
          | Convert { conversion = To_integer; value = inner } -> unconverted inner
          | _ -> node
        in
        (match body.value with
        | Some last -> (
            match in_range (type_of context frame (unconverted last)) application with
            | L.Boolean true -> ()
            | range ->
                (* For arguments of the parameters' types, which the body
                   was read with. *)
                let arguments_in_range =
                  L.conjunction
                    (List.map2
                       (fun (name, _) (_, input) ->
                         in_range (substituted context frame input) (L.Symbol name))
                       bound function_type.inputs)
                in
                fact context frame (L.Forall (bound, L.( ==> ) arguments_in_range range)))
        | None -> ());
        Some term
    | _ -> None

(* A functional body's value over bound names, as a definition states it:
   [bind] binds them in the frame the body reads. Nothing is counted or
   obliged, and a body that the prover cannot read, or whose value needs a
   fresh symbol, gives none. *)
and body_over context frame bound body bind =
  let mark = context.fresh in
  let saved_counters = context.counters in
  context.counters <- [];
  Fun.protect
    ~finally:(fun () -> context.counters <- saved_counters)
    (fun () ->
      try
        let inside =
          bind
            {
              frame with
              bound = List.map fst bound @ frame.bound;
              checking = false;
              result = None;
              loop = None;
            }
        in
        match block_value context inside body with
        | Some (_, defined) when not (made_since context mark defined) -> Some defined
        | _ -> None
      with Unsupported _ | Foreign_unsupported _ -> None)

(* A symbol for a term that holds a pure call, named by the term, and
   equal to it. *)
and named_term context ty term =
  let rec holds_call = function
    | L.Apply (name, arguments) ->
        String.starts_with ~prefix:"function." name || List.exists holds_call arguments
    | L.Forall (_, body) | L.Exists (_, body) -> holds_call body
    | L.Symbol _ | L.Integer _ | L.Boolean _ | L.Bits _ -> false
  in
  if not (holds_call term) then term
  else
    let symbol = "argument." ^ Logic.hash (L.show_term term) in
    let named = L.Symbol symbol in
    once context ("named." ^ symbol) (fun () ->
        declare context (L.Constant (symbol, sort_of context ty));
        context.facts <- L.equal named term :: context.facts);
    named

(* A part's frame, for reading its clauses, with its parameters bound to
   the given terms by position. *)
and part_frame frame (part : part) ~arguments ~substitution =
  let locals, types, self =
    List.fold_left
      (fun (locals, types, self) (position, (parameter : Core.parameter)) ->
        match (parameter.local, List.assoc_opt position arguments) with
        | Self, Some term -> (locals, types, Some (term, parameter.type_))
        | local, Some term ->
            (Locals.add local term locals, Locals.add local parameter.type_ types, self)
        | _, None -> (locals, types, self))
      (Locals.empty, Locals.empty, None)
      (List.mapi (fun position parameter -> (position, parameter)) part.parameters)
  in
  {
    frame with
    source = part.callee;
    locals;
    types;
    old_locals = locals;
    self = Option.map fst self;
    old_self = Option.map fst self;
    self_type = Option.map (fun (_, ty) -> T.substitute substitution ty) self;
    result = None;
    checking = false;
    loop = None;
    updating = None;
    substitution;
  }

(* What a callee promises the lambda it is passed for one parameter: that
   parameter's [requires], read in the callee with the call's other
   arguments, and the lambda's arguments for the inputs it names. *)
and callback_facts context frame (call_ : call) position known arguments =
  match call_.callee with
  | Function { path; type_arguments } -> (
      match
        Option.bind
          (source_at ~reader:(Path.package context.current) context.database path)
          (fun (callee, _, _) -> part_of callee)
      with
      | Some part -> (
          match List.nth_opt part.parameters position with
          | Some { callback_contract = Some { inputs; requires }; _ }
            when List.length inputs = List.length arguments ->
              let substitution =
                match Interface.Impls.signature context.database path with
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
              let inside = part_frame frame part ~arguments:known ~substitution in
              let inside =
                {
                  inside with
                  locals =
                    List.fold_left2
                      (fun locals (local, _) term -> Locals.add local term locals)
                      inside.locals inputs arguments;
                }
              in
              List.map (fun clause -> snd (clause_value context inside clause)) requires
          | _ -> [])
      | None -> [])
  | _ -> []

(* A call through a function-typed parameter whose type has a [requires]
   must meet it. *)
and check_callback_requires context frame (node : expression) through (values : passed list) =
  match through with
  | Some (_, _, Place (Local { local; _ })) -> (
      match
        List.find_opt
          (fun (parameter : Core.parameter) -> parameter.local = local)
          context.parameters
      with
      | Some { callback_contract = Some { inputs; requires }; name; _ }
        when List.length inputs = List.length values ->
          (* The [requires] names the parameters as the caller passed them,
             which is what the caller showed it with. *)
          let locals =
            List.fold_left2
              (fun locals (input, _) (passed : passed) -> Locals.add input passed.term locals)
              frame.old_locals inputs values
          in
          let inside = { frame with locals; self = frame.old_self; checking = false } in
          List.iter
            (fun (clause : expression) ->
              oblige context frame Requires (at frame node)
                (Printf.sprintf "`%s` may not hold for this call through `%s`."
                   (quote frame.source clause.origin)
                   name)
                (snd (clause_value context inside clause)))
            requires
      | _ -> ())
  | _ -> ()

(* Whether a call is to a private method that takes [mut self], which is a
   step of an update: its receiver's invariant is neither shown at the call
   nor assumed after. *)
and updating_helper context (call_ : call) =
  match call_.callee with
  | Function { path; _ } -> is_updating_helper context.database path
  | _ -> false

(* The [impl] of a trait for a known type, with what its generic parameters
   stand for there: one written or derived, whose parameters' bounds hold
   under the bounds of the definition proven, or the definition's own
   [impl]. The [impl] is of the trait with these arguments, so a type with
   an [impl] of [Scale[Int64]] and one of [Scale[Bool]] reaches each by its
   own. *)
and concrete_impl context (trait : T.trait_reference) (ty : T.ty) =
  match ty with
  | Named { path; _ } ->
      let own impl =
        Path.equal impl context.current
        || match context.current with Method { owner; _ } -> Path.equal owner impl | _ -> false
      in
      let bounds = current_bounds context in
      let packages = List.sort_uniq compare [ Path.package context.current; Path.package path ] in
      List.find_map
        (fun package ->
          List.find_map
            (fun impl ->
              match Interface.Impls.impl_interface context.database impl with
              | Some interface -> (
                  let variables =
                    List.map (fun (generic : T.generic) -> generic.generic) interface.impl_generics
                  in
                  match
                    Option.bind (Interface.Impls.match_type ~variables [] interface.for_type ty)
                      (fun arguments ->
                        Interface.Impls.match_arguments ~variables arguments
                          interface.implements.trait_arguments trait.trait_arguments)
                  with
                  | Some arguments
                    when own impl
                         || List.for_all
                              (fun (argument, bound) ->
                                Option.is_some
                                  (Interface.Impls.implements context.database ~bounds argument
                                     bound))
                              (Interface.Impls.required interface.impl_generics arguments) ->
                      Some (impl, arguments)
                  | _ -> None)
              | None -> None)
            (Query.demand context.database Interface.Impls.impls_in (trait.trait, path, package)))
        packages
  | _ -> None

(* The bounds on the generic parameters of the definition proven, and of
   the [impl] it is in. *)
and current_bounds context : Interface.Impls.bounds =
  let impl_generics path =
    match Interface.Impls.impl_interface context.database path with
    | Some interface -> interface.impl_generics
    | None -> []
  in
  let generics =
    match context.current with
    | Method { owner; _ } -> (
        impl_generics owner
        @
        match Interface.Impls.signature context.database context.current with
        | Some signature -> signature.generics
        | None -> [])
    | current -> (
        match Interface.Impls.signature context.database current with
        | Some signature -> signature.generics
        | None -> impl_generics current)
  in
  fun parameter ->
    List.concat_map
      (fun (generic : T.generic) ->
        match generic.kind with
        | Type_generic bounds when generic.generic = parameter -> bounds
        | _ -> [])
      generics

(* A trait's laws, and those of the traits it requires, as facts about a
   type, each quantified over its parameters. A law is shown for each
   [impl] written by hand, by the [impl], so it is a fact wherever the
   trait's methods are used. *)
and assume_laws context frame ~at (trait : T.trait_reference) (ty : T.ty) =
  let key = laws_key trait ty in
  if not (List.mem key context.laws_assumed) then begin
    context.laws_assumed <- key :: context.laws_assumed;
    List.iter
      (fun path ->
        let required =
          if Path.equal path trait.trait then trait
          else { T.trait = path; trait_arguments = []; associated = [] }
        in
        let substitution = trait_substitution context.database required ty in
        let impl = Option.map fst (concrete_impl context required ty) in
        List.iter
          (fun (source, (law : law)) ->
            match law_fact context frame source ~substitution law with
            | Some fact_ ->
                (match impl with
                | Some impl when law_unshown context.database impl required ty law.name ->
                    context.holes <- (context.home, at) :: context.holes
                | _ -> ());
                fact context frame fact_
            | None -> ())
          (laws_of context path))
      (Call_graph.traits_with_required context.database trait.trait)
  end

and laws_key (trait : T.trait_reference) ty = T.show_trait trait ^ " for " ^ type_key ty

and laws_of context trait =
  match
    Option.bind
      (Query.demand context.database Interface.Summary.key trait)
      (source_at_key context.database)
  with
  | Some ({ core = { definition = Trait laws; _ }; _ } as source) ->
      List.map (fun (law : law) -> (source, law)) laws
  | _ -> []

(* A law's frame: its parameters as the given terms, with [Self] and the
   trait's parameters as the substitution says. *)
and law_frame frame source ~substitution (law : law) terms =
  let types = law_parameter_types ~substitution law in
  let locals, types =
    List.fold_left2
      (fun (locals, types_) ((parameter : Core.parameter), ty) term ->
        (Locals.add parameter.local term locals, Locals.add parameter.local ty types_))
      (Locals.empty, Locals.empty)
      (List.combine law.parameters types)
      terms
  in
  {
    frame with
    source;
    locals;
    types;
    old_locals = locals;
    self = None;
    old_self = None;
    result = None;
    checking = false;
    loop = None;
    updating = None;
    substitution;
    self_type = None;
  }

and law_parameter_types ~substitution (law : law) =
  List.map
    (fun (parameter : Core.parameter) -> T.substitute substitution parameter.type_)
    law.parameters

and law_fact context frame source ~substitution (law : law) =
  let types = law_parameter_types ~substitution law in
  if List.exists (fun ty -> T.is_error ty) types then None
  else begin
    context.fresh <- context.fresh + 1;
    let symbols = List.mapi (fun index _ -> Printf.sprintf "law.%d.%d" context.fresh index) types in
    let inside =
      law_frame
        { frame with bound = symbols @ frame.bound }
        source ~substitution law
        (List.map (fun s -> L.Symbol s) symbols)
    in
    try
      let premise =
        L.conjunction
          (List.map (fun clause -> snd (clause_value context inside clause)) law.requires)
      in
      let range =
        L.conjunction (List.map2 (fun symbol ty -> in_range ty (L.Symbol symbol)) symbols types)
      in
      match specification context (fun () -> block_value context inside law.body) with
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
and sequence_path : Path.t = Well_known.path Sequence
and sequence_type element = T.Named { path = sequence_path; arguments = [ T.Type element ] }

and sequence_length context element term =
  let path = Path.Method { owner = sequence_path; name = "length"; receiver = Read } in
  let symbol = "function." ^ Path.show path ^ "[" ^ type_key element ^ "]" in
  declare context (L.Function (symbol, [ sort_of context (sequence_type element) ], L.Int));
  L.Apply (symbol, [ term ])

(* A sequence's sum, by [standard::specification]'s [Sequence.sum], over a
   measure of its elements. *)
and sequence_sum context element term measure =
  let path = Path.Method { owner = sequence_path; name = "sum"; receiver = Read } in
  let symbol = "function." ^ Path.show path ^ "[" ^ type_key element ^ "]" in
  declare context
    (L.Function
       ( symbol,
         [
           sort_of context (sequence_type element);
           sort_of context (T.Function (measure_type element));
         ],
         L.Int ));
  L.Apply (symbol, [ term; measure ])

(* The type of a sum's measure: [fn(Element) -> Integer cost time finite]. *)
and measure_type element : T.function_type =
  {
    inputs = [ (T.Read, element) ];
    output = Returns T.Integer;
    uses = [];
    costs = [ { amortized = false; resource = T.Time; bound = Finite_cost } ];
  }

and sequence_at context element term index =
  let sequence = sequence_type element in
  let index_trait = Well_known.path Index in
  match
    Call_graph.impls_for
      (Query.demand context.database Call_graph.package_impls Path.standard_package)
      [ index_trait ] sequence
  with
  | impl :: _ ->
      let path = Path.Method { owner = impl; name = "at"; receiver = Read } in
      let symbol = "function." ^ Path.show path ^ "[" ^ type_key sequence ^ "]" in
      declare context
        (L.Function (symbol, [ sort_of context sequence; L.Int ], sort_of context element));
      let at sequence index = L.Apply (symbol, [ sequence; index ]) in
      (* An element of a sequence of parts is below the sequence, as a
         field is below its value, so recursion on an element ends. *)
      if context.ranking && constructors context element <> None then
        once context
          ("ranked." ^ type_key sequence)
          (fun () ->
            let each = "ranked.sequence" and index = "ranked.index" in
            let ranked = L.Symbol each and position = L.Symbol index in
            let below = rank context element (at ranked position) in
            context.facts <-
              L.Forall
                ( [ (each, sort_of context sequence); (index, L.Int) ],
                  L.(
                    Apply ("<=", [ int 0; position ])
                    &&& Apply ("<", [ position; sequence_length context element ranked ])
                    ==> (Apply ("<=", [ int 0; below ])
                        &&& Apply ("<", [ below; rank context sequence ranked ]))) )
              :: context.facts);
      Some (at term index)
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

and finite_set_path : Path.t = Well_known.path Finite_set
and finite_map_path : Path.t = Well_known.path Finite_map

(* An array, a [Sequence], or a [FiniteSet] written out: a value whose
   model has the elements in order, or whose set has them. None of them
   allocates: an array is built in place, and the others are only in
   specifications. *)
and list_literal context frame (node : expression) items =
  let ty = type_of context frame node in
  let span = at frame node in
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
    | _ -> unsupported span "a literal of `%s`" (T.show ty)
  in
  let literal =
    match sequence_of context frame ty ~element values with
    | Some literal -> literal
    | None -> (
        match set_of context frame ty ~element values with
        | Some literal -> literal
        | None -> unsupported span "a literal of `%s`" (T.show ty))
  in
  (frame, literal)

(* A slice, [items[a..b]]: a view of the elements from [a] to before [b],
   which must be within the collection, whose model is that run of the
   collection's model. *)
and slice context frame (node : expression) base ~start ~stop ~inclusive =
  let frame, viewed, _, _ = slice_run context frame node base ~start ~stop ~inclusive in
  (frame, viewed)

(* A slice, with its bounds as they were evaluated. *)
and slice_run context frame (node : expression) base ~start ~stop ~inclusive =
  let span = at frame node in
  let base_type = place_type context frame base in
  let element =
    match base_type with
    | Named { arguments = T.Type element :: _; _ } -> element
    | _ -> unsupported span "a slice of `%s`" (T.show base_type)
  in
  let frame, collection = place_value context frame base in
  let model =
    match model_of context base_type collection ~element with
    | Some model -> model
    | None -> unsupported span "a slice of `%s`" (T.show base_type)
  in
  let length = sequence_length context element model in
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
  oblige context frame Requires span
    (Printf.sprintf "`%s` may not be within the collection." (quote frame.source node.origin))
    L.(
      Apply ("<=", [ int 0; low ]) &&& Apply ("<=", [ low; high ]) &&& Apply ("<=", [ high; length ]));
  note_place context frame node (Run (low, high));
  let slice_type = type_of context frame node in
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
  (frame, viewed, low, high)

(* Whether a clause reads its template parameter only as
   [template.literals], so that a template's parts cannot change it. *)
and reads_only_literals (parameter : Core.local) (clause : expression) =
  let fine = ref true in
  let rec visit =
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : expression) ->
          match node.kind with
          | Use (Field { base = Local { local; _ }; field = "literals"; _ }) when local = parameter
            ->
              ()
          | Use place when root_of place = Some parameter -> fine := false
          | _ -> Core_walk.expression_children visit node);
      statement = (fun _ -> fine := false);
      pattern = (fun node -> Core_walk.pattern_children visit node);
    }
  in
  visit.expression clause;
  !fine

and template_trait : Path.t = Well_known.path From_template

(* A tagged template is a call of its tag's [from_template], with the
   template: its literal texts, each a [Literal] whose model is its bytes,
   and its parts, each turned into the tag's [Part] by its [From]. The
   call's [requires], such as that the text is one character, is shown of
   that template. *)
and tagged_template context frame (node : expression) texts (made : expression) =
  let span = at frame node in
  let tag_type = type_of context frame node in
  match made.kind with
  | Call
      {
        callee = Trait_method { trait; name; receiver; evidence = Impl { impl; _ } as evidence; _ };
        arguments = [ Passed { value = template; _ } ];
        _;
      } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match
        method_contract ~reader:(Path.package context.current) context.database trait name receiver
          evidence
      with
      | Some contract ->
          let frame, value_ = operand_value context frame template in
          let own = List.hd contract.parts in
          let entry = part_frame frame own ~arguments:[ (0, value_) ] ~substitution:[] in
          (* A clause that reads only the template's literal texts, of a tag
             whose [impl] is not generic, can be decided by running it. *)
          let evaluable (clause : expression) =
            match (evidence, own.parameters) with
            | Impl { arguments = []; _ }, [ parameter ] ->
                reads_only_literals parameter.local clause
            | _ -> false
          in
          List.iteri
            (fun index (clause : expression) ->
              let evaluation =
                if evaluable clause then Some { from_template = path; texts; clause = index }
                else None
              in
              oblige ?evaluation context frame Requires span
                (Printf.sprintf "This template may not meet `%s`, which its tag requires."
                   (quote own.callee clause.origin))
                (snd (clause_value context entry clause)))
            own.requires;
          let result = arrive context frame "tagged" tag_type in
          assume_valid context frame tag_type result;
          List.iter
            (fun (clause : expression) ->
              assume context frame
                (snd (clause_value context { entry with result = Some result } clause)))
            own.ensures;
          let frame =
            spend context frame
              (callee_amount context frame ~path ~parts:contract.parts
                 ~bound_frame:(fun part ->
                   {
                     (part_frame frame part ~arguments:[ (0, value_) ] ~substitution:[]) with
                     result = Some result;
                   })
                 ~uses:[] ~values:[] ~change:None)
          in
          (frame, result)
      | None -> unsupported span "a tagged template whose tag the prover cannot read")
  | _ -> unsupported span "a tagged template whose tag the prover cannot read"

and sequence_of context frame (ty : T.ty) ~element values =
  let made = arrive context frame "literal" ty in
  let sequence =
    match ty with
    | Named { path; _ } when Path.equal path sequence_path -> Some made
    | Named { path; _ } when Intrinsic.builtin_of_path path = Some Array ->
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
  let finite = T.Named { path = finite_set_path; arguments = [ T.Type element ] } in
  let made = arrive context frame "literal" ty in
  let model =
    match ty with Named { path; _ } when Path.equal path finite_set_path -> Some made | _ -> None
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

(* A specification's [FiniteMap] written out: each key with its value, and
   no other keys. Its keys must be distinct. *)
and map_literal context frame (node : expression) entries =
  let ty = type_of context frame node in
  let key_type, value_type =
    match ty with
    | Named { arguments = [ T.Type key; T.Type value_type ]; _ } -> (key, value_type)
    | _ -> unsupported (at frame node) "a literal of `%s`" (T.show ty)
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
            oblige context frame Disjoint (at frame other_key)
              (Printf.sprintf "The key `%s` may equal an earlier key of this map."
                 (quote frame.source other_key.origin))
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
    | _ -> unsupported (at frame node) "a literal of `%s`" (T.show ty)
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
  (frame, made)

(* Text as a value whose model is its UTF-8 bytes. A literal is one value
   for its text and type, so two literals with the same text are the same
   value, as a key written twice is the same key. *)
and text_value context frame (ty : T.ty) text =
  let symbol = "literal." ^ type_key ty ^ "." ^ Logic.hash text in
  let made = L.Symbol symbol in
  once context ("value of " ^ symbol) (fun () ->
      declare context (L.Constant (symbol, sort_of context ty));
      assume_valid context
        { frame with condition = L.Boolean true; bound = []; binders = [] }
        ty made;
      let byte = T.builtin UInt8 in
      let holds model =
        context.facts <-
          L.equal (sequence_length context byte model) (L.int (String.length text)) :: context.facts;
        String.iteri
          (fun index character ->
            match sequence_at context byte model (L.int index) with
            | Some at -> context.facts <- L.equal at (L.int (Char.code character)) :: context.facts
            | None -> ())
          text
      in
      Option.iter holds (model_of context ty made ~element:byte);
      (* Where its field is seen, the text is also its storage's, which is
         what its potential is read from. *)
      match constructors context ty with
      | Some [ (None, [ (field, Named { path; arguments = [ T.Type element ] }) ]) ]
        when Intrinsic.builtin_of_path path = Some Storage && T.equal element byte ->
          holds
            (buffer_model context Storage byte (L.Apply (selector_name ty None field, [ made ])))
      | _ -> ());
  made

(* A value's model, by the standard library's [impl] of [Model] for its
   type, as a call of [model()] would read it. *)
and model_of context (ty : T.ty) term ~element =
  model_as context ty term ~model:(sequence_type element)

(* A value's model of the given type, by the standard library's [impl] of
   [Model] for its type, as a call of [model()] would read it. *)
and model_as context (ty : T.ty) term ~(model : T.ty) =
  Option.map (fun model_of -> model_of term) (model_function context ty ~model)

(* A type's [model()], as a function of its values, if the standard library
   gives it one. *)
and model_function context (ty : T.ty) ~(model : T.ty) =
  let key = type_key ty ^ " " ^ type_key model in
  match Hashtbl.find_opt context.models key with
  | Some found -> found
  | None ->
      let found = find_model_function context ty ~model in
      Hashtbl.replace context.models key found;
      found

and find_model_function context (ty : T.ty) ~(model : T.ty) =
  let model_trait = Well_known.path Model in
  match
    Call_graph.impls_for
      (Query.demand context.database Call_graph.package_impls Path.standard_package)
      [ model_trait ] ty
  with
  | impl :: _ ->
      let path = Path.Method { owner = impl; name = "model"; receiver = Read } in
      let symbol = "function." ^ Path.show path ^ "[" ^ type_key ty ^ "]" in
      declare context (L.Function (symbol, [ sort_of context ty ], sort_of context model));
      model_ranked context ty ~model symbol;
      (* An array's model is its elements, as many as its type says. *)
      (match ty with
      | Named { path; arguments = [ T.Type element; T.Value count ] }
        when Intrinsic.builtin_of_path path = Some Array ->
          once context ("array." ^ symbol) (fun () ->
              let each = "array.value" in
              let elements = L.Apply (symbol, [ L.Symbol each ]) in
              context.facts <-
                L.Forall
                  ( [ (each, sort_of context ty) ],
                    L.equal
                      (sequence_length context element elements)
                      (substituted_value_term context count) )
                :: context.facts)
      | _ -> ());
      Some (fun term -> L.Apply (symbol, [ term ]))
  | [] -> None

(* A value's model is no higher in the order of parts than the value, so
   an element of a list's model is below the list. [symbol] is the model's
   function. *)
and model_ranked context (ty : T.ty) ~(model : T.ty) symbol =
  if context.ranking then
    once context ("ranked." ^ symbol) (fun () ->
        let each = "ranked.value" in
        context.facts <-
          L.Forall
            ( [ (each, sort_of context ty) ],
              L.Apply
                ( "<=",
                  [
                    rank context model (L.Apply (symbol, [ L.Symbol each ]));
                    rank context ty (L.Symbol each);
                  ] ) )
          :: context.facts)

(* Cursors. A cursor carries what it has handed out and whether it has
   ended as ghost parts of its value. *)
and cursor_trait : Path.t = Well_known.path Cursor

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
        if mentions_result clause = each then
          assume context at (snd (clause_value context inside clause)))
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

and option_path : Path.t = Well_known.path Option

(* A sequence of parts with nothing in it. *)
and empty_parts context frame element =
  let parts = fresh context frame "parts" (sort_of context (sequence_type element)) in
  assume context frame (L.equal (sequence_length context element parts) (L.int 0));
  parts

(* A sequence of parts about which only its length is known. *)
and some_parts context frame element =
  let parts = fresh context frame "parts" (sort_of context (sequence_type element)) in
  assume context frame L.(Apply (">=", [ sequence_length context element parts; int 0 ]));
  parts

(* The parts, with one more after them. *)
and appended context frame element parts part =
  let longer = fresh context frame "parts" (sort_of context (sequence_type element)) in
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
  (* Each sum over the longer sequence adds the new part's measure, as
     [Sequence.append]'s contract says. *)
  context.fresh <- context.fresh + 1;
  let measure = Printf.sprintf "measure.%d" context.fresh in
  assume context frame
    (L.Forall
       ( [ (measure, sort_of context (T.Function (measure_type element))) ],
         L.equal
           (sequence_sum context element longer (L.Symbol measure))
           (L.Apply
              ( "+",
                [
                  sequence_sum context element parts (L.Symbol measure);
                  applied context (measure_type element) (L.Symbol measure) [ part ];
                ] )) ));
  longer

(* Whether a clause mentions [result], so that it holds at each [yield]
   of a lending or yielding method, rather than where the method ends. *)
and mentions_result (clause : expression) =
  let found = ref false in
  Core_walk.expression
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : expression) -> match node.kind with Result -> found := true | _ -> ());
    }
    clause;
  !found

and signature_terminates context path =
  match Interface.Impls.signature context.database path with
  | Some (signature : T.signature) -> signature.terminates
  | None -> true

(* Data *)

(* A field of a value, which is in its type's range like every value. *)
and field_of context frame ty variant field field_type term =
  let part = selected context ty variant field term in
  assume context frame (in_range field_type part);
  (* A part of a value is below it, whatever its type, which is how
     structural recursion is shown to end. *)
  if context.ranking then begin
    let below = rank context field_type part in
    assume context frame
      L.(Apply ("<=", [ int 0; below ]) &&& Apply ("<", [ below; rank context ty term ]))
  end;
  part

(* A field of a value: of one built here, what it was built from. *)
and selected context ty variant field term =
  match (term, constructors context ty) with
  | L.Apply (name, arguments), Some shape when name = constructor_name ty variant -> (
      let fields = Option.value (List.assoc_opt variant shape) ~default:[] in
      match List.find_index (fun (named, _) -> named = field) fields with
      | Some index when index < List.length arguments -> List.nth arguments index
      | _ -> L.Apply (selector_name ty variant field, [ term ]))
  | _ -> L.Apply (selector_name ty variant field, [ term ])

(* A value's place in the order of parts, as Dafny's datatypes have one:
   any field is below the value it is in. *)
and rank context ty term =
  let symbol = "rank." ^ type_key ty in
  declare context (L.Function (symbol, [ sort_of context ty ], L.Int));
  L.Apply (symbol, [ term ])

(* The form of a type, which holds its fields' defaults, its invariants,
   and its potential. *)
and type_source context (ty : T.ty) =
  match ty with
  | Named { path; _ } -> (
      match
        Option.bind
          (Query.demand context.database Interface.Summary.key path)
          (source_at_key context.database)
      with
      | Some ({ core = { definition = Type _; _ }; _ } as source) -> Some source
      | _ -> None)
  | _ -> None

(* A frame for reading a type's own clauses about a value of it. *)
and type_frame context frame source (ty : T.ty) ~self =
  let substitution = match visible_type context ty with Some (_, s) -> s | None -> [] in
  {
    frame with
    source;
    locals = Locals.empty;
    types = Locals.empty;
    old_locals = Locals.empty;
    self;
    old_self = self;
    self_type = Some ty;
    result = None;
    checking = false;
    loop = None;
    updating = None;
    substitution;
  }

(* A function used as a value. *)
and global_value context frame (node : expression) path type_arguments =
  match function_contract ~reader:(Path.package context.current) context.database path with
  | Some contract -> named_function context frame node path type_arguments contract
  | None -> unsupported (at frame node) "a function the prover cannot read, used as a value"

(* A function named as a value is a value of its type known by what it
   promises of its calls: one unit of time per call when its [time] is a
   constant. Naming it is an edge of the call graph that passes no
   arguments, so in a function that must end, it must not reach back. *)
and named_function context frame (node : expression) path type_arguments contract =
  if
    context.terminates && frame.checking
    && Call_graph.reaches context.database ~package:(Path.package context.current) ~from:path
         ~target:context.current
  then
    oblige context frame Termination (at frame node)
      (Printf.sprintf
         "Naming `%s` as a value reaches back here, and such a use passes no arguments the prover \
          can compare, so the recursion cannot be shown to end: write it as a direct call on a \
          part."
         (Path.show path))
      (L.Boolean false);
  let ty = type_of context frame node in
  (* A function with a [requires], used as a value anywhere but passed
     straight to a parameter, which checks it, has a type that keeps no
     [requires], so it must accept every argument of that type. *)
  (match (ty, contract.parts) with
  | T.Function function_type, own :: _
    when own.requires <> [] && frame.checking && not (List.mem node.id context.passed_values) ->
      let inputs =
        List.map
          (fun (_, input) ->
            let input = substituted context frame input in
            let term = arrive context frame "argument" input in
            assume_valid context frame input term;
            term)
          function_type.inputs
      in
      if List.length own.parameters = List.length inputs then begin
        let inside =
          part_frame frame own
            ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
            ~substitution:[]
        in
        List.iter
          (fun (clause : expression) ->
            oblige context frame Requires (at frame node)
              (Printf.sprintf
                 "`%s` is used as a value of `%s`, which promises nothing of its arguments, so its \
                  `%s` may not hold."
                 (Path.show path) (T.show ty) (quote own.callee clause.origin))
              (snd (clause_value context inside clause)))
          own.requires
      end
  | _ -> ());
  let instance =
    match List.map (T.substitute_argument frame.substitution) type_arguments with
    | [] -> ""
    | arguments -> "[" ^ String.concat ", " (List.map argument_key arguments) ^ "]"
  in
  let symbol = "named." ^ Path.show path ^ instance in
  declare context (L.Constant (symbol, sort_of context ty));
  let term = L.Symbol symbol in
  (* Applied, a pure function named as a value is the function: its body,
     where it has a definition that holds for every argument, and
     otherwise the function in the logic. *)
  (match ty with
  | T.Function function_type when in_the_logic function_type && contract.pure ->
      let parameters = parameters_of context frame function_type in
      let inputs = List.map (fun (name, _) -> L.Symbol name) parameters in
      let defined =
        match contract.definition with
        | Some (part, body)
          when part.requires = [] && instance = ""
               && not (List.exists (Path.equal path) context.instantiating) ->
            context.instantiating <- path :: context.instantiating;
            Fun.protect
              ~finally:(fun () -> context.instantiating <- List.tl context.instantiating)
              (fun () ->
                body_over context frame parameters body (fun inside ->
                    part_frame inside part
                      ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
                      ~substitution:[]))
        | _ -> None
      in
      let value =
        match defined with
        | Some defined -> defined
        | None ->
            let output = match function_type.output with Returns output -> output | _ -> T.unit in
            let function_symbol = "function." ^ Path.show path ^ instance in
            declare context
              (L.Function (function_symbol, List.map snd parameters, sort_of context output));
            let value = L.Apply (function_symbol, inputs) in
            if instance = "" then
              contract_for_every_argument context frame contract parameters value;
            value
      in
      fact context frame
        (L.Forall (parameters, L.equal (applied context function_type term inputs) value))
  | _ -> ());
  let constant_time =
    List.exists
      (fun (part : part) ->
        List.exists
          (fun (cost : Core.cost) ->
            match cost with
            | { resource = Time; bound = Order_of { kind = Integer _; _ }; amortized = false; _ } ->
                true
            | _ -> false)
          part.costs)
      contract.parts
  in
  (if constant_time then
     let time = time_of context frame ty term in
     fact context frame (L.equal time (L.int 1)));
  term

(* What a pure function's contract says of its value for every argument:
   where its [requires] holds, its [ensures] does. Its clauses are read over
   the parameters as a quantifier's body is. *)
and contract_for_every_argument context frame (contract : contract) parameters value =
  let inputs = List.map (fun (name, _) -> L.Symbol name) parameters in
  let over =
    {
      frame with
      bound = List.map fst parameters @ frame.bound;
      binders =
        List.rev_map (fun (name, sort) -> (name, sort, L.Boolean true)) parameters @ frame.binders;
      checking = false;
    }
  in
  let read (part : part) =
    {
      (part_frame over part
         ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
         ~substitution:[])
      with
      result = Some value;
    }
  in
  try
    let requiring =
      match contract.parts with
      | own :: others -> if own.requires <> [] || others = [] then [ own ] else others
      | [] -> []
    in
    let requires_of parts =
      L.conjunction
        (List.concat_map
           (fun (part : part) ->
             List.map (fun clause -> snd (clause_value context (read part) clause)) part.requires)
           parts)
    in
    let required = requires_of requiring in
    List.iter
      (fun (part : part) ->
        let required = if List.memq part requiring then required else requires_of [ part ] in
        List.iter
          (fun clause ->
            let ensured = snd (clause_value context (read part) clause) in
            match closed_over_binders over (L.( ==> ) required ensured) with
            | Some closed -> context.facts <- closed :: context.facts
            | None -> ())
          part.ensures)
      contract.parts
  with Unsupported _ | Foreign_unsupported _ -> ()

(* A function named as a value and passed for a function-typed parameter
   must accept every argument the parameter's type promises it, and keep
   the cost clauses the type asks of what is passed. *)
and check_named_callback context frame (call_ : call) (passed : passed) (named : expression) path
    (contract : contract) (values : passed list) =
  let span = at frame named in
  let own = List.hd contract.parts in
  match parameter_type context frame call_ passed.position with
  | Some (T.Function expected) ->
      let inputs =
        List.map
          (fun (_, input) ->
            let input = substituted context frame input in
            let term = arrive context frame "argument" input in
            assume_valid context frame input term;
            term)
          expected.inputs
      in
      let known = List.map (fun (passed : passed) -> (passed.position, passed.term)) values in
      let promised =
        L.conjunction (callback_facts context frame call_ passed.position known inputs)
      in
      let at_call = restrict frame promised in
      (if List.length own.parameters = List.length inputs then
         let inside =
           part_frame frame own
             ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
             ~substitution:[]
         in
         List.iter
           (fun (clause : expression) ->
             oblige context at_call Requires span
               (Printf.sprintf
                  "`%s` may not accept every argument this parameter's type promises it: its `%s` \
                   may not hold."
                  (Path.show path) (quote own.callee clause.origin))
               (snd (clause_value context inside clause)))
           own.requires);
      List.iter
        (fun (cost : T.cost) ->
          if not (keeps_cost context path contract cost) then
            oblige context frame Cost span
              (Printf.sprintf
                 "`%s` does not promise what this parameter's type, `%s`, asks of a function \
                  passed for it."
                 (Path.show path) (T.show (T.Function expected)))
              (L.Boolean false))
        expected.costs
  | _ ->
      if own.requires <> [] || own.costs <> [] then
        unsupported span "a function passed for a parameter whose type the prover cannot read"

(* The type of a callee's parameter, by its position, with the call's type
   arguments. *)
and parameter_type context frame (call_ : call) index =
  match call_.callee with
  | Function { path; type_arguments } -> (
      match Interface.Impls.signature context.database path with
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
  let constant (value : expression) = match value.kind with Integer k -> Some k | _ -> None in
  let same (cost : Core.cost) =
    match (asked.resource, cost.resource) with
    | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
    | _ -> false
  in
  match asked with
  | { resource = Time; bound = Finite_cost; _ } -> signature_terminates context path
  | { resource = Calls _; _ } -> false
  | _ -> (
      match
        List.find_map
          (fun (part : part) ->
            List.find_map (fun cost -> if same cost then Some cost else None) part.costs)
          contract.parts
      with
      | Some cost -> (
          match (asked.bound, cost.bound) with
          | Order_of, (Order_of value | At_most value | Exactly value) -> constant value <> None
          | No_more_than (Some most), (At_most value | Exactly value) -> (
              match constant value with Some k -> Z.leq k most | None -> false)
          | Exactly_cost (Some exact), Exactly value -> constant value = Some exact
          | _ -> false)
      | None -> false)

(* A constant is its value, worked out from its definition, which is made
   of literals, arithmetic, other constants, and values built from them. *)
and constant_value context frame path =
  match
    Option.bind
      (Query.demand context.database Interface.Summary.key path)
      (source_at_key context.database)
  with
  | Some ({ core = { definition = Constant defined; _ }; _ } as constant_source) ->
      (* A constant is one value, a symbol whose value is stated once, as
         a fact of mathematics, wherever it is used. *)
      let symbol = "constant." ^ Path.show path in
      let empty =
        {
          frame with
          source = constant_source;
          locals = Locals.empty;
          types = Locals.empty;
          checking = false;
          self = None;
          updating = None;
          condition = L.Boolean true;
          bound = [];
          binders = [];
        }
      in
      once context ("value of " ^ symbol) (fun () ->
          let ty = type_of context empty defined in
          declare context (L.Constant (symbol, sort_of context ty));
          let _, defined_value = specification context (fun () -> value context empty defined) in
          context.facts <- L.equal (L.Symbol symbol) defined_value :: context.facts);
      L.Symbol symbol
  | _ -> raise (Foreign_unsupported "a constant with errors")

(* Building a record or a variant: its constructor, with each field given
   or defaulted. *)
and construct context frame (node : expression) variant (fields : (string * operand option) list) =
  let ty = type_of context frame node in
  if T.equal ty T.unit then begin
    (* The one value of [Unit]. *)
    ignore (sort_of context T.unit);
    (frame, L.Apply ("Unit.unit", []))
  end
  else
    let frame, given =
      List.fold_left
        (fun (frame, given) (field, written) ->
          match written with
          | Some written ->
              let frame, term = operand_value context frame written in
              (frame, given @ [ (field, term) ])
          | None -> (frame, given @ [ (field, field_default context frame node ty variant field) ]))
        (frame, []) fields
    in
    let frame = spend context frame (construct_amount context frame ty variant) in
    match constructors context ty with
    | Some shape ->
        ignore (sort_of context ty);
        let shaped = match List.assoc_opt variant shape with Some fields -> fields | None -> [] in
        let field_value (name, _) =
          match List.assoc_opt name given with
          | Some term -> term
          | None -> unsupported (at frame node) "a field left out"
        in
        let built = L.Apply (constructor_name ty variant, List.map field_value shaped) in
        check_built context frame node ty built;
        (frame, built)
    | None ->
        (* A type whose fields are not visible here is known by its range. *)
        (frame, arrive context frame "built" ty)

and field_default context frame (node : expression) ty variant field =
  match type_source context ty with
  | Some ({ core = { definition = Type { defaults; _ }; _ }; _ } as source) -> (
      match
        List.find_map
          (fun (in_variant, name, default) ->
            if in_variant = variant && name = field then Some default else None)
          defaults
      with
      | Some default -> snd (value context (type_frame context frame source ty ~self:None) default)
      | None -> unsupported (at frame node) "a field left out without a default")
  | _ -> unsupported (at frame node) "a default of a type with errors"

(* Whether a value matches a pattern, and the names it binds: the
   condition, and the frame with the names bound. A name bound is the part
   of the value it names, which means something only where the condition
   holds, and is used only there. *)
and pattern_match context frame (pattern : pattern) term ty : L.term * frame =
  let span = at frame { id = pattern.id; origin = pattern.origin; type_ = ty; kind = Todo } in
  match pattern.kind with
  | Wildcard -> (L.Boolean true, frame)
  | Bind { local; name; _ } ->
      Hashtbl.replace context.local_names local name;
      (L.Boolean true, bind frame local ty term)
  | Literal literal ->
      let frame, expected = value context frame literal in
      (L.equal term expected, frame)
  | Range { start; stop; inclusive } ->
      let _, low = value context frame start in
      let _, high = value context frame stop in
      ( L.(Apply ("<=", [ low; term ]) &&& Apply ((if inclusive then "<=" else "<"), [ term; high ])),
        frame )
  | Equal_to { value = { kind = String text; _ }; _ } -> (
      (* Text matches when its bytes are the pattern's. *)
      let byte = T.builtin UInt8 in
      match model_of context ty term ~element:byte with
      | Some model ->
          ( L.conjunction
              (L.equal (sequence_length context byte model) (L.int (String.length text))
              :: List.init (String.length text) (fun index ->
                  match sequence_at context byte model (L.int index) with
                  | Some at -> L.equal at (L.int (Char.code text.[index]))
                  | None -> L.Boolean false)),
            frame )
      | None -> unsupported span "a string pattern on `%s`" (T.show ty))
  | Equal_to { value = compared; _ } ->
      let _, expected = value context frame compared in
      (equal_of context frame ty term expected, frame)
  | Variant { variant; fields } ->
      ignore (sort_of context ty);
      if constructors context ty = None then
        unsupported span "a variant of `%s`, which the prover does not see" (T.show ty);
      let test = L.Apply (L.tester (constructor_name ty (Some variant)), [ term ]) in
      let condition, frame = fields_match context frame span ty (Some variant) term fields in
      (L.( &&& ) test condition, frame)
  | Record fields ->
      ignore (sort_of context ty);
      if constructors context ty = None then
        unsupported span "the fields of `%s`, which the prover does not see" (T.show ty);
      fields_match context frame span ty None term fields
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
            Locals.mapi
              (fun id _ ->
                match List.rev matched with
                | (_, last) :: earlier ->
                    List.fold_left
                      (fun otherwise (condition, (after : frame)) ->
                        match Locals.find_opt id after.locals with
                        | Some part -> L.ite condition part otherwise
                        | None -> otherwise)
                      (Locals.find id last.locals) earlier
                | [] -> Locals.find id first.locals)
              (Locals.filter
                 (fun id _ ->
                   List.for_all (fun (_, (after : frame)) -> Locals.mem id after.locals) matched)
                 first.locals)
      in
      let types = match matched with (_, first) :: _ -> first.types | [] -> frame.types in
      (L.disjunction (List.map fst matched), { frame with locals = bound; types })

and fields_match context frame span type_ variant term (fields : (string * pattern) list) =
  let declared =
    match declared_fields context type_ variant with Some declared -> declared | None -> []
  in
  List.fold_left
    (fun (condition, frame) (name, subpattern) ->
      match List.assoc_opt name declared with
      | Some field_type ->
          let part = field_of context frame type_ variant name field_type term in
          let inner, frame = pattern_match context frame subpattern part field_type in
          (L.( &&& ) condition inner, frame)
      | None -> unsupported span "the field `%s`" name)
    (L.Boolean true, frame) fields

(* Each binding a pattern lends [mut] from the value it matches, with how
   the value is rebuilt from what the binding holds when the lend ends:
   through the variants and fields that lead to it, each other field kept. *)
and lent_bindings context frame (pattern : pattern) ty :
    (Core.local * (L.term -> L.term -> L.term)) list =
  match pattern.kind with
  | Bind { local; mode = T.Mut; _ } -> [ (local, fun _ part -> part) ]
  | Variant { variant; fields } -> fields_lent context frame ty (Some variant) fields
  | Record fields -> fields_lent context frame ty None fields
  | Alternatives alternatives ->
      if
        List.exists
          (fun alternative -> lent_bindings context frame alternative ty <> [])
          alternatives
      then
        unsupported
          (span_of frame.source pattern.origin)
          "a `mut` binding in one of several alternatives";
      []
  | Wildcard | Bind _ | Literal _ | Range _ | Equal_to _ -> []

and fields_lent context frame ty variant (fields : (string * pattern) list) =
  match constructors context ty with
  | Some shape ->
      let shaped = match List.assoc_opt variant shape with Some fields -> fields | None -> [] in
      List.concat_map
        (fun (name, subpattern) ->
          match List.assoc_opt name shaped with
          | Some field_type ->
              List.map
                (fun (local, rebuild) ->
                  ( local,
                    fun whole part ->
                      L.Apply
                        ( constructor_name ty variant,
                          List.map
                            (fun (other, _) ->
                              let current = selected context ty variant other whole in
                              if other = name then rebuild current part else current)
                            shaped ) ))
                (lent_bindings context frame subpattern field_type)
          | None -> [])
        fields
  | None -> []

and match_ context frame (node : expression) scrutinees (arms : arm list) =
  let frame, scrutinee_values =
    List.fold_left
      (fun (frame, values) scrutinee ->
        let ty = operand_type context frame scrutinee in
        let frame, term = operand_value context frame scrutinee in
        (frame, (term, ty) :: values))
      (frame, []) scrutinees
  in
  let scrutinee_values = List.rev scrutinee_values in
  let result_type = type_of context frame node in
  let carries_value = not (T.equal result_type T.unit || result_type = T.Never) in
  let scoped (joined : frame) =
    { joined with locals = Locals.filter (fun id _ -> Locals.mem id frame.locals) joined.locals }
  in
  (* Each arm is tried where no arm before it was taken: where its patterns
     did not match, or they did and its guard, which may change locals, was
     false. *)
  let untaken = ref (Some frame) in
  let reached =
    List.filter_map
      (fun (arm_ : arm) ->
        if List.length arm_.patterns <> List.length scrutinee_values then
          unsupported
            (span_of frame.source arm_.origin)
            "an arm with a different number of patterns";
        match !untaken with
        | None -> None
        | Some current ->
            let condition, bound =
              List.fold_left2
                (fun (condition, frame) pattern (term, ty) ->
                  let inner, frame = pattern_match context frame pattern term ty in
                  (L.( &&& ) condition inner, frame))
                (L.Boolean true, current) arm_.patterns scrutinee_values
            in
            let entered = restrict bound condition in
            let entered, passed_over =
              match arm_.guard with
              | Some guard ->
                  let after, test = value context entered guard in
                  (restrict after test, [ scoped (restrict after (L.not_ test)) ])
              | None -> (entered, [])
            in
            untaken := join_frames context (restrict current (L.not_ condition) :: passed_over);
            (* What an arm leaves in each binding lent [mut] goes back into
               the scrutinee where the arm ends, however it ends. *)
            let lent =
              List.concat
                (List.map2
                   (fun pattern (scrutinee, (_, ty)) ->
                     match scrutinee with
                     | Place place ->
                         List.map
                           (fun binding -> (place, ty, binding))
                           (lent_bindings context frame pattern ty)
                     | Value _ -> [])
                   arm_.patterns
                   (List.combine scrutinees scrutinee_values))
            in
            let write_back (at : frame) =
              List.fold_left
                (fun (at : frame) (place, _, (local, rebuild)) ->
                  match Locals.find_opt local at.locals with
                  | Some part ->
                      let _, whole = place_value context { at with checking = false } place in
                      store context at place (rebuild whole part)
                  | None -> at)
                at lent
            in
            if lent = [] then block_value context entered arm_.body
            else begin
              let returns = List.length context.returns in
              let exits =
                Option.map
                  (fun (exits : loop_exits) ->
                    (List.length exits.breaks, List.length exits.continues))
                  frame.loop
              in
              let ended = block_value context entered arm_.body in
              (* Exits are added at the front, so the arm's are the first. *)
              let rewrite count list f =
                let added = List.length list - count in
                List.mapi (fun index item -> if index < added then f item else item) list
              in
              context.returns <-
                rewrite returns context.returns (fun (at, value) -> (write_back at, value));
              (match (frame.loop, exits) with
              | Some exits_, Some (breaks, continues) ->
                  exits_.breaks <- rewrite breaks exits_.breaks write_back;
                  exits_.continues <- rewrite continues exits_.continues write_back
              | _ -> ());
              Option.map (fun (at, term) -> (write_back at, term)) ended
            end)
      arms
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

(* [with]: a record with some fields replaced, each update a path of
   fields. *)
and with_ context frame (node : expression) base updates =
  let span = at frame node in
  let frame, base_term = value context frame base in
  let ty = type_of context frame node in
  let rec replace ty term path replacement =
    match (path, constructors context ty) with
    | [], _ -> replacement
    | field :: rest, Some [ (None, fields) ] ->
        ignore (sort_of context ty);
        L.Apply
          ( constructor_name ty None,
            List.map
              (fun (name_, field_type) ->
                let current = selected context ty None name_ term in
                if name_ = field then replace field_type current rest replacement else current)
              fields )
    | _ -> unsupported span "`with` on `%s`" (T.show ty)
  in
  let frame, term =
    List.fold_left
      (fun (frame, term) (path, updated) ->
        let frame, replacement = value context frame updated in
        (frame, replace ty term path replacement))
      (frame, base_term) updates
  in
  check_built context frame node ty term;
  (frame, term)

(* Type invariants. *)

(* A type's invariants, and the form to read them in. *)
and invariants_of context (ty : T.ty) =
  match type_source context ty with
  | Some ({ core = { definition = Type { invariants = _ :: _ as invariants; _ }; _ }; _ } as source)
    ->
      Some (source, invariants)
  | _ -> None

(* Whether a value meets its type's invariants, and with [deep] its
   fields' too, each read with [self] as the value. The invariant of a type
   whose fields this package does not see is a fact about the value only:
   a value of it comes from the type's own package, which shows it, so
   here it is assumed where a value arrives and shown where one leaves, and
   never unfolded. *)
and validity context frame ~assuming ?(deep = true) ?(own = true) ?(seen = []) ty term =
  if List.exists (T.equal ty) seen || List.exists (T.equal ty) context.validating then
    L.Boolean true
  else
    let validating = context.validating in
    context.validating <- ty :: validating;
    Fun.protect ~finally:(fun () -> context.validating <- validating) @@ fun () ->
    let own =
      match invariants_of context ty with
      | _ when not own -> L.Boolean true
      | Some _ when constructors context ty = None ->
          let symbol = "valid." ^ type_key ty in
          declare context (L.Function (symbol, [ sort_of context ty ], L.Bool));
          L.Apply (symbol, [ term ])
      | Some (source, written) -> (
          let inner = type_frame context frame source ty ~self:(Some term) in
          try
            L.conjunction
              (List.map (fun invariant -> snd (clause_value context inner invariant)) written)
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
                           (selected context ty variant field term)
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

and check_built context frame (node : expression) ty term =
  check_valid context frame (at frame node) ty term ~deep:false ~when_:"for the value built here"

(* A call to a function whose contract the prover reads: its [requires]
   must hold, its [ensures] holds after, and a recursive call decreases. *)
and contract_call context frame (node : expression) (call_ : call) path contract
    (values : passed list) ~lent_final ~havoc_mut ~substitution_of ~instance =
  (* A pure call's result is the function applied to its arguments, so a
     nested call's argument holds every call inside it, which its clauses
     and its definition then repeat at each use. Each argument that holds
     another call is named once, by its term, and the name stands for it.
     The same term gets the same name, so the same call is the same term
     wherever it is made. *)
  let values =
    if contract.pure && contract.result_kind <> `Yields then
      List.map
        (fun (passed : passed) ->
          if passed.mode = T.Mut || L.mentions frame.bound passed.term then passed
          else { passed with term = named_term context passed.type_ passed.term })
        values
    else values
  in
  let caller = frame.source in
  let span = at frame node in
  let argument_at index =
    List.find_map
      (fun (passed : passed) -> if passed.position = index then Some passed.term else None)
      values
  in
  (* Each part binds its own parameters to the call's arguments, or to its
     defaults. *)
  let bindings (part : part) =
    List.mapi
      (fun index (parameter : Core.parameter) ->
        let term =
          match argument_at index with
          | Some term -> Some term
          | None -> (
              match parameter.default with
              | Some default ->
                  let empty =
                    {
                      frame with
                      source = part.callee;
                      locals = Locals.empty;
                      types = Locals.empty;
                      checking = false;
                      updating = None;
                      substitution = substitution_of part;
                    }
                  in
                  Some (snd (value context empty default))
              | None -> None)
        in
        (parameter, term))
      part.parameters
  in
  let bind bindings =
    List.fold_left
      (fun (locals, types, self) ((parameter : Core.parameter), term) ->
        match (parameter.local, term) with
        | Self, Some term -> (locals, types, Some (term, parameter.type_))
        | local, Some term ->
            (Locals.add local term locals, Locals.add local parameter.type_ types, self)
        | _, None -> (locals, types, self))
      (Locals.empty, Locals.empty, None)
      bindings
  in
  let self_of part self = Option.map fst self
  and self_type_of part self =
    Option.map (fun (_, ty) -> T.substitute (substitution_of part) ty) self
  in
  let entry_frame (part : part) =
    let locals, types, self = bind (bindings part) in
    {
      frame with
      source = part.callee;
      locals;
      types;
      old_locals = locals;
      self = self_of part self;
      old_self = self_of part self;
      self_type = self_type_of part self;
      result = None;
      checking = false;
      loop = None;
      updating = None;
      substitution = substitution_of part;
    }
  in
  let own = List.hd contract.parts in
  (* A call in a cycle of the call graph must decrease: the callee's
     measure, at the call's arguments, is below the caller's on entry. *)
  if
    context.terminates && frame.checking
    && (match call_.callee with Trait_method _ -> Call_graph.dispatched call_.callee | _ -> true)
    && Call_graph.reaches context.database ~package:(Path.package context.current) ~from:path
         ~target:context.current
  then
    begin match (context.measures, own.decreases) with
    | [], [] when Path.equal path context.current && structural_parameters context frame own <> []
      ->
        (* With no [decreases], a call on parts of the parameters ends:
           their ranks decrease, compared in the parameters' order. *)
        let pairs = structural_parameters context frame own in
        let before = List.map (fun (ty, entry, _) -> rank context ty entry) pairs in
        let after =
          List.map (fun (ty, _, index) -> rank context ty (argument_at_index values index)) pairs
        in
        oblige context frame Termination span
          "This recursive call may not be on a part of its parameters: give the function a \
           `decreases` clause."
          L.(
            conjunction (List.map (fun b -> Apply ("<=", [ int 0; b ])) before)
            &&& smaller before after)
    | [], _ | _, [] ->
        oblige context frame Termination span
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
        oblige context frame Termination span
          (Printf.sprintf "This call may not decrease `%s`."
             (String.concat ", "
                (List.map (fun (measure : expression) -> quote caller measure.origin) measures)))
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
            let _, term = clause_value context entry clause in
            oblige context frame Requires span
              ?cited:
                (Option.map (fun key -> (key, span_of part.callee clause.origin)) part.callee.key)
              (Printf.sprintf "`%s` may not hold for this call to `%s`."
                 (quote part.callee clause.origin) (Path.show path))
              term;
            term)
          part.requires)
      requiring
  in
  let required = L.conjunction required in
  (* Each part's [ensures] holds where its [requires] does: a trait's, of
     an [impl]'s method whose own precondition is weaker, only where the
     trait's holds too. *)
  let required_by (part : part) =
    if List.memq part requiring then required
    else
      L.conjunction
        (List.map
           (fun (clause : expression) -> snd (clause_value context (entry_frame part) clause))
           part.requires)
  in
  let after = havoc_mut frame in
  (* A pure call's [ensures], where its [requires] holds, and its
     definition are facts of mathematics, true whether or not the body of a
     quantifier around the call runs. *)
  let in_quantifier = contract.pure && frame.binders <> [] in
  let state term = if in_quantifier then fact context after term else assume context after term in
  (* What each [mut] argument holds after the call: what its place holds,
     which [havoc_mut] gave a fresh value. *)
  let changed =
    List.filter_map
      (fun (passed : passed) ->
        match (passed.mode, passed.operand) with
        | T.Mut, Some operand -> (
            try
              Some
                ( passed.position,
                  snd (operand_value context { after with checking = false } operand) )
            with Unsupported _ | Foreign_unsupported _ ->
              Some (passed.position, arrive context after "changed" passed.type_))
        | _ -> None)
      values
  in
  let own_bound = bindings own in
  let own_arguments = List.filter_map snd own_bound in
  let result_type = type_of context frame node in
  let applied_as = ref None in
  let result =
    if
      contract.pure && contract.result_kind <> `Yields
      && List.length own_arguments = List.length own_bound
    then begin
      let symbol = "function." ^ Path.show path ^ instance in
      let sorts =
        List.mapi
          (fun index ((parameter : Core.parameter), _) ->
            match List.find_opt (fun (passed : passed) -> passed.position = index) values with
            | Some passed -> sort_of context passed.type_
            | None ->
                sort_of context
                  (Interface.Impls.normalize context.database
                     ~bounds:(fun _ -> [])
                     (T.substitute (substitution_of own) parameter.type_)))
          own_bound
      in
      declare context (L.Function (symbol, sorts, sort_of context result_type));
      (match (path, own_bound) with
      | Method { name = "model"; receiver = Read; _ }, [ (self, _) ] when self.local = Self ->
          model_ranked context
            (Interface.Impls.normalize context.database
               ~bounds:(fun _ -> [])
               (T.substitute (substitution_of own) self.type_))
            ~model:result_type symbol
      | _ -> ());
      applied_as := Some (symbol, sorts);
      (if
         Path.package path <> Path.package context.current
         && (not (List.mem_assoc symbol context.hidden_bodies))
         &&
         match Interface.Impls.signature context.database path with
         | Some signature -> (
             T.body_is_definition signature && (not signature.transparent)
             (* A body that is a [todo] would define nothing if it were seen. *)
             &&
             match
               Option.bind (source_at context.database path) (fun (callee, _, _) -> body_of callee)
             with
             | Some body -> not (holds_todo body)
             | None -> false)
         | None -> false
       then
         let markable = match path with Method { owner = Impl _; _ } -> false | _ -> true in
         context.hidden_bodies <- (symbol, (Path.show path, markable)) :: context.hidden_bodies);
      let term = L.Apply (symbol, own_arguments) in
      assume context after (in_range result_type term);
      note_known_call context call_ path term own_arguments;
      term
    end
    else if contract.result_kind = `Yields then
      (* A cursor, of the call's own type. *)
      arrive context after "cursor" result_type
    else arrive context after "result" result_type
  in
  if contract.result_kind <> `Yields then assume_valid context after result_type result;
  (* A part lent [mut] goes back into the value it is part of when the lend
     ends, as the caller's statement left it, so that value is valid only
     if the part is, which is checked below. *)
  let left_valid =
    match (contract.result_kind, call_.lends, lent_final) with
    | `Lends, Some T.Mut, Some leave ->
        Some (validity context after ~assuming:false ~deep:true result_type (leave result), leave)
    | _ -> None
  in
  let check_left () =
    match left_valid with
    | Some (_, leave) ->
        check_valid context after span result_type (leave result) ~deep:true
          ~when_:"when the lend of this part ends"
    | None -> ()
  in
  let helper = updating_helper context call_ in
  List.iter
    (fun (passed : passed) ->
      if passed.mode = T.Mut && not (helper && passed.position = 0) then
        match List.assoc_opt passed.position changed with
        | Some term ->
            let valid = validity context after ~assuming:true passed.type_ term in
            assume context after
              (match left_valid with Some (left, _) -> L.( ==> ) left valid | None -> valid)
        | None -> ())
    values;
  if not (List.exists (Path.equal path) context.instantiating) then begin
    context.instantiating <- path :: context.instantiating;
    (* The definition, unfolded once, where the [requires] holds. A body
       the prover cannot read is simply not unfolded. *)
    (match contract.definition with
    | Some (part, body) when not (List.exists (L.mentions after.bound) own_arguments) ->
        let unfolding =
          if in_quantifier then
            { (entry_frame part) with condition = L.Boolean true; bound = []; binders = [] }
          else { (entry_frame part) with condition = after.condition }
        in
        let mark = List.length context.facts in
        (try
           match block_value context unfolding body with
           | Some (_, defined) -> state (L.( ==> ) required (L.equal result defined))
           | None -> ()
         with Unsupported _ | Foreign_unsupported _ -> ());
        List.iter (fun fact -> Hashtbl.replace context.unfolded fact ()) (facts_since context mark)
    | Some (part, body) when part.requires = [] -> (
        (* Called on a quantifier's bound values, the definition is stated
           once for every argument, so that it holds for each of them. *)
        match !applied_as with
        | Some (symbol, sorts) ->
            once context ("definition of " ^ symbol) (fun () ->
                let parameters =
                  List.mapi (fun index sort -> (Printf.sprintf "defined.%d" index, sort)) sorts
                in
                let inputs = List.map (fun (name, _) -> L.Symbol name) parameters in
                let outside = { after with bound = []; binders = []; condition = L.Boolean true } in
                match
                  body_over context outside parameters body (fun inside ->
                      part_frame inside part
                        ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
                        ~substitution:(substitution_of part))
                with
                | Some defined ->
                    context.facts <-
                      L.Forall (parameters, L.equal (L.Apply (symbol, inputs)) defined)
                      :: context.facts
                | None -> ())
        | None -> ())
    | None
      when List.for_all (fun (part : part) -> part.requires = []) contract.parts
           && List.exists (L.mentions after.bound) own_arguments -> (
        (* Known by its contract alone and called on a quantifier's bound
           values, the callee's [ensures] is stated once, for every valid
           argument. *)
        match !applied_as with
        | Some (symbol, sorts) ->
            once context ("contract of " ^ symbol) (fun () ->
                let parameters =
                  List.mapi (fun index sort -> (Printf.sprintf "ensured.%d" index, sort)) sorts
                in
                let inputs = List.map (fun (name, _) -> L.Symbol name) parameters in
                let outside =
                  {
                    after with
                    bound = List.map fst parameters;
                    binders = [];
                    condition = L.Boolean true;
                    checking = false;
                  }
                in
                let mark = context.fresh in
                let valid =
                  L.conjunction
                    (List.map2
                       (fun ((parameter : Core.parameter), _) input ->
                         validity context outside ~assuming:true
                           (T.substitute (substitution_of own) parameter.type_)
                           input)
                       own_bound inputs)
                in
                let ensured =
                  List.concat_map
                    (fun (part : part) ->
                      let inside =
                        {
                          (part_frame outside part
                             ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
                             ~substitution:(substitution_of part))
                          with
                          result = Some (L.Apply (symbol, inputs));
                          checking = false;
                        }
                      in
                      List.filter_map
                        (fun clause ->
                          match snd (clause_value context inside clause) with
                          | term when not (made_since context mark term) -> Some term
                          | _ -> None
                          | exception (Unsupported _ | Foreign_unsupported _) -> None)
                        part.ensures)
                    contract.parts
                in
                if ensured <> [] && not (made_since context mark valid) then
                  context.facts <-
                    L.Forall (parameters, L.( ==> ) valid (L.conjunction ensured)) :: context.facts)
        | None -> ())
    | _ -> ());
    (* The [ensures], after, where the [requires] held: [mut] parameters
       have their new values, and [old] the ones they had. *)
    let assume_ensures keep =
      List.iter
        (fun (part : part) ->
          let entry = bindings part in
          let exit_bindings =
            List.mapi
              (fun index (parameter, term) ->
                ( parameter,
                  match List.assoc_opt index changed with Some term -> Some term | None -> term ))
              entry
          in
          let entry_locals, types, entry_self = bind entry in
          let exit_locals, _, exit_self = bind exit_bindings in
          let ensures_frame =
            {
              frame with
              source = part.callee;
              condition = after.condition;
              locals = exit_locals;
              types;
              old_locals = entry_locals;
              self = self_of part exit_self;
              old_self = self_of part entry_self;
              self_type = self_type_of part entry_self;
              result = Some result;
              checking = false;
              loop = None;
              updating = None;
              substitution = substitution_of part;
            }
          in
          let ensures_frame =
            match contract.result_kind with
            | `Lends ->
                (* The part as lent, and the parts handed out: the one part, as
                 the caller's statement left it. *)
                let left = match lent_final with Some leave -> leave result | None -> result in
                let none = empty_parts context after result_type in
                {
                  ensures_frame with
                  yielded = Some (appended context after result_type none left);
                  finished = Some (L.Boolean true);
                }
            | `Returns | `Yields -> ensures_frame
          in
          List.iter
            (fun (clause : expression) ->
              if keep clause then
                let frame_for_clause =
                  if contract.result_kind = `Lends && mentions_result clause then
                    {
                      ensures_frame with
                      locals = entry_locals;
                      self = self_of part entry_self;
                      yielded = None;
                    }
                  else ensures_frame
                in
                match clause_value context frame_for_clause clause with
                | _, term ->
                    (* A pure call's [ensures], where its [requires] holds, is a
                   fact of mathematics, true whether or not a quantifier's
                   body around it runs. *)
                    state (L.( ==> ) (required_by part) term))
            part.ensures)
        (* A yielding method's clauses are about each part it hands out and
         how it ends, which each pull of the cursor it makes meets. *)
        (if contract.result_kind = `Yields then [] else contract.parts)
    in
    (* A lend's clauses about the part as lent come before the check of what
       the caller left in it, and those about how the lend ends, which read
       that part, after. *)
    let about_part clause = contract.result_kind <> `Lends || mentions_result clause in
    assume_ensures about_part;
    check_left ();
    assume_ensures (fun clause -> not (about_part clause));
    context.instantiating <- List.tl context.instantiating
  end
  else check_left ();
  (if contract.result_kind = `Yields then
     match result_type with
     | T.Cursor _ as cursor_type -> (
         match Interface.Impls.signature context.database path with
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
     arguments as passed and [result]. How much the potential of what the
     call changed grew: what it returns and leaves in [mut] arguments, less
     what it was given to change or to keep. *)
  let change () =
    List.fold_left
      (fun total (passed : passed) ->
        let ty = passed.type_ in
        match passed.mode with
        | T.Mut -> (
            match List.assoc_opt passed.position changed with
            | Some later ->
                Costs.plus total
                  (Costs.minus
                     (potential context after ty later)
                     (potential context frame ty passed.term))
            | None -> total)
        | T.Own -> Costs.minus total (potential context frame ty passed.term)
        | T.Read -> total)
      (match contract.result_kind with
      | `Yields -> Costs.zero
      | `Lends -> (
          (* A part lent stays where it was, so the call hands over none
             of its potential; what the caller's statement did to it, the
             method does not pay for, and the caller does. *)
          match lent_final with
          | Some leave ->
              Costs.minus
                (potential context after result_type result)
                (potential context after result_type (leave result))
          | None -> Costs.zero)
      | `Returns -> potential context after result_type result)
      values
  in
  let after =
    spend context after (fun counter ->
        match (call_.callee, counter.resource) with
        | Capability_method _, Calls _ ->
            (* A call of a capability's method is one of its calls. *)
            step_amount context after call_ values counter
        | _ ->
            (* A trait's method that promises only that it ends takes at most
               [time(T.method)] for the type it is called on. *)
            let ends_in =
              match call_.callee with
              | Trait_method _ when signature_terminates context path ->
                  Some (method_time context frame call_.callee)
              | _ -> None
            in
            callee_amount ?ends_in context after ~path ~parts:contract.parts
              ~bound_frame:(fun part ->
                { (entry_frame part) with result = Some result; condition = after.condition })
              ~uses:call_.uses ~values ~change:(Some change) counter)
  in
  (after, result)

(* A call that running code could give a value: a function that is
   compiled and not generic, reached directly, with every argument an
   integer or [Bool] literal and a result of one of those. *)
and note_known_call context (call_ : call) path term arguments =
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
  match Interface.Impls.signature context.database path with
  | Some
      ({ specification_only = false; generics = []; output = Returns result; _ } as signature :
        T.signature)
    when direct
         (* Running a callee reads its body, which a caller in another
            package may read only when it is [transparent]. *)
         && (Path.package path = Path.package context.current || signature.transparent)
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
and structural_parameters context frame (own : part) =
  List.concat
    (List.mapi
       (fun index (parameter : Core.parameter) ->
         match parameter.local with
         | Self -> (
             match (frame.old_self, frame.self_type) with
             | Some entry, Some ty when is_datatype ty -> [ (ty, entry, index) ]
             | _ -> [])
         | local -> (
             match (Locals.find_opt local frame.old_locals, local_type context frame local) with
             | Some entry, Some ty when is_datatype ty -> [ (ty, entry, index) ]
             | _ -> []))
       own.parameters)

and is_datatype ty = match ty with T.Named _ -> builtin ty = None | _ -> false

and argument_at_index (values : passed list) index =
  match
    List.find_map
      (fun (passed : passed) -> if passed.position = index then Some passed.term else None)
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

(* Costs: what each step spends. *)

(* The counters a body's loops' [cost] clauses count, outside lambdas,
   which count on their own. *)
and loop_counters locals (body : block) =
  let found = ref [] in
  let note (clauses : loop_clause list) =
    List.iter
      (function
        | Cost cost -> (
            match resource_of cost ~locals with
            | Some resource ->
                found :=
                  { Costs.resource; counting = counting_of cost; amortized = false } :: !found
            | None -> raise (Foreign_unsupported "this `calls` target"))
        | Invariant _ | Decreases _ -> ())
      clauses
  in
  let rec visit =
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : expression) ->
          match node.kind with Lambda _ -> () | _ -> Core_walk.expression_children visit node);
      statement =
        (fun (node : statement) ->
          (match node.kind with
          | While { clauses; _ } | For { clauses; _ } -> note clauses
          | _ -> ());
          Core_walk.statement_children visit node);
      pattern = (fun node -> Core_walk.pattern_children visit node);
    }
  in
  Core_walk.block visit body;
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
  let amount = fresh context frame "spent" L.Int in
  let least = match counter.resource with Time -> 1 | _ -> 0 in
  assume context frame (L.Apply ("<=", [ L.int least; amount ]));
  amount

(* An amount from zero to [bound], for a counter that counts exactly. *)
and bounded_amount context frame bound =
  let amount = fresh context frame "spent" L.Int in
  assume context frame L.(Apply ("<=", [ int 0; amount ]) &&& Apply ("<=", [ amount; bound ]));
  amount

(* Whether a cost clause is about a counter's resource. A [calls] clause's
   target is read with the locals of the clause's own form. *)
and same_resource (cost : Core.cost) ~locals (counter : Costs.counter) =
  match (cost.resource, counter.resource) with
  | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
  | Calls _, Calls counted -> (
      match resource_of cost ~locals with
      | Some (Calls target) -> Costs.covers ~clause:target ~counter:counted
      | _ -> false)
  | _ -> false

(* What a clause promises of a counter, in the counter's way of counting:
   [assumed] is the bound to assume for a call back into the definition
   proven, which is the induction hypothesis, and [change] is how much the
   potential of what an amortized clause's call changed grew, which it
   paid for out of its bound. *)
and promised_amount context frame (counter : Costs.counter) (bound : bound) ~evaluate ~assumed
    ~exact_target ~change =
  match (bound, counter.counting) with
  | Order_of g, Units ->
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
  | (Order_of _ | Finite), _ -> unknown_amount context frame counter

(* How much a potential grew, or zero where it fell or cannot be read. *)
and growth change =
  try Costs.at_least_zero (change ()) with Unsupported _ | Foreign_unsupported _ -> Costs.zero

(* What a call to a callee whose clauses are read spends of a counter: its
   clause about the counter's resource, from its first part that has one.
   A call back into the definition proven, through a cycle, assumes its
   [O(...)] bound with the definition's own constants; every function of a
   cycle is then proven with the first pair, so that each assumes of the
   others what they show. *)
and callee_amount ?ends_in context after ~path ~(parts : part list) ~(bound_frame : part -> frame)
    ~uses ~(values : passed list) ~change (counter : Costs.counter) =
  let assumed =
    if
      counter.counting = Units
      && Call_graph.reaches context.database ~package:(Path.package context.current) ~from:path
           ~target:context.current
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
    List.filter_map
      (fun (cost : Core.cost) ->
        if same_resource cost ~locals:frame.locals counter then Some (part, frame, cost) else None)
      part.costs
  in
  let amount (_, (frame : frame), (cost : Core.cost)) =
    let exact_target =
      match (cost.resource, counter.resource) with
      | Calls (Capability _), Calls (Capability_method _) -> false
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
  (* A callee with a plain and an amortized bound on the same resource is
     counted, for each counter, by the clause of the counter's kind: an
     amortized bound pays for the potential the call leaves, which an
     amortized counter is about, and a plain one is all a plain counter
     needs. *)
  let first_clauses () =
    let amortized_first = Option.is_some change && counter.amortized in
    List.find_map
      (fun part ->
        match clauses_of part with
        | [] -> None
        | found ->
            let amortized, plain =
              List.partition (fun (_, _, (cost : Core.cost)) -> cost.amortized) found
            in
            Some (if amortized_first then amortized @ plain else plain @ amortized))
      parts
  in
  match counter.resource with
  | Calls target when call_reaches context after uses values target = L.Boolean false -> Costs.zero
  | Calls (Through term) -> (
      let reaches = call_reaches context after uses values (Through term) in
      (* Each parameter the function value is passed for must have a
         clause about it. *)
      let receiving =
        List.filter_map
          (fun (passed : passed) -> if passed.term = term then Some passed.position else None)
          values
      in
      let captured =
        List.exists
          (fun (passed : passed) -> lambda_captures_target context passed.term term)
          values
      in
      match first_clauses () with
      | Some found
        when (not captured) && List.length found >= List.length receiving && receiving <> [] ->
          List.fold_left (fun total clause -> Costs.plus total (amount clause)) Costs.zero found
      | _ -> spent_where reaches (unknown_amount context after counter))
  | _ -> (
      (* [time(T.method)] is the most one call takes plus the potential it
         makes, so a call that makes potential has paid for it. *)
      let within_time time =
        Costs.minus
          (Costs.plus time (L.int 1))
          (match change with Some change -> growth change | None -> Costs.zero)
      in
      match (first_clauses (), counter.resource, counter.counting, ends_in) with
      | Some ((_, _, { bound = Finite; _ }) :: _), Time, Units, Some time -> within_time time
      | Some (clause :: _), _, _, _ -> amount clause
      | _, Time, Units, Some time -> within_time time
      | _ -> unknown_amount context after counter)

(* Whether a call can reach a [calls] clause's target: a function value
   passed to it, or captured by a lambda passed to it, or a capability it
   uses. *)
and call_reaches context frame uses (values : passed list) (target : Costs.target) =
  match target with
  | Through term ->
      L.disjunction
        (List.map
           (fun (passed : passed) ->
             if lambda_captures_target context passed.term term then L.Boolean true
             else may_be_target context frame passed.term passed.type_ term)
           values)
  | Capability path | Capability_method (path, _) ->
      L.Boolean
        (List.exists
           (function
             | T.Capability used -> Path.equal used path
             | T.Capability_parameter _ | T.Capability_projection _ | T.Capability_variable _ ->
                 true)
           uses)

(* Whether a function value is a [calls] clause's target: the target
   itself, or a value of its sort that may equal it, as one chosen by [if]
   or read from a field may. *)
and may_be_target context frame term ty target =
  if term = target then L.Boolean true
  else
    match List.assoc_opt target context.call_targets with
    | Some local -> (
        match (ty, local_type context frame local) with
        | T.Function _, Some target_type when sort_of context ty = sort_of context target_type ->
            L.equal term target
        | _ -> L.Boolean false)
    | None -> L.Boolean false

(* An amount spent only where [condition] holds. *)
and spent_where condition amount =
  match condition with
  | L.Boolean true -> amount
  | L.Boolean false -> Costs.zero
  | condition -> L.ite condition amount Costs.zero

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
  | Allocations -> by_clause T.Allocations
  | Allocated_bytes -> by_clause T.Allocated_bytes
  | Calls (Through term) ->
      if lambda_captures_target context callee_term term then unknown_amount context frame counter
      else
        spent_where
          (may_be_target context frame callee_term (T.Function function_type) term)
          (L.int 1)
  | Calls (Capability path | Capability_method (path, _)) ->
      if
        List.exists
          (function
            | T.Capability used -> Path.equal used path
            | T.Capability_parameter _ | T.Capability_projection _ | T.Capability_variable _ -> true)
          function_type.uses
      then unknown_amount context frame counter
      else Costs.zero

(* [time(f)], the time one call through a function value takes: one unit
   when its type has an [O(...)] bound, at least one otherwise, and for a
   lambda whose calls the prover could bound, that bound. *)
(* What the intrinsic module's storage and views hold, as the compiler
   declares it: each is a sequence of its elements, its model, and each
   operation changes or reads that sequence. An operation that stops the
   program on a bad index says what holds when it returns. *)
and buffer_operation context frame ~(node : expression) (operation : Intrinsic.operation) element
    operands ~changed known =
  let length sequence = sequence_length context element sequence in
  (* No buffer is larger than C lets an object be, half the address space,
     so a buffer's length fits an [ISize] as well as a [USize]. *)
  let fits value = L.(Apply ("<=", [ int 0; value ]) &&& in_range (T.builtin ISize) value) in
  let model builtin term =
    let sequence = buffer_model context builtin element term in
    assume context frame (fits (length sequence));
    sequence
  in
  let view = model Intrinsic.View in
  (* A storage also has room for some elements, at least as many as it
     holds. *)
  let capacity term = buffer_capacity context element term in
  let storage term =
    let sequence = model Intrinsic.Storage term in
    assume context frame
      L.(Apply ("<=", [ length sequence; capacity term ]) &&& fits (capacity term));
    sequence
  in
  let needs ?(what = "have the room it writes into") condition =
    oblige context frame Requires (at frame node)
      (Printf.sprintf "`%s` may not %s." (quote frame.source node.origin) what)
      condition
  in
  let keeps_capacity () =
    assume context frame (L.equal (capacity (List.hd changed)) (capacity (List.hd operands)))
  in
  let at sequence index =
    match sequence_at context element sequence index with
    | Some term -> term
    | None -> raise (Foreign_unsupported "the elements of a storage")
  in
  let bound () =
    context.fresh <- context.fresh + 1;
    Printf.sprintf "index.%d" context.fresh
  in
  let within index low high = L.(Apply ("<=", [ low; index ]) &&& Apply ("<", [ index; high ])) in
  let all name low high body =
    L.Forall ([ (name, L.Int) ], L.(within (Symbol name) low high ==> body))
  in
  let in_bounds index sequence = within index (L.int 0) (length sequence) in
  let each_sum relation =
    context.fresh <- context.fresh + 1;
    let measure = Printf.sprintf "measure.%d" context.fresh in
    L.Forall
      ( [ (measure, sort_of context (T.Function (measure_type element))) ],
        relation
          (fun sequence -> sequence_sum context element sequence (L.Symbol measure))
          (fun value -> applied context (measure_type element) (L.Symbol measure) [ value ]) )
  in
  let changed_storage () = storage (List.hd changed) in
  match (operation, operands) with
  | Storage_model, [ buffer ] -> storage buffer
  | View_model, [ buffer ] -> view buffer
  | Storage_empty, _ ->
      assume context frame (L.equal (length (storage known)) (L.int 0));
      known
  | Storage_with_capacity, [ room ] ->
      assume context frame
        L.(equal (length (storage known)) (int 0) &&& equal (capacity known) room);
      known
  | Storage_length, [ buffer ] -> length (storage buffer)
  | View_length, [ buffer ] -> length (view buffer)
  | Storage_capacity, [ buffer ] ->
      ignore (storage buffer);
      capacity buffer
  | Storage_set_capacity, [ buffer; room ] ->
      needs (L.Apply (">=", [ room; length (storage buffer) ]));
      assume context frame (L.equal (changed_storage ()) (storage buffer));
      assume context frame (L.equal (capacity (List.hd changed)) room);
      known
  | Storage_lengthen, [ buffer; by ] ->
      (* What the C library wrote into its room is the storage's. *)
      let before = storage buffer and after = changed_storage () in
      needs (L.Apply ("<=", [ L.Apply ("+", [ length before; by ]); capacity buffer ]));
      keeps_capacity ();
      let k = bound () in
      assume context frame (L.equal (length after) (L.Apply ("+", [ length before; by ])));
      assume context frame
        (all k (L.int 0) (length before) (L.equal (at after (L.Symbol k)) (at before (L.Symbol k))));
      known
  | Storage_shorten, [ buffer; shorter ] ->
      (* The first [shorter] elements, in the same room. *)
      let before = storage buffer and after = changed_storage () in
      needs ~what:"be given a length at most the storage's"
        (L.Apply ("<=", [ shorter; length before ]));
      keeps_capacity ();
      let k = bound () in
      assume context frame (L.equal (length after) shorter);
      assume context frame
        (all k (L.int 0) shorter (L.equal (at after (L.Symbol k)) (at before (L.Symbol k))));
      known
  | Storage_push, [ buffer; value ] ->
      needs (L.Apply ("<", [ length (storage buffer); capacity buffer ]));
      keeps_capacity ();
      let longer = appended context frame element (storage buffer) value in
      assume context frame (L.equal (changed_storage ()) longer);
      known
  | Storage_pop, [ _ ] ->
      keeps_capacity ();
      let longer = appended context frame element (changed_storage ()) known in
      assume context frame (L.equal (storage (List.hd operands)) longer);
      known
  | Storage_insert, [ buffer; index; value ] ->
      let before = storage buffer and after = changed_storage () in
      needs (L.Apply ("<", [ length before; capacity buffer ]));
      keeps_capacity ();
      let k = bound () in
      assume context frame
        (L.conjunction
           [
             L.Apply ("<=", [ L.int 0; index ]);
             L.Apply ("<=", [ index; length before ]);
             L.equal (length after) (L.Apply ("+", [ length before; L.int 1 ]));
             L.equal (at after index) value;
           ]);
      assume context frame
        (all k (L.int 0) index (L.equal (at after (L.Symbol k)) (at before (L.Symbol k))));
      let k = bound () in
      assume context frame
        (all k index (length before)
           (L.equal (at after (L.Apply ("+", [ L.Symbol k; L.int 1 ]))) (at before (L.Symbol k))));
      let k = bound () in
      assume context frame
        (all k
           (L.Apply ("+", [ index; L.int 1 ]))
           (length after)
           (L.equal (at after (L.Symbol k)) (at before (L.Apply ("-", [ L.Symbol k; L.int 1 ])))));
      assume context frame
        (each_sum (fun sum measure ->
             L.equal (sum after) (L.Apply ("+", [ sum before; measure value ]))));
      known
  | Storage_remove, [ buffer; index ] ->
      keeps_capacity ();
      let before = storage buffer and after = changed_storage () in
      let k = bound () in
      assume context frame
        (L.conjunction
           [
             in_bounds index before;
             L.equal (length after) (L.Apply ("-", [ length before; L.int 1 ]));
             L.equal known (at before index);
           ]);
      assume context frame
        (all k (L.int 0) index (L.equal (at after (L.Symbol k)) (at before (L.Symbol k))));
      let k = bound () in
      assume context frame
        (all k index (length after)
           (L.equal (at after (L.Symbol k)) (at before (L.Apply ("+", [ L.Symbol k; L.int 1 ])))));
      assume context frame
        (each_sum (fun sum measure ->
             L.equal (sum before) (L.Apply ("+", [ sum after; measure known ]))));
      known
  | (Storage_swap | View_swap), [ buffer; first; second ] ->
      let before, after =
        if operation = View_swap then (view buffer, view (List.hd changed))
        else begin
          keeps_capacity ();
          (storage buffer, changed_storage ())
        end
      in
      let k = bound () in
      assume context frame
        (L.conjunction
           [
             in_bounds first before;
             in_bounds second before;
             L.equal (length after) (length before);
             L.equal (at after first) (at before second);
             L.equal (at after second) (at before first);
           ]);
      assume context frame
        (all k (L.int 0) (length before)
           L.(
             not_ (equal (Symbol k) first)
             &&& not_ (equal (Symbol k) second)
             ==> equal (at after (Symbol k)) (at before (Symbol k))));
      assume context frame (each_sum (fun sum _ -> L.equal (sum after) (sum before)));
      known
  | (Storage_at | Storage_at_mut), [ buffer; index ] ->
      assume context frame (in_bounds index (storage buffer));
      at (storage buffer) index
  | View_at_mut, [ buffer; index ] ->
      assume context frame (in_bounds index (view buffer));
      at (view buffer) index
  | Storage_view_mut, [ buffer ] ->
      (* A view of the storage's elements, to change them through. The
         storage keeps its elements; a static one gets a buffer of its own,
         so its capacity may change. *)
      assume context frame
        L.(equal (view known) (storage buffer) &&& equal (changed_storage ()) (storage buffer));
      known
  | (Storage_take_view | View_take_view), [ owner; part; start ] ->
      (* The owner's elements from [start] are the view's, which changed
         them, and the owner is otherwise as it was. *)
      let before, after =
        if operation = View_take_view then (view owner, view (List.hd changed))
        else (storage owner, changed_storage ())
      in
      let run = view part in
      needs L.(Apply ("<=", [ Apply ("+", [ start; length run ]); length before ]));
      if operation = Storage_take_view then keeps_capacity ();
      run_replaced context frame element ~before ~after ~start
        ~stop:(L.Apply ("+", [ start; length run ]))
        ~run:(Some run);
      known
  | View_at, [ buffer; index ] ->
      assume context frame (in_bounds index (view buffer));
      at (view buffer) index
  | Storage_view, [ buffer ] ->
      assume context frame (L.equal (view known) (storage buffer));
      known
  | Compare_bytes, [ left; right ] -> byte_order context (view left) (view right)
  | View_slice, [ buffer; start; stop ] ->
      let whole = view buffer and part = view known in
      let k = bound () in
      assume context frame
        (L.conjunction
           [
             L.Apply ("<=", [ L.int 0; start ]);
             L.Apply ("<=", [ start; stop ]);
             L.Apply ("<=", [ stop; length whole ]);
             L.equal (length part) (L.Apply ("-", [ stop; start ]));
           ]);
      assume context frame
        (all k (L.int 0) (length part)
           (L.equal (at part (L.Symbol k)) (at whole (L.Apply ("+", [ start; L.Symbol k ])))));
      known
  | _ -> known

(* [compare_bytes] of two byte sequences, as the compiler makes it: their
   lexicographic order, below zero, zero, or above zero, which is zero
   exactly when they are the same bytes, and is a total order. *)
and byte_order context left right =
  let sequence = sort_of context (sequence_type (T.builtin UInt8)) in
  let symbol = "compare_bytes.order" in
  let first = not (Hashtbl.mem context.declared symbol) in
  declare context (L.Function (symbol, [ sequence; sequence ], L.Int));
  let order a b = L.Apply (symbol, [ a; b ]) in
  if first then begin
    let a = L.Symbol "bytes.first" and b = L.Symbol "bytes.second" and c = L.Symbol "bytes.third" in
    let over names body = L.Forall (List.map (fun name -> (name, sequence)) names, body) in
    context.facts <-
      over [ "bytes.first"; "bytes.second" ]
        L.(
          Apply ("<=", [ int (-1); order a b ])
          &&& Apply ("<=", [ order a b; int 1 ])
          &&& (equal (order a b) (int 0) ==> equal a b)
          &&& equal (order b a) (Apply ("-", [ order a b ])))
      :: over [ "bytes.first" ] (L.equal (order a a) (L.int 0))
      :: over
           [ "bytes.first"; "bytes.second"; "bytes.third" ]
           L.(
             Apply ("<", [ order a b; int 0 ])
             &&& Apply ("<", [ order b c; int 0 ])
             ==> Apply ("<", [ order a c; int 0 ]))
      :: context.facts
  end;
  order left right

(* How many elements a storage has room for, as a function of it. *)
and buffer_capacity context element term =
  let ty = T.Named { path = Intrinsic.builtin_path Storage; arguments = [ T.Type element ] } in
  let symbol = "capacity." ^ type_key ty in
  declare context (L.Function (symbol, [ sort_of context ty ], L.Int));
  L.Apply (symbol, [ term ])

(* The sequence a storage or a view holds, as a function of it. *)
and buffer_model context (builtin : Intrinsic.builtin) element term =
  let ty = T.Named { path = Intrinsic.builtin_path builtin; arguments = [ T.Type element ] } in
  let symbol = "model." ^ type_key ty in
  declare context
    (L.Function (symbol, [ sort_of context ty ], sort_of context (sequence_type element)));
  L.Apply (symbol, [ term ])

(* Whether a call through a value of a function type is a function in the
   logic: it ends, uses no capabilities, changes none of its arguments, and
   returns its result. *)
and in_the_logic (function_type : T.function_type) =
  T.terminates function_type && function_type.uses = []
  && List.for_all (fun (mode, _) -> mode <> T.Mut) function_type.inputs
  && match function_type.output with Returns _ -> true | _ -> false

(* A function value applied to its arguments, through the [apply] of its
   type's sorts. *)
and applied context (function_type : T.function_type) callee arguments =
  let inputs = List.map (fun (_, input) -> sort_of context input) function_type.inputs in
  let output =
    sort_of context (match function_type.output with Returns output -> output | _ -> T.unit)
  in
  let value_sort = sort_of context (T.Function function_type) in
  let symbol =
    String.concat "." ("apply" :: List.map sort_label ((value_sort :: inputs) @ [ output ]))
  in
  declare context (L.Function (symbol, value_sort :: inputs, output));
  L.Apply (symbol, callee :: arguments)

(* Bound names for each input of a function type, at this depth of
   quantifiers. *)
and parameters_of context frame (function_type : T.function_type) =
  let depth = List.length frame.bound in
  List.mapi
    (fun index (_, input) ->
      ( Printf.sprintf "parameter.%d.%d" depth index,
        sort_of context (substituted context frame input) ))
    function_type.inputs

and time_of context frame (ty : T.ty) term =
  let sort = sort_of context ty in
  let symbol = "time." ^ match sort with L.Uninterpreted name -> name | _ -> "value" in
  declare context (L.Function (symbol, [ sort ], L.Int));
  let time = L.Apply (symbol, [ term ]) in
  fact context frame (L.Apply ("<=", [ L.int 1; time ]));
  (match ty with
  | T.Function { costs; _ }
    when List.exists (fun (cost : T.cost) -> cost.resource = T.Time && cost.bound = Order_of) costs
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

(* What building a record or a variant spends: one allocation, of its
   block, for a variant that is held by reference. *)
and construct_amount context frame (ty : T.ty) variant (counter : Costs.counter) =
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
  | Time | Calls _ -> Costs.zero

(* What a call whose contract is not read spends. *)
and step_amount context frame (call_ : call) (values : passed list) (counter : Costs.counter) =
  match call_.callee with
  | Intrinsic { operation; type_arguments } -> (
      let cost = Intrinsic_signatures.cost operation in
      match counter.resource with
      | Time -> (
          match (cost.time, counter.counting) with
          | Constant_time, _ -> Costs.zero
          | Linear_in position, Units -> (
              match List.find_opt (fun (passed : passed) -> passed.position = position) values with
              | Some passed -> (
                  match passed.type_ with
                  | T.Named { path; arguments = [ T.Type element ] } -> (
                      match Intrinsic.builtin_of_path path with
                      | Some ((Storage | View) as builtin) ->
                          sequence_length context element
                            (buffer_model context builtin element passed.term)
                      | _ -> unknown_amount context frame counter)
                  | _ -> unknown_amount context frame counter)
              | None -> unknown_amount context frame counter)
          | (Linear_in _ | Unbounded_time), _ -> unknown_amount context frame counter)
      | Allocations | Allocated_bytes -> (
          match (cost.allocations, counter.resource, counter.counting) with
          | No_allocations, _, _ -> Costs.zero
          | One_if_positive amount, resource, counting -> (
              let given =
                match amount with
                | Argument position ->
                    Option.map
                      (fun (passed : passed) -> passed.term)
                      (List.find_opt (fun (passed : passed) -> passed.position = position) values)
                | Generic name -> generic_argument context frame operation type_arguments name
              in
              match given with
              | Some given when resource = Allocations || counting = Units ->
                  L.ite (L.Apply (">", [ given; L.int 0 ])) (L.int 1) (L.int 0)
              | _ -> unknown_amount context frame counter)
          | Unknown_allocations, _, _ -> unknown_amount context frame counter)
      | Calls _ -> Costs.zero)
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
          | Some part ->
              let inside =
                part_frame frame part
                  ~arguments:
                    (List.map (fun (passed : passed) -> (passed.position, passed.term)) values)
                  ~substitution:[]
              in
              callee_amount context frame
                ~path:(Path.Method { owner = capability; name; receiver = Static })
                ~parts:[ part ]
                ~bound_frame:(fun _ -> inside)
                ~uses:call_.uses ~values ~change:None counter
          | None -> unknown_amount context frame counter))
  | Function _ | Trait_method _ | Indirect _ -> (
      match counter.resource with
      | Calls target ->
          spent_where
            (call_reaches context frame call_.uses values target)
            (unknown_amount context frame counter)
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
and specification_function context frame (node : expression) (measure : specification_function)
    arguments =
  (* A specification function never runs, so a callback read for it is
     not used as a value. *)
  let values =
    reading_callback context (fun () ->
        List.map (fun argument -> snd (value context frame argument)) arguments)
  in
  match (measure, values, arguments) with
  | Log, [ n ], [ argument ] ->
      let log = log_of context frame n in
      (* [log] of a value of a bounded type is at most [log] of the type's
         largest value: its width, for an unsigned type. *)
      let rec unconverted (node : expression) =
        match node.kind with
        | Convert { conversion = To_integer; value = inner } -> unconverted inner
        | _ -> node
      in
      (match bounds (type_of context frame (unconverted argument)) with
      | Some (_, high) when not (L.mentions frame.bound n) ->
          fact context frame
            L.(Apply ("<=", [ n; Integer high ]) ==> Apply ("<=", [ log; int (Z.numbits high) ]))
      | _ -> ());
      Some (frame, log)
  | Power, [ base; exponent ], _ -> Some (frame, power_of context frame base exponent)
  | Time, [ f ], [ function_value ] ->
      Some (frame, time_of context frame (type_of context frame function_value) f)
  | _ -> unsupported (at frame node) "this specification function"

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
  (* Of a number, it is the number's bit length: the smallest integer at
     least log2(n + 1). *)
  (match n with
  | L.Integer k ->
      fact context frame
        (L.equal
           (L.Apply (Costs.log_symbol, [ n ]))
           (L.int (if Z.sign k <= 0 then 0 else Z.numbits k)))
  | _ -> ());
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
  (* Of two numbers, it is their power. *)
  (match (base, exponent) with
  | L.Integer b, L.Integer e when Z.sign e >= 0 && Z.leq e (Z.of_int 256) ->
      fact context frame
        (L.equal
           (L.Apply (Costs.power_symbol, [ base; exponent ]))
           (L.Integer (Z.pow b (Z.to_int e))))
  | _ -> ());
  L.Apply (Costs.power_symbol, [ base; exponent ])

(* [time(T.method)]: the longest any one call of a trait's method on a type
   takes in this run, a constant of the run, at least one step. It is one
   symbol for each method and type, so a callee's bound and its caller's
   are about the same term. *)
and method_time context frame (callee : callee) =
  match callee with
  | Trait_method { trait; name; receiver; self_type; _ } ->
      trait_method_time context frame
        (Path.Method { owner = trait.trait; name; receiver })
        (substituted context frame self_type)
  | _ -> raise (Foreign_unsupported "the time of what is not a trait's method")

and trait_method_time context frame (method_ : Path.t) self_type =
  let symbol =
    Printf.sprintf "time.method.%s" (Path.show method_) ^ "[" ^ type_key self_type ^ "]"
  in
  declare context (L.Constant (symbol, L.Int));
  fact context frame (L.Apply ("<=", [ L.int 1; L.Symbol symbol ]));
  L.Symbol symbol

(* A built-in copy: of a [Plain] value that holds no potential, a copy of
   its bits; of any other, a call of [Copyable.copy], which takes
   [time(T.copy)] and pays for the potential the copy holds, as a trait's
   method that promises only that it ends does. *)
and copied context frame ty term =
  if
    context.counters = []
    || Interface.Impls.plain context.database ~bounds:(current_bounds context) ty
       && not (try has_potential context ty with Foreign_unsupported _ -> true)
  then frame
  else
    spend context frame (fun (counter : Costs.counter) ->
        match (counter.resource, counter.counting) with
        | Time, Units ->
            let time =
              trait_method_time context frame
                (Path.Method
                   { owner = Interface.Impls.copyable_path; name = "copy"; receiver = Read })
                ty
            in
            let made =
              try potential context frame ty term
              with Unsupported _ | Foreign_unsupported _ -> Costs.zero
            in
            Costs.minus (Costs.plus time (L.int 1)) made
        | _ -> unknown_amount context frame counter)

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
            match clause with
            | Cost cost
              when same_resource cost ~locals:frame.locals counter
                   && counting_of cost = counter.counting ->
                Some cost
            | _ -> None)
          clauses
      in
      let rule =
        match written with
        | Some cost ->
            let constants =
              match counter.counting with
              | Units ->
                  let constants = Costs.constants (Printf.sprintf "loop.%d" cost.origin) in
                  context.groups <- constants :: context.groups;
                  declare context (L.Constant (constants.factor, L.Int));
                  declare context (L.Constant (constants.addend, L.Int));
                  Some constants
              | At_most | Exactly -> None
            in
            Clause_bound (cost, constants)
        | None ->
            Per_iteration
              {
                per = fresh context frame "per" L.Int;
                per_held =
                  Option.map (fun held -> (fresh context frame "per" L.Int, held frame)) held;
              }
      in
      { counter; key; entry; rule; held })
    context.counters

and counting_of (cost : Core.cost) : Costs.counting =
  match cost.bound with Order_of _ | Finite -> Units | At_most _ -> At_most | Exactly _ -> Exactly

(* A loop's [cost] clause, about what the loop has spent so far, at [at]. *)
and loop_clause_holds context (at : frame) (counter : Costs.counter) (cost : Core.cost) constants
    ~since =
  let g =
    match cost.bound with
    | Order_of g | At_most g | Exactly g -> snd (value context { at with checking = false } g)
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
    { head with spent = List.map (fun cost -> (cost.key, fresh context head "spent" L.Int)) costs }
  in
  List.iter
    (fun cost ->
      let at_head = spent_at head cost.key in
      match cost.rule with
      | Clause_bound (written, constants) ->
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
      | Clause_bound (written, constants) ->
          (* The bound is well defined, as every specification must be. *)
          (match written.bound with
          | Order_of g | At_most g | Exactly g -> ignore (value context frame g)
          | Finite -> ());
          oblige context frame Cost
            (span_of frame.source written.origin)
            (Printf.sprintf "The loop's `%s` may not hold on entry to the loop."
               (quote frame.source written.origin))
            (loop_clause_holds context frame cost.counter written constants ~since:Costs.zero)
      | Per_iteration _ -> ())
    costs

(* After the body: each bound on one iteration is worked out from what the
   iterations that ended spent, and every iteration, ended or left by
   [break], is shown to be within its counter's bound. An iteration that
   spends or saves potential is bounded with the potential the loop
   holds. *)
and loop_iterations context (loop : statement) head costs ~mark ~facts ~ends ~breaks =
  let span = span_of head.source loop.origin in
  List.iter
    (fun cost ->
      match cost.rule with
      | Clause_bound (written_cost, constants) ->
          List.iter
            (fun (frame, when_) ->
              oblige context frame Cost
                (span_of frame.source written_cost.origin)
                (Printf.sprintf "The loop's `%s` may not hold %s."
                   (quote frame.source written_cost.origin)
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
          (* Where an iteration spends or saves potential, what it spends is
             bounded with the potential the loop holds, which telescopes,
             or, where that is not found, by itself; otherwise by itself. *)
          let held_rule =
            match (per_held, cost.held) with
            | Some (per_held, _), Some held
              when List.exists (fun f -> mentions_potential (plain f)) frames ->
                [
                  ( per_held,
                    fun (frame : frame) ->
                      Costs.normalize
                        (Costs.plus (plain frame) (Costs.minus (held frame) (held head))) );
                ]
            | _ -> []
          in
          let facts = facts @ List.map (fun (frame : frame) -> frame.condition) frames in
          let bounded (per, spent_in) =
            let spent = List.map spent_in frames in
            let most =
              match spent with
              | [] -> Costs.zero
              | first :: rest -> List.fold_left Costs.larger first rest
            in
            Option.map
              (fun bound -> (per, spent, bound))
              (Costs.bound_on ~varies:(made_since context mark) ~facts most)
          in
          match List.find_map bounded (held_rule @ [ (per, plain) ]) with
          | Some (per, spent, bound) ->
              fact context head (L.equal per bound);
              List.iter2
                (fun (frame : frame) spent ->
                  oblige context frame Cost span
                    "The prover cannot show that this iteration of the loop spends no more than \
                     the bound it found for every iteration from what the loop does not change: \
                     give the loop a `cost` clause."
                    (counted_with ~counter:cost.counter ~at:spent ~bound:per))
                frames spent
          | None ->
              oblige context head Cost span
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
        | Clause_bound (written, _) ->
            let g =
              match written.bound with
              | Order_of g | At_most g | Exactly g ->
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
      (fun id -> Option.map (fun ty -> (`Local id, ty)) (local_type context frame id))
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
                match Locals.find_opt id frame.locals with
                | Some term -> Costs.plus total (potential context frame ty term)
                | None -> total)
            | `Self, Some self -> Costs.plus total (potential context frame ty self)
            | `Self, None -> total)
          Costs.zero typed)

(* Potentials. *)

(* A type's own [cost potential], from its form. *)
and potential_clause context (ty : T.ty) =
  match type_source context ty with
  | Some ({ core = { definition = Type { potential = Some value; _ }; _ }; _ } as source) ->
      Some (source, value)
  | _ -> None

(* Whether a value of a type can hold potential: its type declares one, or
   a part of it can, whether or not this package sees its fields, or it is a
   growable buffer, a storage or a type whose model is the sequence one
   holds, which saves potential for growing. A type parameter may stand for
   such a type. *)
and has_potential context ?(seen = []) (ty : T.ty) =
  if seen <> [] then holds_potential_type context ~seen ty
  else
    let key = type_key ty in
    match Hashtbl.find_opt context.holds_potential key with
    | Some found -> found
    | None ->
        let found = holds_potential_type context ~seen ty in
        Hashtbl.replace context.holds_potential key found;
        found

and holds_potential_type context ~seen (ty : T.ty) =
  if List.exists (T.equal ty) seen then false
  else
    match ty with
    | Parameter _ -> true
    | Named _ when Option.is_some (buffer_elements context ty) -> true
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
              | Todo_type | Builtin_type _ | Error_shape _ -> []
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
and potential context frame ?(seen = []) (ty : T.ty) term =
  if not (has_potential context ty) then Costs.zero
  else begin
    let held = held_symbol context ty term in
    if (not (List.mem held context.potentials)) && not (L.mentions frame.bound term) then begin
      context.potentials <- held :: context.potentials;
      fact context frame
        L.(validity context frame ~assuming:true ty term ==> Apply ("<=", [ int 0; held ]));
      match (potential_clause context ty, constructors context ty) with
      (* A type whose fields are seen holds what they hold; one whose fields
         are not, as a [List] outside its package, is read as the buffer its
         model says it is. *)
      | None, None when Option.is_some (buffer_elements context ty) -> (
          (* A buffer's potential is what it saved for growing, as a
             doubling array saves it: twice its length less its capacity,
             and never below zero, so at most two units for each element;
             and its elements' potentials. A view cannot grow, so it saves
             nothing of its own. *)
          match buffer_elements context ty with
          | Some (element, model) ->
              let sequence = model term in
              let slack = buffer_slack context ty term in
              let length = sequence_length context element sequence in
              fact context frame
                L.(
                  Apply ("<=", [ int 0; slack ])
                  &&& Apply ("<=", [ slack; Apply ("*", [ int 2; length ]) ]));
              (match ty with
              | Named { path; _ } when Intrinsic.builtin_of_path path = Some Storage ->
                  let saved =
                    L.Apply
                      ( "-",
                        [ L.Apply ("*", [ L.int 2; length ]); buffer_capacity context element term ]
                      )
                  in
                  fact context frame
                    (L.equal slack (L.ite (L.Apply (">=", [ saved; L.int 0 ])) saved (L.int 0)))
              | Named { path; _ }
                when Intrinsic.builtin_of_path path = Some View
                     || Intrinsic.builtin_of_path path = Some Array ->
                  fact context frame (L.equal slack (L.int 0))
              | _ -> ());
              let elements =
                if has_potential context element then
                  sequence_sum context element sequence (potential_measure context element)
                else Costs.zero
              in
              fact context frame (L.equal held (Costs.plus slack elements))
          | None -> ())
      | clause, Some shape -> (
          try
            (* Without a clause, a type holds nothing of its own. *)
            let own =
              match clause with
              | Some (source, written) ->
                  snd (value context (type_frame context frame source ty ~self:(Some term)) written)
              | None -> Costs.zero
            in
            let parts = parts_potential context frame ~seen ty term in
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
    (* A record that holds nothing of its own holds what its parts hold,
       which is the same term as theirs wherever they change. *)
    match (potential_clause context ty, constructors context ty) with
    | None, Some [ (None, fields) ] when Option.is_none (buffer_elements context ty) -> (
        try parts_potential context frame ~seen ty term (None, fields)
        with Unsupported _ | Foreign_unsupported _ -> held)
    | _ -> held
  end

(* The potential a value's parts hold, for one variant's fields: each
   unfolded in turn, except a part of a type already being unfolded, which
   would unfold forever. *)
and parts_potential context frame ~seen ty term (variant, fields) =
  List.fold_left
    (fun total (field, field_type) ->
      if has_potential context field_type then
        let part = selected context ty variant field term in
        Costs.plus total
          (if List.exists (T.equal field_type) (ty :: seen) then held_symbol context field_type part
           else potential context frame ~seen:(ty :: seen) field_type part)
      else total)
    Costs.zero fields

(* A growable buffer's elements and model: a storage, by its own model, or
   a type whose [Model] is the sequence of the storage it holds in its one
   field, as a [List] and a [String] are. *)
and buffer_elements context (ty : T.ty) =
  let key = type_key ty in
  match Hashtbl.find_opt context.buffers key with
  | Some found -> found
  | None ->
      let found = find_buffer_elements context ty in
      Hashtbl.replace context.buffers key found;
      found

and find_buffer_elements context (ty : T.ty) =
  match ty with
  | Named { path; arguments = [ T.Type element; T.Value _ ] }
    when Intrinsic.builtin_of_path path = Some Array ->
      Option.map
        (fun model_of -> (element, model_of))
        (model_function context ty ~model:(sequence_type element))
  | Named { path; arguments = [ T.Type element ] }
    when Intrinsic.builtin_of_path path = Some Storage ->
      Some (element, fun term -> buffer_model context Storage element term)
  | Named { path; arguments = [ T.Type element ] } when Intrinsic.builtin_of_path path = Some View
    ->
      Some (element, fun term -> buffer_model context View element term)
  | Named { path; arguments } when builtin ty = None -> (
      match Query.demand context.database Interface.Environment.interface path with
      | Some (Interface.Environment.Type_interface { shape = Record [ field ]; type_generics; _ })
        -> (
          let substitution =
            try
              List.combine
                (List.map (fun (generic : T.generic) -> generic.generic) type_generics)
                arguments
            with Invalid_argument _ -> []
          in
          match T.substitute substitution field.field_type with
          | Named { path = field_path; arguments = [ T.Type element ] }
            when Intrinsic.builtin_of_path field_path = Some Storage
                 || Intrinsic.builtin_of_path field_path = Some View ->
              Option.map
                (fun model_of -> (element, model_of))
                (model_function context ty ~model:(sequence_type element))
          | _ -> None)
      | _ -> None)
  | _ -> None

(* What a buffer has saved for growing, as a function of it. *)
and buffer_slack context (ty : T.ty) term =
  let symbol = "slack." ^ type_key ty in
  declare context (L.Function (symbol, [ sort_of context ty ], L.Int));
  L.Apply (symbol, [ term ])

(* A value's potential as a measure, for a sum over a collection of such
   values: applied, it is the potential. *)
and potential_measure context element =
  let symbol = "potential.measure." ^ type_key element in
  let measure = measure_type element in
  declare context (L.Constant (symbol, sort_of context (T.Function measure)));
  let term = L.Symbol symbol in
  if not (List.mem term context.potentials) then begin
    context.potentials <- term :: context.potentials;
    let each = "potential.element" in
    context.facts <-
      L.Forall
        ( [ (each, sort_of context element) ],
          L.equal
            (applied context measure term [ L.Symbol each ])
            (held_symbol context element (L.Symbol each)) )
      :: context.facts
  end;
  term

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

and block_value context frame (body : block) =
  let rec go frame = function
    | [] -> (
        match body.value with
        | Some last -> expression context frame last
        | None -> Some (frame, L.Boolean true))
    | statement_ :: rest -> (
        match statement context frame statement_ with Some frame -> go frame rest | None -> None)
  in
  match go frame body.statements with
  | Some (after, term) ->
      (* Locals declared inside the block end with it. *)
      let locals = Locals.filter (fun id _ -> Locals.mem id frame.locals) after.locals in
      Some ({ after with locals }, term)
  | None -> None

and statement context frame (node : statement) : frame option =
  if frame.source.key = Some context.home then
    try statement_kind context frame node
    with Foreign_unsupported message ->
      raise (Unsupported (span_of frame.source node.origin, message))
  else statement_kind context frame node

(* A proof is ghost code, which a build leaves out: what it shows is known
   after it, but the program goes on from where it was, with nothing the
   proof changed, whichever way the proof ends, or if it never ends. A
   [todo] in it stands for the proof still to write, so what follows is not
   shown on the paths that reach one, which are what this gives. *)
and ghost context frame body =
  let proving = context.proving
  and returns = context.returns
  and leaving = context.leaving
  and unfinished = context.unfinished in
  context.proving <- true;
  context.unfinished <- [];
  Fun.protect
    ~finally:(fun () ->
      context.proving <- proving;
      context.returns <- returns;
      context.leaving <- leaving;
      context.unfinished <- unfinished)
    (fun () ->
      ignore (block_value context { frame with loop = None } body);
      L.disjunction context.unfinished)

and statement_kind context frame (node : statement) : frame option =
  let span = span_of frame.source node.origin in
  match node.kind with
  | Evaluate value_ -> Option.map fst (expression context frame value_)
  | Let { pattern; value = initial; else_ = None } ->
      (* A [let]'s pattern cannot fail, so only its names matter. *)
      let ty = operand_type context frame initial in
      let frame, term = operand_value context frame initial in
      let _, frame = pattern_match context frame pattern term ty in
      Some frame
  | Let { pattern; value = initial; else_ = Some otherwise } -> (
      (* The pattern may fail, and the [else] block, which must leave the
         path, runs where it does. *)
      let ty = operand_type context frame initial in
      let frame, term = operand_value context frame initial in
      let matched, bound = pattern_match context frame pattern term ty in
      match block_value context (restrict frame (L.not_ matched)) otherwise with
      | Some (fallen, _) ->
          oblige context fallen Unreachable span
            "This `else` block may finish, but it must leave the path, since the pattern did not \
             match."
            (L.Boolean false);
          Some (restrict bound matched)
      | None -> Some (restrict bound matched))
  | Assign { target; value = assigned } ->
      let frame, new_value = value context frame assigned in
      Some (store context frame target new_value)
  | Compound_assign { target; value = updated } ->
      (* The target is worked out once: what it holds is what [updating]
         names in the value it takes. *)
      let frame, current = place_value context frame target in
      let after, new_value = value context { frame with updating = Some current } updated in
      Some (store context { after with updating = frame.updating } target new_value)
  | While { condition; clauses; body } -> while_ context frame node condition clauses body
  | For { pattern; iteration; clauses; body; _ } ->
      (* A loop's iterations change disjoint places, so however they run, as
         tasks or at once, they can be read one after another. *)
      for_ context frame node pattern iteration clauses body
  | Assert { value = asserted; _ } ->
      let frame, term = value context frame asserted in
      if is_test context then assume context frame term
      else
        oblige context frame Assertion (at frame asserted)
          (Printf.sprintf "`%s` may not hold." (quote frame.source asserted.origin))
          term;
      Some frame
  | Proof block_ -> Some (restrict frame (L.not_ (ghost context frame block_)))
  | Parallel branches ->
      (* Branches are disjoint, so they can run in order. *)
      List.fold_left
        (fun frame branch ->
          match frame with Some frame -> statement context frame branch | None -> None)
        (Some frame) branches
  | Concurrent branches -> concurrent context frame node branches
  | Yield { mode; part } -> handing_out context frame node mode part

(* A [concurrent] block. Its branches change disjoint places, and a
   capability call gives a fresh value whoever calls in between, so they
   are read one after another, as [parallel]'s are. An early exit from a
   branch takes effect where the block ends, after the other branches,
   which are cancelled and run to their own ends: each later branch runs
   from where the exit was as well as from where the branches before it
   ended, and each exit is then taken with what its path changed, or, if
   it leaves tasks around this block too, left to them. *)
and concurrent context frame (node : statement) branches =
  let outer = context.leaving in
  let from_here (left : leaving) =
    match left.tasks with Branch { block; _ } :: _ -> block = node.origin | _ -> false
  in
  let run start branch =
    context.leaving <- [];
    let ended = statement context start branch in
    let left = context.leaving in
    (ended, left)
  in
  let normal, pending =
    List.fold_left
      (fun (normal, pending) branch ->
        let normal, left =
          match normal with Some start -> run start branch | None -> (None, [])
        in
        let pending =
          List.concat_map
            (fun (waiting : leaving) ->
              match run waiting.at branch with
              | Some ended, _ -> [ { waiting with at = ended } ]
              | None, stopped ->
                  (* The branch left too, so either exit may be the one
                     taken, with what the branch did before it left. *)
                  List.map (fun (stop : leaving) -> { waiting with at = stop.at }) stopped @ stopped)
            pending
        in
        (normal, pending @ left))
      (Some frame, []) branches
  in
  let passed_on =
    List.filter_map
      (fun (left : leaving) ->
        if not (from_here left) then Some left
        else
          match List.tl left.tasks with
          | _ :: _ as outer_tasks -> Some { left with tasks = outer_tasks }
          | [] -> (
              match left.exit with
              | Returning value ->
                  context.returns <- (left.at, value) :: context.returns;
                  None
              | Breaking -> (
                  match left.at.loop with
                  | Some exits ->
                      exits.breaks <- left.at :: exits.breaks;
                      None
                  | None -> unsupported (span_of frame.source node.origin) "`break` outside a loop")
              | Continuing -> (
                  match left.at.loop with
                  | Some exits ->
                      exits.continues <- left.at :: exits.continues;
                      None
                  | None ->
                      unsupported (span_of frame.source node.origin) "`continue` outside a loop")))
      pending
  in
  context.leaving <- outer @ passed_on;
  normal

(* A [yield] in a lending or yielding method's own body: the part meets
   the clauses about each part; a [mut] part comes back as the caller left
   it, which is any value of its type; and a yielding method may end here,
   if a loop stops it, so its other clauses and [self]'s invariant hold. *)
and handing_out context frame (node : statement) (mode : T.mode) (part : operand) =
  let span = span_of frame.source node.origin in
  match (context.hands_out, context.handing, frame.handed_out) with
  | Some (part_type, kind), Some (each, at_end), Some before ->
      let frame, handed = operand_value context frame part in
      let show clauses ~at ~result ~yielded ~finished ~when_ =
        List.iter
          (fun (clause : expression) ->
            let _, term =
              clause_value context { at with result; yielded = Some yielded; finished } clause
            in
            oblige context at Ensures (span_of at.source clause.origin)
              (Printf.sprintf "`%s` may not hold %s." (quote at.source clause.origin) when_)
              term)
          clauses
      in
      show each ~at:frame ~result:(Some handed) ~yielded:before ~finished:None
        ~when_:"for the part handed out here";
      check_valid context frame span part_type handed ~deep:true
        ~when_:"for the part handed out here";
      (* What the caller leaves in a part lent [mut] is stored back in each
         place it lends. *)
      let frame, part_after =
        if mode = T.Mut && Core_walk.lent_places part <> [] then (
          let part_after = arrive context frame "lent" part_type in
          if kind = `Lends then
            context.lent_back <- (part_type, handed, part_after) :: context.lent_back;
          (written_back context frame part part_type part_after, part_after))
        else (frame, handed)
      in
      let after = appended context frame part_type before part_after in
      let frame = { frame with handed_out = Some after } in
      if kind = `Yields then begin
        show at_end ~at:frame ~result:None ~yielded:after ~finished:(Some (L.Boolean false))
          ~when_:"at this `yield`, where a loop may stop the method";
        match (frame.self, frame.self_type) with
        | Some self, Some self_type ->
            check_valid context frame span self_type self ~deep:true
              ~when_:"for `self` at this `yield`, where a loop may stop the method"
        | _ -> ()
      end;
      Some frame
  | _ -> unsupported span "`yield` outside a lending or yielding method's body"

(* The frame after a [mut] lend of [part] ends with the value [after]: a
   lent place has its part of [after], and a field built from a value is
   discarded. A variant's field is its part only where [after] is still
   that variant, and is otherwise a value nothing more is known about. *)
and written_back context frame (part : operand) ty after =
  match part with
  | Place place -> store context frame place after
  | Value { kind = Construct { variant; fields }; _ } -> (
      match constructors context ty with
      | Some shape ->
          let shaped = Option.value (List.assoc_opt variant shape) ~default:[] in
          List.fold_left
            (fun frame (name, field) ->
              match (field, List.assoc_opt name shaped) with
              | Some field, Some field_type when Core_walk.lent_places field <> [] ->
                  let selected = field_of context frame ty variant name field_type after in
                  let value =
                    match variant with
                    | None -> selected
                    | Some _ ->
                        L.ite
                          (L.Apply (L.tester (constructor_name ty variant), [ after ]))
                          selected
                          (arrive context frame "lent" field_type)
                  in
                  written_back context frame field field_type value
              | _ -> frame)
            frame fields
      | None -> raise (Foreign_unsupported (Printf.sprintf "the fields of `%s`" (T.show ty))))
  | Value _ -> frame

(* A storage whose element at [index] is [part], and which is otherwise the
   one it was. *)
and storage_updated context frame element storage index part =
  let storage_type =
    T.Named { path = Intrinsic.builtin_path Storage; arguments = [ T.Type element ] }
  in
  let updated = arrive context frame "changed" storage_type in
  replaced context frame element
    ~before:(buffer_model context Storage element storage)
    ~after:(buffer_model context Storage element updated)
    index part;
  assume context frame
    (L.equal (buffer_capacity context element updated) (buffer_capacity context element storage));
  updated

(* An array whose element at [index] is [part], and which is otherwise the
   one it was. *)
and array_updated context frame (array_type : T.ty) array index part =
  match array_type with
  | Named { arguments = T.Type element :: _; _ } ->
      let updated = arrive context frame "changed" array_type in
      replaced context frame element
        ~before:(array_model context frame array_type array)
        ~after:(array_model context frame array_type updated)
        index part;
      updated
  | _ -> raise (Foreign_unsupported (Printf.sprintf "the elements of `%s`" (T.show array_type)))

(* The owner of a slice lent to change, after the change: as long as it
   was, and the same outside the slice's run. *)
and sliced_owner_changed context frame (base : place) ~start ~stop =
  let owner_type = place_type context frame base in
  let element =
    match owner_type with
    | Named { arguments = T.Type element :: _; _ } -> element
    | _ -> raise (Foreign_unsupported (Printf.sprintf "a slice of `%s`" (T.show owner_type)))
  in
  let frame, owner = place_value context frame base in
  let changed = arrive context frame "changed" owner_type in
  match
    (model_of context owner_type owner ~element, model_of context owner_type changed ~element)
  with
  | Some before, Some after ->
      run_replaced context frame element ~before ~after ~start ~stop ~run:None;
      assume_valid context frame owner_type changed;
      store context frame base changed
  | _ -> raise (Foreign_unsupported (Printf.sprintf "a slice of `%s`" (T.show owner_type)))

(* That one sequence is another as long, the same outside the run from
   [start] to before [stop], and, where [run] is given, [run]'s elements in
   that run. *)
and run_replaced context frame element ~before ~after ~start ~stop ~run =
  let length sequence = sequence_length context element sequence in
  let at sequence index =
    match sequence_at context element sequence index with
    | Some term -> term
    | None -> raise (Foreign_unsupported "the elements of a sequence")
  in
  context.fresh <- context.fresh + 1;
  let k = Printf.sprintf "index.%d" context.fresh in
  let index = L.Symbol k in
  let inside =
    match run with
    | Some run -> L.equal (at after index) (at run (L.Apply ("-", [ index; start ])))
    | None -> L.Boolean true
  in
  assume context frame (L.equal (length after) (length before));
  assume context frame
    (L.Forall
       ( [ (k, L.Int) ],
         L.(
           Apply ("<=", [ int 0; index ])
           &&& Apply ("<", [ index; length before ])
           ==> ite
                 (Apply ("<=", [ start; index ]) &&& Apply ("<", [ index; stop ]))
                 inside
                 (equal (at after index) (at before index))) ))

(* That one sequence is another with the element at [index] replaced by
   [part]. *)
and replaced context frame element ~before ~after index part =
  let length sequence = sequence_length context element sequence in
  let at sequence index =
    match sequence_at context element sequence index with
    | Some term -> term
    | None -> raise (Foreign_unsupported "the elements of a sequence")
  in
  context.fresh <- context.fresh + 1;
  let k = Printf.sprintf "index.%d" context.fresh in
  assume context frame
    (L.conjunction [ L.equal (length after) (length before); L.equal (at after index) part ]);
  assume context frame
    (L.Forall
       ( [ (k, L.Int) ],
         L.(
           Apply ("<=", [ int 0; Symbol k ])
           &&& Apply ("<", [ Symbol k; length before ])
           &&& not_ (equal (Symbol k) index)
           ==> equal (at after (Symbol k)) (at before (Symbol k))) ))

(* The local or [self] a place is part of, which takes a fresh value when
   a part of it changes in a way the prover does not follow. *)
and havoc_root context frame (place : place) =
  match root_of place with
  | Some Self -> (
      match frame.self_type with
      | Some ty -> { frame with self = Some (arrive context frame "changed" ty) }
      | None -> raise (Foreign_unsupported "changing `self` outside a method"))
  | Some local -> (
      match local_type context frame local with
      | Some ty ->
          { frame with locals = Locals.add local (arrive context frame "changed" ty) frame.locals }
      | None -> raise (Foreign_unsupported "changing this place"))
  | None -> raise (Foreign_unsupported "changing this place")

(* Stores a value into a place: a local, [self], a field of a place, which
   rebuilds the value it is in, or a part lent to change, which goes back
   where it came from: into its storage, for [storage_at_mut], or through
   the lending method's contract, which says how its receiver takes the
   part back. *)
and store context frame (place : place) new_value =
  match place with
  | Local { local = Self; _ } -> { frame with self = Some new_value }
  | Local { local; _ } -> { frame with locals = Locals.add local new_value frame.locals }
  | Constant _ -> raise (Foreign_unsupported "assigning to a constant")
  | Field _ when lent_root place -> store_lent context frame place (fun _ -> new_value)
  | Field { base; field; _ } -> (
      let base_type = place_type context frame base in
      match constructors context base_type with
      | Some [ (None, fields) ] ->
          let frame, base_value = place_value context frame base in
          let rebuilt =
            L.Apply
              ( constructor_name base_type None,
                List.map
                  (fun (name_, _) ->
                    if name_ = field then new_value
                    else selected context base_type None name_ base_value)
                  fields )
          in
          store context frame base rebuilt
      | _ ->
          raise
            (Foreign_unsupported (Printf.sprintf "assigning to a field of `%s`" (T.show base_type)))
      )
  | Lent
      {
        kind =
          Call
            {
              callee =
                Intrinsic { operation = Storage_at_mut; type_arguments = T.Type element :: _ };
              arguments = [ Passed { value = Place storage; _ }; Passed { value = index; _ } ];
              _;
            };
        _;
      } ->
      let element = substituted context frame element in
      let _, index = operand_value context { frame with checking = false } index in
      let frame, buffer = place_value context frame storage in
      store context frame storage (storage_updated context frame element buffer index new_value)
  | Lent
      {
        kind =
          Call
            {
              callee = Intrinsic { operation = Array_at_mut; _ };
              arguments = [ Passed { value = Place array; _ }; Passed { value = index; _ } ];
              _;
            };
        _;
      } ->
      let _, index = operand_value context { frame with checking = false } index in
      let array_type = place_type context frame array in
      let frame, before = place_value context frame array in
      store context frame array (array_updated context frame array_type before index new_value)
  | Lent
      {
        kind =
          Call
            {
              callee = Intrinsic { operation = View_at_mut; type_arguments = T.Type element :: _ };
              arguments = [ Passed { value = Place owner; _ }; Passed { value = index; _ } ];
              _;
            };
        _;
      } ->
      let element = substituted context frame element in
      let _, index = operand_value context { frame with checking = false } index in
      let frame, before = place_value context frame owner in
      let updated = arrive context frame "changed" (place_type context frame owner) in
      replaced context frame element
        ~before:(buffer_model context View element before)
        ~after:(buffer_model context View element updated)
        index new_value;
      store context frame owner updated
  | Lent { kind = Call { lends = Some T.Mut; _ }; _ } ->
      store_lent context frame place (fun _ -> new_value)
  | Lent _ | Temporary _ -> raise (Foreign_unsupported "assigning to this place")

(* Whether a place is a part, through fields, of what a call lends to be
   changed. *)
and lent_root (place : place) =
  match place with
  | Lent { kind = Call { lends = Some T.Mut; callee; _ }; _ } -> (
      match callee with
      | Intrinsic { operation = Storage_at_mut | Array_at_mut | View_at_mut; _ } -> false
      | _ -> true)
  | Field { base; _ } -> lent_root base
  | _ -> false

(* Stores into a part of what a call lends to be changed: the call is made
   once, and what the caller leaves in the part it lends is [leave] of that
   part, so a field's new value is built into the part as lent. *)
and store_lent context frame (place : place) leave =
  match place with
  | Lent ({ kind = Call call_; _ } as node) -> (
      match resolved_call ~lent_final:leave context frame node call_ with
      | Some (after, _) -> after
      | None -> havoc_root context frame place)
  | Field { base; field; _ } -> (
      let base_type = place_type context frame base in
      match constructors context base_type with
      | Some [ (None, fields) ] ->
          store_lent context frame base (fun base_value ->
              L.Apply
                ( constructor_name base_type None,
                  List.map
                    (fun (name_, _) ->
                      let current = selected context base_type None name_ base_value in
                      if name_ = field then leave current else current)
                    fields ))
      | _ ->
          raise
            (Foreign_unsupported (Printf.sprintf "assigning to a field of `%s`" (T.show base_type)))
      )
  | _ -> store context frame place (leave (snd (place_value context frame place)))

(* What a loop's body may change, which is havocked at its head: the local
   or [self] that each place it assigns to, lends to change, or pulls is
   part of. *)
and changed_places ?(condition : expression option) frame (body : block) : changed =
  let locals = ref [] and self = ref false in
  let note (place : place) =
    match root_of place with
    | Some Self -> self := true
    | Some local -> locals := local :: !locals
    | None -> ()
  in
  let rec visit =
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : expression) ->
          (match node.kind with
          | Call { arguments; _ } ->
              List.iter
                (function
                  | Passed { mode = T.Mut; value = Place place } -> note place
                  | Passed { mode = T.Mut; value = Value { kind = Slice { base; _ }; _ } } ->
                      note base
                  | Passed _ | Default -> ())
                arguments
          | Cursor_next place -> note place
          | Match { scrutinees; arms; _ } ->
              List.iteri
                (fun index scrutinee ->
                  match scrutinee with
                  | Place place
                    when List.exists
                           (fun (arm_ : arm) ->
                             match List.nth_opt arm_.patterns index with
                             | Some pattern -> lends_mut pattern
                             | None -> false)
                           arms ->
                      note place
                  | Place _ | Value _ -> ())
                scrutinees
          | _ -> ());
          Core_walk.expression_children visit node);
      statement =
        (fun (node : statement) ->
          (match node.kind with
          | Assign { target; _ } | Compound_assign { target; _ } -> note target
          | For { iteration = Cursor { cursor = place; _ }; _ } -> note place
          | Yield { mode = T.Mut; part } -> List.iter note (Core_walk.lent_places part)
          | _ -> ());
          Core_walk.statement_children visit node);
      pattern = (fun node -> Core_walk.pattern_children visit node);
    }
  in
  Option.iter (Core_walk.expression visit) condition;
  Core_walk.block visit body;
  {
    changed_locals =
      List.sort_uniq compare
        (List.filter (fun local -> local <> Self && Locals.mem local frame.locals) !locals);
    changes_self = !self && frame.self <> None;
  }

and havoc context frame (changed : changed) =
  let frame =
    List.fold_left
      (fun frame local ->
        let ty = match local_type context frame local with Some ty -> ty | None -> T.Integer in
        { frame with locals = Locals.add local (arrive context frame "loop" ty) frame.locals })
      frame changed.changed_locals
  in
  match (changed.changes_self, frame.self_type) with
  | true, Some ty -> { frame with self = Some (arrive context frame "loop" ty) }
  | _ -> frame

(* Validity is an invariant of every loop: each value the loop changes
   that is valid on entry is valid at the head of each iteration, so each
   iteration must keep it valid. A value that is not valid on entry, as
   [self] may not be in a private method that updates it, is not held to
   it. *)
and kept_validity context (entry : frame) (changed : changed) =
  let kept name ty before read =
    match validity context entry ~assuming:false ~deep:true ty before with
    | L.Boolean true -> None
    | valid -> Some (name, ty, valid, read)
  in
  List.filter_map
    (fun local ->
      match (local_type context entry local, Locals.find_opt local entry.locals) with
      | Some ty, Some before ->
          kept
            (Option.value (Hashtbl.find_opt context.local_names local) ~default:"a local")
            ty before
            (fun (at : frame) -> Locals.find_opt local at.locals)
      | _ -> None)
    changed.changed_locals
  @
  match (changed.changes_self, entry.self, entry.self_type) with
  | true, Some before, Some ty ->
      Option.to_list (kept "self" ty before (fun (at : frame) -> at.self))
  | _ -> []

and assume_kept_validity context head kept =
  List.iter
    (fun (_, ty, valid_on_entry, read) ->
      match read head with
      | Some term ->
          assume context head
            (L.( ==> ) valid_on_entry (validity context head ~assuming:true ~deep:true ty term))
      | None -> ())
    kept

and check_kept_validity context end_ span kept =
  List.iter
    (fun (name, ty, valid_on_entry, read) ->
      match read end_ with
      | Some term ->
          oblige context end_ Invariant span
            (Printf.sprintf "The invariant of `%s` may not hold for `%s` after an iteration."
               (T.show ty) name)
            (L.( ==> ) valid_on_entry (validity context end_ ~assuming:false ~deep:true ty term))
      | None -> ())
    kept

and invariants (clauses : loop_clause list) =
  List.filter_map (function Invariant value -> Some value | _ -> None) clauses

and check_invariants context frame clauses ~when_ =
  List.iter
    (fun (invariant : expression) ->
      let _, term = clause_value context frame invariant in
      oblige context frame Invariant (at frame invariant)
        (Printf.sprintf "The loop invariant `%s` may not hold %s."
           (quote frame.source invariant.origin)
           when_)
        term)
    (invariants clauses)

and assume_invariants context frame clauses =
  List.iter
    (fun (invariant : expression) ->
      let _, term = clause_value context { frame with checking = false } invariant in
      assume context frame term)
    (invariants clauses)

and measures_of clauses =
  List.find_map (function Decreases measures -> Some measures | _ -> None) clauses

and while_ context frame (node : statement) condition clauses body =
  let span = span_of frame.source node.origin in
  check_invariants context frame clauses ~when_:"on entry to the loop";
  (* The condition runs at the head of each iteration, so what it changes
     and what it spends are the iteration's. *)
  let changed = changed_places ~condition frame body in
  let costs = loop_costs context frame clauses ~held:(held_by context frame changed) in
  loop_entry context frame costs;
  let mark = context.fresh and facts_mark = List.length context.facts in
  let kept = kept_validity context frame changed in
  let head = havoc context frame changed in
  assume_kept_validity context head kept;
  let head =
    if contains_yield body then { head with handed_out = havoc_parts context head } else head
  in
  let iterations = iterations_so_far context head costs in
  let head = loop_head context head costs ~iterations in
  assume_invariants context head clauses;
  let top = head in
  let head, test = value context head condition in
  let exits = { breaks = []; continues = [] } in
  let inside = { (restrict head test) with loop = Some exits } in
  let inside = spend context inside one_step in
  let measures =
    match (measures_of clauses, condition.kind) with
    | Some measures, _ -> `Written measures
    | ( None,
        Compare
          { comparison = (Less | Less_equal | Greater | Greater_equal) as compared; left; right } )
    (* A guessed measure is read again at the end of each iteration, so its
       operands must be functional: evaluating one again must not repeat
       what it changes. *)
      when functional_expression left && functional_expression right ->
        `Guessed (left, right, compared)
    | None, _ -> `None
  in
  let measure_terms (at : frame) =
    match measures with
    | `Written measures ->
        Some
          (List.map
             (fun measure -> snd (value context { at with checking = false } measure))
             measures)
    | `Guessed (left, right, compared) -> (
        let _, l = value context { at with checking = false } left in
        let _, r = value context { at with checking = false } right in
        match compared with
        | Less -> Some [ L.Apply ("-", [ r; l ]) ]
        | Less_equal -> Some [ L.Apply ("+", [ L.Apply ("-", [ r; l ]); L.int 1 ]) ]
        | Greater -> Some [ L.Apply ("-", [ l; r ]) ]
        | _ -> Some [ L.Apply ("+", [ L.Apply ("-", [ l; r ]); L.int 1 ]) ])
    | `None -> None
  in
  let start_measures = if context.terminates then measure_terms inside else None in
  if context.terminates && start_measures = None then
    oblige context inside Termination span "This loop may not end: give it a `decreases` clause."
      (L.Boolean false);
  (* With one measure, which every iteration shows to start at or above
     zero and to decrease, the loop runs at most one more time than the
     measure on entry. A ghost [last] is the measure at the start of the
     latest iteration. *)
  let most =
    match (start_measures, measure_terms frame, iterations) with
    | Some [ at_head ], Some [ on_entry ], Some iterations ->
        let last = fresh context head "last" L.Int in
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
  loop_iterations context node top costs ~mark
    ~facts:(facts_since context facts_mark @ [ inside.condition ])
    ~ends ~breaks:exits.breaks;
  List.iter
    (fun (end_ : frame) ->
      let end_ = { end_ with loop = frame.loop } in
      check_invariants context end_ clauses ~when_:"after an iteration";
      check_kept_validity context end_ span kept;
      match (start_measures, measure_terms end_) with
      | Some before, Some after ->
          oblige context end_ Termination span "This loop's measure may not decrease."
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
      { joined with locals = Locals.filter (fun id _ -> Locals.mem id frame.locals) joined.locals })

(* A ghost count of a loop's iterations so far, when the loop counts a
   cost by them. *)
and iterations_so_far context head costs =
  if
    List.exists
      (fun (cost : loop_cost) ->
        match cost.rule with Per_iteration _ -> true | Clause_bound _ -> false)
      costs
  then begin
    let iterations = fresh context head "iterations" L.Int in
    assume context head (L.Apply ("<=", [ L.int 0; iterations ]));
    Some iterations
  end
  else None

and one_step (counter : Costs.counter) =
  match counter.resource with Time -> L.int 1 | _ -> Costs.zero

and for_ context frame (node : statement) (pattern : pattern) (iteration : iteration) clauses body =
  let span = span_of frame.source node.origin in
  match iteration with
  | Integer_range { start; stop; inclusive } ->
      let element = substituted context frame pattern.type_ in
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
      let kept = kept_validity context frame changed in
      let head = havoc context frame changed in
      assume_kept_validity context head kept;
      let head =
        if contains_yield body then { head with handed_out = havoc_parts context head } else head
      in
      (* The [n]th iteration, from 0, has the index [low + n]. *)
      let count =
        Costs.normalize
          (if inclusive then Costs.plus (Costs.minus high low) (L.int 1) else Costs.minus high low)
      in
      let iterations = fresh context head "iterations" L.Int in
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
       | Some found ->
           assume context head
             (L.Forall
                ( [ (position, L.Int) ],
                  L.(
                    Apply ("<=", [ int 0; Symbol position ])
                    &&& Apply ("<", [ Symbol position; iterations ])
                    ==> equal found (Apply ("+", [ low; Symbol position ]))) ))
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
      let _, inside = pattern_match context inside pattern index element in
      let finished = block_value context inside body in
      let ends =
        (match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues
      in
      let with_through (f : frame) = { f with loop = frame.loop; yielded = Some through } in
      loop_iterations context node head costs ~mark
        ~facts:(facts_since context facts_mark @ [ inside.condition ])
        ~ends:(List.map with_through ends)
        ~breaks:(List.map with_through exits.breaks);
      List.iter
        (fun (end_ : frame) ->
          check_invariants context (with_through end_) clauses ~when_:"after an iteration";
          check_kept_validity context end_ span kept)
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
          {
            joined with
            locals = Locals.filter (fun id _ -> Locals.mem id frame.locals) joined.locals;
          })
  | Yielding_call ({ kind = Call call_; _ } as driven) ->
      each_loop context frame node pattern driven call_ clauses body
  | Yielding_call _ -> unsupported span "this `for` loop"
  | Cursor { cursor; next = None } -> (
      match place_type context frame cursor with
      | T.Cursor { method_; _ } as cursor_type ->
          pulled_loop context frame node pattern cursor clauses body ~cursor_type ~method_
      | _ -> unsupported span "this `for` loop")
  | Cursor { cursor; next = Some next } ->
      own_cursor_loop context frame node pattern cursor next clauses body
        ~cursor_type:(place_type context frame cursor)

(* A [for] loop over a yielding method: each element is a fresh value
   that meets the method's clauses for each part, and the loop ends when
   the method has a [time] clause. *)
and each_loop context frame (node : statement) (pattern : pattern) (driven : expression)
    (call_ : call) clauses body =
  let span = span_of frame.source node.origin in
  let frame, values = call_arguments context frame driven call_ ~facts_for:(fun _ _ _ -> []) in
  let arguments = List.map (fun (passed : passed) -> (passed.position, passed.term)) values in
  let path, terminates, contract, substitution =
    match call_.callee with
    | Function { path; type_arguments } -> (
        let substitution =
          match Interface.Impls.signature context.database path with
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
        match Interface.Impls.signature context.database path with
        | Some signature ->
            ( Some path,
              signature.terminates,
              function_contract ~reader:(Path.package context.current) context.database path,
              substitution )
        | None -> (Some path, false, None, substitution))
    | Trait_method { trait; name; receiver; evidence; self_type; _ } ->
        (* A trait's yielding method, read by its [impl]'s contract where the
           call reaches one and otherwise by the trait's, with [Self] the
           type it is called on. *)
        let self_type = substituted context frame self_type in
        let trait =
          {
            trait with
            trait_arguments =
              List.map (T.substitute_argument frame.substitution) trait.trait_arguments;
          }
        in
        let evidence : evidence =
          match evidence with
          | Bound -> (
              match concrete_impl context trait self_type with
              | Some (impl, arguments) -> Impl { impl; arguments }
              | None -> evidence)
          | _ -> evidence
        in
        let path =
          match evidence with
          | Impl { impl; _ } -> Path.Method { owner = impl; name; receiver }
          | Bound | Dynamic -> Path.Method { owner = trait.trait; name; receiver }
        in
        ( Some path,
          signature_terminates context path,
          method_contract ~reader:(Path.package context.current) context.database trait name
            receiver evidence,
          [ ({ T.owner = trait.trait; name = "Self" }, T.Type self_type) ] )
    | _ -> (None, false, None, [])
  in
  if context.terminates && not terminates then
    oblige context frame Termination span
      "This loop may not end: the method it loops over has no `time` clause." (L.Boolean false);
  let element_type = substituted context frame pattern.type_ in
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
            if mentions_result clause = each then
              assume context at (snd (clause_value context inside clause)))
          own.ensures
    | _ -> ()
  in
  (* The method's own work, by its cost clauses, once for the loop. *)
  let frame =
    match (contract, path) with
    | Some contract, Some path ->
        spend context frame
          (callee_amount context frame ~path ~parts:contract.parts
             ~bound_frame:(fun part -> method_frame frame part)
             ~uses:call_.uses ~values ~change:None)
    | _ -> spend context frame (unknown_amount context frame)
  in
  (* A loop over a collection [mut] changes the collection too. *)
  let changed =
    let in_body = changed_places frame body in
    List.fold_left
      (fun (changed : changed) (passed : passed) ->
        match (passed.mode, passed.operand) with
        | T.Mut, Some (Place place) -> (
            match root_of place with
            | Some Self -> { changed with changes_self = frame.self <> None }
            | Some local ->
                {
                  changed with
                  changed_locals = List.sort_uniq compare (local :: changed.changed_locals);
                }
            | None -> unsupported span "looping over this place `mut`")
        | _ -> changed)
      in_body values
  in
  receiving_loop context frame node pattern clauses body ~element_type ~changed
    ~start:(fun head -> some_parts context head element_type)
    ~receive:(fun head before ->
      (* Each time round, the method either hands out another part or ends. *)
      let another = fresh context head "another" L.Bool in
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

(* What a loop changes, with the local or [self] its cursor is in, which
   each pull changes. *)
and with_cursor frame (node : statement) (changed : changed) (cursor : place) =
  match root_of cursor with
  | Some Self -> { changed with changes_self = frame.self <> None }
  | Some local ->
      { changed with changed_locals = List.sort_uniq compare (local :: changed.changed_locals) }
  | None ->
      unsupported
        (span_of frame.source node.origin)
        "a loop over a cursor that is not in a local or a field of one"

(* A [for] loop over a cursor pulls it until it ends, putting the cursor
   that is left back where it was. Its [yielded] is everything the cursor
   has handed out, before the loop too. *)
and pulled_loop context frame (node : statement) pattern (cursor_place : place) clauses body
    ~cursor_type ~method_ =
  let span = span_of frame.source node.origin in
  let frame, cursor = place_value context frame cursor_place in
  let made =
    match List.assoc_opt cursor context.cursors with
    | Some made -> made
    | None -> unsupported span "a loop over a cursor whose method the prover does not know"
  in
  if context.terminates && not (signature_terminates context method_) then
    oblige context frame Termination span
      "This loop may not end: the method its cursor comes from has no `time` clause."
      (L.Boolean false);
  let changed = with_cursor frame node (changed_places frame body) cursor_place in
  let at_head = ref cursor in
  receiving_loop context frame node pattern clauses body ~element_type:made.element ~changed
    ~start:(fun head ->
      let _, cursor = place_value context { head with checking = false } cursor_place in
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
        advance = (fun (frame : frame) -> store context frame cursor_place later);
      })

(* A [for] loop over a value of a type's own [Cursor]: each iteration
   calls its [next] by the [impl]'s contract, and the loop ends at [None].
   Such a cursor promises no end, so in a function that must end, the loop
   needs a [decreases] clause, which each iteration decreases. *)
and own_cursor_loop context frame (node : statement) (pattern : pattern) (cursor_place : place)
    (next : callee) clauses body ~cursor_type =
  let span = span_of frame.source node.origin in
  let frame, _ = place_value context frame cursor_place in
  let element_type = substituted context frame pattern.type_ in
  let trait, evidence =
    match next with
    | Trait_method { trait; evidence = Impl _ as evidence; _ } -> (trait, evidence)
    | _ ->
        unsupported span "a loop over `%s`, whose `Cursor` the prover cannot find"
          (T.show cursor_type)
  in
  let impl = match evidence with Impl { impl; _ } -> impl | _ -> assert false in
  let contract =
    match
      method_contract ~reader:(Path.package context.current) context.database trait "next" Mut
        evidence
    with
    | Some contract -> contract
    | None ->
        unsupported span "a loop over `%s`, whose `next` the prover cannot read"
          (T.show cursor_type)
  in
  let path = Path.Method { owner = impl; name = "next"; receiver = Mut } in
  let option_type = T.Named { path = option_path; arguments = [ T.Type element_type ] } in
  let call_ : call =
    {
      callee = next;
      arguments = [ Passed { mode = T.Mut; value = Place cursor_place } ];
      lends = None;
      uses = [];
    }
  in
  let pulling : expression =
    { id = node.id; origin = node.origin; type_ = option_type; kind = Call call_ }
  in
  let measures = measures_of clauses in
  if context.terminates && not (signature_terminates context path) then
    oblige context frame Termination span
      (Printf.sprintf "This loop may not end: `%s`'s `next` has no `time` clause."
         (T.show cursor_type))
      (L.Boolean false);
  if context.terminates && measures = None then
    oblige context frame Termination span
      "This loop may not end: a cursor of a type's own promises no end, so give the loop a \
       `decreases` clause."
      (L.Boolean false);
  let measured (at : frame) =
    Option.map
      (List.map (fun measure -> snd (value context { at with checking = false } measure)))
      measures
  in
  let changed = with_cursor frame node (changed_places frame body) cursor_place in
  receiving_loop context frame node pattern clauses body ~element_type ~changed
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
                    oblige context end_ Termination span "This loop's measure may not decrease."
                      (smaller before after)
                | None -> ())
              ends
        | None -> ())
    ~start:(fun head -> some_parts context head element_type)
    ~receive:(fun head before ->
      let _, cursor = place_value context { head with checking = false } cursor_place in
      let havoc_mut (frame : frame) =
        store context frame cursor_place (arrive context frame "changed" cursor_type)
      in
      let after, pulled =
        contract_call ~lent_final:None context head pulling call_ path contract
          [
            {
              position = 0;
              mode = T.Mut;
              operand = Some (Place cursor_place);
              type_ = cursor_type;
              term = cursor;
              run = None;
            };
          ]
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
            let _, now = place_value context { after with checking = false } cursor_place in
            { (store context frame cursor_place now) with spent = after.spent });
      })

(* A [for] loop that receives parts one at a time: from a yielding method
   it calls, or from a cursor it pulls. [start] is what was received before
   an iteration, at the head, and [receive] is what an iteration receives,
   having assumed what the method says of it. *)
and receiving_loop ?(each_iteration = fun ~head:_ ~ends:_ -> ()) context frame (node : statement)
    (pattern : pattern) clauses body ~element_type ~changed ~start ~receive =
  let entry = { frame with yielded = Some (empty_parts context frame element_type) } in
  check_invariants context entry clauses ~when_:"on entry to the loop";
  let costs = loop_costs context frame clauses ~held:(held_by context frame changed) in
  loop_entry context entry costs;
  let mark = context.fresh and facts_mark = List.length context.facts in
  let kept = kept_validity context frame changed in
  let head = havoc context frame changed in
  assume_kept_validity context head kept;
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
  loop_iterations context node head costs ~mark
    ~facts:(facts_since context facts_mark @ [ inside.condition ])
    ~ends:(List.map with_through ends)
    ~breaks:(List.map with_through exits.breaks);
  List.iter
    (fun (end_ : frame) ->
      check_invariants context (with_through end_) clauses ~when_:"after an iteration";
      check_kept_validity context end_ (span_of frame.source node.origin) kept)
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
      { joined with locals = Locals.filter (fun id _ -> Locals.mem id frame.locals) joined.locals })

(* Whether a loop's body hands out parts of the method it is in. *)
and contains_yield (body : block) =
  let found = ref false in
  let rec visit =
    {
      Core_walk.ignore_all with
      expression = (fun node -> Core_walk.expression_children visit node);
      statement =
        (fun (node : statement) ->
          (match node.kind with Yield _ -> found := true | _ -> ());
          Core_walk.statement_children visit node);
      pattern = (fun node -> Core_walk.pattern_children visit node);
    }
  in
  Core_walk.block visit body;
  !found

and havoc_parts context frame =
  match context.hands_out with
  | Some (part, _) -> Some (some_parts context frame part)
  | None -> frame.handed_out

(* Definitions *)

let new_context database ~home ~current ~terminates ~measures =
  {
    home;
    laws_assumed = [];
    database;
    current;
    terminates;
    measures;
    declarations = [];
    declared = Hashtbl.create 64;
    facts = [];
    unfolded = Hashtbl.create 64;
    obligations = [];
    fresh = 0;
    values = [];
    local_names = Hashtbl.create 16;
    returns = [];
    leaving = [];
    lent_back = [];
    instantiating = [];
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
    models = Hashtbl.create 16;
    holds_potential = Hashtbl.create 16;
    buffers = Hashtbl.create 16;
    equalities = [];
    known_calls = [];
    hidden_bodies = [];
    cursors = [];
    proving = false;
    holes = [];
    unfinished = [];
    call_targets = [];
    passed_values = [];
    reading_callback = false;
    validating = [];
    ranking =
      terminates && measures = []
      && Call_graph.recursive database ~package:(Path.package current) current;
    disjoint =
      (match Query.demand database Ownership.ownership home with
      | Some ownership -> ownership.disjoint
      | None -> []);
    indexes = [];
  }

let outcome context = { obligations = List.rev context.obligations; holes = List.rev context.holes }

(* A frame at the start of a definition, before its parameters are bound. *)
let empty_frame source =
  {
    source;
    locals = Locals.empty;
    types = Locals.empty;
    old_locals = Locals.empty;
    self = None;
    old_self = None;
    result = None;
    condition = L.Boolean true;
    checking = true;
    bound = [];
    binders = [];
    loop = None;
    substitution = [];
    self_type = None;
    yielded = None;
    finished = None;
    handed_out = None;
    updating = None;
    spent = [];
  }

(* The span of the whole definition, for an obligation about how it
   returns. *)
let definition_span (source : source) =
  let spans = Lazy.force source.spans in
  match Array.length spans with 0 -> Span.make 0 0 | count -> spans.(count - 1)

(* A cost clause, as a promise about one counter, shown at each way its
   definition returns. A trait's clause, which an [impl]'s method keeps, is
   read in the trait's form. *)
type promise = {
  counter : Costs.counter;
  clause : Core.cost;
  constants : Costs.constants option;
  written_in : source;
  inherited : bool;
}

let promises context (source : source) locals (costs : Core.cost list) ~inherited =
  List.filter_map
    (fun (cost : Core.cost) ->
      match cost with
      | { resource = Time; bound = Finite; _ } -> None
      | _ -> (
          match resource_of cost ~locals with
          | None -> unsupported (span_of source cost.origin) "this `calls` target"
          | Some resource ->
              let counter =
                { Costs.resource; counting = counting_of cost; amortized = cost.amortized }
              in
              let key = Costs.key counter in
              (match (cost.resource, resource) with
              | Calls (Function_parameter local), Calls (Through term) ->
                  context.call_targets <- (term, local) :: context.call_targets
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
              Some { counter; clause = cost; constants; written_in = source; inherited }))
    costs

(* What a method's inherited clauses come from, for messages: its trait,
   or its capability. *)
let promised_by database (source : source) =
  match source.key with
  | Some { path = Method { owner; _ }; _ }
    when Interface.Summary.kind_of database owner = Some Names.Capability ->
      "capability"
  | _ -> "trait"

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
    | Order_of g | At_most g | Exactly g -> snd (value context { at with checking = false } g)
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
       Printf.sprintf "This method may spend more than its %s's `%s` allows."
         (promised_by context.database promise.written_in)
         (quote promise.written_in promise.clause.origin)
     else
       Printf.sprintf "This may spend more than `%s` allows."
         (quote promise.written_in promise.clause.origin))
    goal

(* A function, method, or theorem: its parameters arrive, its
   preconditions are assumed, its body runs, and its postconditions and
   cost clauses are shown at each way it returns. [inherited] is, for an
   [impl]'s method, its trait's clauses, with the substitution they are
   read under and the body the trait provides, if any. *)
let function_ ?(proof = false) ?(updating_helper = false) ?inherited database (source : source)
    ~path =
  let parameters, contract, body =
    match source.core.definition with
    | Function { parameters; contract; body = Some body } -> (parameters, contract, body)
    | _ -> unsupported (definition_span source) "a function without a body"
  in
  let signature = Interface.Impls.signature database path in
  let terminates =
    proof
    || match signature with Some (signature : T.signature) -> signature.terminates | None -> false
  in
  let home = match source.key with Some key -> key | None -> invalid_arg "Translate.function_" in
  let context = new_context database ~home ~current:path ~terminates ~measures:contract.decreases in
  let returns_span = definition_span source in
  context.proving <- proof;
  context.parameters <- parameters;
  let output = match signature with Some { output = Returns ty; _ } -> Some ty | _ -> None in
  let start =
    List.fold_left
      (fun frame (parameter : Core.parameter) ->
        match parameter.local with
        | Self ->
            let self_type =
              match signature with
              | Some { receiver = Some (_, ty); _ } -> ty
              | _ -> unsupported returns_span "`self` without a type"
            in
            let self = arrive context frame "self" self_type in
            (* A step of an update may be given a value in the middle of
               one. *)
            if not updating_helper then assume_valid context frame self_type self;
            { frame with self = Some self; self_type = Some self_type }
        | local ->
            let ty = parameter.type_ in
            let term = arrive context frame ("parameter." ^ parameter.name) ty in
            (match term with
            | L.Symbol symbol -> context.values <- (symbol, parameter.name) :: context.values
            | _ -> ());
            assume_valid context frame ty term;
            bind frame local ty term)
      (empty_frame source) parameters
  in
  let start = { start with old_locals = start.locals; old_self = start.self } in
  (* A lending or yielding method hands out parts: its postconditions that
     mention [result] hold at each [yield], and its others where it ends. *)
  let start =
    match signature with
    | Some { output = (Yields (_, part) | Lends (_, part)) as output; _ } ->
        let kind = match output with Lends _ -> `Lends | _ -> `Yields in
        context.hands_out <- Some (part, kind);
        context.handing <-
          Some
            ( List.filter mentions_result contract.ensures,
              List.filter (fun clause -> not (mentions_result clause)) contract.ensures );
        { start with handed_out = Some (empty_parts context start part) }
    | _ -> start
  in
  (* Each parameter's value, [self] first, as a call's arguments are
     numbered. *)
  let values_of (at : frame) =
    List.filter_map
      (fun (parameter : Core.parameter) ->
        match parameter.local with Self -> at.self | local -> Locals.find_opt local at.locals)
      parameters
  in
  (* A capability's method takes no [self], but the method an [impl] of the
     capability writes does, so the [impl]'s [self] is left out when the
     two are paired. *)
  let paired terms =
    match (inherited, parameters, terms) with
    | Some ((part : part), _, _), { local = Self; _ } :: _, _ :: rest
      when not
             (List.exists
                (fun (parameter : Core.parameter) -> parameter.local = Self)
                part.parameters) ->
        rest
    | _ -> terms
  in
  let values_of (at : frame) = paired (values_of at) in
  let own_terms = values_of start in
  (* An [impl]'s method also keeps its trait's or its capability's contract:
     the precondition is what callers through a bound or the capability
     show, so it is assumed, and implies the method's own; the
     postcondition is what they assume, so it is shown. *)
  let trait_frame (at : frame) ~result =
    match inherited with
    | Some ((part : part), substitution, _) when List.length part.parameters = List.length own_terms
      ->
        let locals, types, self, old_locals =
          List.fold_left2
            (fun (locals, types, self, old_locals) (parameter : Core.parameter) (entry, exit_) ->
              match parameter.local with
              | Self -> (locals, types, Some (exit_, parameter.type_), old_locals)
              | local ->
                  ( Locals.add local exit_ locals,
                    Locals.add local parameter.type_ types,
                    self,
                    Locals.add local entry old_locals ))
            (Locals.empty, Locals.empty, None, Locals.empty)
            part.parameters
            (List.combine own_terms (values_of at))
        in
        Some
          ( part,
            {
              at with
              source = part.callee;
              locals;
              types;
              old_locals;
              self = Option.map fst self;
              old_self = start.self;
              self_type = Option.map (fun (_, ty) -> T.substitute substitution ty) self;
              result;
              checking = false;
              loop = None;
              updating = None;
              substitution;
            } )
    | _ -> None
  in
  let own_requires = List.map (fun (clause : condition) -> clause.value) contract.requires in
  (* The trait's precondition, on entry: what its postcondition and cost
     clauses are promised under. *)
  let trait_requires =
    match trait_frame start ~result:None with
    | Some (part, inside) ->
        L.conjunction
          (List.map (fun clause -> snd (clause_value context inside clause)) part.requires)
    | None -> L.Boolean true
  in
  (* Its cost clauses, and its trait's, each count from zero. *)
  let promised =
    promises context source start.locals contract.costs ~inherited:false
    @
    match trait_frame start ~result:None with
    | Some (part, inside) -> promises context part.callee inside.locals part.costs ~inherited:true
    | None -> []
  in
  context.counters <-
    distinct_counters
      (List.map (fun promise -> promise.counter) promised @ loop_counters start.locals body);
  let start =
    {
      start with
      spent = List.map (fun counter -> (Costs.key counter, Costs.zero)) context.counters;
    }
  in
  let start =
    match trait_frame start ~result:None with
    | Some (part, _)
    (* A tag's [from_template] may require more than its trait, since only
       a template calls it, where the tag is known; a call through a bound
       is an error, which keeps that sound. *)
      when not
             (match part.callee.key with
             | Some { path = Method { owner; _ }; _ } -> Path.equal owner template_trait
             | _ -> false) ->
        if own_requires = [] then begin
          assume context start trait_requires;
          start
        end
        else begin
          ignore
            (List.fold_left
               (fun frame (clause : expression) ->
                 let frame, term = clause_value context frame clause in
                 oblige context frame Requires (at frame clause)
                   (Printf.sprintf
                      "`%s` may not follow from the trait's precondition, which callers through \
                       the trait show, and an `impl`'s precondition must."
                      (quote source clause.origin))
                   term;
                 frame)
               (restrict start trait_requires) own_requires);
          List.fold_left
            (fun frame (clause : expression) ->
              let frame, term = clause_value context frame clause in
              assume context frame term;
              frame)
            start own_requires
        end
    | _ ->
        List.fold_left
          (fun frame (clause : expression) ->
            let frame, term = clause_value context frame clause in
            assume context frame term;
            frame)
          start own_requires
  in
  (* Each of its own cost bounds is well defined, read where it is
     checked: on entry, with any result. *)
  List.iter
    (fun (promise : promise) ->
      if not promise.inherited then
        match promise.clause.bound with
        | Order_of g | At_most g | Exactly g ->
            let result = Option.map (arrive context start "result") output in
            ignore (value context { start with result } g)
        | Finite -> ())
    promised;
  let finished = block_value context start body in
  let returns =
    (match finished with Some (frame, term) -> [ (frame, Some term) ] | None -> [])
    @ List.rev context.returns
  in
  let mut_parameters =
    List.filter
      (fun (parameter : Core.parameter) -> parameter.mode = T.Mut && parameter.local <> Self)
      parameters
  in
  let mut_self =
    List.exists
      (fun (parameter : Core.parameter) -> parameter.mode = T.Mut && parameter.local = Self)
      parameters
  in
  List.iter
    (fun ((frame : frame), returned) ->
      let frame = { frame with result = returned } in
      (* What other code sees again: the result, each [mut] parameter, and
         [mut self], unless this is a step of an update. *)
      (match (returned, output) with
      | Some term, Some output ->
          check_valid context frame returns_span output term ~deep:true
            ~when_:"for the value returned"
      | _ -> ());
      List.iter
        (fun (parameter : Core.parameter) ->
          match
            (Locals.find_opt parameter.local frame.locals, local_type context frame parameter.local)
          with
          | Some term, Some ty ->
              check_valid context frame returns_span ty term ~deep:true
                ~when_:(Printf.sprintf "for `%s` when the function returns" parameter.name)
          | _ -> ())
        mut_parameters;
      (match (mut_self, updating_helper, frame.self, frame.self_type) with
      | true, false, Some self, Some self_type ->
          check_valid context frame returns_span self_type self ~deep:true
            ~when_:"for `self` when the method returns"
      | _ -> ());
      (match (context.handing, frame.handed_out) with
      | Some (_, at_end), Some handed_out ->
          (* The postconditions about how a lending or yielding method ends,
             with everything it handed out, having run to its end. *)
          List.iter
            (fun (ensured : expression) ->
              let _, term =
                value context
                  { frame with yielded = Some handed_out; finished = Some (L.Boolean true) }
                  ensured
              in
              oblige context frame Ensures (at frame ensured)
                (Printf.sprintf "`%s` may not hold when the method ends."
                   (quote source ensured.origin))
                term)
            at_end
      | _ ->
          List.iter
            (fun (ensured : expression) ->
              let _, term = clause_value context frame ensured in
              oblige context frame Ensures (at frame ensured)
                (Printf.sprintf "`%s` may not hold when the function returns."
                   (quote source ensured.origin))
                term)
            contract.ensures);
      (* How much the potential of what the definition returns and changes
         grew, less what it was given to keep, for an amortized bound. *)
      let change () =
        let given =
          List.fold_left
            (fun total (parameter : Core.parameter) ->
              let entry, later, ty =
                match parameter.local with
                | Self -> (start.self, frame.self, frame.self_type)
                | local ->
                    ( Locals.find_opt local start.locals,
                      Locals.find_opt local frame.locals,
                      local_type context frame local )
              in
              match (parameter.mode, entry, ty) with
              | (T.Mut | T.Own), Some entry, Some ty ->
                  let kept =
                    match (parameter.mode, later) with
                    | T.Mut, Some later -> potential context frame ty later
                    | _ -> Costs.zero
                  in
                  Costs.plus total (Costs.minus kept (potential context frame ty entry))
              | _ -> total)
            Costs.zero parameters
        in
        (* What the caller does to a part lent to it [mut] is the caller's
           to pay for, so the part's own change in potential is not the
           method's. *)
        let given =
          List.fold_left
            (fun total (ty, handed, back) ->
              Costs.minus total
                (Costs.minus (potential context frame ty back) (potential context frame ty handed)))
            given context.lent_back
        in
        match (returned, output) with
        | Some term, Some output -> Costs.plus given (potential context frame output term)
        | _ -> given
      in
      let under_trait = restrict frame trait_requires in
      List.iter
        (fun promise ->
          if promise.inherited then
            match trait_frame frame ~result:returned with
            | Some (_, inside) ->
                keep_promise context under_trait promise
                  ~at:{ inside with locals = inside.old_locals; self = inside.old_self }
                  ~span:returns_span ~change
            | None -> ()
          else
            keep_promise context frame promise
              ~at:{ frame with locals = frame.old_locals; self = frame.old_self; result = returned }
              ~span:(span_of source promise.clause.origin)
              ~change)
        promised;
      match trait_frame frame ~result:returned with
      | Some (part, inside) ->
          List.iter
            (fun (clause : expression) ->
              let _, term = clause_value context inside clause in
              oblige context under_trait Ensures returns_span
                (Printf.sprintf "The %s's `%s` may not hold when this method returns."
                   (promised_by database part.callee)
                   (quote part.callee clause.origin))
                term)
            part.ensures;
          (* A method that replaces one its trait provides must return what
             the provided body returns, which is its definition. *)
          begin match (inherited, returned) with
          | Some (_, _, Some provided), Some returned ->
              if functional_block provided then
                begin match block_value context inside provided with
                | Some (_, defined) ->
                    oblige context frame Ensures returns_span
                      "This method replaces one its trait provides, so it must return what the \
                       provided body returns, and it may not."
                      (L.equal returned defined)
                | None -> ()
                end
              else
                oblige context frame Ensures returns_span
                  "This method replaces one its trait provides, whose body is not functional, so \
                   there is no definition to show this one agrees with."
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
  let home = match source.key with Some key -> key | None -> invalid_arg "Translate.laws" in
  let context = new_context database ~home ~current:impl ~terminates:false ~measures:[] in
  let start = empty_frame source in
  let substitution = trait_substitution database trait for_type in
  List.iter
    (fun (law_source, (law : law)) ->
      let types = law_parameter_types ~substitution law in
      if not (List.exists (fun ty -> T.is_error ty) types) then begin
        (* The other laws are facts here, and this one is not. *)
        context.laws_assumed <- laws_key trait for_type :: context.laws_assumed;
        let terms =
          List.map
            (fun ty ->
              let term = arrive context start "law" ty in
              assume_valid context start ty term;
              term)
            types
        in
        let inside = law_frame start law_source ~substitution law terms in
        List.iter
          (fun clause -> assume context start (snd (clause_value context inside clause)))
          law.requires;
        (* A [proof]'s statements are hints: its calls' postconditions are
           facts where their preconditions hold, which is all a proof
           needs. Its parameters are bound by position to the law's
           arguments, its generic parameters stand for the type's
           arguments, and the law's [requires] are assumed. *)
        let start =
          List.fold_left
            (fun start
                 ( (proof_source : source),
                   renaming,
                   (parameters : Core.parameter list),
                   (body : block) ) ->
              let locals, types =
                List.fold_left2
                  (fun (locals, types) (parameter : Core.parameter) term ->
                    ( Locals.add parameter.local term locals,
                      Locals.add parameter.local (T.substitute renaming parameter.type_) types ))
                  (start.locals, start.types) parameters
                  (List.filteri (fun index _ -> index < List.length parameters) terms)
              in
              restrict start
                (L.not_
                   (ghost context
                      {
                        start with
                        source = proof_source;
                        checking = false;
                        locals;
                        types;
                        substitution = renaming;
                      }
                      body)))
            start
            (List.filter_map
               (fun (name, proof) -> if name = law.name then Some proof else None)
               proofs)
        in
        match specification context (fun () -> block_value context inside law.body) with
        | Some (_, holds) ->
            oblige context start Law at
              (Printf.sprintf "The law `%s.%s` may not hold for `%s`." (T.show_trait trait) law.name
                 (T.show for_type))
              holds
        | None -> ()
      end)
    (laws_of context trait.trait);
  outcome context

(* A type's own clauses. Each invariant is well defined for a value whose
   fields meet their own types' invariants, given the invariants before
   it. The type's [cost potential] is well defined and never below zero
   for a value that meets its invariants, which is what makes each
   potential a fact about every valid value. *)
let type_ database (source : source) ~path =
  let home = match source.key with Some key -> key | None -> invalid_arg "Translate.type_" in
  let context = new_context database ~home ~current:path ~terminates:false ~measures:[] in
  (match source.core.definition with
  | Type { invariants; potential; _ } ->
      let ty =
        match Query.demand database Interface.Environment.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            T.Named
              { path; arguments = Interface.Environment.generic_arguments interface.type_generics }
        | _ -> T.Named { path; arguments = [] }
      in
      let start = { (empty_frame source) with self_type = Some ty } in
      let value_ = arrive context start "value" ty in
      assume context start (validity context start ~assuming:true ~own:false ty value_);
      let at_value = { start with self = Some value_; old_self = Some value_ } in
      List.iter
        (fun invariant ->
          let after, holds = clause_value context at_value invariant in
          assume context after holds)
        invariants;
      Option.iter
        (fun written ->
          let _, own = value context at_value written in
          oblige context at_value Cost (at at_value written)
            (Printf.sprintf
               "The potential of `%s` may be below zero for a value that meets its invariants."
               (T.show ty))
            (L.Apply ("<=", [ L.int 0; own ])))
        potential
  | _ -> ());
  outcome context

let test database (source : source) ~path =
  let home = match source.key with Some key -> key | None -> invalid_arg "Translate.test" in
  let context = new_context database ~home ~current:path ~terminates:false ~measures:[] in
  (match source.core.definition with
  | Test body -> ignore (block_value context (empty_frame source) body)
  | _ -> ());
  outcome context

(* A constant's value is well defined, as any expression is: its
   arithmetic stays in range, and its shifts and divisions are valid. *)
let constant database (source : source) ~path =
  let home = match source.key with Some key -> key | None -> invalid_arg "Translate.constant" in
  let context = new_context database ~home ~current:path ~terminates:false ~measures:[] in
  (match source.core.definition with
  | Constant defined -> ignore (value context (empty_frame source) defined)
  | _ -> ());
  outcome context

let theorem database source ~path = function_ ~proof:true database source ~path
