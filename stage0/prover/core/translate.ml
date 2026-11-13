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
module Symbol = Logic.Symbol

let variable ?(numbers = []) label = Symbol.Variable { label; numbers }

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

let bug format = Compiler_bug.bug ~stage:"Prover" format

(* A clause that running compiled code can decide: one of a tag's
   [from_template]'s, by its position, for a template of these literal
   texts. *)
type evaluation = { from_template : Path.t; texts : string list; clause : int }

(* A call whose arguments are all known, of a function that is compiled and
   not generic: its term in the logic, which running it can give a value.
   A [Bool] is 0 or 1, in its arguments and its result. *)
type known_call = {
  function_ : Path.t;
  arguments : Z.t list;
  term : Logic.term;
  result_is_bool : bool;
}

type obligation = {
  code : Code.prover;
  span : span;  (** Relative to the definition being proven. *)
  message : string;
  cited : (Names.key * span) option;
      (** The clause it comes from, in the definition that states it, where that is not the one
          being proven: a callee's [requires]. *)
  fixes : span Diagnostic.fix list;  (** Edits of the definition proven that would show it. *)
  query : Logic.query;
  values : (Logic.symbol * string) list;
      (** Each prover symbol a counterexample shows, with its name. *)
  locals : (Logic.symbol * string) list;
      (** The locals whose values are symbols where the obligation is made, with their names: asked
          for only once the query has a counterexample, so the query's key stays its own. *)
  evaluation : evaluation option;  (** Running code that decides it, where there is any. *)
  known_calls : known_call list;  (** The calls its query mentions that running code can give. *)
  decisions : (string * string option * Logic.term * Logic.term) list;
      (** Each [if] and [match] arm of the definition before it, in order: the message where its
          condition holds and, for an [if], where it does not, where it is reached, and its
          condition, whose values a counterexample tells. *)
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

(* The definition being proven from [source]. *)
let home source =
  match source.key with Some key -> key | None -> bug "%s has no definition key" source.name

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
   tasks it leaves end: the tasks, innermost first, where it was, and its
   action then. *)
and leaving = { tasks : Core.task list; at : frame; exit : exit_ }
and exit_ = Returning of Logic.term option | Breaking | Continuing

(* Where a path is: the value of each local, the values on entry for
   [old], the path's condition, and the values of [self] and [result]. *)
and frame = {
  source : source;
  locals : Logic.term Locals.t;
  types : Types.ty Locals.t;  (** Each local's type, as it was bound. *)
  old_locals : Logic.term Locals.t;
  self : Logic.term option;
  old_self : Logic.term option;
  result : Logic.term option;
  condition : Logic.term;
  checking : bool;  (** Whether obligations are made here; not in a callee's clauses. *)
  bound : Logic.symbol list;  (** Symbols bound by quantifiers around this point. *)
  binders : (Logic.symbol * Logic.sort * Logic.term) list;
      (** The quantifiers around this point, innermost first: each bound symbol, its sort, and the
          premise it ranges over. *)
  loop : loop_exits option;
  substitution : Types.substitution;
      (** The type arguments of the callee whose clauses are read here, for its generic types. *)
  self_type : Types.ty option;  (** The type of [self], whose fields an invariant names. *)
  yielded : Logic.term option;
      (** The value of [yielded] here: the parts a lending or yielding callee yielded, or the values
          a [for] loop's earlier iterations received. *)
  finished : Logic.term option;  (** The value of [finished] here. *)
  yielded_so_far : Logic.term option;
      (** In a lending or yielding method's own body, the parts it has yielded so far. *)
  updating : Logic.term option;  (** The update target's value before the update. *)
  spent : (Costs.counter * Logic.term) list;
      (** Each counter's cost so far in the definition being proven. *)
}

(* The locals, and whether [self], a loop's body may change. *)
type changed = { changed_locals : Core.local list; changes_self : bool }

(* How a loop bounds a counter: by its [cost] clause about it, or by its
   iterations times a bound on one, and, where the values it changes hold
   potential, also with that potential, from its value on entry. *)
type loop_rule =
  | Clause_bound of Core.cost
  | Per_iteration of { per : Logic.term; per_held : (Logic.term * Logic.term) option }

type loop_cost = {
  counter : Costs.counter;
  entry : Logic.term;  (** The counter on entry to the loop. *)
  rule : loop_rule;
  held : (frame -> Logic.term) option;  (** The potential of the values the loop changes. *)
}

(* Which elements an index or a range reaches: one, or the run from a start
   to before a stop. *)
type place_value = One of Logic.term | Run of Logic.term * Logic.term

(* Where a cursor came from: a call to a yielding method, whose clauses
   each pull meets, read in [method_frame] with the call's arguments. *)
type cursor = { method_frame : frame; own : part; element : Types.ty }

(* The receipt of one iteration of a loop that receives parts: whether
   there is another part, the part, the parts received through it, and how
   the loop's own state moves on, as a cursor does when pulled. *)
type received = {
  has_another : Logic.term;
  element : Logic.term;
  through : Logic.term;
  advance : frame -> frame;
}

(* A loop at its head before its invariants are assumed: its counters,
   the fresh-name counter and the fact count on entry, the validity facts
   each iteration preserves, and the frame with the body's changes
   havocked. *)
type loop_start = {
  loop_costs : loop_cost list;
  fresh_mark : int;
  facts_mark : int;
  preserved : (string * Types.ty * Logic.term * (frame -> Logic.term option)) list;
  havocked : frame;
}

(* The place a [mut] argument is passed from: how its value is read after
   the call, and how a new value is written to it. *)
type passed_place = { read : frame -> Logic.term; write : frame -> Logic.term -> frame }

(* An argument of a call, as the callee is given it: its position, its
   mode, its source expression, if any, its type, and its value. *)
type passed = {
  position : int;
  mode : Types.mode;
  operand : operand option;  (** [None] for a default. *)
  passed_place : passed_place option;  (** For an argument that is a place, the place. *)
  type_ : Types.ty;
  term : Logic.term;
  run : (Logic.term * Logic.term) option;
      (** A slice argument's bounds, as the argument was evaluated, for writing back a [mut]
          callee's changes. *)
}

(* How a [for] loop's body runs and its iterations' values are read, where
   the MIR gives them: [run_body] runs the body from the frame inside it,
   given the element, and gives the frames that end an iteration and those
   that leave by [break]; [range] is a range's bounds, [arguments] a
   yielding call's arguments by position, and [cursor] the place of a
   cursor pulled. *)
type driven = {
  run_body : frame -> Logic.term -> frame list * frame list;
  range : (Logic.term * Logic.term) option;
  arguments :
    (int -> (Logic.term * passed_place option * (Logic.term * Logic.term) option) option) option;
  cursor : passed_place option;
}

(* A fact stated once in a definition's proof, by its subject. *)
type stated =
  | In_range of Logic.symbol  (** That a symbol's values are in its type's range. *)
  | Value_of of Logic.symbol  (** A constant's value. *)
  | Definition_of of Logic.symbol  (** A pure function's definition, for every argument. *)
  | Contract_of of Logic.symbol  (** A pure function's [ensures], for every valid argument. *)
  | Exclusive of Logic.symbol  (** That at most one of a symbol's kind holds. *)
  | Array_length of Logic.symbol  (** The length of an array's model, by the model's function. *)
  | Ranked_model of Logic.symbol  (** That a model is below its value, by the model's function. *)
  | Ranked_elements of string  (** That a sequence's elements are below it, by its type's key. *)

type context = {
  database : Query.context;
  current : Path.t;
  mutable terminates : bool;
      (** Whether the code being proven must end: the definition's [time] clause, or, in a lambda,
          its function type's. *)
  mutable parameters : Core.parameter list;  (** The definition's, for its callbacks' [requires]. *)
  measures : expression list;  (** Its [decreases], for its recursive calls. *)
  mutable declarations : Logic.declaration list;
  declared : (Logic.symbol, unit) Hashtbl.t;
  datatypes : (string, unit) Hashtbl.t;  (** The sorts declared as datatypes, by name. *)
  stated : (stated, unit) Hashtbl.t;
  mutable facts : Logic.term list;  (** Reversed. *)
  mutable obligations : obligation list;  (** Reversed. *)
  mutable fresh : int;
  mutable values : (Logic.symbol * string) list;  (** For counterexamples. *)
  local_names : (Core.local, string) Hashtbl.t;  (** Each local's name, as its pattern binds it. *)
  mutable returns : (frame * Logic.term option) list;
  mutable leaving : leaving list;  (** The early exits of the [concurrent] code being read. *)
  mutable lent_back : (Types.ty * Logic.term * Logic.term) list;
      (** Each part a lending method lends [mut]: its type, as it was lent, and as it came back. *)
  mutable instantiating : Path.t list;  (** Contracts being assumed, to stop at recursion. *)
  disjoint : (int * int) list;
      (** The ownership check's pairs of indexes, by the origin of each, that must differ. *)
  mutable indexes : (int * (place_value * span)) list;
      (** The value of each such index or range, once read. *)
  mutable evaluated_keys : (Core.id * Logic.term) list;
      (** The terms of the index keys of the target of the assignment being translated, by node.
          Reading and storing the target look them up, so that no key is evaluated twice. *)
  mutable yielded_part : (Types.ty * [ `Lends | `Yields ]) option;
      (** In a lending or yielding method's body, the type of the parts it yields. *)
  mutable yield_ensures : (expression list * expression list) option;
      (** Its [ensures]: the clauses for each [yield], which mention [result], and the others. *)
  home : Names.key;  (** The definition being proven, whose spans and obligations are in it. *)
  mutable laws_assumed : string list;  (** Each trait and type whose laws are facts already. *)
  mutable counters : Costs.counter list;
      (** The counters of the cost clauses of the definition being proven. *)
  mutable own_bounds : Costs.counter list;
      (** The counters of the definition's own [O(...)] bounds, which a call back into it assumes.
      *)
  fresh_order : (Logic.symbol, int) Hashtbl.t;
      (** Each fresh symbol's number, to tell the symbols a loop made. *)
  mutable logs : (Logic.term * bool) list;
      (** Each term [log] is applied to, and whether halved. *)
  mutable powers : (Logic.term * Logic.term) list;
      (** Each base and exponent [power] is applied to. *)
  mutable lambda_times : (Logic.term * (Logic.term * obligation list)) list;
      (** A lambda's bound on the time of one call, and the obligations that show it, made only once
          the bound is used. *)
  mutable lambda_captures : (Logic.term * Core.local list) list;  (** Each lambda's captures. *)
  lambda_definitions : (Logic.symbol, Logic.term) Hashtbl.t;
      (** Each functional lambda's definition, by its symbol, which names its captures. *)
  mutable potentials : Logic.term list;  (** Each value's potential whose definition is a fact. *)
  models : (string, (Logic.term -> Logic.term) option) Hashtbl.t;
      (** Each type's model function, by the types' keys, which reading it takes the standard
          library's impls to find, and which is asked at every potential. *)
  holds_potential : (string, bool) Hashtbl.t;  (** Whether each type can hold potential. *)
  buffers : (string, (Types.ty * (Logic.term -> Logic.term)) option) Hashtbl.t;
      (** Each type's elements and model as a buffer's, where it is one. *)
  mutable equalities : Logic.term list;  (** Each derived [==] whose definition is a fact. *)
  mutable known_calls : known_call list;  (** Each call running code can give a value. *)
  mutable decisions : (string * string option * Logic.term * Logic.term) list;
      (** Each [if] and [match] arm read so far, reversed. *)
  mutable iteration_returns : (Core.origin * Types.ty option) list;
      (** Each [return] from an iteration of a [concurrent for], by its loop, with the type of its
          value: taken where the loop ends. *)
  mutable entry : Logic.symbol list;
      (** The symbols of the definition's parameters and [self] as they arrive. *)
  mutable cursors : (Logic.term * cursor) list;  (** Where each cursor value came from. *)
  mutable proving : bool;
      (** In a theorem, a [proof] block, or a law's proof, where a [todo] is a hole. *)
  mutable holes : (Names.key * span) list;  (** Reversed. *)
  mutable unfinished : Logic.term list;
      (** The condition of each path a [todo] ends in the [proof] block being read. *)
  mutable call_targets : (Logic.term * Core.local) list;
      (** Each function-typed parameter a [calls] clause counts, with its local. *)
  mutable passed_values : int list;
      (** Each named function passed directly as an argument, which the call checks against the
          parameter's function type. *)
  mutable reading_callback : bool;
      (** Reading a function-typed parameter to call it or pass it, where its [requires] is checked,
          not lost. *)
  ranking : bool;
      (** Whether the definition proven may show a recursive call ends by being on a part of its
          parameters, the one use of the order of parts, which is stated only then. *)
  mutable scopes : (Logic.symbol * Logic.term list ref) list;
      (** Each quantifier whose body is being read, innermost first, by its bound symbol, with the
          facts made in its body that name it. *)
  quantifier_facts : (Logic.term, Logic.term list) Hashtbl.t;
      (** Each quantifier read, with the facts its body made that name its bound symbol. *)
  mutable quantifier_symbols : Logic.symbol list;
      (** Every quantifier's bound symbol, which a fact stated outside its quantifier must not name.
      *)
  mutable validating : Types.ty list;
      (** The types whose invariants are being read, around this point. A type is valid inside the
          reading of its own invariant, as it is inside its own fields, so a type that holds itself
          through another's invariant is read once. *)
}

(* The package a callee is read from, for [source_at]: the definition's. *)
let reading_package context = Some (Path.package context.current)

(* Symbols and facts *)

let declare context (declaration : Logic.declaration) =
  match declaration with
  | Constant (name, _) | Function (name, _, _) ->
      if not (Hashtbl.mem context.declared name) then begin
        Hashtbl.replace context.declared name ();
        context.declarations <- declaration :: context.declarations
      end
  | Datatype _ -> invalid_arg "Translate.declare: a datatype is declared by its sort"

(* A symbol for a value made at this point. Inside quantifiers it is a
   function of their bound symbols, since the value can differ for each of
   theirs. *)
let value_symbol context frame name sort =
  match List.rev frame.binders with
  | [] ->
      declare context (Logic.Constant (name, sort));
      Logic.Symbol name
  | outermost_first ->
      declare context
        (Logic.Function (name, List.map (fun (_, sort, _) -> sort) outermost_first, sort));
      Logic.Apply (name, List.map (fun (bound, _, _) -> Logic.Symbol bound) outermost_first)

(* A name no other symbol of the query has, for a bound variable. *)
let fresh_name context label =
  context.fresh <- context.fresh + 1;
  variable label ~numbers:[ context.fresh ]

let fresh context frame label sort =
  let name = fresh_name context label in
  Hashtbl.replace context.fresh_order name context.fresh;
  value_symbol context frame name sort

(* Whether a term mentions a fresh symbol made after [mark]: a value a
   loop changes, or one made inside it. *)
let mentions_fresh_after context mark term =
  let is_fresh_after name =
    match Hashtbl.find_opt context.fresh_order name with
    | Some order -> order > mark
    | None -> false
  in
  let rec walk = function
    | Logic.Symbol name -> is_fresh_after name
    | Logic.Integer _ | Logic.Boolean _ | Logic.Bits _ -> false
    | Logic.Apply (name, arguments) -> is_fresh_after name || List.exists walk arguments
    | Logic.Operation (_, arguments) -> List.exists walk arguments
    | Logic.Is (_, argument) -> walk argument
    | Logic.Forall (_, body) | Logic.Exists (_, body) -> walk body
  in
  walk term

(* A statement made inside quantifiers, closed over them: true for every
   value of each bound symbol that its premise admits. [None] when it names
   a symbol bound by something other than a quantifier, such as a lambda's
   parameter, where it has no meaning outside. *)
let closed_over_binders frame term =
  let names = List.map (fun (name, _, _) -> name) frame.binders in
  if Logic.mentions (List.filter (fun name -> not (List.mem name names)) frame.bound) term then None
  else if not (Logic.mentions names term) then Some term
  else
    let outermost_first = List.rev frame.binders in
    Some
      (Logic.Forall
         ( List.map (fun (name, sort, _) -> (name, sort)) outermost_first,
           Logic.( ==> )
             (Logic.conjunction (List.map (fun (_, _, premise) -> premise) outermost_first))
             term ))

(* A fact that names bound symbols, kept with the innermost quantifier
   whose symbol it names, where every bound symbol it names is a
   quantifier's. A goal that quantifiers are skolemized in has it as a
   hypothesis, where it costs the solver nothing to instantiate. *)
let in_scope context frame term =
  let named = List.filter (fun name -> Logic.mentions [ name ] term) frame.bound in
  if List.for_all (fun name -> List.mem_assoc name context.scopes) named then
    match List.find_opt (fun (name, _) -> List.mem name named) context.scopes with
    | Some (_, facts) -> facts := term :: !facts
    | None -> ()

(* The facts of the quantifiers whose bound symbols are [names]. *)
let scope_facts context names =
  List.concat_map
    (fun (name, facts) -> if List.mem name names then List.rev !facts else [])
    context.scopes

(* A goal with the facts of each quantifier it skolemizes as hypotheses:
   each [forall] where the goal holds it, and each [exists] where it holds
   it negated. The facts hold for every value, so the goal means the same.
   A value made in a body is a function of every quantifier around it, so
   a fact can name an outer quantifier's symbol that the quantifier's own
   term does not; it is added only where every quantifier symbol it names
   is bound, by a quantifier the goal is in or by [binders], which the
   obligation is closed over. *)
let with_quantifier_facts ?(binders = []) context term =
  let stated bound fact =
    List.for_all
      (fun name -> List.mem name bound || not (Logic.mentions [ name ] fact))
      context.quantifier_symbols
  in
  let rec walk positive bound term =
    let facts symbols =
      let bound = List.map fst symbols @ bound in
      ( bound,
        List.filter (stated bound)
          (Option.value ~default:[] (Hashtbl.find_opt context.quantifier_facts term)) )
    in
    match term with
    | Logic.Forall (symbols, body) when positive ->
        let bound, facts = facts symbols in
        let body = walk positive bound body in
        Logic.Forall
          ( symbols,
            match facts with [] -> body | facts -> Logic.( ==> ) (Logic.conjunction facts) body )
    | Logic.Exists (symbols, body) when not positive ->
        let bound, facts = facts symbols in
        let body = walk positive bound body in
        Logic.Exists
          ( symbols,
            match facts with [] -> body | facts -> Logic.( &&& ) (Logic.conjunction facts) body )
    | Logic.Operation ((("and" | "or") as operator), parts) ->
        Logic.Operation (operator, List.map (walk positive bound) parts)
    | Logic.Operation ("=>", [ premise; conclusion ]) ->
        Logic.Operation ("=>", [ walk (not positive) bound premise; walk positive bound conclusion ])
    | Logic.Operation ("not", [ inner ]) ->
        Logic.Operation ("not", [ walk (not positive) bound inner ])
    | term -> term
  in
  walk true binders term

(* A fact of mathematics, true on every path. One that names a bound
   symbol is not stated for every value of it, since a body's calls give
   many such facts and the solver spends its steps on them, but kept with
   its quantifier. *)
let fact context frame term =
  if not (Logic.mentions frame.bound term) then context.facts <- term :: context.facts
  else in_scope context frame term

(* A fact is guarded by its path's condition, and kept with its
   quantifier where either names a bound symbol, as [fact] says. *)
let assume context frame term =
  match term with
  | Logic.Boolean true -> ()
  | _ ->
      let guarded = Logic.( ==> ) frame.condition term in
      if not (Logic.mentions frame.bound term || Logic.mentions frame.bound frame.condition) then
        context.facts <- guarded :: context.facts
      else in_scope context frame guarded

(* An obligation is shown by its own query, and is a fact for the code
   after it. Inside a quantifier it is shown for each value the
   quantifier's premise admits, which is how a quantifier's body is shown
   to be well defined. *)
(* A fix that adds a [requires] to the definition proven, before its body's
   brace, which starts a line where the header has clauses and ends its
   first line where it has none. *)
let add_requires context frame required =
  let text = Lazy.force frame.source.text in
  let brace =
    match Option.bind frame.source.key (Query.demand context.database Names.definition) with
    | Some { kind = Function { body; _ }; _ } when body.span.start < String.length text ->
        Some body.span.start
    | _ -> None
  in
  let edit =
    match brace with
    | Some at when at > 0 && text.[at - 1] = '\n' ->
        Some (Diagnostic.insert (Syntax.Span.zero_width at) ("  requires " ^ required ^ "\n"))
    | Some at when at > 0 && text.[at - 1] = ' ' ->
        Some (Diagnostic.replace (Syntax.Span.make (at - 1) at) ("\n  requires " ^ required ^ "\n"))
    | _ -> None
  in
  match edit with
  | Some edit -> [ Diagnostic.fix (Printf.sprintf "Add `requires %s`" required) [ edit ] ]
  | None -> []

(* A goal about the definition's parameters as they arrive, written as
   Truss: comparisons, logic, and arithmetic of parameters and literals,
   which a [requires] states exactly, since a specification's integers do
   not overflow. *)
let truss_of_goal context term =
  let name symbol =
    if List.mem symbol context.entry then
      match List.assoc_opt symbol context.values with Some name -> Some name | None -> Some "self"
    else None
  in
  let named = ref false in
  let all printed = if List.mem None printed then None else Some (List.filter_map Fun.id printed) in
  let rec atom = function
    | Logic.Symbol symbol ->
        let printed = name symbol in
        if printed <> None then named := true;
        printed
    | Logic.Integer value -> Some (Z.to_string value)
    | Logic.Boolean value -> Some (if value then "true" else "false")
    | _ -> None
  and value term = arithmetic 0 term
  and arithmetic level = function
    | Logic.Operation ((("+" | "*") as operator), (_ :: _ :: _ as parts)) ->
        let inner = if operator = "+" then 1 else 2 in
        Option.map
          (fun printed -> parenthesized level inner (String.concat (" " ^ operator ^ " ") printed))
          (all (List.map (arithmetic inner) parts))
    | Logic.Operation ("-", [ left; right ]) ->
        Option.map
          (fun printed -> parenthesized level 1 (String.concat " - " printed))
          (all [ arithmetic 1 left; arithmetic 2 right ])
    | Logic.Operation ("-", [ inner ]) ->
        Option.map (fun printed -> parenthesized level 3 ("-" ^ printed)) (arithmetic 3 inner)
    | Logic.Integer value when Z.sign value < 0 && level > 0 -> Some ("(" ^ Z.to_string value ^ ")")
    | term -> atom term
  and parenthesized level inner text = if inner < level then "(" ^ text ^ ")" else text
  and print = function
    | Logic.Operation ((("<" | "<=" | ">" | ">=" | "=") as operator), [ left; right ]) -> (
        match (value left, value right) with
        | Some left, Some right ->
            Some (Printf.sprintf "%s %s %s" left (if operator = "=" then "==" else operator) right)
        | _ -> None)
    | Logic.Operation ("and", parts) -> joined " && " parts
    | Logic.Operation ("or", parts) -> joined " || " parts
    | Logic.Operation ("not", [ inner ]) -> Option.map (Printf.sprintf "!(%s)") (print inner)
    | Logic.Operation ("=>", [ premise; conclusion ]) -> (
        match (print premise, print conclusion) with
        | Some premise, Some conclusion -> Some (Printf.sprintf "(%s) ==> (%s)" premise conclusion)
        | _ -> None)
    | term -> atom term
  and joined separator parts =
    Option.map
      (fun printed -> "(" ^ String.concat separator printed ^ ")")
      (all (List.map print parts))
  in
  let printed =
    match term with
    | Logic.Operation ("and", parts) ->
        Option.map (String.concat " && ") (all (List.map print parts))
    | Logic.Operation ("or", parts) ->
        Option.map (String.concat " || ") (all (List.map print parts))
    | term -> print term
  in
  if !named then printed else None

(* Bitwise operations, exactly: each defined as the operation on its
   operands' bits of their type's width, read back as an integer, which
   the solver decides by bit-blasting. *)
let bitwise_operations =
  [
    "and";
    "or";
    "xor";
    "complement";
    "shift_left";
    "shift_right";
    "rotate_left";
    "rotate_right";
    "swap_bytes";
  ]

let bitwise_of : Logic.symbol -> _ = function
  | Opaque_operation { operation; integer = Some (bits, signed); _ }
    when List.mem operation bitwise_operations ->
      Some (operation, bits, signed)
  | _ -> None

let exactly (query : Logic.query) =
  let bitwise_terms = ref [] in
  let rec walk bound = function
    | Logic.Apply (name, arguments) as term ->
        (if bitwise_of name <> None && not (List.mem_assoc term !bitwise_terms) then
           let named = List.filter (fun (symbol, _) -> Logic.mentions [ symbol ] term) bound in
           bitwise_terms := (term, named) :: !bitwise_terms);
        List.iter (walk bound) arguments
    | Logic.Forall (symbols, body) | Logic.Exists (symbols, body) -> walk (symbols @ bound) body
    | term -> List.iter (walk bound) (Logic.arguments term)
  in
  List.iter (walk []) (query.goal :: query.facts);
  let definition term =
    match term with
    | Logic.Apply (name, arguments) -> (
        match (bitwise_of name, arguments) with
        | Some (operation, bits, signed), first :: rest ->
            let bits_of value = Logic.Operation (Printf.sprintf "(_ int2bv %d)" bits, [ value ]) in
            let operand_bits = bits_of first in
            let result =
              match (operation, rest) with
              | "complement", _ -> Some (Logic.Operation ("bvnot", [ operand_bits ]))
              | "and", [ second_operand ] ->
                  Some (Logic.Operation ("bvand", [ operand_bits; bits_of second_operand ]))
              | "or", [ second_operand ] ->
                  Some (Logic.Operation ("bvor", [ operand_bits; bits_of second_operand ]))
              | "xor", [ second_operand ] ->
                  Some (Logic.Operation ("bvxor", [ operand_bits; bits_of second_operand ]))
              | "shift_left", [ second_operand ] ->
                  Some (Logic.Operation ("bvshl", [ operand_bits; bits_of second_operand ]))
              | "shift_right", [ second_operand ] ->
                  Some
                    (Logic.Operation
                       ( (if signed then "bvashr" else "bvlshr"),
                         [ operand_bits; bits_of second_operand ] ))
              | ("rotate_left" | "rotate_right"), [ second_operand ] ->
                  (* By the amount modulo the width, with what leaves one end
                     coming in at the other. *)
                  let by = bits_of (Logic.Operation ("mod", [ second_operand; Logic.int bits ])) in
                  let rest = Logic.Operation ("bvsub", [ bits_of (Logic.int bits); by ]) in
                  let towards, back =
                    if operation = "rotate_left" then ("bvshl", "bvlshr") else ("bvlshr", "bvshl")
                  in
                  Some
                    (Logic.Operation
                       ( "bvor",
                         [
                           Logic.Operation (towards, [ operand_bits; by ]);
                           Logic.Operation (back, [ operand_bits; rest ]);
                         ] ))
              | "swap_bytes", _ ->
                  let byte index =
                    Logic.Operation
                      ( Printf.sprintf "(_ extract %d %d)" ((8 * index) + 7) (8 * index),
                        [ operand_bits ] )
                  in
                  let bytes = List.init (bits / 8) byte in
                  Some
                    (List.fold_left
                       (fun swapped next -> Logic.Operation ("concat", [ swapped; next ]))
                       (List.hd bytes) (List.tl bytes))
              | _ -> None
            in
            Option.map
              (fun result ->
                let unsigned = Logic.Operation ("bv2nat", [ result ]) in
                let value =
                  if signed then
                    let half = Logic.Integer (Z.shift_left Z.one (bits - 1)) in
                    Logic.ite
                      (Logic.Operation (">=", [ unsigned; half ]))
                      (Logic.Operation ("-", [ unsigned; Logic.Integer (Z.shift_left Z.one bits) ]))
                      unsigned
                  else unsigned
                in
                Logic.equal term value)
              result
        | _ -> None)
    | _ -> None
  in
  (* A term under a quantifier that names its bound symbols is defined for
     each of their values. *)
  let defined (term, named) =
    Option.map
      (fun definition -> if named = [] then definition else Logic.Forall (named, definition))
      (definition term)
  in
  { query with facts = query.facts @ List.filter_map defined (List.rev !bitwise_terms) }

let rec oblige ?evaluation ?cited ?(fixes = []) context frame code span message goal =
  match
    obligation_at ?evaluation context frame code span message
      (with_quantifier_facts
         ~binders:(List.map (fun (name, _, _) -> name) frame.binders)
         context goal)
  with
  | Some obligation ->
      (* Without a fix of its own, a goal about the parameters alone is
         offered as a [requires]. *)
      let fixes =
        match fixes with
        | [] when frame.source.key = Some context.home && frame.checking -> (
            let goal =
              match frame.condition with
              | Logic.Boolean true -> goal
              | condition -> Logic.( ==> ) condition goal
            in
            match truss_of_goal context goal with
            | Some required -> add_requires context frame required
            | None -> [])
        | fixes -> fixes
      in
      context.obligations <- { obligation with cited; fixes } :: context.obligations;
      assume context frame goal
  | None -> ()

(* An obligation made but not yet added, for one that is needed only if
   its goal is used. *)
and obligation_at ?evaluation context frame code span message goal =
  if not frame.checking then None
  else if not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition) then
    Some (make_obligation ?evaluation context frame code span message goal)
  else
    let names = List.map (fun (name, _, _) -> name) frame.binders in
    let goal =
      match scope_facts context names with
      | [] -> goal
      | facts -> Logic.( ==> ) (Logic.conjunction facts) goal
    in
    match closed_over_binders frame (Logic.( ==> ) frame.condition goal) with
    | Some closed ->
        Some
          (make_obligation ?evaluation context
             { frame with condition = Logic.Boolean true }
             code span message closed)
    | None -> None

and make_obligation ?evaluation context frame code span message goal =
  let query =
    Logic.prune
      {
        declarations = List.rev context.declarations;
        facts = List.rev context.facts;
        goal = Logic.( ==> ) frame.condition goal;
      }
  in
  let known_calls =
    List.filter
      (fun (known : known_call) ->
        let mentioned term = occurs known.term term in
        mentioned query.goal || List.exists mentioned query.facts)
      context.known_calls
  in
  {
    code;
    span;
    message;
    cited = None;
    fixes = [];
    query;
    values = context.values;
    decisions = List.rev context.decisions;
    locals =
      Locals.fold
        (fun local term shown ->
          match (term, Hashtbl.find_opt context.local_names local) with
          | Logic.Symbol symbol, Some name
            when not (List.mem_assoc symbol context.values || List.mem_assoc symbol shown) ->
              (symbol, name) :: shown
          | _ -> shown)
        frame.locals
        (match frame.result with
        | Some (Logic.Symbol symbol) when not (List.mem_assoc symbol context.values) ->
            [ (symbol, "result") ]
        | _ -> []);
    evaluation;
    known_calls;
  }

(* Whether a term holds another. *)
and occurs part term =
  term = part
  ||
  match term with
  | Logic.Forall (_, body) | Logic.Exists (_, body) -> occurs part body
  | term -> List.exists (occurs part) (Logic.arguments term)

(* Where a node came from in its form's text, by its origin. *)
let span_of (source : source) origin =
  let spans = Lazy.force source.spans in
  if origin >= 0 && origin < Array.length spans then spans.(origin) else Syntax.Span.make 0 0

(* A node's source text, for messages. *)
let quote source origin =
  let span = span_of source origin in
  let text = Lazy.force source.text in
  if span.stop > span.start && span.stop <= String.length text then
    String.sub text span.start (span.stop - span.start)
  else "this expression"

(* Where a node of the form read here is. *)
let at frame (node : expression) = span_of frame.source node.origin

(* The base, the start, and the stop, if any, of a slice's call. *)
let slice_parts (call : expression) =
  match call.kind with
  | Call
      {
        arguments = Passed { value = Place base; _ } :: Passed { value = Value start; _ } :: rest;
        _;
      } -> (
      match rest with
      | [] -> (base, start, None)
      | [ Passed { value = Value stop; _ } ] -> (base, start, Some stop)
      | _ -> bug "a slice whose call has more than three arguments")
  | _ -> bug "a slice whose call does not take its base and its bounds"

(* Types *)

let builtin ty = Types.builtin_of ty

let bounds (ty : Types.ty) =
  if Types.is_builtin Character ty then Some (Z.zero, Z.of_int 0x10FFFF) else Types.integer_range ty

let width (ty : Types.ty) = Option.map fst (Types.integer_bits ty)
let is_numeric (ty : Types.ty) = match ty with Types.Integer -> true | _ -> bounds ty <> None

(* A float type's widths in the solver's floating-point theory: its
   exponent's, and its significand's, with the hidden bit. *)
let float_format (ty : Types.ty) =
  match builtin ty with Some Float32 -> Some (8, 24) | Some Float64 -> Some (11, 53) | _ -> None

(* A float literal, bit for bit. *)
let float_literal (exponent, significand) value =
  let bits =
    if exponent = 8 then Z.extract (Z.of_int32 (Int32.bits_of_float value)) 0 32
    else Z.extract (Z.of_int64 (Int64.bits_of_float value)) 0 64
  in
  let fraction = significand - 1 in
  Logic.Operation
    ( "fp",
      [
        Logic.Bits (1, Z.extract bits (exponent + fraction) 1);
        Logic.Bits (exponent, Z.extract bits fraction exponent);
        Logic.Bits (fraction, Z.extract bits 0 fraction);
      ] )

(* IEEE 754 arithmetic, rounding to nearest with ties to even, and the
   lawful [==] and ordering of floats: every NaN is equal to every other
   and ordered after every number, and otherwise IEEE's, so [-0.0 == 0.0]. *)
let float_operation name left right =
  Logic.Operation (name, [ Logic.Operation ("RNE", []); left; right ])

let is_nan value = Logic.Operation ("fp.isNaN", [ value ])

(* A float cut toward zero, as a real number. *)
let truncated value =
  Logic.Operation
    ( "fp.to_real",
      [ Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTZ", []); value ]) ] )

let float_equal left right =
  Logic.(Operation ("fp.eq", [ left; right ]) ||| (is_nan left &&& is_nan right))

let float_less left right =
  Logic.(not_ (is_nan left) &&& is_nan right ||| Operation ("fp.lt", [ left; right ]))

let is_bool ty = Types.is_builtin Bool ty

(* A type's name in the logic, unique across modules, as [Types.show] is not. *)
let rec type_key (ty : Types.ty) =
  match ty with
  | Named { path; arguments = [] } -> Path.show path
  | Named { path; arguments } ->
      Path.show path ^ "[" ^ String.concat ", " (List.map argument_key arguments) ^ "]"
  | _ -> Types.show ty

and argument_key = function
  | Types.Type ty -> type_key ty
  | argument -> Types.show_argument argument

let constructor_name (ty : Types.ty) variant =
  let type_name =
    match ty with Named { path = Top { name; _ }; _ } -> name | _ -> Types.show ty
  in
  Symbol.Constructor { type_key = type_key ty; type_name; variant }

let selector_name ty variant field = Symbol.Field { type_key = type_key ty; variant; field }
let is_standard_equal = Well_known.is Equal
let equal_trait = Well_known.path Equal

(* [frame] without the locals declared after [outer]: those of a block,
   an arm, or a loop end with it. *)
let end_scope ~(outer : frame) (frame : frame) =
  { frame with locals = Locals.filter (fun id _ -> Locals.mem id outer.locals) frame.locals }

(* A callee's generics paired with its type arguments, as the frame sees
   them. *)
let callee_substitution frame (signature : Types.signature) type_arguments =
  let rec pair (generics : Types.generic list) arguments =
    match (generics, arguments) with
    | generic :: generics, argument :: arguments ->
        (generic.generic, Types.substitute_argument frame.substitution argument)
        :: pair generics arguments
    | _ -> []
  in
  pair signature.generics type_arguments

(* A type's interface, when it is a type whose fields this package sees. *)
let visible_type context (ty : Types.ty) =
  match ty with
  | Named { path; arguments } when builtin ty = None -> (
      match Query.demand context.database Interface.Environment.interface path with
      | Some (Interface.Environment.Type_interface interface)
        when (not interface.opaque) || Path.package path = Path.package context.current ->
          let substitution =
            Option.value ~default:[] (Types.substitution_of interface.type_generics arguments)
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
      let fields (list : Types.field list) =
        List.sort compare
          (List.map
             (fun (field : Types.field) ->
               (field.field_name, Types.substitute substitution field.field_type))
             list)
      in
      match interface.shape with
      | Record list -> Some [ (None, fields list) ]
      | Sum variants ->
          Some
            (List.sort compare
               (List.map
                  (fun (variant : Types.variant) ->
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
      let fields (list : Types.field list) =
        List.map
          (fun (field : Types.field) ->
            (field.field_name, Types.substitute substitution field.field_type))
          list
      in
      match (interface.shape, variant) with
      | Record list, None -> Some (fields list)
      | Sum variants, Some name -> (
          match
            List.find_opt (fun (variant : Types.variant) -> variant.variant_name = name) variants
          with
          | Some { fields = Some list; _ } -> Some (fields list)
          | Some { fields = None; _ } -> Some []
          | None -> None)
      | _ -> None)
  | None -> None

let rec sort_of context (ty : Types.ty) : Logic.sort =
  if is_numeric ty then Int
  else if is_bool ty then Bool
  else
    match (ty, float_format ty) with
    | _, Some (exponent, significand) -> Float (exponent, significand)
    | _ when Types.equal ty Types.unit ->
        (* One value, so any two are equal. *)
        if not (Hashtbl.mem context.datatypes "Unit") then begin
          Hashtbl.replace context.datatypes "Unit" ();
          context.declarations <-
            Logic.Datatype ("Unit", [ (Symbol.Unit, []) ]) :: context.declarations
        end;
        Uninterpreted "Unit"
    | Function function_type, _ ->
        (* One sort for each number of inputs, whatever the clauses, so a
           value keeps its sort where a function type is widened. *)
        Uninterpreted (Printf.sprintf "function/%d" (List.length function_type.inputs))
    | _ -> begin
        let name = type_key ty in
        (if not (Hashtbl.mem context.datatypes name) then
           match constructors context ty with
           | Some shape ->
               (* Marked first, so a recursive type's fields find it declared. *)
               Hashtbl.replace context.datatypes name ();
               let declaration =
                 Logic.Datatype
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
let rec structural context ?(seen = []) (ty : Types.ty) =
  if is_numeric ty || is_bool ty || Types.is_builtin Character ty || Types.equal ty Types.unit then
    true
  else if List.exists (Types.equal ty) seen then true
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
(* The size of a built-in scalar on the 64-bit targets the address space
   is taken from. A type of another size, which may be zero, has none. *)
let scalar_bytes element : int option =
  match Types.builtin_of element with
  | Some (Int8 | UInt8 | Bool) -> Some 1
  | Some (Int16 | UInt16) -> Some 2
  | Some (Int32 | UInt32 | Float32 | Character) -> Some 4
  | Some (Int64 | UInt64 | USize | ISize | Float64) -> Some 8
  | _ -> None

let in_range ty term =
  match bounds ty with
  | Some (low, high) ->
      let in_bounds =
        Logic.(Operation ("<=", [ Integer low; term ]) &&& Operation ("<=", [ term; Integer high ]))
      in
      if Types.is_builtin Character ty then
        Logic.(
          in_bounds
          &&& not_
                (Operation ("<=", [ int 0xD800; term ]) &&& Operation ("<=", [ term; int 0xDFFF ])))
      else in_bounds
  | None -> Logic.Boolean true

(* Runs [make] the first time a fact is met in a definition's proof, for a
   fact that is stated once. *)
let once context stated make =
  if not (Hashtbl.mem context.stated stated) then begin
    Hashtbl.replace context.stated stated ();
    make ()
  end

(* A term with its quantifiers' bound names numbered in the order they
   appear, so two terms that differ only in those names are the same. *)
let canonical_binders term =
  let count = ref 0 in
  let rec walk renamed = function
    | Logic.Symbol name -> (
        match List.assoc_opt name renamed with
        | Some other -> Logic.Symbol other
        | None -> Logic.Symbol name)
    | ( Logic.Integer _ | Logic.Boolean _ | Logic.Bits _ | Logic.Apply _ | Logic.Operation _
      | Logic.Is _ ) as term ->
        Logic.map_arguments (walk renamed) term
    | Logic.Forall (bound, body) ->
        let bound, renamed = rename renamed bound in
        Logic.Forall (bound, walk renamed body)
    | Logic.Exists (bound, body) ->
        let bound, renamed = rename renamed bound in
        Logic.Exists (bound, walk renamed body)
  and rename renamed bound =
    List.fold_right
      (fun (name, sort) (bound, renamed) ->
        incr count;
        let other = Symbol.Variable { label = "binder"; numbers = [ !count ] } in
        ((other, sort) :: bound, (name, other) :: renamed))
      bound ([], renamed)
  in
  walk [] term

(* A value of a type that arrives from outside the known facts: a parameter,
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

(* A type in a frame, substituted and normalized: a trait's [Self.Key]
   read for a [List] is a [USize]. *)
let substituted context frame ty =
  Interface.Impls.normalize context.database
    ~bounds:(fun _ -> [])
    (Types.substitute frame.substitution ty)

let type_of context frame (node : expression) = substituted context frame node.type_

let local_type context frame local =
  Option.map (substituted context frame) (Locals.find_opt local frame.types)

(* Whether a term mentions a value's potential: a type's potential, or a
   growable buffer's slack, which a type that holds one, as a [String] does
   in its own package, unfolds to. *)
let mentions_potential term =
  let rec walk = function
    | Logic.Apply ((Symbol.Potential _ | Symbol.Slack _), _) -> true
    | Logic.Forall (_, body) | Logic.Exists (_, body) -> walk body
    | term -> List.exists walk (Logic.arguments term)
  in
  walk term

(* Paths *)

let restrict frame condition = { frame with condition = Logic.( &&& ) frame.condition condition }

(* Joins paths: the condition is that one of them was taken, and each
   local whose values differ gets a fresh symbol each path defines. *)
let join context ?value_type frames =
  match frames with
  | [] -> None
  | [ (frame, value) ] -> Some (frame, value)
  | (first, _) :: _ ->
      let condition = Logic.disjunction (List.map (fun (frame, _) -> frame.condition) frames) in
      (* The joined condition is named, so that each later fact on the path
         names it rather than repeating every branch's condition, which
         would grow with each join. *)
      let condition =
        match condition with
        | Logic.Boolean _ | Logic.Symbol _ -> condition
        | _ when Logic.mentions first.bound condition -> condition
        | _ ->
            let path = fresh context first "path" Logic.Bool in
            fact context first (Logic.equal path condition);
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
                   Logic.mentions first.bound frame.condition
                   || match term with Some term -> Logic.mentions first.bound term | None -> false)
                 values -> (
            (* Inside a quantifier, a fact about a fresh symbol could not
               mention the bound variable, so the value is an [ite]. *)
            match List.rev values with
            | (_, Some last) :: earlier ->
                Some
                  (List.fold_left
                     (fun otherwise ((frame : frame), term) ->
                       match term with
                       | Some term -> Logic.ite frame.condition term otherwise
                       | None -> otherwise)
                     last earlier)
            | _ -> None)
        | _ ->
            let symbol = fresh context first prefix sort in
            List.iter
              (fun ((frame : frame), term) ->
                match term with
                | Some term ->
                    fact context first (Logic.( ==> ) frame.condition (Logic.equal symbol term))
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
              | None -> ( match term with Logic.Boolean _ -> Logic.Bool | _ -> Logic.Int)
            in
            match define "joined" sort (fun frame _ -> Locals.find_opt id frame.locals) with
            | Some joined -> joined
            | None -> term)
          first.locals
      in
      (* [self] and the parts a lending or yielding method has yielded change
         along paths too, like locals. *)
      let self =
        match first.self_type with
        | Some ty -> (
            match define "self" (sort_of context ty) (fun frame _ -> frame.self) with
            | Some joined -> Some joined
            | None -> first.self)
        | None -> first.self
      in
      (* A path's cost, in terms of the joined values: on that path each
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
        List.fold_left (fun amount (from, into) -> Logic.replace ~from ~into amount) amount renamed
      in
      (* At a join, a counter is a fresh symbol defined as an [ite] of the
         paths' costs, which a loop's per-iteration bound can see through. *)
      let spent =
        List.map
          (fun (key, term) ->
            let values =
              List.map
                (fun ((frame : frame), _) ->
                  ( frame.condition,
                    in_joined frame
                      (match List.assoc_opt key frame.spent with
                      | Some spent_term -> spent_term
                      | None -> term) ))
                frames
            in
            match values with
            | (_, first_value) :: rest
              when List.for_all (fun (_, variant) -> variant = first_value) rest ->
                (key, first_value)
            | _ ->
                let choice =
                  match List.rev values with
                  | (_, last) :: earlier ->
                      List.fold_left
                        (fun otherwise (condition, value) -> Logic.ite condition value otherwise)
                        last earlier
                  | [] -> term
                in
                (* A choice that names a potential stays a choice, so that a
                   loop sees the potential each path changed, which the
                   potential the loop holds cancels. *)
                if Logic.mentions first.bound choice || mentions_potential choice then (key, choice)
                else
                  let symbol = fresh context first "spent" Logic.Int in
                  fact context first (Logic.equal symbol choice);
                  (key, symbol))
          first.spent
      in
      let value =
        match value_type with
        | Some ty -> define "value" (sort_of context ty) (fun _ value -> value)
        | None -> None
      in
      let yielded_so_far =
        match context.yielded_part with
        | Some (part, _) -> (
            match
              define "parts"
                (sort_of context
                   (Types.Named { path = Well_known.path Sequence; arguments = [ Types.Type part ] }))
                (fun frame _ -> frame.yielded_so_far)
            with
            | Some joined -> Some joined
            | None -> first.yielded_so_far)
        | None -> first.yielded_so_far
      in
      Some ({ merged with locals; spent; self; yielded_so_far }, value)

let join_frames context frames =
  Option.map fst (join context (List.map (fun frame -> (frame, None)) frames))

(* Calls: callee contracts *)

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
type form_origin = Written | Derived | Provided

(* The form of a function or a method by its path, with the substitution it
   is read under: the [impl]'s, for the form of the trait's method that the
   [impl] leaves to it. A caller reads its callee's specification, whose
   body is there only where the callee is a function in the logic, so
   editing another body proves no caller again; a caller in another
   package, [reading_package], reads the specification the callee's package
   exports. *)
let source_at ?reading_package database (path : Path.t) =
  let specification =
    match reading_package with
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
              (fun (impl : Types.impl_interface) ->
                Option.map
                  (fun key -> (source_of database key core, substitution, Provided))
                  (Query.demand database Interface.Summary.key
                     (Method { owner = impl.implements.trait; name; receiver })))
        | None, _ -> None)

(* The substitution a trait's clauses and laws are read with for a type: [Self] the
   type, and each of the trait's parameters its argument. *)
let trait_substitution database (trait : Types.trait_reference) (ty : Types.ty) =
  let generics =
    match Query.demand database Interface.Environment.interface trait.trait with
    | Some (Interface.Environment.Trait_interface interface) ->
        List.map (fun (generic : Types.generic) -> generic.generic) interface.trait_generics
    | _ -> []
  in
  let rec pair generics arguments =
    match (generics, arguments) with
    | generic :: generics, argument :: arguments -> (generic, argument) :: pair generics arguments
    | _ -> []
  in
  ({ Types.owner = trait.trait; name = "Self" }, Types.Type ty)
  :: pair generics trait.trait_arguments

(* A form's clauses about its definition. *)
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

(* Whether a pattern binds a part of its scrutinee [mut]. *)
let rec lends_mut (pattern : pattern) =
  match pattern.kind with
  | Bind { mode = Types.Mut; _ } -> true
  | Variant { fields; _ } | Record fields -> List.exists (fun (_, inner) -> lends_mut inner) fields
  | Alternatives alternatives -> List.exists lends_mut alternatives
  | Wildcard | Bind _ | Literal _ | Range _ | Equal_to _ -> false

let holds_todo body =
  Core_walk.block_exists
    ~expression:(fun (node : Core.expression) -> match node.kind with Todo -> true | _ -> false)
    body

(* The [proof]s written for a trait's laws on a type, in the package: each
   law's name, with the proof's source, the renaming of the proof's generic
   parameters to the type's arguments, and the proof's parameters and body. *)
let law_proofs database package (trait : Types.trait_reference) (for_type : Types.ty) =
  let same_argument (left : Types.argument) (right : Types.argument) =
    match (left, right) with Type left, Type right -> Types.equal left right | _ -> left = right
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
                List.map (fun (generic : Types.generic) -> generic.generic) proven.generics
              in
              match Interface.Impls.match_type ~variables [] proven.for_type for_type with
              | Some renaming
                when List.equal same_argument
                       (List.map (Types.substitute_argument renaming) proven.trait.trait_arguments)
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
   are about its methods' results, so they wait, as the methods'
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
let law_unshown database (impl : Path.t) (trait : Types.trait_reference) for_type name =
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
let is_functional walk =
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
                  (function Passed { mode = Types.Mut; _ } -> true | Passed _ | Default -> false)
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
    let child_binds = ref false in
    Core_walk.pattern_children
      {
        Core_walk.ignore_all with
        pattern = (fun inner -> if binds_variable inner then child_binds := true);
      }
      pattern;
    !child_binds || match pattern.kind with Bind { is_var; _ } -> is_var | _ -> false
  in
  walk visit;
  !fine

let is_functional_block (body : block) = is_functional (fun visit -> Core_walk.block visit body)

let is_functional_expression (node : expression) =
  is_functional (fun visit -> Core_walk.expression visit node)

let make_contract database path ~own ~others ~body =
  let signature = Interface.Impls.signature database path in
  let pure =
    match signature with
    | Some (signature : Types.signature) -> (
        (* A function of its arguments: it may take them [own], but
           changes none of the caller's. *)
        signature.uses = Types.no_capabilities
        && signature.terminates
        && List.for_all
             (fun (info : Types.parameter_info) -> info.mode <> Types.Mut)
             signature.parameters
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
    | Some body when pure && result_kind = `Returns && is_functional_block body -> Some (own, body)
    | _ -> None
  in
  { parts = own :: others; pure; result_kind; definition }

(* The contract of a function, a theorem, or a type's own method. *)
let function_contract ?reading_package database (path : Path.t) =
  Option.bind (source_at ?reading_package database path) (fun (callee, _, _) ->
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
let method_contract ?reading_package database (trait : Types.trait_reference) name receiver
    (evidence : evidence) =
  let trait_side = trait_part database trait.trait name receiver in
  match evidence with
  | Impl { impl; _ } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match source_at ?reading_package database path with
      | Some (callee, _, (Written | Derived)) ->
          Option.map
            (fun own ->
              make_contract database path ~own ~others:(Option.to_list trait_side)
                ~body:(body_of callee))
            (part_of callee)
      | Some (_, _, Provided) | None ->
          (* A method the [impl] leaves to its trait: the trait's clauses and
             default body, with the [impl]'s signature for the method. *)
          Option.map
            (fun own ->
              make_contract database path ~own ~others:[]
                ~body:(provided_body database trait.trait name receiver))
            trait_side)
  | Bound | Dynamic ->
      Option.map
        (fun own ->
          make_contract database
            (Path.Method { owner = trait.trait; name; receiver })
            ~own ~others:[] ~body:None)
        trait_side

let distinct_counters counters =
  List.fold_left
    (fun distinct counter -> if List.mem counter distinct then distinct else distinct @ [ counter ])
    [] counters

(* A cost clause's resource, with the locals it is read with, which give
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

(* The local or [self] a place is part of: the root an assignment or a
   [mut] lend of it changes. *)
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

let rec expression context frame (node : expression) : (frame * Logic.term) option =
  if frame.source.key = Some context.home then
    match List.assoc_opt node.id context.evaluated_keys with
    | Some term -> Some (frame, term)
    | None -> (
        try expression_kind context frame node
        with Foreign_unsupported message -> raise (Unsupported (at frame node, message)))
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
      Logic.(Operation ("<", [ index; start ]) ||| Operation ("<=", [ stop; index ]))
    in
    List.iter
      (fun (first, second) ->
        if first = origin || second = origin then
          match (List.assoc_opt first context.indexes, List.assoc_opt second context.indexes) with
          | Some (left, (first_span : span)), Some (right, (second_span : span)) ->
              let apart =
                match (left, right) with
                | One left, One right -> Logic.not_ (Logic.equal left right)
                | One index, Run (start, stop) | Run (start, stop), One index ->
                    outside index start stop
                | Run (start, stop), Run (other_start, other_stop) ->
                    Logic.disjunction
                      [
                        Logic.Operation ("<=", [ stop; other_start ]);
                        Logic.Operation ("<=", [ other_stop; start ]);
                        Logic.Operation ("<=", [ stop; start ]);
                        Logic.Operation ("<=", [ other_stop; other_start ]);
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
                (Types.show base_type)));
      ignore (sort_of context base_type);
      (frame, field_of context frame base_type None field (substituted context frame type_) term)
  | Lent node | Temporary node -> value context frame node

and operand_value context frame = function
  | Place place -> place_value context frame place
  | Value node -> value context frame node

(* A function-typed parameter whose type has a [requires], read as a value
   other than to call it or pass it to a parameter: the value's type keeps
   no [requires], so the [requires] must hold for every argument. *)
(* Fresh valid arguments for a callback's inputs. *)
and callback_arguments context frame inputs =
  List.map
    (fun (_, input) ->
      let input = substituted context frame input in
      let term = arrive context frame "argument" input in
      assume_valid context frame input term;
      term)
    inputs

(* The frame a callback parameter's [requires] is read in: its inputs bound
   to [arguments], over the caller's state on entry. *)
and callback_contract_frame frame inputs arguments =
  let locals =
    List.fold_left2
      (fun locals (input, _) term -> Locals.add input term locals)
      frame.old_locals inputs arguments
  in
  { frame with locals; self = frame.old_self; checking = false }

and escaping_callback context frame local =
  match
    ( List.find_opt (fun (parameter : Core.parameter) -> parameter.local = local) context.parameters,
      local_type context frame local )
  with
  | ( Some { callback_contract = Some { inputs; requires = _ :: _ as requires }; name; _ },
      Some (Types.Function function_type) )
    when List.length inputs = List.length function_type.inputs ->
      let arguments = callback_arguments context frame function_type.inputs in
      check_callback_contract context frame
        (span_of frame.source (List.hd requires).origin)
        ~name inputs requires arguments ~promised:(Logic.Boolean true)
        ~why:"is used as a value whose type promises nothing of its arguments"
  | _ -> ()

and reading_callback : 'a. _ -> (unit -> 'a) -> 'a =
 fun context read ->
  let saved = context.reading_callback in
  context.reading_callback <- true;
  Fun.protect ~finally:(fun () -> context.reading_callback <- saved) read

(* A function-typed parameter passed on for another callee's parameter:
   that parameter's promise about its arguments must imply this one's
   [requires]. *)
and check_forwarded_callback context frame (node : expression) (call_ : call) (passed : passed)
    local values =
  match
    List.find_opt (fun (parameter : Core.parameter) -> parameter.local = local) context.parameters
  with
  | Some { callback_contract = Some { inputs; requires = _ :: _ as requires }; name; _ } -> (
      match parameter_type context frame call_ passed.position with
      | Some (Types.Function expected) when List.length expected.inputs = List.length inputs ->
          let arguments = callback_arguments context frame expected.inputs in
          let known = List.map (fun (passed : passed) -> (passed.position, passed.term)) values in
          check_callback_contract context frame (at frame node) ~name inputs requires arguments
            ~promised:
              (Logic.conjunction
                 (callback_facts context frame call_ passed.position known arguments))
            ~why:"is passed for a parameter that may not promise its `requires`"
      | _ -> escaping_callback context frame local)
  | _ -> ()

(* That a function-typed parameter's [requires], read with its parameters
   as they were on entry, holds wherever [promised] does. *)
and check_callback_contract context frame span ~name inputs requires arguments ~promised ~why =
  let inside = callback_contract_frame frame inputs arguments in
  List.iter
    (fun (clause : expression) ->
      oblige context (restrict frame promised) Requires span
        (Printf.sprintf "`%s` %s, so its `%s` may not hold." name why
           (quote frame.source clause.origin))
        (snd (clause_value context inside clause)))
    requires

and expression_kind context frame (node : expression) : (frame * Logic.term) option =
  let source = frame.source in
  match node.kind with
  | Integer number -> Some (frame, Logic.Integer number)
  | Float number -> (
      match float_format (type_of context frame node) with
      | Some format -> Some (frame, float_literal format number)
      | None -> unsupported (at frame node) "a float literal without a float type")
  | Boolean value -> Some (frame, Logic.Boolean value)
  | String text -> Some (frame, text_value context frame (type_of context frame node) text)
  | Template { literals; call = template_call } ->
      Some (tagged_template context frame node literals template_call)
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
  | Slice { call } ->
      let base, start, stop = slice_parts call in
      Some (slice context frame node base ~start:(Some start) ~stop ~inclusive:false)
  | Call call_ -> (
      match resolved_call context frame node call_ with
      | Some _ when Types.equal (type_of context frame node) Types.Never ->
          (* A call that gives [Never] does not return, so the path ends. *)
          None
      | translated -> translated)
  | Operator { operation; arguments } -> Some (operator context frame node operation arguments)
  | Compare { comparison = compared; left; right } ->
      let operand_type = type_of context frame left in
      let frame, left_term = value context frame left in
      let frame, right_term = value context frame right in
      Some
        ( frame,
          if float_format operand_type <> None then
            match compared with
            | Equal -> float_equal left_term right_term
            | Not_equal -> Logic.not_ (float_equal left_term right_term)
            | Less -> float_less left_term right_term
            | Less_equal ->
                Logic.( ||| ) (float_less left_term right_term) (float_equal left_term right_term)
            | Greater -> float_less right_term left_term
            | Greater_equal ->
                Logic.( ||| ) (float_less right_term left_term) (float_equal left_term right_term)
          else
            match comparison compared with
            | Some symbol when compared = Equal ->
                ignore symbol;
                Logic.equal left_term right_term
            | Some symbol -> Logic.Operation (symbol, [ left_term; right_term ])
            | None -> Logic.not_ (Logic.equal left_term right_term) )
  | Not inner ->
      let frame, term = value context frame inner in
      Some (frame, Logic.not_ term)
  | And (left, right) ->
      let frame, left_value = value context frame left in
      short_circuit context frame right ~runs:left_value ~otherwise:(Logic.Boolean false)
        ~binds:true (Logic.( &&& ) left_value)
  | Or (left, right) ->
      let frame, left_value = value context frame left in
      short_circuit context frame right ~runs:(Logic.not_ left_value)
        ~otherwise:(Logic.Boolean true) ~binds:false (Logic.( ||| ) left_value)
  | Implies (left, right) ->
      let frame, left_value = value context frame left in
      short_circuit context frame right ~runs:left_value ~otherwise:(Logic.Boolean true)
        ~binds:false (Logic.( ==> ) left_value)
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
      | Some cursor_method ->
          let pulled, later = pull context frame cursor_method cursor ~cursor_type in
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
          | _, Types.Function actual, Types.Function expected
            when not (List.for_all (fun cost -> List.mem cost actual.costs) expected.costs) ->
              unsupported (at frame node) "a function value's costs"
          | _ -> ());
          Some (frame, term)
      | To_integer -> Some (frame, term)
      | From_integer ->
          let ty = type_of context frame node in
          oblige context frame Out_of_range (at frame node)
            (Printf.sprintf "`%s` may not fit in `%s`." (quote source node.origin) (Types.show ty))
            (in_range ty term);
          Some (frame, term))
  | To_any { value = inner; _ } ->
      (* A value of [any Trait], known through the trait's contracts: one
         allocation, of the block that holds the value. *)
      let frame, _ = value context frame inner in
      let frame =
        spend context frame (fun (counter : Costs.counter) ->
            match (counter.resource, counter.counting) with
            | Allocations, _ -> Logic.int 1
            | Allocated_bytes, Units -> Logic.int 1
            | Allocated_bytes, (At_most | Exactly) -> unknown_amount context frame counter
            | (Time | Calls _), _ -> Costs.zero)
      in
      Some (frame, arrive context frame "any" (type_of context frame node))
  | If { condition; then_; else_; _ } -> if_ context frame node condition then_ else_
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
                | Types.Mut, Place place ->
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
        (Logic.Boolean false);
      None
  | Todo ->
      (* The code after a [todo] on its path is not proven, and a build refuses
         any program that can reach it. In a proof it is a hole. *)
      if context.proving then begin
        context.holes <- (context.home, at frame node) :: context.holes;
        context.unfinished <- frame.condition :: context.unfinished
      end;
      Some
        ( { frame with condition = Logic.Boolean false },
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
  | Quantified { quantifier; binder; body } -> quantified context frame quantifier binder body
  | Yielded -> (
      (* The parts the innermost loop has received, or else, in a lending or
         yielding method's body, the parts the method has yielded. *)
      match (frame.yielded, frame.yielded_so_far) with
      | Some yielded, _ -> Some (frame, yielded)
      | None, Some yielded_so_far when source.key = Some context.home -> Some (frame, yielded_so_far)
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
      Some (frame, Logic.equal first_value second_value)
  | Specification_function { function_; arguments } ->
      specification_function context frame node function_ arguments
  | Method_time callee -> Some (frame, method_time context frame callee)
  | Task_exit { tasks; exit } -> (
      (* The exit is where the block it leaves ends, after the other
         branches, so here it is only recorded. *)
      match tasks with
      | [ Iteration { loop } ] -> (
          (* The iterations after it are cancelled and run to their ends, so
             this one ends here, and the loop ends when they all have: a
             [break] is then where the loop ends, and a [return] is taken
             there, with a value known by its type. *)
          match frame.loop with
          | Some exits ->
              let ended =
                match exit.kind with
                | Return (Some returned) -> (
                    match expression context frame returned with
                    | Some (after, _) ->
                        context.iteration_returns <-
                          (loop, Some (type_of context frame returned)) :: context.iteration_returns;
                        Some after
                    | None -> None)
                | Return None ->
                    context.iteration_returns <- (loop, None) :: context.iteration_returns;
                    Some frame
                | Break | Continue -> Some frame
                | _ ->
                    unsupported (at frame node)
                      "an early exit that is not a `return`, `break`, or `continue`"
              in
              (match ended with
              | Some ended -> exits.continues <- ended :: exits.continues
              | None -> ());
              None
          | None -> unsupported (at frame node) "an early exit outside its loop")
      | Iteration _ :: _ ->
          unsupported (at frame node)
            "an early exit from an iteration of a `concurrent for` loop to tasks around it"
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
   [&&] keeps its right side's bindings, as an [is] does. *)
and short_circuit context frame right ~runs ~otherwise ~binds combine =
  let after, right_value = value context (restrict frame runs) right in
  (* The right operand's cost accrues only on the path that evaluates
     it, so a right operand with a cost joins the two paths. *)
  let changed =
    Locals.exists (fun id term -> Locals.find_opt id after.locals <> Some term) frame.locals
    || after.self <> frame.self || after.spent <> frame.spent
  in
  if not changed then
    Some ((if binds then { after with condition = frame.condition } else frame), combine right_value)
  else
    match
      join context ~value_type:Types.bool
        [ (after, Some right_value); (restrict frame (Logic.not_ runs), Some otherwise) ]
    with
    | Some (joined, Some term) -> Some (joined, term)
    | Some (joined, None) -> Some (joined, Logic.Boolean true)
    | None -> None

and equal_of context frame (ty : Types.ty) left right =
  if structural context ty then Logic.equal left right
  else if float_format ty <> None then float_equal left right
  else
    match written_equal context ty left right with
    | Some equal -> equal
    | None -> derived_equal context frame ty left right

(* [==] on a type with a written [impl] of [Equal]: a call of its [equal],
   so that the [impl]'s postcondition holds of it. *)
and written_equal context ty left right =
  match concrete_impl context { trait = equal_trait; trait_arguments = []; associated = [] } ty with
  | Some (((Impl _ : Path.t) as impl), arguments) -> (
      let evidence : evidence = Impl { impl; arguments } in
      match
        method_contract ?reading_package:(reading_package context) context.database
          { trait = equal_trait; trait_arguments = []; associated = [] }
          "equal" Read evidence
      with
      | Some contract when contract.pure ->
          let symbol =
            Symbol.Function
              {
                callee = Path.Method { owner = impl; name = "equal"; receiver = Read };
                instance = [ type_key ty ];
              }
          in
          let sort = sort_of context ty in
          declare context (Logic.Function (symbol, [ sort; sort ], Logic.Bool));
          Some (Logic.Apply (symbol, [ left; right ]))
      | _ -> None)
  | _ -> None

and derived_equal context frame (ty : Types.ty) left right =
  let sort = sort_of context ty in
  let symbol = Symbol.Equal (type_key ty) in
  declare context (Logic.Function (symbol, [ sort; sort ], Logic.Bool));
  let equal = Logic.Apply (symbol, [ left; right ]) in
  (match (visible_type context ty, constructors context ty) with
  | Some (interface, _), Some shape
    when List.exists is_standard_equal interface.derives
         && (not (List.mem equal context.equalities))
         && not (Logic.mentions frame.bound equal) ->
      context.equalities <- equal :: context.equalities;
      let fields_equal (variant, fields) =
        Logic.conjunction
          (List.map
             (fun (field, field_type) ->
               let selector = selector_name ty variant field in
               let left = Logic.Apply (selector, [ left ])
               and right = Logic.Apply (selector, [ right ]) in
               if structural context field_type then Logic.equal left right
               else if float_format field_type <> None then float_equal left right
               else
                 match written_equal context field_type left right with
                 | Some equal -> equal
                 | None ->
                     (* Unfolded only when it is compared itself. *)
                     let symbol = Symbol.Equal (type_key field_type) in
                     declare context
                       (Logic.Function
                          ( symbol,
                            [ sort_of context field_type; sort_of context field_type ],
                            Logic.Bool ));
                     Logic.Apply (symbol, [ left; right ]))
             fields)
      in
      let defined =
        match shape with
        | [ ((None, _) as record) ] -> fields_equal record
        | variants ->
            Logic.disjunction
              (List.map
                 (fun ((variant, _) as one) ->
                   let is_variant term = Logic.Is (constructor_name ty variant, term) in
                   Logic.(is_variant left &&& is_variant right &&& fields_equal one))
                 variants)
      in
      fact context frame (Logic.equal equal defined)
  | _ -> ());
  equal

(* An operation the solver knows only by the range of its result. *)
and opaque_operation context frame ty name arguments =
  let sorts = List.map (fun _ -> Logic.Int) arguments in
  let integer =
    Option.map
      (fun bits -> (bits, match bounds ty with Some (low, _) -> Z.sign low < 0 | None -> false))
      (width ty)
  in
  let symbol = Symbol.Opaque_operation { operation = name; type_key = type_key ty; integer } in
  declare context (Logic.Function (symbol, sorts, sort_of context ty));
  let term = Logic.Apply (symbol, arguments) in
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
  ( frame,
    primitive_operation context frame ~node operation [ ty ] operands
      ~arguments:(List.map Option.some arguments) ~fallback:(fun () ->
        if float_format ty <> None then arrive context frame "operator" ty
        else unsupported (at frame node) "this operator") )

(* A primitive operation on built-in types, written as an operator or as a
   call of the intrinsic module's operation: either way it has the same
   obligations and facts. [types] are the operation's type arguments, the
   operands' type first. [arguments] are the operands' expressions where
   they are values, for the text of a diagnostic and its fixes. [fallback]
   is the result of an operation the logic does not model. *)
and primitive_operation context frame ~node (operation : Intrinsic.operation) types operands
    ~(arguments : expression option list) ~fallback =
  let source = frame.source in
  let span = at frame node in
  let argument index = Option.join (List.nth_opt arguments index) in
  let is_float = match types with ty :: _ -> float_format ty <> None | [] -> false in
  let exact operation left right =
    match (operation : Intrinsic.operation) with
    | Add | Wrapping_add | Add_overflows -> Logic.Operation ("+", [ left; right ])
    | Subtract | Wrapping_subtract | Subtract_overflows -> Logic.Operation ("-", [ left; right ])
    | _ -> Logic.Operation ("*", [ left; right ])
  in
  match (operation, types, operands) with
  | Add, _ :: _, [ left; right ] when is_float -> float_operation "fp.add" left right
  | Subtract, _ :: _, [ left; right ] when is_float -> float_operation "fp.sub" left right
  | Multiply, _ :: _, [ left; right ] when is_float -> float_operation "fp.mul" left right
  | Divide, _ :: _, [ left; right ] when is_float -> float_operation "fp.div" left right
  | Negate, _ :: _, [ value ] when is_float -> Logic.Operation ("fp.neg", [ value ])
  | (Add | Subtract | Multiply | Divide | Remainder), ty :: _, [ left; right ] when not is_float ->
      let result =
        arithmetic ?operand:(argument 0) ?divisor:(argument 1) context frame node ty operation left
          right
      in
      if bounds ty <> None then assume context frame (in_range ty result);
      result
  | Negate, ty :: _, [ inner ] when not is_float ->
      let negated = Logic.Operation ("-", [ inner ]) in
      if bounds ty <> None then
        oblige context frame Overflow span
          (Printf.sprintf "`%s` may overflow `%s`." (quote source node.origin) (Types.show ty))
          (in_range ty negated)
      else if ty <> Types.Integer then unsupported span "negating a value of `%s`" (Types.show ty);
      negated
  | Complement, ty :: _, [ inner ] -> opaque_operation context frame ty "complement" [ inner ]
  | (Shift_left | Shift_right), ty :: _, [ left; right ] ->
      (match width ty with
      | Some bits ->
          let at_amount, text, fixes =
            match argument 1 with
            | Some amount ->
                ( at frame amount,
                  Printf.sprintf "The shift amount `%s`" (quote source amount.origin),
                  match parameter_operand context frame amount right with
                  | Some text -> add_requires context frame (Printf.sprintf "%s < %d" text bits)
                  | None -> [] )
            | None ->
                (span, Printf.sprintf "The shift amount in `%s`" (quote source node.origin), [])
          in
          oblige context frame Shift at_amount ~fixes
            (Printf.sprintf "%s may not be less than %d." text bits)
            Logic.(Operation ("<", [ right; int bits ]))
      | None -> unsupported span "a shift of `%s`" (Types.show ty));
      let name = match operation with Shift_left -> "shift_left" | _ -> "shift_right" in
      let shifted = opaque_operation context frame ty name [ left; right ] in
      (* An unsigned shift multiplies or divides by a power of two: to the
         left exactly, where the product fits. A shift by less than the
         width scales by at most the top bit, so [1 << k] fits. *)
      (match (bounds ty, width ty) with
      | Some (low, high), Some bits
        when Z.equal low Z.zero && not (Logic.mentions frame.bound right) ->
          let scale = power_of context frame (Logic.int 2) right in
          assume context frame
            Logic.(
              Operation ("<=", [ int 0; right ])
              &&& Operation ("<", [ right; int bits ])
              ==> (Operation ("<=", [ int 1; scale ])
                  &&& Operation ("<=", [ scale; Integer (Z.shift_left Z.one (bits - 1)) ])));
          assume context frame
            (match operation with
            | Shift_left ->
                Logic.(
                  Operation ("<=", [ Operation ("*", [ left; scale ]); Integer high ])
                  ==> equal shifted (Operation ("*", [ left; scale ])))
            | _ -> Logic.equal shifted (Logic.truncated_divide left scale))
      | _ -> ());
      shifted
  | (Bit_and | Bit_or | Bit_xor), ty :: _, [ left; right ] ->
      let name = match operation with Bit_and -> "and" | Bit_or -> "or" | _ -> "xor" in
      let term = opaque_operation context frame ty name [ left; right ] in
      (* Of unsigned values, [and] is at most each operand, [or] at
         least each, and [or] and [xor] at most their sum and below each
         power of two both operands are below. Of signed values, [and]
         with a nonnegative operand lies from zero to that operand. *)
      (match bounds ty with
      | Some (low, _) when Z.sign low < 0 && operation = Bit_and ->
          let masked_by operand =
            Logic.(
              Operation ("<=", [ int 0; operand ])
              ==> (Operation ("<=", [ int 0; term ]) &&& Operation ("<=", [ term; operand ])))
          in
          assume context frame Logic.(masked_by left &&& masked_by right)
      | Some (low, _) when Z.equal low Z.zero -> (
          let at_most bound = Logic.Operation ("<=", [ term; bound ]) in
          match operation with
          | Bit_and -> assume context frame Logic.(at_most left &&& at_most right)
          | _ ->
              let sum = Logic.Operation ("+", [ left; right ]) in
              if operation = Bit_or then
                assume context frame
                  Logic.(Operation ("<=", [ left; term ]) &&& Operation ("<=", [ right; term ]));
              assume context frame (at_most sum);
              declare context
                (Logic.Function (Symbol.Cost_power, [ Logic.Int; Logic.Int ], Logic.Int));
              let exponent = Logic.Symbol (variable "exponent") in
              let below value =
                Logic.Operation
                  ("<", [ value; Logic.Apply (Symbol.Cost_power, [ Logic.int 2; exponent ]) ])
              in
              assume context frame
                (Logic.Forall
                   ( [ (variable "exponent", Logic.Int) ],
                     Logic.(
                       Operation ("<=", [ int 0; exponent ])
                       &&& below left &&& below right ==> below term) )))
      | _ -> ());
      term
  | (Wrapping_add | Wrapping_subtract | Wrapping_multiply), ty :: _, [ left; right ]
    when bounds ty <> None ->
      let low, high = Option.get (bounds ty) in
      let modulus = Z.succ (Z.sub high low) in
      Logic.Operation
        ( "+",
          [
            Logic.Integer low;
            Logic.Operation
              ( "mod",
                [
                  Logic.Operation ("-", [ exact operation left right; Logic.Integer low ]);
                  Logic.Integer modulus;
                ] );
          ] )
  | (Add_overflows | Subtract_overflows | Multiply_overflows), ty :: _, [ left; right ]
    when bounds ty <> None ->
      Logic.not_ (in_range ty (exact operation left right))
  | Equal, _ :: _, [ left; right ] when is_float -> float_equal left right
  | Less, _ :: _, [ left; right ] when is_float -> float_less left right
  | Equal, ty :: _, [ left; right ] when bounds ty <> None -> Logic.equal left right
  | Less, ty :: _, [ left; right ] when bounds ty <> None -> Logic.Operation ("<", [ left; right ])
  | Fits, [ source; target ], [ value ] when bounds source <> None && bounds target <> None ->
      in_range target value
  | Fits, [ source; target ], [ value ] when float_format source <> None && bounds target <> None ->
      float_fits target value
  | Convert, [ source; target ], [ value ]
    when bounds source <> None && bounds target <> None && not (Types.is_builtin Character target)
    ->
      let known = fallback () in
      assume context frame Logic.(in_range target value ==> equal known value);
      known
  | (Leading_zeros | Trailing_zeros | Count_ones), ty :: _, [ value ] when bounds ty <> None -> (
      let low, _ = Option.get (bounds ty) in
      (* Each count of bits is a function of the value, at most the width,
         and for an unsigned value the three are related: a nonzero value
         lies between the powers of two its leading zeros give, has no
         more ones than the bits below its highest one, all of them where
         it is one less than a power of two, and its lowest one below its
         highest; zero has no ones and is all zeros. *)
      match width ty with
      | Some bits ->
          let count name =
            let symbol = Symbol.Bit_count { count = name; width = bits } in
            declare context (Logic.Function (symbol, [ Logic.Int ], Logic.Int));
            Logic.Apply (symbol, [ value ])
          in
          let leading = count "leading_zeros"
          and trailing = count "trailing_zeros"
          and ones = count "count_ones" in
          let term =
            match operation with Leading_zeros -> leading | Trailing_zeros -> trailing | _ -> ones
          in
          assume context frame
            Logic.(Operation ("<=", [ int 0; term ]) &&& Operation ("<=", [ term; int bits ]));
          (if Z.equal low Z.zero && not (Logic.mentions frame.bound value) then
             let power exponent = power_of context frame (Logic.int 2) exponent in
             let width = Logic.int bits in
             let nonzero = Logic.not_ (Logic.equal value (Logic.int 0)) in
             let below_highest = Logic.Operation ("-", [ width; leading ]) in
             List.iter (assume context frame)
               Logic.
                 [
                   Operation ("<=", [ int 0; leading ])
                   &&& Operation ("<=", [ leading; width ])
                   &&& Operation ("<=", [ int 0; trailing ])
                   &&& Operation ("<=", [ trailing; width ])
                   &&& Operation ("<=", [ int 0; ones ])
                   &&& Operation ("<=", [ ones; width ]);
                   nonzero
                   ==> (Operation
                          ("<=", [ power (Operation ("-", [ int (bits - 1); leading ])); value ])
                       &&& Operation ("<", [ value; power below_highest ]));
                   equal (equal ones (int 0)) (equal value (int 0));
                   nonzero ==> Operation ("<=", [ ones; below_highest ]);
                   nonzero
                   &&& equal (Operation ("+", [ value; int 1 ])) (power below_highest)
                   ==> equal ones below_highest;
                   nonzero
                   ==> Operation ("<=", [ Operation ("+", [ trailing; leading ]); int (bits - 1) ]);
                   equal value (int 0) ==> (equal trailing width &&& equal leading width);
                 ]);
          term
      | None -> fallback ())
  | _ -> (
      match (operation, types) with
      | (Ieee_equal | Ieee_less), ty :: _ when float_format ty <> None -> (
          match operands with
          | [ left; right ] ->
              Logic.Operation
                ((if operation = Ieee_equal then "fp.eq" else "fp.lt"), [ left; right ])
          | _ -> fallback ())
      | (Square_root | Floor | Ceiling | Truncate | Round_to_even), ty :: _
        when float_format ty <> None -> (
          (* The rounding the compiled operation does, as IEEE 754 names it. *)
          match operands with
          | [ value ] -> (
              match operation with
              | Square_root -> Logic.Operation ("fp.sqrt", [ Logic.Operation ("RNE", []); value ])
              | Floor ->
                  Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTN", []); value ])
              | Ceiling ->
                  Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTP", []); value ])
              | Truncate ->
                  Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTZ", []); value ])
              | _ -> Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RNE", []); value ]))
          | _ -> fallback ())
      | Fused_multiply_add, ty :: _ when float_format ty <> None -> (
          match operands with
          | [ value; multiplier; addend ] ->
              Logic.Operation ("fp.fma", [ Logic.Operation ("RNE", []); value; multiplier; addend ])
          | _ -> fallback ())
      | Is_nan, ty :: _ when float_format ty <> None -> (
          match operands with [ value ] -> is_nan value | _ -> fallback ())
      | From_bits, [ bits; target ] when bounds bits <> None -> (
          match (operands, float_format target, width bits) with
          | [ value ], Some (exponent, significand), Some width ->
              Logic.Operation
                ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
                  [ Logic.Operation (Printf.sprintf "(_ int2bv %d)" width, [ value ]) ] )
          | _ -> fallback ())
      | To_bits, [ source; bits ] when bounds bits <> None -> (
          (* A float's bits are those that make it again, which every float but
         a NaN has one of. *)
          match (operands, float_format source, width bits) with
          | [ value ], Some (exponent, significand), Some width ->
              assume context frame
                Logic.(
                  not_ (is_nan value)
                  ==> equal
                        (Operation
                           ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
                             [ Operation (Printf.sprintf "(_ int2bv %d)" width, [ fallback () ]) ]
                           ))
                        value);
              fallback ()
          | _ -> fallback ())
      | Multiply_high, ty :: _ when bounds ty <> None -> (
          (* The product's upper word: the exact product divided by the type's
         size, rounded down, which is its upper word signed or not. *)
          match (operands, width ty) with
          | [ left; right ], Some bits ->
              Logic.Operation
                ( "div",
                  [
                    Logic.Operation ("*", [ left; right ]); Logic.Integer (Z.shift_left Z.one bits);
                  ] )
          | _ -> fallback ())
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
                   "`%s` may not fit `%s`: it must be a number that, cut toward zero, is in its \
                    range."
                   (quote frame.source node.origin) (Types.show target))
                (float_fits target value);
              Logic.Operation ("to_int", [ truncated value ])
          | _ -> fallback ())
      | Convert, [ source; target ] when bounds source <> None && float_format target <> None -> (
          (* An integer becomes the float nearest it, ties to even, as the
         compiled cast rounds: exactly it, where the float can hold it. *)
          match (operands, float_format target) with
          | [ value ], Some (exponent, significand) ->
              Logic.Operation
                ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
                  [ Logic.Operation ("RNE", []); Logic.Operation ("to_real", [ value ]) ] )
          | _ -> fallback ())
      | Convert, [ _; target ] when Types.is_builtin Character target -> (
          (* A [Character] is made from an integer only when the integer is a
         Unicode scalar value, which the conversion does not check. *)
          match operands with
          | [ value ] ->
              oblige context frame Requires (at frame node)
                (Printf.sprintf
                   "`%s` may not be a Unicode scalar value, which a `Character` must be."
                   (quote frame.source node.origin))
                (in_range target value);
              value
          | _ -> fallback ())
      | _ -> fallback ())

and arithmetic ?operand ?divisor context frame (node : expression) ty
    (operation : Intrinsic.operation) left right =
  let source = frame.source in
  let span = at frame node in
  let exact =
    match operation with
    | Add -> Logic.Operation ("+", [ left; right ])
    | Subtract -> Logic.Operation ("-", [ left; right ])
    | Multiply -> Logic.Operation ("*", [ left; right ])
    | Divide -> Logic.truncated_divide left right
    | _ -> Logic.truncated_remainder left right
  in
  (match operation with
  | Divide | Remainder ->
      oblige context frame Division span
        ~fixes:
          (match
             Option.bind divisor (fun divisor -> parameter_operand context frame divisor right)
           with
          | Some text -> add_requires context frame (text ^ " != 0")
          | None -> [])
        (Printf.sprintf "The divisor in `%s` may be zero." (quote source node.origin))
        (Logic.not_ (Logic.equal right (Logic.int 0)))
  | _ -> ());
  (match bounds ty with
  | Some (low, _) when operation = Divide || operation = Remainder ->
      if Z.sign low < 0 then
        oblige context frame Overflow span
          (Printf.sprintf "`%s` may overflow `%s`: the least value over -1."
             (quote source node.origin) (Types.show ty))
          (Logic.not_ Logic.(equal left (Integer low) &&& equal right (int (-1))))
  | Some (low, high) ->
      let unsigned = Z.sign low = 0 && not (Types.is_builtin Character ty) in
      oblige context frame Overflow span
        ~fixes:
          (match operand with
          | Some operand -> overflow_fix context frame ty operation operand left right
          | None -> [])
        (Printf.sprintf "`%s` may overflow `%s`." (quote source node.origin) (Types.show ty))
        (match operation with
        | (Add | Multiply) when unsigned -> Logic.Operation ("<=", [ exact; Integer high ])
        | Subtract when unsigned -> Logic.Operation ("<=", [ Integer low; exact ])
        | _ -> in_range ty exact)
  | None -> ());
  exact

and if_ context frame (node : expression) condition (then_ : block) (else_ : block option) =
  let frame, test = value context frame condition in
  (if frame.checking && frame.source.key = Some context.home then
     let text = quote frame.source condition.origin in
     context.decisions <-
       ( Printf.sprintf "`%s` is true" text,
         Some (Printf.sprintf "`%s` is false" text),
         frame.condition,
         test )
       :: context.decisions);
  let then_result = block_value context (restrict frame test) then_ in
  let otherwise = restrict frame (Logic.not_ test) in
  let else_result =
    match else_ with
    | Some block_ -> block_value context otherwise block_
    | None -> Some (otherwise, Logic.Boolean true)
  in
  let ty = type_of context frame node in
  let carries_value = else_ <> None && not (Types.equal ty Types.unit || ty = Types.Never) in
  let reached = List.filter_map Fun.id [ then_result; else_result ] in
  if carries_value then
    match
      join context ~value_type:ty (List.map (fun (frame, term) -> (frame, Some term)) reached)
    with
    | Some (frame, Some term) -> Some (frame, term)
    | Some (frame, None) -> Some (frame, Logic.Boolean true)
    | None -> None
  else
    Option.map
      (fun frame -> (frame, Logic.Boolean true))
      (join_frames context (List.map fst reached))

and quantified context frame (quantifier : Syntax.quantifier) binder body =
  let make ?count bound_symbol sort premise body_frame =
    let mark = context.fresh in
    (* The body runs only for the values the premise admits, which may be
       none, so its assumptions hold only for them. *)
    let body_frame =
      restrict
        { body_frame with binders = (bound_symbol, sort, premise) :: body_frame.binders }
        premise
    in
    let facts = ref [] in
    context.scopes <- (bound_symbol, facts) :: context.scopes;
    context.quantifier_symbols <- bound_symbol :: context.quantifier_symbols;
    let after, body_value =
      Fun.protect
        ~finally:(fun () -> context.scopes <- List.tl context.scopes)
        (fun () -> value context body_frame body)
    in
    let bound = [ (bound_symbol, sort) ] in
    (* In code, a quantifier over a range runs its body once for each value
       in it, which costs that many times the body's cost, when that cost
       is the same for every value. *)
    let frame =
      match count with
      | Some count when frame.checking ->
          spend context frame (fun counter ->
              let spent =
                match
                  (List.assoc_opt counter body_frame.spent, List.assoc_opt counter after.spent)
                with
                | Some start, Some total -> Costs.since ~start total
                | _ -> Costs.zero
              in
              if mentions_fresh_after context mark spent || Logic.mentions [ bound_symbol ] spent
              then unknown_amount context frame counter
              else
                match counter.counting with
                | Units ->
                    Costs.plus
                      (Costs.times (Costs.at_least_zero count) (Costs.plus spent (Logic.int 1)))
                      (Logic.int 1)
                | At_most | Exactly ->
                    if spent = Costs.zero then Costs.zero else unknown_amount context frame counter)
      | _ -> frame
    in
    let term =
      match quantifier with
      | Forall -> Logic.Forall (bound, Logic.( ==> ) premise body_value)
      | Exists -> Logic.Exists (bound, Logic.( &&& ) premise body_value)
    in
    if !facts <> [] then Hashtbl.replace context.quantifier_facts term (List.rev !facts);
    Some (frame, term)
  in
  let symbol = fresh_name context "bound" in
  let inner = { frame with bound = symbol :: frame.bound } in
  let each = Logic.Symbol symbol in
  (* Over a collection's elements: by index into its sequence, or each
     value its set contains, each matched against the binding's pattern,
     which names its parts and leaves out the values it does not match. *)
  let over_collection (pattern : pattern) (collection_type : Types.ty) collected span =
    let element = substituted context frame pattern.type_ in
    let set_path = Well_known.path Set in
    match collection_type with
    | Named { path; _ } when Path.equal path set_path || Path.equal path finite_set_path ->
        let finite = Types.Named { path = finite_set_path; arguments = [ Types.Type element ] } in
        let model =
          if Path.equal path finite_set_path then Some collected
          else model_as context collection_type collected ~model:finite
        in
        let model =
          match model with
          | Some model -> model
          | None -> unsupported span "a quantifier over `%s`" (Types.show collection_type)
        in
        let matched, inner = pattern_match context inner pattern each element in
        make symbol (sort_of context element)
          (Logic.( &&& )
             (finite_function context finite "contains" Logic.Bool
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
            | Some element_value ->
                let length = sequence_length context element sequence in
                let matched, inner = pattern_match context inner pattern element_value element in
                make ~count:length symbol Int
                  Logic.(
                    Operation ("<=", [ int 0; each ])
                    &&& Operation ("<", [ each; length ])
                    &&& matched)
                  inner
            | None -> unsupported span "a quantifier over `%s`" (Types.show collection_type))
        | None -> unsupported span "a quantifier over `%s`" (Types.show collection_type))
  in
  match binder with
  | Over_type { local; type_; _ } ->
      (* Over every value of a type: each in its range, and meeting its
         type's invariants. *)
      let ty = substituted context frame type_ in
      let inner = bind inner local ty each in
      make symbol (sort_of context ty)
        (Logic.( &&& ) (in_range ty each) (validity context inner ~assuming:true ty each))
        inner
  | Over_range { pattern; start; stop; inclusive } ->
      let _, low = value context frame start in
      let _, high = value context frame stop in
      let _, inner =
        pattern_match context inner pattern each (substituted context frame pattern.type_)
      in
      let premise =
        Logic.(
          Operation ("<=", [ low; each ])
          &&& Operation ((if inclusive then "<=" else "<"), [ each; high ]))
      in
      let count =
        if inclusive then Costs.plus (Costs.minus high low) (Logic.int 1) else Costs.minus high low
      in
      make ~count symbol Int premise inner
  | Over_collection { pattern; collection } ->
      over_collection pattern
        (type_of context frame collection)
        (snd (value context frame collection))
        (at frame collection)
  (* In executable code, the collection is the argument of the [each] call. *)
  | Over_each
      {
        pattern;
        call = { kind = Call { arguments = [ Passed { value = collection; _ } ]; _ }; _ } as call;
      } ->
      over_collection pattern
        (operand_type context frame collection)
        (snd (operand_value context frame collection))
        (at frame call)
  | Over_each { call; _ } -> unsupported (at frame call) "this quantifier's loop"

(* A [USize] generic argument's value: a literal, the frame's
   substitution for a parameter, or else the parameter as an uninterpreted
   constant. *)
and value_term context frame (value : Types.value) =
  match value with
  | Value_parameter parameter -> (
      match List.assoc_opt parameter frame.substitution with
      | Some (Types.Value argument) when argument <> Value_parameter parameter ->
          value_term context frame argument
      | _ -> substituted_value_term context value)
  | Known _ | Value_variable _ -> substituted_value_term context value

(* A value already substituted: a number, or a generic, which is a [USize]
   on every path. *)
and substituted_value_term context (value : Types.value) =
  match value with
  | Known number -> Logic.Integer number
  | Value_parameter parameter ->
      let symbol = Symbol.Generic_value { owner = parameter.owner; name = parameter.name } in
      once context (In_range symbol) (fun () ->
          declare context (Logic.Constant (symbol, Int));
          context.facts <- in_range (Types.builtin USize) (Logic.Symbol symbol) :: context.facts);
      Logic.Symbol symbol
  | Value_variable _ -> raise (Foreign_unsupported "an unsolved size")

(* The value of an intrinsic's [USize] generic argument, by the generic's
   name. *)
and generic_argument context frame (operation : Intrinsic.operation) type_arguments name =
  let generics = (Intrinsic_signatures.signature operation).generics in
  List.find_map
    (fun ((generic : Types.generic), argument) ->
      match argument with
      | Types.Value value when generic.generic.name = name -> Some (value_term context frame value)
      | _ -> None)
    (try List.combine generics type_arguments with Invalid_argument _ -> [])

(* An array's elements: a sequence as long as its type says. *)
and array_model context frame (ty : Types.ty) term =
  match ty with
  | Named { arguments = [ Types.Type element; Types.Value count ]; _ } -> (
      match model_of context ty term ~element with
      | Some sequence ->
          assume context frame
            (Logic.equal
               (sequence_length context element sequence)
               (value_term context frame count));
          sequence
      | None -> raise (Foreign_unsupported (Printf.sprintf "the elements of `%s`" (Types.show ty))))
  | _ -> raise (Foreign_unsupported (Printf.sprintf "the elements of `%s`" (Types.show ty)))

(* Calls *)

(* A call's arguments, as its callee is given them, in its order: each
   written one with its value, and none for a default, which the callee's
   own form holds. Lambdas are proven last, as the type checker checks
   them, so that the [requires] of a callback's type can mention the other
   arguments. *)
and call_arguments ?given context frame (node : expression) (call_ : call) ~facts_for =
  let indexed = List.mapi (fun position argument -> (position, argument)) call_.arguments in
  let is_lambda = function
    | Passed { value = Value { kind = Lambda _; _ }; _ } -> true
    | Passed _ | Default -> false
  in
  let frame, evaluated =
    List.fold_left
      (fun (frame, evaluated) (position, (argument : argument)) ->
        match argument with
        | Passed { mode; value = operand; _ } when not (is_lambda argument) ->
            let type_ = operand_type context frame operand in
            let given = Option.bind given (fun given -> given position) in
            let frame, term, run =
              match (operand, given) with
              | _, Some (term, _, run) -> (frame, term, run)
              | Value ({ kind = Slice { call }; _ } as slice_node), None ->
                  let base, start, stop = slice_parts call in
                  let frame, term, low, high =
                    slice_run context frame slice_node base ~start:(Some start) ~stop
                      ~inclusive:false
                  in
                  (frame, term, Some (low, high))
              | Place (Local _), None ->
                  let frame, term =
                    reading_callback context (fun () -> operand_value context frame operand)
                  in
                  (frame, term, None)
              | _, None ->
                  let frame, term = operand_value context frame operand in
                  (frame, term, None)
            in
            let passed_place =
              match (given, operand) with
              | Some (_, passed_place, _), _ -> passed_place
              | None, Place place -> Some (core_place context place)
              | None, Value _ ->
                  (* A value passed [mut], such as a slice, is read again after
                     the call; where it goes back is its own business. *)
                  Some
                    {
                      read =
                        (fun frame ->
                          snd (operand_value context { frame with checking = false } operand));
                      write = (fun frame _ -> frame);
                    }
            in
            ( frame,
              evaluated
              @ [ { position; mode; operand = Some operand; passed_place; type_; term; run } ] )
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
              _;
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
                passed_place = None;
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

(* A Core place as the place of a [mut] argument. A place the prover cannot
   store into forgets its root. *)
and core_place context place =
  {
    read = (fun frame -> snd (place_value context { frame with checking = false } place));
    write =
      (fun frame term ->
        try store context frame place term
        with Unsupported _ | Foreign_unsupported _ -> havoc_root context frame place);
  }

(* A call. [given] has the value of each argument the caller evaluated
   already, by position, with its place, and the callee's value [callee]. *)
and resolved_call ?lent_final ?given ?callee context frame (node : expression) (call_ : call) =
  let span = at frame node in
  (* A call through a function value gives the value first. *)
  let frame, through =
    match (call_.callee, callee) with
    | Indirect callee, Some term -> (frame, Some (operand_type context frame callee, term, callee))
    | Indirect callee, None ->
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
      | Passed { value = Value argument; _ } -> (
          match unwidened argument with
          | { kind = Function_value _; id; _ } ->
              context.passed_values <- id :: context.passed_values
          | _ -> ())
      | Passed _ | Default -> ())
    call_.arguments;
  let frame, values =
    call_arguments ?given context frame node call_ ~facts_for:(fun position known arguments ->
        callback_facts context frame call_ position known arguments)
  in
  List.iter
    (fun (passed : passed) ->
      match passed.operand with
      | Some (Value argument) -> (
          match unwidened argument with
          | { kind = Function_value { path; _ }; _ } as named -> (
              match
                function_contract ?reading_package:(reading_package context) context.database path
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
     element, through its collection's [lends mut] index. *)
  let havoc_mut frame =
    List.fold_left
      (fun frame (passed : passed) ->
        match (passed.mode, passed.passed_place, passed.operand) with
        | Types.Mut, _, Some (Value { kind = Slice { call }; _ }) -> (
            let base, _, _ = slice_parts call in
            (* The callee changes the elements of the run the slice views,
               and nothing else of its owner: the slice read again after the
               call is a view of the new run, which the callee's
               postconditions are about. *)
            match passed.run with
            | Some (start, stop) -> (
                try sliced_owner_changed context frame base ~start ~stop
                with Unsupported _ | Foreign_unsupported _ -> havoc_root context frame base)
            | None -> havoc_root context frame base)
        | Types.Mut, Some place, _ ->
            place.write frame (arrive context frame "changed" passed.type_)
        | _ -> frame)
      frame values
  in
  let arguments_of (type_arguments : Types.argument list) =
    List.map
      (fun argument ->
        match Types.substitute_argument frame.substitution argument with
        | Types.Type ty -> Types.Type (substituted context frame ty)
        | other -> other)
      type_arguments
  in
  let generics_of path =
    match Interface.Impls.signature context.database path with
    | Some (signature : Types.signature) ->
        List.map (fun (generic : Types.generic) -> generic.generic) signature.generics
    | None -> []
  in
  (* Pairs generic parameters with arguments, leaving out those already
     given, such as an [impl]'s. *)
  let pair parameters arguments ~fixed =
    let parameters =
      List.filter (fun parameter -> not (List.mem_assoc parameter fixed)) parameters
    in
    let rec pair_remaining parameters arguments =
      match (parameters, arguments) with
      | parameter :: parameters, argument :: arguments ->
          (parameter, argument) :: pair_remaining parameters arguments
      | _ -> []
    in
    fixed @ pair_remaining parameters arguments
  in
  (* In a function with a [time] clause, every call must end, and an
     [impl] used where a bound needs one must not reach back here. *)
  if context.terminates && frame.checking then begin
    let ends =
      match call_.callee with
      | Function { path; _ } -> signature_terminates context path
      | Trait_method { evidence = Impl { impl; _ }; name; receiver; _ } ->
          signature_terminates context (Path.Method { owner = impl; name; receiver })
      | Trait_method { trait; name; receiver; evidence = Bound; self_type; _ } -> (
          (* A bound on a type the frame's substitution makes known, as in
             code proven once for each integer type, reaches its [impl]. *)
          let trait =
            {
              trait with
              trait_arguments =
                List.map
                  (function
                    | Types.Type ty -> Types.Type (substituted context frame ty)
                    | argument -> argument)
                  trait.trait_arguments;
            }
          in
          match concrete_impl context trait (substituted context frame self_type) with
          | Some (impl, _)
            when Interface.Impls.signature context.database
                   (Path.Method { owner = impl; name; receiver })
                 <> None ->
              signature_terminates context (Path.Method { owner = impl; name; receiver })
          | _ -> signature_terminates context (Path.Method { owner = trait.trait; name; receiver }))
      | Trait_method { trait; name; receiver; _ } ->
          signature_terminates context (Path.Method { owner = trait.trait; name; receiver })
      | Capability_method { capability; name } ->
          signature_terminates context (Path.Method { owner = capability; name; receiver = Static })
      | Indirect _ -> (
          match through with
          | Some (Types.Function function_type, _, _) -> Types.terminates function_type
          | _ -> false)
      | Intrinsic _ -> true
    in
    if not ends then
      oblige context frame Termination span
        "This call may not end, since its callee has no `time` clause, so neither may this \
         function."
        (Logic.Boolean false);
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
            (Logic.Boolean false))
      (Call_graph.impls_used context.database impls call_.callee)
  end;
  let with_contract ?(substitution_of = fun _ -> []) ?(instance = []) path = function
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
      let substitution = pair (generics_of path) arguments ~fixed:[] in
      with_contract
        ~substitution_of:(fun _ -> substitution)
        ~instance:(List.map argument_key arguments) path
        (function_contract ?reading_package:(reading_package context) context.database path)
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
      | ("minimum_value" | "maximum_value" | "bit_width"), _, []
        when Well_known.is Fixed_width_integer trait.trait && Types.integer_bits self_type <> None
        -> (
          (* A built-in integer type's bounds and bits are numbers, so that
             an obligation that names them stays linear. *)
          match (name, Types.integer_range self_type, Types.integer_bits self_type) with
          | "minimum_value", Some (low, _), _ -> Some (frame, Logic.Integer low)
          | "maximum_value", Some (_, high), _ -> Some (frame, Logic.Integer high)
          | _, _, Some (bits, _) -> Some (frame, Logic.int bits)
          | _ -> None)
      | "equal", _, [ left; right ]
        when Path.equal trait.trait equal_trait && structural context self_type ->
          (* [==] on a type with identity semantics is the solver's
             equality. *)
          Some (frame, Logic.equal left right)
      | "equal", Impl { impl = Derived _; _ }, [ left; right ]
        when Path.equal trait.trait equal_trait ->
          (* A derived [impl] is defined by the rule that derived it. *)
          Some (frame, equal_of context frame self_type left right)
      | _ ->
          (match evidence with
          | (Bound | Dynamic) when name = "from_template" && Path.equal trait.trait template_trait
            ->
              oblige context frame Requires span
                "A call of `from_template` through a bound or `any` cannot see the tag's \
                 `requires` on its template: build the value with a template, where the tag is \
                 known."
                (Logic.Boolean false)
          | _ -> ());
          let trait_path = Path.Method { owner = trait.trait; name; receiver } in
          (* The trait's clauses are about [Self] and the trait's parameters. *)
          let trait_substitution =
            pair (generics_of trait_path) arguments
              ~fixed:(trait_substitution context.database trait self_type)
          in
          let path, own_substitution =
            match evidence with
            | Impl { impl; arguments = impl_arguments } ->
                let impl_substitution =
                  List.map
                    (fun (parameter, argument) ->
                      (parameter, Types.substitute_argument frame.substitution argument))
                    impl_arguments
                in
                let path = Path.Method { owner = impl; name; receiver } in
                (path, pair (generics_of path) arguments ~fixed:impl_substitution)
            | _ -> (trait_path, trait_substitution)
          in
          let substitution_of (part : part) =
            if part.inherited then trait_substitution else own_substitution
          in
          with_contract ~substitution_of
            ~instance:(List.map argument_key (Types.Type self_type :: arguments))
            path
            (method_contract ?reading_package:(reading_package context) context.database trait name
               receiver evidence))
  | Indirect _ ->
      check_callback_requires context frame node through values;
      let frame = havoc_mut frame in
      let frame =
        match through with
        | _ when context.counters = [] -> frame
        | Some (Types.Function function_type, callee_term, _) ->
            spend context frame (function_value_amount context frame function_type callee_term)
        | _ -> spend context frame (unknown_amount context frame)
      in
      let result =
        match through with
        | Some (Types.Function function_type, callee_term, _) when in_the_logic function_type ->
            let term =
              applied context function_type callee_term
                (List.map (fun (passed : passed) -> passed.term) values)
            in
            assume context frame (in_range result_type term);
            term
        | _ -> arrive context frame "result" result_type
      in
      (* A function value meets its type's invariants where it returns, as
         a function does, so its result and the final value of a [mut]
         argument are valid. *)
      assume_valid context frame result_type result;
      List.iter
        (fun (passed : passed) ->
          match (passed.mode, passed.passed_place) with
          | Types.Mut, Some place -> (
              try assume_valid context frame passed.type_ (place.read frame)
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
         when the borrower's final value is written back. *)
      let frame =
        match operation with
        | Storage_at_mut | Array_at_mut | View_at_mut -> frame
        | _ -> havoc_mut frame
      in
      let operands = List.map (fun (passed : passed) -> passed.term) values in
      (* Each argument's value after the call: a [mut] one read again. *)
      let changed =
        List.map
          (fun (passed : passed) ->
            match (passed.mode, passed.passed_place) with
            | Types.Mut, Some place -> (
                try place.read frame with Unsupported _ | Foreign_unsupported _ -> passed.term)
            | _ -> passed.term)
          values
      in
      let types =
        List.filter_map
          (function Types.Type ty -> Some (substituted context frame ty) | _ -> None)
          type_arguments
      in
      let result =
        match (operation, values) with
        | Array_model, [ array ] -> array_model context frame array.type_ array.term
        | Array_take_view, [ array; part; start ] -> (
            match (array.type_, changed) with
            | Named { arguments = Types.Type element :: _; _ }, after :: _ ->
                let before = array_model context frame array.type_ array.term in
                let run = buffer_model context View element part.term in
                oblige context frame Requires (at frame node)
                  (Printf.sprintf "`%s` may not take back a view within the array."
                     (quote frame.source node.origin))
                  Logic.(
                    Operation
                      ( "<=",
                        [
                          Operation ("+", [ start.term; sequence_length context element run ]);
                          sequence_length context element before;
                        ] ));
                run_replaced context frame element ~before
                  ~after:(array_model context frame array.type_ after)
                  ~start:start.term
                  ~stop:(Logic.Operation ("+", [ start.term; sequence_length context element run ]))
                  ~run:(Some run);
                arrive context frame "result" result_type
            | _ -> arrive context frame "result" result_type)
        | Array_view, [ array ] -> (
            (* A view of the array's elements. *)
            match array.type_ with
            | Named { arguments = Types.Type element :: _; _ } ->
                let view = arrive context frame "view" result_type in
                assume context frame
                  (Logic.equal
                     (buffer_model context View element view)
                     (array_model context frame array.type_ array.term));
                view
            | _ -> arrive context frame "view" result_type)
        | Array_at_mut, [ array; index ] -> (
            (* The element at [index], lent [mut] until the lend ends, when the
               borrower's final value is written back to the array. *)
            match array.type_ with
            | Named { arguments = Types.Type element :: _; _ } -> (
                let model = array_model context frame array.type_ array.term in
                oblige context frame Requires (at frame node)
                  (Printf.sprintf "`%s` may not be within the array."
                     (quote frame.source node.origin))
                  Logic.(
                    Operation ("<=", [ int 0; index.term ])
                    &&& Operation ("<", [ index.term; sequence_length context element model ]));
                match sequence_at context element model index.term with
                | Some part -> part
                | None -> arrive context frame "part" result_type)
            | _ -> arrive context frame "part" result_type)
        | Storage_from_array, [ array ] -> (
            (* The array's elements, moved into storage with room for exactly
               them. *)
            match array.type_ with
            | Named { arguments = [ Types.Type element; Types.Value count ]; _ } ->
                let storage = arrive context frame "storage" result_type in
                let elements = buffer_model context Storage element storage in
                let count = value_term context frame count in
                assume context frame
                  Logic.(
                    equal elements (array_model context frame array.type_ array.term)
                    &&& equal (sequence_length context element elements) count
                    &&& equal (buffer_capacity context element storage) count);
                storage
            | _ -> arrive context frame "storage" result_type)
        | Array_from_storage, [ storage ] -> (
            (* The storage's elements, moved into an array, which must be
               exactly as many as the array's count. *)
            match result_type with
            | Named { arguments = [ Types.Type element; Types.Value count ]; _ } ->
                let elements = buffer_model context Storage element storage.term in
                let count = value_term context frame count in
                oblige context frame Requires (at frame node)
                  (Printf.sprintf "`%s` may not have as many elements as the array's count."
                     (quote frame.source node.origin))
                  (Logic.equal (sequence_length context element elements) count);
                let array = arrive context frame "array" result_type in
                assume context frame
                  (Logic.equal (array_model context frame result_type array) elements);
                array
            | _ -> arrive context frame "array" result_type)
        | _ ->
            let arguments =
              List.map
                (fun (passed : passed) ->
                  match passed.operand with Some (Value argument) -> Some argument | _ -> None)
                values
            in
            intrinsic context frame ~node operation types operands ~arguments ~changed result_type
      in
      let frame = spend context frame (step_amount context frame call_ values) in
      Some (frame, result)

(* The result of an intrinsic operation on integers, as the compiler declares
   it. Arithmetic that stops the program on overflow or a zero divisor gives
   the exact result when it returns; wrapping arithmetic gives the exact
   result brought into range by a remainder; the overflow tests, the
   comparisons, and [fits] are exact; and [convert] keeps a value that
   fits. Anything else is known by its type alone. *)
and handle_descriptor context handle =
  let handle_sort = sort_of context (Types.builtin Handle) in
  declare context (Logic.Function (Symbol.Handle_descriptor, [ handle_sort ], Logic.Int));
  Logic.Apply (Symbol.Handle_descriptor, [ handle ])

and intrinsic context frame ~node (operation : Intrinsic.operation) types operands ~arguments
    ~changed result_type =
  let known = arrive context frame "result" result_type in
  match (operation, types) with
  | Shared_update, _ ->
      (* [change]'s result, which is a function value's result: valid. *)
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
      buffer_operation context frame ~node operation (Types.builtin UInt8) operands ~changed known
  | Libc function_, _ -> libc_call context frame ~node function_ operands ~changed known
  | Libc_number number, _ -> libc_number context frame number
  | (System_is_os _ | System_is_architecture _), _ ->
      (* The system a program runs on is one for the whole run, and it is at
         most one operating system and one architecture. *)
      let symbol operation = Symbol.System (Intrinsic.operation_name operation) in
      let kind =
        List.filter
          (fun (other : Intrinsic.operation) ->
            match (operation, other) with
            | System_is_os _, System_is_os _ | System_is_architecture _, System_is_architecture _ ->
                true
            | _ -> false)
          Intrinsic.operations
      in
      List.iter (fun other -> declare context (Logic.Constant (symbol other, Logic.Bool))) kind;
      once context
        (Exclusive (symbol operation))
        (fun () ->
          List.iteri
            (fun index first ->
              List.iteri
                (fun later second ->
                  if later > index then
                    context.facts <-
                      Logic.(not_ (Symbol (symbol first) &&& Symbol (symbol second)))
                      :: context.facts)
                kind)
            kind);
      Logic.Symbol (symbol operation)
  | View_address, element :: _ when scalar_bytes element <> None -> (
      (* A view's elements lie in memory, so they end within the address
         space, and a view with any is not at zero. *)
      match (operands, scalar_bytes element) with
      | [ view ], Some bytes ->
          let length = sequence_length context element (buffer_model context View element view) in
          assume context frame
            Logic.(
              Operation
                ( "<=",
                  [
                    Operation ("+", [ known; Operation ("*", [ int bytes; length ]) ]);
                    Integer (Z.shift_left Z.one 64);
                  ] )
              &&& (Operation (">", [ length; int 0 ]) ==> Operation (">=", [ known; int 1 ])));
          known
      | _ -> known)
  | Environment_entry, _ ->
      (* An entry is a C string without its end, so none of its bytes is
         zero. *)
      let byte = Types.builtin UInt8 in
      let model = buffer_model context View byte known in
      let length = sequence_length context byte model in
      (match sequence_at context byte model (Logic.Symbol (variable "entry.index")) with
      | Some at ->
          assume context frame
            (Logic.Forall
               ( [ (variable "entry.index", Logic.Int) ],
                 Logic.(
                   Operation ("<=", [ int 0; Symbol (variable "entry.index") ])
                   &&& Operation ("<", [ Symbol (variable "entry.index"); length ])
                   ==> not_ (equal at (int 0))) ))
      | None -> ());
      known
  | Handle_from, _ -> (
      (* A handle's descriptor is a function of it, and the one it was made
         from. *)
      match operands with
      | [ descriptor ] ->
          assume context frame (Logic.equal (handle_descriptor context known) descriptor);
          known
      | _ -> known)
  | Handle_descriptor, _ -> (
      match operands with
      | [ handle ] ->
          let descriptor = handle_descriptor context handle in
          assume context frame (in_range (Types.builtin Int32) descriptor);
          descriptor
      | _ -> known)
  | _ ->
      primitive_operation context frame ~node operation types operands ~arguments
        ~fallback:(fun () -> known)

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
          (fun value ->
            if each = 1 then value else Logic.Operation ("*", [ Logic.int each; value ]))
          (value_of by)
    | Exactly elements -> Some (Logic.int elements)
    | Number number -> Some (libc_number context frame number)
    | Through_zero -> None
  in
  let needs requirement condition =
    oblige context frame Requires (at frame node)
      (Printf.sprintf "`%s` may not %s." (quote frame.source node.origin) requirement)
      condition
  in
  let element_of scalar = Types.builtin (Intrinsic.libc_builtin scalar) in
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
            Logic.(
              equal (length element (model after)) (length element (model before))
              &&& equal (capacity after) (capacity before));
          match (passes, count extent) with
          | Room _, counted ->
              assume context frame (Logic.equal (model after) (model before));
              Option.iter
                (fun counted ->
                  needs "have the room it writes into"
                    (Logic.Operation
                       ( "<=",
                         [
                           Logic.Operation ("+", [ length element (model before); counted ]);
                           capacity before;
                         ] )))
                counted
          | _, Some counted ->
              needs "have the elements it changes"
                (Logic.Operation ("<=", [ counted; length element (model before) ]))
          | _, None -> ())
      | Some (Libc.Elements (scalar, extent)), Some view, _ -> (
          let element = element_of scalar in
          let elements = buffer_model context View element view in
          match count extent with
          | Some counted ->
              needs "have the elements it reads"
                (Logic.Operation ("<=", [ counted; length element elements ]))
          | None ->
              let last = Logic.Operation ("-", [ length element elements; Logic.int 1 ]) in
              needs "end with a zero, which it reads up to"
                Logic.(
                  Operation (">=", [ length element elements; int 1 ])
                  &&&
                  match sequence_at context element elements last with
                  | Some last_element -> equal last_element (int 0)
                  | None -> Boolean false))
      | _ -> ())
    arguments;
  (match Option.bind at_most value_of with
  | Some bound ->
      assume context frame
        Logic.(Operation (">=", [ known; int 0 ]) ==> Operation ("<=", [ known; bound ]))
  | None -> ());
  known

(* A number of the system that the C library's headers define, such as
   [PATH_MAX]: one constant, whatever call gives it, so the room a caller
   makes for it and the room a function needs are the same term. *)
and libc_number context frame (number : Libc.number) =
  let symbol = Symbol.Libc_number (Libc.number_name number) in
  declare context (Logic.Constant (symbol, Logic.Int));
  let term = Logic.Symbol symbol in
  assume context frame
    (in_range (Types.builtin (Intrinsic.libc_builtin (Libc.number_type number))) term);
  term

(* Whether a float is a number that, cut toward zero, is in an integer
   type's range. *)
and float_fits target value =
  match bounds target with
  | Some (low, high) ->
      let cut = truncated value in
      Logic.(
        not_ (is_nan value)
        &&& not_ (Operation ("fp.isInfinite", [ value ]))
        &&& Operation ("<=", [ Integer low; cut ])
        &&& Operation ("<=", [ cut; Integer high ]))
  | None -> Logic.Boolean false

(* Lambdas and callbacks *)

(* A lambda is proven where it is written, with fresh arguments that
   satisfy its function type's [requires]; it is proven to terminate
   exactly when its function type has a [time] clause; and it is a value
   about which nothing more is known. *)
and lambda context frame (node : expression) (parameters : pattern list) captures (body : block)
    ~facts =
  (* Inside a quantifier, a lambda that captures none of its bound values is
     one function for every one of them, so it is read outside it. *)
  let captured (capture : capture) =
    match capture.local with Self -> frame.self | local -> Locals.find_opt local frame.locals
  in
  if
    frame.bound <> []
    && List.for_all
         (fun capture ->
           match captured capture with
           | Some term -> not (Logic.mentions frame.bound term)
           | None -> false)
         captures
  then
    (* The bound values stay bound, so a fact about the lambda's arguments
       that names one is still left out. *)
    let _, term =
      read_lambda ~capture_free:true context
        { frame with binders = []; condition = Logic.Boolean true }
        node parameters captures body ~facts
    in
    (frame, term)
  else read_lambda context frame node parameters captures body ~facts

and read_lambda ?(capture_free = false) context frame (node : expression)
    (parameters : pattern list) captures (body : block) ~facts =
  let span = at frame node in
  let ty = type_of context frame node in
  let function_type =
    match ty with Types.Function function_type -> function_type | _ -> unsupported span "a lambda"
  in
  if List.length parameters <> List.length function_type.inputs then
    unsupported span "a lambda with a different number of parameters";
  (* A lambda's body may run any number of times, including none, so it is
     proven under a fresh path condition: its assumptions about its
     arguments and callees hold on no other path. *)
  let called = fresh context frame "called" Logic.Bool in
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
  (* A lambda's costs are counted apart from the enclosing function: the
     cost clauses of its type, and, where the enclosing function counts
     time, its time, to bound [time(f)] for it. *)
  let promised =
    List.filter_map
      (fun (cost : Types.cost) ->
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
            Some (counter, cost.bound)
        | _ -> None)
      function_type.costs
  in
  let time_units = { Costs.resource = Time; counting = Units; amortized = false } in
  let counts_time =
    List.exists
      (fun (counter : Costs.counter) -> counter.resource = Time && counter.counting = Units)
      context.counters
  in
  let times_by_type = List.exists (fun (counter, _) -> counter = time_units) promised in
  (* A call back into the definition around it still assumes its bound. *)
  let saved_counters = context.counters in
  context.counters <-
    distinct_counters
      ((if counts_time then [ time_units ] else [])
      @ List.map fst promised @ loop_counters inside.locals body);
  let inside =
    { inside with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
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
  context.terminates <- Types.terminates function_type;
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
                | Types.Mut, Bind { local; _ } -> (
                    match Locals.find_opt local exit_.locals with
                    | Some term ->
                        check_valid context exit_ span (substituted context frame input) term
                          ~deep:true ~when_:"for a `mut` parameter when this lambda ends"
                    | None -> ())
                | _ -> ())
              parameters function_type.inputs)
          !ended;
        let spent_of (exit_ : frame) counter =
          match List.assoc_opt counter exit_.spent with Some term -> term | None -> Costs.zero
        in
        List.iter
          (fun (exit_ : frame) ->
            List.iter
              (fun (counter, (bound : Types.cost_bound)) ->
                let spent = spent_of exit_ counter in
                let goal =
                  match bound with
                  | Order_of -> Costs.at_most spent (Costs.bound (Logic.int 1))
                  | No_more_than (Some limit) -> Costs.at_most spent (Logic.Integer limit)
                  | Exactly_cost (Some limit) -> Logic.equal spent (Logic.Integer limit)
                  | _ -> Logic.Boolean true
                in
                oblige context exit_ Cost span
                  (Printf.sprintf "This lambda may spend more than its type, `%s`, allows."
                     (Types.show ty))
                  goal)
              promised)
          exits;
        (* A bound on the time of one call in terms of the values the lambda
           does not change, proven only once a cost uses it. *)
        if counts_time && not times_by_type then
          let spent = List.map (fun exit_ -> spent_of exit_ time_units) exits in
          let most =
            match spent with
            | [] -> Costs.zero
            | first :: rest -> List.fold_left Costs.larger first rest
          in
          match
            Costs.bound_on
              ~varies:(mentions_fresh_after context mark)
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
        if in_the_logic function_type then
          add_lambda_facts context frame ~capture_free function_type term ~called ~arguments
            ~start_fresh ~end_fresh ~start_declarations ~premises
            ~shown:(facts_since context facts_mark) ~ended:!ended;
        term
  in
  context.lambda_captures <-
    (term, List.map (fun (capture : capture) -> capture.local) captures) :: context.lambda_captures;
  (match pending with
  | Some pending_time -> context.lambda_times <- (term, pending_time) :: context.lambda_times
  | None -> ());
  (frame, term)

(* The behavior of a lambda whose body is not its definition, for every
   argument: its body ran on arguments that are arbitrary but for
   [premises], so the facts it proved, and the value it ended with on each path, hold for each
   argument the premises admit, since its type promises that it ends, and
   so is called wherever it is applied. Over each argument, each value made in the
   body is a function of the arguments, since it can differ for each. A
   nested lambda's symbol, named after its captures, is not such a
   function, so a body with one gives nothing. *)
and add_lambda_facts context frame ~capture_free function_type term ~called ~arguments ~start_fresh
    ~end_fresh ~start_declarations ~premises ~shown ~ended =
  let declared_here =
    List.filteri
      (fun index _ -> index < List.length context.declarations - start_declarations)
      context.declarations
  in
  (* A functional lambda inside is named after its captures, so where
     a capture is something the body made, the arguments among them, its symbol
     is renamed, as a value the body made is, to a function of the
     arguments. *)
  let captures_fresh = function
    | Symbol.Lambda _ as name when not (Hashtbl.mem context.fresh_order name) -> (
        match Hashtbl.find_opt context.lambda_definitions name with
        | Some defined -> mentions_fresh_after context start_fresh defined
        | None -> false)
    | _ -> false
  in
  begin
    let parameters =
      List.mapi
        (fun index (_, input) ->
          (variable "lambda.argument" ~numbers:[ index ], sort_of context input))
        function_type.Types.inputs
    in
    let variables = List.map (fun (name, _) -> Logic.Symbol name) parameters in
    let renamed = Hashtbl.create 16 in
    (match called with
    | Logic.Symbol name -> Hashtbl.replace renamed name (Logic.Boolean true)
    | _ -> ());
    List.iter2
      (fun argument variable ->
        match argument with Logic.Symbol name -> Hashtbl.replace renamed name variable | _ -> ())
      arguments variables;
    (* Inside a quantifier, a value made in the body is a function of its
       bound values, and becomes one of those and the arguments. *)
    let functions = Hashtbl.create 8 in
    List.iter
      (function
        | Logic.Constant (name, sort) when not (Hashtbl.mem renamed name) ->
            let is_fresh_in_body =
              match Hashtbl.find_opt context.fresh_order name with
              | Some order -> order > start_fresh && order <= end_fresh
              | None -> captures_fresh name
            in
            if is_fresh_in_body then begin
              let over = Symbol.Over name in
              declare context (Logic.Function (over, List.map snd parameters, sort));
              Hashtbl.replace renamed name (Logic.Apply (over, variables))
            end
        | Logic.Function (name, inputs, sort) when frame.binders <> [] -> (
            match Hashtbl.find_opt context.fresh_order name with
            | Some order when order > start_fresh && order <= end_fresh ->
                let over = Symbol.Over name in
                declare context (Logic.Function (over, inputs @ List.map snd parameters, sort));
                Hashtbl.replace functions name over
            | _ -> ())
        | _ -> ())
      declared_here;
    let rec over = function
      | Logic.Symbol name as symbol -> Option.value (Hashtbl.find_opt renamed name) ~default:symbol
      | (Logic.Integer _ | Logic.Boolean _ | Logic.Bits _) as term -> term
      | Logic.Apply (name, _)
        when match called with Logic.Apply (called_name, _) -> called_name = name | _ -> false ->
          Logic.Boolean true
      | Logic.Apply (name, arguments) when Hashtbl.mem functions name ->
          Logic.Apply (Hashtbl.find functions name, List.map over arguments @ variables)
      | (Logic.Apply _ | Logic.Operation _ | Logic.Is _) as term -> Logic.map_arguments over term
      | Logic.Forall (bound, body) -> Logic.Forall (bound, over body)
      | Logic.Exists (bound, body) -> Logic.Exists (bound, over body)
    in
    let premise = over (Logic.conjunction premises) in
    let applied_here = applied context function_type term variables in
    let statements =
      List.map over shown
      @ List.filter_map
          (fun ((exit_ : frame), value) ->
            Option.map
              (fun value ->
                Logic.( ==> ) (over exit_.condition) (Logic.equal applied_here (over value)))
              value)
          ended
    in
    (* A lambda that captures a quantifier's bound values states its behavior
       for each of them, closed over the quantifier. *)
    List.iter
      (fun statement ->
        let stated = Logic.Forall (parameters, Logic.( ==> ) premise statement) in
        if frame.bound = [] || capture_free then context.facts <- stated :: context.facts
        else
          match closed_over_binders frame stated with
          | Some closed -> context.facts <- closed :: context.facts
          | None -> ())
      statements
  end

(* A clause's value: a specification, which never runs, so it spends
   nothing whatever it calls. *)
and clause_value context frame (clause : expression) =
  without_costs context (fun () -> value context frame clause)

(* Reading code that never runs, as a specification, which spends nothing. *)
and without_costs : 'a. _ -> (unit -> 'a) -> 'a =
 fun context read ->
  let saved = context.counters in
  context.counters <- [];
  Fun.protect ~finally:(fun () -> context.counters <- saved) read

(* A lambda whose body is functional, as a function in the logic: applied,
   it is its body. Lambdas with the same body over the same captured values
   are the same function, so a bound and a loop's bound that both write
   [(row) => row.length()] mean the same sum. A body whose value needs a
   fresh symbol, or that the prover cannot read, gives no definition. *)
and lambda_definition context frame (function_type : Types.function_type) parameters (body : block)
    =
  if not (in_the_logic function_type && is_functional_block body) then None
  else
    let bound = parameters_of context frame function_type in
    let defined =
      body_over context frame bound body (fun inside ->
          List.fold_left2
            (fun inside (pattern : pattern) ((name, _), (_, input)) ->
              snd
                (pattern_match context inside pattern (Logic.Symbol name)
                   (substituted context frame input)))
            inside parameters
            (List.combine bound function_type.inputs))
    in
    match defined with
    | Some defined ->
        let defined = canonical_binders defined in
        (* The same body is the same function wherever it is written, so its
           parameters are named by position alone in its symbol. *)
        let named_by_position =
          List.fold_left
            (fun term (index, (name, _)) ->
              Logic.replace ~from:(Logic.Symbol name)
                ~into:(Logic.Symbol (variable "parameter" ~numbers:[ index ]))
                term)
            defined
            (List.mapi (fun index parameter -> (index, parameter)) bound)
        in
        let symbol = Symbol.Lambda { sorts = List.map snd bound; definition = named_by_position } in
        let sort = sort_of context (Types.Function function_type) in
        (* A lambda that captures a quantifier's bound symbol is a function
           of it. *)
        let term =
          if Logic.mentions frame.bound defined then value_symbol context frame symbol sort
          else value_symbol context { frame with binders = [] } symbol sort
        in
        let application =
          applied context function_type term (List.map (fun (name, _) -> Logic.Symbol name) bound)
        in
        Hashtbl.replace context.lambda_definitions symbol defined;
        fact context frame (Logic.Forall (bound, Logic.equal application defined));
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
            | Logic.Boolean true -> ()
            | range ->
                (* For arguments of the parameters' types, which the body
                   was read with. *)
                let arguments_in_range =
                  Logic.conjunction
                    (List.map2
                       (fun (name, _) (_, input) ->
                         in_range (substituted context frame input) (Logic.Symbol name))
                       bound function_type.inputs)
                in
                fact context frame (Logic.Forall (bound, Logic.( ==> ) arguments_in_range range)))
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
        | Some (_, defined) when not (mentions_fresh_after context mark defined) -> Some defined
        | _ -> None
      with Unsupported _ | Foreign_unsupported _ -> None)

(* A symbol for a term that holds a pure call, named by the term, and
   equal to it. *)
and named_term context ty term =
  let rec holds_call = function
    | Logic.Apply (Symbol.Function _, _) -> true
    | Logic.Forall (_, body) | Logic.Exists (_, body) -> holds_call body
    | term -> List.exists holds_call (Logic.arguments term)
  in
  if not (holds_call term) then term
  else
    let symbol = Symbol.Argument term in
    let named = Logic.Symbol symbol in
    once context (Value_of symbol) (fun () ->
        declare context (Logic.Constant (symbol, sort_of context ty));
        context.facts <- Logic.equal named term :: context.facts);
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
    self_type = Option.map (fun (_, ty) -> Types.substitute substitution ty) self;
    result = None;
    checking = false;
    loop = None;
    updating = None;
    substitution;
  }

(* A callee's promise to the lambda passed for one parameter: that
   parameter's [requires], read in the callee with the call's other
   arguments, and the lambda's arguments for the inputs it names. *)
and callback_facts context frame (call_ : call) position known arguments =
  match call_.callee with
  | Function { path; type_arguments } -> (
      match
        Option.bind
          (source_at ?reading_package:(reading_package context) context.database path)
          (fun (callee, _, _) -> part_of callee)
      with
      | Some part -> (
          match List.nth_opt part.parameters position with
          | Some { callback_contract = Some { inputs; requires }; _ }
            when List.length inputs = List.length arguments ->
              let substitution =
                match Interface.Impls.signature context.database path with
                | Some (signature : Types.signature) ->
                    callee_substitution frame signature type_arguments
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
          (* The [requires] is read with the callback's parameters bound to
             this call's arguments. *)
          let inside =
            callback_contract_frame frame inputs
              (List.map (fun (passed : passed) -> passed.term) values)
          in
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

(* The [impl] of a trait for a known type, with its generic parameters'
   instantiation there: one written or derived, whose parameters' bounds hold
   under the bounds of the definition proven, or the definition's own
   [impl]. The [impl] is of the trait with these arguments, so a type with
   an [impl] of [Scale[Int64]] and one of [Scale[Bool]] reaches each by its
   own. *)
and concrete_impl context (trait : Types.trait_reference) (ty : Types.ty) =
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
                    List.map
                      (fun (generic : Types.generic) -> generic.generic)
                      interface.impl_generics
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
  fun parameter -> Types.bounds_of generics parameter

(* A trait's laws, and those of the traits it requires, as facts about a
   type, each quantified over its parameters. A law is shown for each
   [impl] written by hand, by the [impl], so it is a fact wherever the
   trait's methods are used. *)
and assume_laws context frame ~at (trait : Types.trait_reference) (ty : Types.ty) =
  let key = laws_key trait ty in
  if not (List.mem key context.laws_assumed) then begin
    context.laws_assumed <- key :: context.laws_assumed;
    List.iter
      (fun path ->
        let required =
          if Path.equal path trait.trait then trait
          else { Types.trait = path; trait_arguments = []; associated = [] }
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

and laws_key (trait : Types.trait_reference) ty = Types.show_trait trait ^ " for " ^ type_key ty

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
    (fun (parameter : Core.parameter) -> Types.substitute substitution parameter.type_)
    law.parameters

and law_fact context frame source ~substitution (law : law) =
  let types = law_parameter_types ~substitution law in
  if List.exists (fun ty -> Types.is_error ty) types then None
  else begin
    context.fresh <- context.fresh + 1;
    let symbols =
      List.mapi
        (fun index _ -> Symbol.Variable { label = "law"; numbers = [ context.fresh; index ] })
        types
    in
    let inside =
      law_frame
        { frame with bound = symbols @ frame.bound }
        source ~substitution law
        (List.map (fun symbol -> Logic.Symbol symbol) symbols)
    in
    try
      let premise =
        Logic.conjunction
          (List.map (fun clause -> snd (clause_value context inside clause)) law.requires)
      in
      let range =
        Logic.conjunction
          (List.map2 (fun symbol ty -> in_range ty (Logic.Symbol symbol)) symbols types)
      in
      match without_costs context (fun () -> block_value context inside law.body) with
      | Some (_, holds) ->
          Some
            (Logic.Forall
               ( List.map2 (fun symbol ty -> (symbol, sort_of context ty)) symbols types,
                 Logic.( ==> ) (Logic.( &&& ) range premise) holds ))
      | None -> None
    with Unsupported _ | Foreign_unsupported _ -> None
  end

(* Sequences of handed-out parts, through the same functions in the
   logic that the contracts of [standard::specification] are about. *)
and sequence_path : Path.t = Well_known.path Sequence
and sequence_type element = Types.Named { path = sequence_path; arguments = [ Types.Type element ] }

and sequence_length context element term =
  let path = Path.Method { owner = sequence_path; name = "length"; receiver = Read } in
  let symbol = Symbol.Function { callee = path; instance = [ type_key element ] } in
  declare context (Logic.Function (symbol, [ sort_of context (sequence_type element) ], Logic.Int));
  Logic.Apply (symbol, [ term ])

(* A sequence's sum, by [standard::specification]'s [Sequence.sum], over a
   measure of its elements. *)
and sequence_sum context element term measure =
  let path = Path.Method { owner = sequence_path; name = "sum"; receiver = Read } in
  let symbol = Symbol.Function { callee = path; instance = [ type_key element ] } in
  declare context
    (Logic.Function
       ( symbol,
         [
           sort_of context (sequence_type element);
           sort_of context (Types.Function (measure_type element));
         ],
         Logic.Int ));
  Logic.Apply (symbol, [ term; measure ])

(* The type of a sum's measure: [fn(Element) -> Integer cost time finite]. *)
and measure_type element : Types.function_type =
  {
    inputs = [ (Types.Read, element) ];
    output = Returns Types.Integer;
    uses = Types.no_capabilities;
    costs = [ { amortized = false; resource = Types.Time; bound = Finite_cost } ];
  }

(* [sequence_at], for a sequence whose elements the prover reads. *)
and element_at context element term index =
  match sequence_at context element term index with
  | Some term -> term
  | None -> raise (Foreign_unsupported "the elements of a sequence")

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
      let symbol = Symbol.Function { callee = path; instance = [ type_key sequence ] } in
      declare context
        (Logic.Function (symbol, [ sort_of context sequence; Logic.Int ], sort_of context element));
      let at sequence index = Logic.Apply (symbol, [ sequence; index ]) in
      (* An element of a sequence of parts is below the sequence, as a
         field is below its value, so recursion on an element ends. *)
      if context.ranking && constructors context element <> None then
        once context
          (Ranked_elements (type_key sequence))
          (fun () ->
            let each = Symbol.Variable { label = "ranked.sequence"; numbers = [] }
            and index = Symbol.Variable { label = "ranked.index"; numbers = [] } in
            let ranked = Logic.Symbol each and position = Logic.Symbol index in
            let below = rank context element (at ranked position) in
            context.facts <-
              Logic.Forall
                ( [ (each, sort_of context sequence); (index, Logic.Int) ],
                  Logic.(
                    Operation ("<=", [ int 0; position ])
                    &&& Operation ("<", [ position; sequence_length context element ranked ])
                    ==> (Operation ("<=", [ int 0; below ])
                        &&& Operation ("<", [ below; rank context sequence ranked ]))) )
              :: context.facts);
      Some (at term index)
  | [] -> None

(* Two sequences with the same length and the same elements are identical:
   the one fact about sequences their contracts cannot state, since a
   contract describes a result. It is stated for each two that are
   compared, which keeps the solver from comparing every two it knows. *)
and extensional context frame (ty : Types.ty) left right =
  match ty with
  | Named { path; arguments = [ Types.Type element ] } when Path.equal path sequence_path -> (
      let index = fresh_name context "index" in
      match
        ( sequence_at context element left (Logic.Symbol index),
          sequence_at context element right (Logic.Symbol index) )
      with
      | Some at_a, Some at_b ->
          let length = sequence_length context element in
          fact context frame
            Logic.(
              equal (length left) (length right)
              &&& Forall
                    ( [ (index, Int) ],
                      Operation ("<=", [ int 0; Symbol index ])
                      &&& Operation ("<", [ Symbol index; length left ])
                      ==> equal at_a at_b )
              ==> equal left right)
      | _ -> ())
  | Named { path; arguments }
    when Path.equal path finite_set_path || Path.equal path finite_map_path -> (
      (* A set by its elements, and a map by its keys and their values. *)
      let finite_map = Path.equal path finite_map_path in
      match arguments with
      | Types.Type key :: rest ->
          let each = fresh_name context "key" in
          let function_ name output inputs = finite_function context ty name output inputs in
          let key_sort = sort_of context key in
          let has =
            function_
              (if finite_map then "contains_key" else "contains")
              Logic.Bool
              [ (Logic.Symbol each, key_sort) ]
          in
          let same =
            if finite_map then
              match rest with
              | [ Types.Type value_type ] ->
                  let get =
                    function_ "get" (sort_of context value_type) [ (Logic.Symbol each, key_sort) ]
                  in
                  Logic.(
                    equal (has left) (has right) &&& (has left ==> equal (get left) (get right)))
              | _ -> Logic.equal (has left) (has right)
            else Logic.equal (has left) (has right)
          in
          fact context frame
            Logic.(
              Forall ([ (each, key_sort) ], in_range key (Symbol each) ==> same)
              ==> equal left right)
      | _ -> ())
  | _ -> ()

(* A method of a [FiniteSet] or a [FiniteMap], as a function in the logic,
   applied to a value of it and the inputs given with their sorts. *)
and finite_function context (ty : Types.ty) name output inputs =
  match ty with
  | Named { path; arguments } ->
      let symbol =
        Symbol.Function
          {
            callee = Path.Method { owner = path; name; receiver = Read };
            instance = List.map argument_key arguments;
          }
      in
      declare context (Logic.Function (symbol, sort_of context ty :: List.map snd inputs, output));
      fun term -> Logic.Apply (symbol, term :: List.map fst inputs)
  | _ -> fun term -> term

and finite_set_path : Path.t = Well_known.path Finite_set
and finite_map_path : Path.t = Well_known.path Finite_map

(* An array, a [Sequence], or a [FiniteSet] written out: a value whose
   model has the elements in order, or whose set has them. None of them
   allocates: an array is built in place, and the others are only in
   specifications. *)
(* A literal of a sequence or a set. [given], where the MIR evaluated them,
   is its items' values. *)
and list_literal ?given context frame (node : expression) items =
  let ty = type_of context frame node in
  let span = at frame node in
  let frame, values =
    match given with
    | Some values -> (frame, values)
    | None ->
        List.fold_left
          (fun (frame, values) item ->
            let frame, term = value context frame item in
            (frame, values @ [ term ]))
          (frame, []) items
  in
  let element =
    match ty with
    | Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> unsupported span "a literal of `%s`" (Types.show ty)
  in
  let literal =
    match sequence_of context frame ty ~element values with
    | Some literal -> literal
    | None -> (
        match set_of context frame ty ~element values with
        | Some literal -> literal
        | None -> unsupported span "a literal of `%s`" (Types.show ty))
  in
  (frame, literal)

(* A slice, [items[a..b]]: a view of the elements from [a] to before [b],
   which must be within the collection, whose model is that run of the
   collection's model. *)
and slice context frame (node : expression) base ~start ~stop ~inclusive =
  let frame, viewed, _, _ = slice_run context frame node base ~start ~stop ~inclusive in
  (frame, viewed)

(* A slice, with its bounds as they were evaluated. [given], where the MIR
   evaluated them, is the collection's type and value, the start, and the
   stop, if any. *)
and slice_run ?given context frame (node : expression) base ~start ~stop ~inclusive =
  let span = at frame node in
  let base_type =
    match given with
    | Some (base_type, _, _, _) -> base_type
    | None -> place_type context frame base
  in
  let element =
    match base_type with
    | Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> unsupported span "a slice of `%s`" (Types.show base_type)
  in
  let frame, collection =
    match given with
    | Some (_, collection, _, _) -> (frame, collection)
    | None -> place_value context frame base
  in
  let model =
    match model_of context base_type collection ~element with
    | Some model -> model
    | None -> unsupported span "a slice of `%s`" (Types.show base_type)
  in
  let length = sequence_length context element model in
  let frame, low =
    match (given, start) with
    | Some (_, _, low, _), _ -> (frame, low)
    | None, Some start -> value context frame start
    | None, None -> (frame, Logic.int 0)
  in
  let frame, high =
    let bounded frame high = (frame, if inclusive then Costs.plus high (Logic.int 1) else high) in
    match (given, stop) with
    | Some (_, _, _, Some high), _ -> bounded frame high
    | None, Some stop ->
        let frame, high = value context frame stop in
        bounded frame high
    | Some (_, _, _, None), _ | None, None ->
        assume context frame (Operation ("<=", [ Logic.int 0; length ]));
        (frame, length)
  in
  oblige context frame Requires span
    (Printf.sprintf "`%s` may not be within the collection." (quote frame.source node.origin))
    Logic.(
      Operation ("<=", [ int 0; low ])
      &&& Operation ("<=", [ low; high ])
      &&& Operation ("<=", [ high; length ]));
  note_place context frame node (Run (low, high));
  let slice_type = type_of context frame node in
  let viewed = arrive context frame "slice" slice_type in
  (match model_of context slice_type viewed ~element with
  | Some viewed_model -> (
      let count = Costs.minus high low in
      assume context frame (Logic.equal (sequence_length context element viewed_model) count);
      let position = fresh_name context "index" in
      match
        ( sequence_at context element viewed_model (Logic.Symbol position),
          sequence_at context element model (Costs.plus low (Logic.Symbol position)) )
      with
      | Some inside, Some outside ->
          assume context frame
            (Logic.Forall
               ( [ (position, Logic.Int) ],
                 Logic.(
                   Operation ("<=", [ int 0; Symbol position ])
                   &&& Operation ("<", [ Symbol position; count ])
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
(* A tagged template. [given], where the MIR evaluated it, is the
   template's value. *)
and tagged_template ?given context frame (node : expression) texts (template_call : expression) =
  let span = at frame node in
  let tag_type = type_of context frame node in
  match template_call.kind with
  | Call
      {
        callee = Trait_method { trait; name; receiver; evidence = Impl { impl; _ } as evidence; _ };
        arguments = [ Passed { value = template; _ } ];
        _;
      } -> (
      let path = Path.Method { owner = impl; name; receiver } in
      match
        method_contract ?reading_package:(reading_package context) context.database trait name
          receiver evidence
      with
      | Some contract ->
          let frame, value_ =
            match given with
            | Some value_ -> (frame, value_)
            | None -> operand_value context frame template
          in
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

and sequence_of context frame (ty : Types.ty) ~element values =
  let literal = arrive context frame "literal" ty in
  let sequence =
    match ty with
    | Named { path; _ } when Path.equal path sequence_path -> Some literal
    | Named { path; _ } when Intrinsic.builtin_of_path path = Some Array ->
        model_of context ty literal ~element
    | _ -> None
  in
  Option.map
    (fun sequence ->
      assume_valid context frame ty literal;
      assume context frame
        (Logic.equal (sequence_length context element sequence) (Logic.int (List.length values)));
      List.iteri
        (fun index item ->
          match sequence_at context element sequence (Logic.int index) with
          | Some at -> assume context frame (Logic.equal at item)
          | None -> ())
        values;
      literal)
    sequence

(* A [Set] or a [FiniteSet] of these elements: one that contains each of
   them and nothing else, so no more of them than were written. *)
and set_of context frame (ty : Types.ty) ~element values =
  let finite = Types.Named { path = finite_set_path; arguments = [ Types.Type element ] } in
  let literal = arrive context frame "literal" ty in
  let model =
    match ty with
    | Named { path; _ } when Path.equal path finite_set_path -> Some literal
    | _ -> None
  in
  Option.map
    (fun model ->
      assume_valid context frame ty literal;
      let element_sort = sort_of context element in
      let contains value =
        finite_function context finite "contains" Logic.Bool [ (value, element_sort) ] model
      in
      List.iter (fun value -> assume context frame (contains value)) values;
      only_members context frame "value" element_sort contains values;
      let size = finite_function context finite "size" Logic.Int [] model in
      assume context frame (Costs.at_most size (Logic.int (List.length values)));
      literal)
    model

(* That [contains] holds of nothing but [members]: a literal set's
   elements, or a literal map's keys. *)
and only_members context frame label sort contains members =
  let each = fresh_name context label in
  assume context frame
    (Logic.Forall
       ( [ (each, sort) ],
         Logic.( ==> ) (contains (Logic.Symbol each))
           (Logic.disjunction (List.map (Logic.equal (Logic.Symbol each)) members)) ))

(* A specification's [FiniteMap] written out: each key with its value, and
   no other keys. Its keys must be distinct. *)
and map_literal context frame (node : expression) entries =
  let ty = type_of context frame node in
  let key_type, value_type =
    match ty with
    | Named { arguments = [ Types.Type key; Types.Type value_type ]; _ } -> (key, value_type)
    | _ -> unsupported (at frame node) "a literal of `%s`" (Types.show ty)
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
              (Logic.not_ (equal_of context frame key_type key_term other_term)))
        terms)
    terms;
  let finite =
    Types.Named
      { path = finite_map_path; arguments = [ Types.Type key_type; Types.Type value_type ] }
  in
  let literal = arrive context frame "literal" ty in
  let model =
    match ty with
    | Named { path; _ } when Path.equal path finite_map_path -> literal
    | _ -> unsupported (at frame node) "a literal of `%s`" (Types.show ty)
  in
  assume_valid context frame ty literal;
  let key_sort = sort_of context key_type in
  let has key =
    finite_function context finite "contains_key" Logic.Bool [ (key, key_sort) ] model
  in
  let get key =
    finite_function context finite "get" (sort_of context value_type) [ (key, key_sort) ] model
  in
  List.iter
    (fun (_, key, entry) -> assume context frame Logic.(has key &&& equal (get key) entry))
    terms;
  only_members context frame "key" key_sort has (List.map (fun (_, key, _) -> key) terms);
  assume context frame
    (Logic.equal
       (finite_function context finite "size" Logic.Int [] model)
       (Logic.int (List.length terms)));
  (frame, literal)

(* Text as a value whose model is its UTF-8 bytes. A literal is one value
   for its text and type, so two literals with the same text are the same
   value, as a key written twice is the same key. *)
and text_value context frame (ty : Types.ty) text =
  let symbol = Symbol.Literal { type_key = type_key ty; text } in
  let literal = Logic.Symbol symbol in
  once context (Value_of symbol) (fun () ->
      declare context (Logic.Constant (symbol, sort_of context ty));
      assume_valid context
        { frame with condition = Logic.Boolean true; bound = []; binders = [] }
        ty literal;
      let byte = Types.builtin UInt8 in
      let holds model =
        context.facts <-
          Logic.equal (sequence_length context byte model) (Logic.int (String.length text))
          :: context.facts;
        String.iteri
          (fun index character ->
            match sequence_at context byte model (Logic.int index) with
            | Some at ->
                context.facts <- Logic.equal at (Logic.int (Char.code character)) :: context.facts
            | None -> ())
          text
      in
      Option.iter holds (model_of context ty literal ~element:byte);
      (* Where its field is seen, the text is also its storage's, from
         which its potential is read. *)
      match constructors context ty with
      | Some [ (None, [ (field, Named { path; arguments = [ Types.Type element ] }) ]) ]
        when Intrinsic.builtin_of_path path = Some Storage && Types.equal element byte ->
          holds
            (buffer_model context Storage byte
               (Logic.Apply (selector_name ty None field, [ literal ])))
      | _ -> ());
  literal

(* A value's model, by the standard library's [impl] of [Model] for its
   type, as a call of [model()] would read it. *)
and model_of context (ty : Types.ty) term ~element =
  model_as context ty term ~model:(sequence_type element)

(* A value's model of the given type, by the standard library's [impl] of
   [Model] for its type, as a call of [model()] would read it. *)
and model_as context (ty : Types.ty) term ~(model : Types.ty) =
  Option.map (fun model_of -> model_of term) (model_function context ty ~model)

(* A type's [model()], as a function of its values, if the standard library
   gives it one. *)
and model_function context (ty : Types.ty) ~(model : Types.ty) =
  let key = type_key ty ^ " " ^ type_key model in
  match Hashtbl.find_opt context.models key with
  | Some model_fn -> model_fn
  | None ->
      let model_fn = find_model_function context ty ~model in
      Hashtbl.replace context.models key model_fn;
      model_fn

and find_model_function context (ty : Types.ty) ~(model : Types.ty) =
  let model_trait = Well_known.path Model in
  match
    Call_graph.impls_for
      (Query.demand context.database Call_graph.package_impls Path.standard_package)
      [ model_trait ] ty
  with
  | impl :: _ ->
      let path = Path.Method { owner = impl; name = "model"; receiver = Read } in
      let symbol = Symbol.Function { callee = path; instance = [ type_key ty ] } in
      declare context (Logic.Function (symbol, [ sort_of context ty ], sort_of context model));
      model_ranked context ty ~model symbol;
      (* An array's model is its elements, as many as its type says. *)
      (match ty with
      | Named { path; arguments = [ Types.Type element; Types.Value count ] }
        when Intrinsic.builtin_of_path path = Some Array ->
          once context (Array_length symbol) (fun () ->
              let each = Symbol.Variable { label = "array.value"; numbers = [] } in
              let elements = Logic.Apply (symbol, [ Logic.Symbol each ]) in
              context.facts <-
                Logic.Forall
                  ( [ (each, sort_of context ty) ],
                    Logic.equal
                      (sequence_length context element elements)
                      (substituted_value_term context count) )
                :: context.facts)
      | _ -> ());
      Some (fun term -> Logic.Apply (symbol, [ term ]))
  | [] -> None

(* A value's model is no higher in the order of parts than the value, so
   an element of a list's model is below the list. [symbol] is the model's
   function. *)
and model_ranked context (ty : Types.ty) ~(model : Types.ty) symbol =
  if context.ranking then
    once context (Ranked_model symbol) (fun () ->
        let each = Symbol.Variable { label = "ranked.value"; numbers = [] } in
        context.facts <-
          Logic.Forall
            ( [ (each, sort_of context ty) ],
              Logic.Operation
                ( "<=",
                  [
                    rank context model (Logic.Apply (symbol, [ Logic.Symbol each ]));
                    rank context ty (Logic.Symbol each);
                  ] ) )
          :: context.facts)

(* Cursors. A cursor carries its yielded parts and whether it has
   ended as ghost parts of its value. *)
and cursor_trait : Path.t = Well_known.path Cursor

and cursor_yielded context cursor_type element cursor =
  let sort = sort_of context cursor_type in
  let symbol = Symbol.Cursor_yielded (type_key cursor_type) in
  declare context (Logic.Function (symbol, [ sort ], sort_of context (sequence_type element)));
  Logic.Apply (symbol, [ cursor ])

and cursor_ended context cursor_type cursor =
  let symbol = Symbol.Cursor_ended (type_key cursor_type) in
  declare context (Logic.Function (symbol, [ sort_of context cursor_type ], Logic.Bool));
  Logic.Apply (symbol, [ cursor ])

(* A pull: [Some] of a part that meets the method's clauses for each part,
   after which the cursor has handed it out too and the method's other
   clauses hold, as where it may stop; or [None], once the method has
   ended, after which its other clauses hold with [finished] true. The
   cursor that is left is a new value, from the same call. *)
and pull context frame (cursor_method : cursor) cursor ~cursor_type =
  let element = cursor_method.element in
  let option_type = Types.Named { path = option_path; arguments = [ Types.Type element ] } in
  ignore (sort_of context option_type);
  let later = arrive context frame "cursor" cursor_type in
  context.cursors <- (later, cursor_method) :: context.cursors;
  let pulled = arrive context frame "pulled" option_type in
  let some = Logic.Is (constructor_name option_type (Some "Some"), pulled) in
  let part = Logic.Apply (selector_name option_type (Some "Some") "value", [ pulled ]) in
  let before = cursor_yielded context cursor_type element cursor in
  let clauses (at : frame) ~each ~result ~yielded ~finished =
    let inside =
      {
        cursor_method.method_frame with
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
      cursor_method.own.ensures
  in
  assume context frame (Logic.( ==> ) (cursor_ended context cursor_type cursor) (Logic.not_ some));
  let handed = restrict frame some in
  assume_valid context handed element part;
  clauses handed ~each:true ~result:(Some part) ~yielded:before ~finished:None;
  let through = appended context handed element before part in
  assume context handed
    Logic.(
      equal (cursor_yielded context cursor_type element later) through
      &&& not_ (cursor_ended context cursor_type later));
  clauses handed ~each:false ~result:None ~yielded:through ~finished:(Some (Logic.Boolean false));
  let none = restrict frame (Logic.not_ some) in
  assume context none
    Logic.(
      equal (cursor_yielded context cursor_type element later) before
      &&& cursor_ended context cursor_type later);
  clauses none ~each:false ~result:None ~yielded:before ~finished:(Some (Logic.Boolean true));
  (pulled, later)

and option_path : Path.t = Well_known.path Option

(* A sequence of parts with nothing in it. *)
and empty_parts context frame element =
  let parts = fresh context frame "parts" (sort_of context (sequence_type element)) in
  assume context frame (Logic.equal (sequence_length context element parts) (Logic.int 0));
  parts

(* A sequence of parts about which only its length is known. *)
and some_parts context frame element =
  let parts = fresh context frame "parts" (sort_of context (sequence_type element)) in
  assume context frame Logic.(Operation (">=", [ sequence_length context element parts; int 0 ]));
  parts

(* The parts, with one more after them. *)
and appended context frame element parts part =
  let longer = fresh context frame "parts" (sort_of context (sequence_type element)) in
  let length = sequence_length context element parts in
  assume context frame
    Logic.(
      Operation (">=", [ length; int 0 ])
      &&& equal (sequence_length context element longer) (Operation ("+", [ length; int 1 ])));
  (match (sequence_at context element longer length, frame.bound) with
  | Some last, _ -> assume context frame (Logic.equal last part)
  | None, _ -> ());
  let index = fresh_name context "index" in
  (match
     ( sequence_at context element longer (Logic.Symbol index),
       sequence_at context element parts (Logic.Symbol index) )
   with
  | Some after, Some before ->
      assume context frame
        (Logic.Forall
           ( [ (index, Logic.Int) ],
             Logic.(
               Operation ("<=", [ int 0; Symbol index ])
               &&& Operation ("<", [ Symbol index; length ])
               ==> equal after before) ))
  | _ -> ());
  (* Each sum over the longer sequence adds the new part's measure, as
     [Sequence.append]'s contract says. *)
  let measure = fresh_name context "measure" in
  assume context frame
    (Logic.Forall
       ( [ (measure, sort_of context (Types.Function (measure_type element))) ],
         Logic.equal
           (sequence_sum context element longer (Logic.Symbol measure))
           (Logic.Operation
              ( "+",
                [
                  sequence_sum context element parts (Logic.Symbol measure);
                  applied context (measure_type element) (Logic.Symbol measure) [ part ];
                ] )) ));
  longer

(* Whether a clause mentions [result], so that it holds at each [yield]
   of a lending or yielding method, rather than where the method ends. *)
and mentions_result clause =
  Core_walk.expression_exists
    ~expression:(fun (node : expression) -> match node.kind with Result -> true | _ -> false)
    clause

and signature_terminates context path =
  match Interface.Impls.signature context.database path with
  | Some (signature : Types.signature) -> signature.terminates
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
      Logic.(
        Operation ("<=", [ int 0; below ]) &&& Operation ("<", [ below; rank context ty term ]))
  end;
  part

(* A field of a value: of one built here, the value it was built from. *)
and selected context ty variant field term =
  match (term, constructors context ty) with
  | Logic.Apply (name, arguments), Some shape when name = constructor_name ty variant -> (
      let fields = Option.value (List.assoc_opt variant shape) ~default:[] in
      match List.find_index (fun (named, _) -> named = field) fields with
      | Some index when index < List.length arguments -> List.nth arguments index
      | _ -> Logic.Apply (selector_name ty variant field, [ term ]))
  | _ -> Logic.Apply (selector_name ty variant field, [ term ])

(* A value's place in the order of parts, as Dafny's datatypes have one:
   any field is below the value it is in. *)
and rank context ty term =
  let symbol = Symbol.Rank (type_key ty) in
  declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

(* The form of a type, which holds its fields' defaults, its invariants,
   and its potential. *)
and type_source context (ty : Types.ty) =
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
and type_frame context frame source (ty : Types.ty) ~self =
  let substitution = match visible_type context ty with Some (_, symbol) -> symbol | None -> [] in
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
  match function_contract ?reading_package:(reading_package context) context.database path with
  | Some contract -> named_function context frame node path type_arguments contract
  | None -> unsupported (at frame node) "a function the prover cannot read, used as a value"

(* A function named as a value is a value of its type known by its
   promise about its calls: one unit of time per call when its [time] is a
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
      (Logic.Boolean false);
  let ty = type_of context frame node in
  (* A function with a [requires], used as a value anywhere but passed
     straight to a parameter, which checks it, has a type that keeps no
     [requires], so it must accept every argument of that type. *)
  (match (ty, contract.parts) with
  | Types.Function function_type, own :: _
    when own.requires <> [] && frame.checking && not (List.mem node.id context.passed_values) ->
      let inputs = callback_arguments context frame function_type.inputs in
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
                 (Path.show path) (Types.show ty) (quote own.callee clause.origin))
              (snd (clause_value context inside clause)))
          own.requires
      end
  | _ -> ());
  let instance =
    List.map argument_key (List.map (Types.substitute_argument frame.substitution) type_arguments)
  in
  let symbol = Symbol.Function_value { callee = path; instance } in
  declare context (Logic.Constant (symbol, sort_of context ty));
  let term = Logic.Symbol symbol in
  (* Applied, a pure function named as a value is the function: its body,
     where it has a definition that holds for every argument, and
     otherwise the function in the logic. *)
  (match ty with
  | Types.Function function_type when in_the_logic function_type && contract.pure ->
      let parameters = parameters_of context frame function_type in
      let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
      let defined =
        match contract.definition with
        | Some (part, body)
          when part.requires = [] && instance = []
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
            let output =
              match function_type.output with Returns output -> output | _ -> Types.unit
            in
            let function_symbol = Symbol.Function { callee = path; instance } in
            declare context
              (Logic.Function (function_symbol, List.map snd parameters, sort_of context output));
            let value = Logic.Apply (function_symbol, inputs) in
            if instance = [] then
              contract_for_every_argument context frame contract parameters value;
            value
      in
      fact context frame
        (Logic.Forall (parameters, Logic.equal (applied context function_type term inputs) value))
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
     fact context frame (Logic.equal time (Logic.int 1)));
  term

(* A pure function's contract about its value for every argument:
   where its [requires] holds, its [ensures] does. Its clauses are read over
   the parameters as a quantifier's body is. *)
and contract_for_every_argument context frame (contract : contract) parameters value =
  let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
  let over =
    {
      frame with
      bound = List.map fst parameters @ frame.bound;
      binders =
        List.rev_map (fun (name, sort) -> (name, sort, Logic.Boolean true)) parameters
        @ frame.binders;
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
      Logic.conjunction
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
            match snd (clause_value context (read part) clause) with
            | ensured -> (
                match closed_over_binders over (Logic.( ==> ) required ensured) with
                | Some closed -> context.facts <- closed :: context.facts
                | None -> ())
            | exception Foreign_unsupported _ -> ())
          part.ensures)
      contract.parts
  with Unsupported _ | Foreign_unsupported _ -> ()

(* A function named as a value and passed for a function-typed parameter
   must accept every argument the parameter's type promises it, and keep
   the cost clauses the type asks of the passed function. *)
and check_named_callback context frame (call_ : call) (passed : passed) (named : expression) path
    (contract : contract) (values : passed list) =
  let span = at frame named in
  let own = List.hd contract.parts in
  match parameter_type context frame call_ passed.position with
  | Some (Types.Function expected) ->
      let inputs = callback_arguments context frame expected.inputs in
      let known = List.map (fun (passed : passed) -> (passed.position, passed.term)) values in
      let promised =
        Logic.conjunction (callback_facts context frame call_ passed.position known inputs)
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
        (fun (cost : Types.cost) ->
          if not (keeps_cost context path contract cost) then
            oblige context frame Cost span
              (Printf.sprintf
                 "`%s` does not promise the contract this parameter's type, `%s`, asks of a \
                  function passed for it."
                 (Path.show path)
                 (Types.show (Types.Function expected)))
              (Logic.Boolean false))
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
      | Some (signature : Types.signature) ->
          let types =
            (match signature.receiver with
              | Some ((Read | Mut | Own), ty) -> [ ty ]
              | Some (Static, _) | None -> [])
            @ List.map (fun (info : Types.parameter_info) -> info.type_) signature.parameters
          in
          Option.map
            (Types.substitute (callee_substitution frame signature type_arguments))
            (List.nth_opt types index)
      | None -> None)
  | _ -> None

(* Whether a named function's cost clauses imply one a function type asks
   for, which can only be a constant: a constant [O(...)], or a number of
   at most, or exactly, the asked bound. *)
and keeps_cost context path (contract : contract) (asked : Types.cost) =
  let constant (value : expression) =
    match value.kind with Integer limit -> Some limit | _ -> None
  in
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
              match constant value with Some limit -> Z.leq limit most | None -> false)
          | Exactly_cost (Some exact), Exactly value -> constant value = Some exact
          | _ -> false)
      | None -> false)

(* A constant is its value, computed from its definition, which is made
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
      let symbol = Symbol.Constant path in
      let empty =
        {
          frame with
          source = constant_source;
          locals = Locals.empty;
          types = Locals.empty;
          checking = false;
          self = None;
          updating = None;
          condition = Logic.Boolean true;
          bound = [];
          binders = [];
        }
      in
      once context (Value_of symbol) (fun () ->
          let ty = type_of context empty defined in
          declare context (Logic.Constant (symbol, sort_of context ty));
          let _, defined_value = without_costs context (fun () -> value context empty defined) in
          context.facts <- Logic.equal (Logic.Symbol symbol) defined_value :: context.facts);
      Logic.Symbol symbol
  | _ -> raise (Foreign_unsupported "a constant with errors")

(* Building a record or a variant: its constructor, with each field given
   or defaulted. *)
(* A constructor applied to its fields. [given] has the value of each field
   the caller evaluated already. *)
and construct ?(given = fun _ -> None) context frame (node : expression) variant
    (fields : (string * operand option) list) =
  let ty = type_of context frame node in
  if Types.equal ty Types.unit then begin
    (* The one value of [Unit]. *)
    ignore (sort_of context Types.unit);
    (frame, Logic.Apply (Symbol.Unit, []))
  end
  else
    let frame, field_terms =
      List.fold_left
        (fun (frame, field_terms) (field, written) ->
          match (written, given field) with
          | Some _, Some term -> (frame, field_terms @ [ (field, term) ])
          | Some written, None ->
              let frame, term = operand_value context frame written in
              (frame, field_terms @ [ (field, term) ])
          | None, _ ->
              (frame, field_terms @ [ (field, field_default context frame node ty variant field) ]))
        (frame, []) fields
    in
    let frame = spend context frame (construct_amount context frame ty variant) in
    match constructors context ty with
    | Some shape ->
        ignore (sort_of context ty);
        let shaped = match List.assoc_opt variant shape with Some fields -> fields | None -> [] in
        let field_value (name, _) =
          match List.assoc_opt name field_terms with
          | Some term -> term
          | None -> unsupported (at frame node) "a field left out"
        in
        let built = Logic.Apply (constructor_name ty variant, List.map field_value shaped) in
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
and pattern_match context frame (pattern : pattern) term ty : Logic.term * frame =
  let span = at frame { id = pattern.id; origin = pattern.origin; type_ = ty; kind = Todo } in
  match pattern.kind with
  | Wildcard -> (Logic.Boolean true, frame)
  | Bind { local; name; _ } ->
      Hashtbl.replace context.local_names local name;
      (Logic.Boolean true, bind frame local ty term)
  | Literal literal ->
      let frame, expected = value context frame literal in
      (Logic.equal term expected, frame)
  | Range { start; stop; inclusive } ->
      let _, low = value context frame start in
      let _, high = value context frame stop in
      ( Logic.(
          Operation ("<=", [ low; term ])
          &&& Operation ((if inclusive then "<=" else "<"), [ term; high ])),
        frame )
  | Equal_to { value = { kind = String text; _ }; _ } -> (
      (* Text matches when its bytes are the pattern's. *)
      let byte = Types.builtin UInt8 in
      match model_of context ty term ~element:byte with
      | Some model ->
          ( Logic.conjunction
              (Logic.equal (sequence_length context byte model) (Logic.int (String.length text))
              :: List.init (String.length text) (fun index ->
                  match sequence_at context byte model (Logic.int index) with
                  | Some at -> Logic.equal at (Logic.int (Char.code text.[index]))
                  | None -> Logic.Boolean false)),
            frame )
      | None -> unsupported span "a string pattern on `%s`" (Types.show ty))
  | Equal_to { value = compared; _ } ->
      let _, expected = value context frame compared in
      (equal_of context frame ty term expected, frame)
  | Variant { variant; fields } ->
      ignore (sort_of context ty);
      if constructors context ty = None then
        unsupported span "a variant of `%s`, which the prover does not see" (Types.show ty);
      let test = Logic.Is (constructor_name ty (Some variant), term) in
      let condition, frame = fields_match context frame span ty (Some variant) term fields in
      (Logic.( &&& ) test condition, frame)
  | Record fields ->
      ignore (sort_of context ty);
      if constructors context ty = None then
        unsupported span "the fields of `%s`, which the prover does not see" (Types.show ty);
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
                        | Some part -> Logic.ite condition part otherwise
                        | None -> otherwise)
                      (Locals.find id last.locals) earlier
                | [] -> Locals.find id first.locals)
              (Locals.filter
                 (fun id _ ->
                   List.for_all (fun (_, (after : frame)) -> Locals.mem id after.locals) matched)
                 first.locals)
      in
      let types = match matched with (_, first) :: _ -> first.types | [] -> frame.types in
      (Logic.disjunction (List.map fst matched), { frame with locals = bound; types })

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
          (Logic.( &&& ) condition inner, frame)
      | None -> unsupported span "the field `%s`" name)
    (Logic.Boolean true, frame) fields

(* Each binding a pattern lends [mut] from the value it matches, with how
   the value is rebuilt from the binding's final value when the lend ends:
   through the variants and fields that lead to it, each other field kept. *)
and lent_bindings context frame (pattern : pattern) ty :
    (Core.local * (Logic.term -> Logic.term -> Logic.term)) list =
  match pattern.kind with
  | Bind { local; mode = Types.Mut; _ } -> [ (local, fun _ part -> part) ]
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
                      Logic.Apply
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
  let carries_value = not (Types.equal result_type Types.unit || result_type = Types.Never) in
  let scoped = end_scope ~outer:frame in
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
                  (Logic.( &&& ) condition inner, frame))
                (Logic.Boolean true, current) arm_.patterns scrutinee_values
            in
            let entered = restrict bound condition in
            (match arm_.patterns with
            | _ :: _ when current.checking && current.source.key = Some context.home ->
                context.decisions <-
                  ( Printf.sprintf "the arm `%s` is taken"
                      (String.concat ", "
                         (List.map
                            (fun (pattern : pattern) -> quote current.source pattern.origin)
                            arm_.patterns)),
                    None,
                    current.condition,
                    condition )
                  :: context.decisions
            | _ -> ());
            let entered, passed_over =
              match arm_.guard with
              | Some guard ->
                  let after, test = value context entered guard in
                  (restrict after test, [ scoped (restrict after (Logic.not_ test)) ])
              | None -> (entered, [])
            in
            untaken := join_frames context (restrict current (Logic.not_ condition) :: passed_over);
            (* The final value of each binding an arm lends [mut] goes back into
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
              let rewrite count list exit_frame =
                let added = List.length list - count in
                List.mapi (fun index item -> if index < added then exit_frame item else item) list
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
    match
      join context ~value_type:result_type
        (List.map (fun (exit_frame, spent_term) -> (exit_frame, Some spent_term)) reached)
    with
    | Some (joined, Some term) -> Some (scoped joined, term)
    | Some (joined, None) -> Some (scoped joined, Logic.Boolean true)
    | None -> None
  else
    Option.map
      (fun joined -> (scoped joined, Logic.Boolean true))
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
        Logic.Apply
          ( constructor_name ty None,
            List.map
              (fun (name_, field_type) ->
                let current = selected context ty None name_ term in
                if name_ = field then replace field_type current rest replacement else current)
              fields )
    | _ -> unsupported span "`with` on `%s`" (Types.show ty)
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
and invariants_of context (ty : Types.ty) =
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
  if List.exists (Types.equal ty) seen || List.exists (Types.equal ty) context.validating then
    Logic.Boolean true
  else
    let validating = context.validating in
    context.validating <- ty :: validating;
    Fun.protect ~finally:(fun () -> context.validating <- validating) @@ fun () ->
    let own =
      match invariants_of context ty with
      | _ when not own -> Logic.Boolean true
      | Some _ when constructors context ty = None ->
          let symbol = Symbol.Valid (type_key ty) in
          declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Bool));
          Logic.Apply (symbol, [ term ])
      | Some (source, written) -> (
          let inner = type_frame context frame source ty ~self:(Some term) in
          try
            Logic.conjunction
              (List.map (fun invariant -> snd (clause_value context inner invariant)) written)
          with Unsupported _ | Foreign_unsupported _ when assuming -> Logic.Boolean true)
      | None -> Logic.Boolean true
    in
    let fields =
      if not deep then Logic.Boolean true
      else
        match constructors context ty with
        | Some shape ->
            Logic.conjunction
              (List.concat_map
                 (fun (variant, fields) ->
                   List.map
                     (fun (field, field_type) ->
                       let part =
                         validity context frame ~assuming ~deep ~seen:(ty :: seen) field_type
                           (selected context ty variant field term)
                       in
                       match (variant, part) with
                       | _, Logic.Boolean true -> part
                       | Some name_, _ ->
                           Logic.( ==> ) (Logic.Is (constructor_name ty (Some name_), term)) part
                       | None, _ -> part)
                     fields)
                 shape)
        | None -> Logic.Boolean true
    in
    Logic.( &&& ) own fields

and assume_valid context frame ty term =
  assume context frame (validity context frame ~assuming:true ty term)

and check_valid context frame span ty term ~deep ~when_ =
  match validity context frame ~assuming:false ~deep ty term with
  | Logic.Boolean true -> ()
  | valid ->
      oblige context frame Invariant span
        (Printf.sprintf "The invariant of `%s` may not hold %s." (Types.show ty) when_)
        valid

and check_built context frame (node : expression) ty term =
  check_valid context frame (at frame node) ty term ~deep:false ~when_:"for the value built here"

(* A fix for a callee's [requires] that is about the definition's
   parameters alone: the clause, with each of the callee's parameters
   written as its argument, as a [requires] of the definition, which then
   holds at every call of it instead. *)
and requires_fix context frame (part : part) (clause : expression) term (values : passed list) =
  let fixed name =
    List.mem name context.entry
    || match name with Symbol.Constant _ | Symbol.Literal _ -> true | _ -> false
  in
  let operand_origin = function
    | Value (expression : expression) -> Some expression.origin
    | Place (Local { origin; _ } | Constant { origin; _ } | Field { origin; _ }) -> Some origin
    | Place _ -> None
  in
  let simple text =
    String.for_all
      (fun character ->
        character = '_' || character = '.'
        || Char.code character >= 128
        || (character >= 'a' && character <= 'z')
        || (character >= 'A' && character <= 'Z')
        || (character >= '0' && character <= '9'))
      text
  in
  let written =
    List.filter_map
      (fun (index, (parameter : Core.parameter)) ->
        match List.find_opt (fun (passed : passed) -> passed.position = index) values with
        | Some { operand = Some operand; _ } -> (
            match operand_origin operand with
            | Some origin ->
                let text = quote frame.source origin in
                Some (parameter.local, if simple text then text else "(" ^ text ^ ")")
            | None -> None)
        | _ -> None)
      (List.mapi (fun index parameter -> (index, parameter)) part.parameters)
  in
  if frame.source.key <> Some context.home || not (List.for_all fixed (Logic.free_symbols term))
  then []
  else
    let clause_span = span_of part.callee clause.origin in
    let clause_text = quote part.callee clause.origin in
    (* Each reference to a parameter in the clause, with the argument's text. *)
    let references = ref [] in
    Core_walk.expression
      {
        Core_walk.ignore_all with
        place =
          (function
          | Local { local; origin; _ } -> (
              match List.assoc_opt local written with
              | Some text -> references := (span_of part.callee origin, text) :: !references
              | None -> ())
          | _ -> ());
      }
      clause;
    let buffer = Buffer.create (String.length clause_text) in
    let next =
      List.fold_left
        (fun next ((span : span), text) ->
          let start = span.start - clause_span.start and stop = span.stop - clause_span.start in
          if start < next || stop > String.length clause_text then next
          else begin
            Buffer.add_string buffer (String.sub clause_text next (start - next));
            Buffer.add_string buffer text;
            stop
          end)
        0
        (List.sort_uniq compare !references)
    in
    Buffer.add_string buffer (String.sub clause_text next (String.length clause_text - next));
    if written <> [] || part.parameters = [] then
      add_requires context frame (Buffer.contents buffer)
    else []

(* An operand's text, where its value names only the definition's
   parameters as they arrive, so that a clause about it can be the
   definition's [requires]. *)
and parameter_operand context frame (operand : expression) term =
  if
    frame.source.key = Some context.home
    && (not (Logic.quantified term))
    &&
    match Logic.free_symbols term with
    | _ :: _ as names -> List.for_all (fun name -> List.mem name context.entry) names
    | [] -> false
  then
    let text = quote frame.source operand.origin in
    let plain =
      String.for_all
        (fun character ->
          character = '_' || character = '.'
          || (character >= 'a' && character <= 'z')
          || (character >= 'A' && character <= 'Z')
          || (character >= '0' && character <= '9'))
        text
    in
    Some (if plain then text else "(" ^ text ^ ")")
  else None

(* A fix for an overflow of an operation on the definition's parameters
   and a literal: the bound the other operand must be within, as a
   [requires], which an operation [count + 1] on a [UInt8] gives as
   [requires count <= 254]. *)
and overflow_fix context frame ty (operation : Intrinsic.operation) (operand : expression) left
    right =
  match (bounds ty, right, parameter_operand context frame operand left) with
  | Some (low, high), Logic.Integer limit, Some text -> (
      let clause relation limit =
        if Z.leq low limit && Z.leq limit high then
          add_requires context frame (Printf.sprintf "%s %s %s" text relation (Z.to_string limit))
        else []
      in
      match operation with
      | Add when Z.sign limit > 0 -> clause "<=" (Z.sub high limit)
      | Add when Z.sign limit < 0 -> clause ">=" (Z.sub low limit)
      | Subtract when Z.sign limit > 0 -> clause ">=" (Z.add low limit)
      | Subtract when Z.sign limit < 0 -> clause "<=" (Z.add high limit)
      | Multiply when Z.sign limit > 0 && Z.sign low = 0 -> clause "<=" (Z.div high limit)
      | _ -> [])
  | _ -> []

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
          if passed.mode = Types.Mut || Logic.mentions frame.bound passed.term then passed
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
  let self_of self = Option.map fst self
  and self_type_of part self =
    Option.map (fun (_, ty) -> Types.substitute (substitution_of part) ty) self
  in
  let entry_frame (part : part) =
    let locals, types, self = bind (bindings part) in
    {
      frame with
      source = part.callee;
      locals;
      types;
      old_locals = locals;
      self = self_of self;
      old_self = self_of self;
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
          Logic.(
            conjunction
              (List.map (fun right_term -> Operation ("<=", [ int 0; right_term ])) before)
            &&& lexicographically_less before after)
    | [], _ | _, [] ->
        oblige context frame Termination span
          (Printf.sprintf
             "This call to `%s` may not end: it calls back here, and both need a `decreases` \
              clause for the prover to show that the recursion ends."
             (Path.show path))
          (Logic.Boolean false)
    | measures, callee_measures ->
        let current_frame =
          { frame with checking = false; locals = frame.old_locals; self = frame.old_self }
        in
        let callee_entry = entry_frame own in
        let rec prefix before after =
          match (before, after) with
          | right_term :: before, left_term :: after ->
              let rest_before, rest_after = prefix before after in
              (right_term :: rest_before, left_term :: rest_after)
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
          (lexicographically_less before after)
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
              ~fixes:(requires_fix context frame part clause term values)
              (Printf.sprintf "`%s` may not hold for this call to `%s`."
                 (quote part.callee clause.origin) (Path.show path))
              term;
            term)
          part.requires)
      requiring
  in
  let required = Logic.conjunction required in
  (* Each part's [ensures] holds where its [requires] does: a trait's, of
     an [impl]'s method whose own precondition is weaker, only where the
     trait's holds too. *)
  let required_by (part : part) =
    if List.memq part requiring then required
    else
      Logic.conjunction
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
  (* Each [mut] argument's value after the call: its place's value, which
     [havoc_mut] made fresh. *)
  let changed =
    List.filter_map
      (fun (passed : passed) ->
        match (passed.mode, passed.passed_place) with
        | Types.Mut, Some place -> (
            try Some (passed.position, place.read after)
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
      let symbol = Symbol.Function { callee = path; instance } in
      let sorts =
        List.mapi
          (fun index ((parameter : Core.parameter), _) ->
            match List.find_opt (fun (passed : passed) -> passed.position = index) values with
            | Some passed -> sort_of context passed.type_
            | None ->
                sort_of context
                  (Interface.Impls.normalize context.database
                     ~bounds:(fun _ -> [])
                     (Types.substitute (substitution_of own) parameter.type_)))
          own_bound
      in
      declare context (Logic.Function (symbol, sorts, sort_of context result_type));
      (match (path, own_bound) with
      | Method { name = "model"; receiver = Read; _ }, [ (self, _) ] when self.local = Self ->
          model_ranked context
            (Interface.Impls.normalize context.database
               ~bounds:(fun _ -> [])
               (Types.substitute (substitution_of own) self.type_))
            ~model:result_type symbol
      | _ -> ());
      applied_as := Some (symbol, sorts);
      let term = Logic.Apply (symbol, own_arguments) in
      assume context after (in_range result_type term);
      (* Called on a quantifier's bound values, where that fact would name
         them, the result is in its type's range for every argument, which
         is true of a pure function: outside its [requires] its value is
         one the logic leaves free. *)
      if bounds result_type <> None && List.exists (Logic.mentions after.bound) own_arguments then
        once context (In_range symbol) (fun () ->
            let parameters =
              List.mapi
                (fun index sort ->
                  (Symbol.Variable { label = "ranged"; numbers = [ index ] }, sort))
                sorts
            in
            context.facts <-
              Logic.Forall
                ( parameters,
                  in_range result_type
                    (Logic.Apply (symbol, List.map (fun (name, _) -> Logic.Symbol name) parameters))
                )
              :: context.facts);
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
    | `Lends, Some Types.Mut, Some leave ->
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
  let is_updating_helper = updating_helper context call_ in
  List.iter
    (fun (passed : passed) ->
      if passed.mode = Types.Mut && not (is_updating_helper && passed.position = 0) then
        match List.assoc_opt passed.position changed with
        | Some term ->
            let valid = validity context after ~assuming:true passed.type_ term in
            assume context after
              (match left_valid with Some (left, _) -> Logic.( ==> ) left valid | None -> valid)
        | None -> ())
    values;
  if not (List.exists (Path.equal path) context.instantiating) then begin
    context.instantiating <- path :: context.instantiating;
    (* The definition, unfolded once, where the [requires] holds. A body
       the prover cannot read is simply not unfolded. *)
    (match contract.definition with
    | Some (part, body) when not (List.exists (Logic.mentions after.bound) own_arguments) -> (
        let unfolding =
          if in_quantifier then
            { (entry_frame part) with condition = Logic.Boolean true; bound = []; binders = [] }
          else { (entry_frame part) with condition = after.condition }
        in
        try
          match block_value context unfolding body with
          | Some (_, defined) -> state (Logic.( ==> ) required (Logic.equal result defined))
          | None -> ()
        with Unsupported _ | Foreign_unsupported _ -> ())
    | Some (part, body) when part.requires = [] -> (
        (* Called on a quantifier's bound values, the definition is stated
           once for every argument, so that it holds for each of them. *)
        match !applied_as with
        | Some (symbol, sorts) ->
            once context (Definition_of symbol) (fun () ->
                let parameters =
                  List.mapi
                    (fun index sort ->
                      (Symbol.Variable { label = "defined"; numbers = [ index ] }, sort))
                    sorts
                in
                let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
                let outside =
                  { after with bound = []; binders = []; condition = Logic.Boolean true }
                in
                match
                  body_over context outside parameters body (fun inside ->
                      part_frame inside part
                        ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
                        ~substitution:(substitution_of part))
                with
                | Some defined ->
                    context.facts <-
                      Logic.Forall (parameters, Logic.equal (Logic.Apply (symbol, inputs)) defined)
                      :: context.facts
                | None -> ())
        | None -> ())
    | (None | Some _) when List.exists (Logic.mentions after.bound) own_arguments -> (
        (* Called on a quantifier's bound values, a callee known by its
           contract alone, or with a [requires], has its [ensures] stated
           once, for every valid argument where its [requires] holds. *)
        match !applied_as with
        | Some (symbol, sorts) ->
            once context (Contract_of symbol) (fun () ->
                let parameters =
                  List.mapi
                    (fun index sort ->
                      (Symbol.Variable { label = "ensured"; numbers = [ index ] }, sort))
                    sorts
                in
                let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
                let outside =
                  {
                    after with
                    bound = List.map fst parameters;
                    binders = [];
                    condition = Logic.Boolean true;
                    checking = false;
                  }
                in
                let mark = context.fresh in
                let valid =
                  Logic.conjunction
                    (List.map2
                       (fun ((parameter : Core.parameter), _) input ->
                         validity context outside ~assuming:true
                           (Types.substitute (substitution_of own) parameter.type_)
                           input)
                       own_bound inputs)
                in
                let readable clause inside =
                  match snd (clause_value context inside clause) with
                  | term when not (mentions_fresh_after context mark term) -> Some term
                  | _ -> None
                  | exception (Unsupported _ | Foreign_unsupported _) -> None
                in
                let ensured =
                  List.filter_map
                    (fun (part : part) ->
                      let inside =
                        {
                          (part_frame outside part
                             ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
                             ~substitution:(substitution_of part))
                          with
                          result = Some (Logic.Apply (symbol, inputs));
                          checking = false;
                        }
                      in
                      let required =
                        List.map (fun clause -> readable clause inside) part.requires
                      in
                      match List.filter_map (fun clause -> readable clause inside) part.ensures with
                      | [] -> None
                      | _ when List.mem None required -> None
                      | ensures ->
                          Some
                            Logic.(
                              conjunction (List.filter_map Fun.id required) ==> conjunction ensures))
                    contract.parts
                in
                if ensured <> [] && not (mentions_fresh_after context mark valid) then
                  context.facts <-
                    Logic.Forall (parameters, Logic.( ==> ) valid (Logic.conjunction ensured))
                    :: context.facts)
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
          (* Called inside a quantifier on no bound value, the call's
             [ensures] is a fact outside the quantifier, as its definition
             is: true whether or not the quantifier's body runs. *)
          let is_unbound_in_quantifier =
            in_quantifier && not (List.exists (Logic.mentions after.bound) own_arguments)
          in
          let ensures_frame =
            {
              frame with
              source = part.callee;
              condition = (if is_unbound_in_quantifier then Logic.Boolean true else after.condition);
              bound = (if is_unbound_in_quantifier then [] else frame.bound);
              binders = (if is_unbound_in_quantifier then [] else frame.binders);
              locals = exit_locals;
              types;
              old_locals = entry_locals;
              self = self_of exit_self;
              old_self = self_of entry_self;
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
                (* The part as lent, and the parts yielded: the one part, as
                 the caller's statement left it. *)
                let left = match lent_final with Some leave -> leave result | None -> result in
                let none = empty_parts context after result_type in
                {
                  ensures_frame with
                  yielded = Some (appended context after result_type none left);
                  finished = Some (Logic.Boolean true);
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
                      self = self_of entry_self;
                      yielded = None;
                    }
                  else ensures_frame
                in
                (* A clause that reads what this package cannot see, such
                   as an opaque type's fields, is a fact only in the
                   callee's own package, and leaving a fact out is sound. *)
                match clause_value context frame_for_clause clause with
                | _, term ->
                    (* A pure call's [ensures], where its [requires] holds, is a
                   fact of mathematics, true whether or not a quantifier's
                   body around it runs. *)
                    state (Logic.( ==> ) (required_by part) term)
                | exception Foreign_unsupported _ -> ())
            part.ensures)
        (* A yielding method's clauses are about each part it yields and
         how it ends, which each pull of the cursor it makes meets. *)
        (if contract.result_kind = `Yields then [] else contract.parts)
    in
    (* A lend's clauses about the part as lent come before the check of
       the caller's final value in it, and those about how the lend ends, which read
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
     | Types.Cursor _ as cursor_type -> (
         match Interface.Impls.signature context.database path with
         | Some { output = Yields (_, element); _ } ->
             let element = Types.substitute (substitution_of own) element in
             let cursor_method = { method_frame = entry_frame own; own; element } in
             context.cursors <- (result, cursor_method) :: context.cursors;
             assume context after
               Logic.(
                 equal
                   (sequence_length context element
                      (cursor_yielded context cursor_type element result))
                   (int 0)
                 &&& not_ (cursor_ended context cursor_type result))
         | _ -> ())
     | _ -> ());
  (* The call's cost is the callee's cost clauses with the arguments and
     [result] substituted. [change] is the call's change in potential: that
     of its result and its [mut] arguments after the call, less that of its
     [mut] and [own] arguments before it. *)
  let change () =
    List.fold_left
      (fun total (passed : passed) ->
        let ty = passed.type_ in
        match passed.mode with
        | Types.Mut -> (
            match List.assoc_opt passed.position changed with
            | Some later ->
                Costs.plus total
                  (Costs.minus
                     (potential context after ty later)
                     (potential context frame ty passed.term))
            | None -> total)
        | Types.Own -> Costs.minus total (potential context frame ty passed.term)
        | Types.Read -> total)
      (match contract.result_kind with
      | `Yields -> Costs.zero
      | `Lends -> (
          (* A lent part stays in place, so the call hands over none of its
             potential, and the caller, not the method, pays for the
             caller's changes to it. *)
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
               [time(Types.method)] for the type it is called on. *)
            let ends_in =
              match call_.callee with
              | Trait_method _ when signature_terminates context path ->
                  Some (method_time context frame call_.callee)
              | _ -> None
            in
            callee_amount ?ends_in context after ~path ~parts:contract.parts
              ~bound_frame:(fun part ->
                { (entry_frame part) with result = Some result; condition = after.condition })
              ~uses:(call_.uses :> Types.capability list)
              ~values ~change:(Some change) counter)
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
    | Logic.Integer value -> Some value
    | Logic.Boolean value -> Some (if value then Z.one else Z.zero)
    | _ -> None
  in
  let values = List.filter_map literal arguments in
  match Interface.Impls.signature context.database path with
  | Some
      ({ specification_only = false; generics = []; output = Returns result; _ } : Types.signature)
    when direct
         (* Running a callee reads its body, so only a callee of the
            definition's own package is run. *)
         && Path.package path = Path.package context.current
         && List.length values = List.length arguments
         && (is_numeric result || is_bool result)
         && not (Types.equal result Types.Integer) ->
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

and is_datatype ty = match ty with Types.Named _ -> builtin ty = None | _ -> false

and argument_at_index (values : passed list) index =
  match
    List.find_map
      (fun (passed : passed) -> if passed.position = index then Some passed.term else None)
      values
  with
  | Some term -> term
  | None -> Logic.Boolean false

and lexicographically_less before after =
  match (before, after) with
  | [ right ], [ left ] ->
      Logic.(Operation ("<=", [ int 0; right ]) &&& Operation ("<", [ left; right ]))
  | right :: before, left :: after ->
      Logic.(
        Operation ("<=", [ int 0; right ])
        &&& (Operation ("<", [ left; right ])
            ||| (equal left right &&& lexicographically_less before after)))
  | _ -> Logic.Boolean true

(* Costs: each step's cost. *)

(* The counters a body's loops' [cost] clauses count, outside lambdas,
   which count on their own. *)
and loop_counters locals (body : block) =
  let counters = ref [] in
  let note (clauses : loop_clause list) =
    List.iter
      (function
        | Cost cost -> (
            match resource_of cost ~locals with
            | Some resource ->
                counters :=
                  { Costs.resource; counting = counting_of cost; amortized = false } :: !counters
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
  List.rev !counters

(* Each counter, increased by one step's cost. *)
and spend context frame (amount : Costs.counter -> Logic.term) =
  if context.counters = [] then frame
  else
    {
      frame with
      spent =
        List.map
          (fun (counter, term) ->
            if List.mem counter context.counters then (counter, Costs.plus term (amount counter))
            else (counter, term))
          frame.spent;
    }

(* An amount nothing bounds: at least zero, or one for a call's time. *)
and unknown_amount context frame (counter : Costs.counter) =
  let amount = fresh context frame "spent" Logic.Int in
  let least = match counter.resource with Time -> 1 | _ -> 0 in
  assume context frame (Logic.Operation ("<=", [ Logic.int least; amount ]));
  amount

(* An amount from zero to [bound], for a counter that counts exactly. *)
and bounded_amount context frame bound =
  let amount = fresh context frame "spent" Logic.Int in
  assume context frame
    Logic.(Operation ("<=", [ int 0; amount ]) &&& Operation ("<=", [ amount; bound ]));
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

(* A clause's bound on a counter, in the counter's way of counting:
   [is_recursive_call] is whether the call is back into the definition
   proven, which assumes the bound as the induction hypothesis, and
   [change] is the growth in potential of the values an amortized clause's
   call changed, which it
   paid for out of its bound. *)
and promised_amount context frame (counter : Costs.counter) (bound : bound) ~evaluate
    ~is_recursive_call ~exact_target ~change =
  match (bound, counter.counting) with
  | Order_of amount, Units ->
      let amount = evaluate amount in
      let amount =
        if is_recursive_call then
          let hypothesis = Costs.at_least_zero (Costs.bound amount) in
          if counter.resource = Time then Costs.plus hypothesis (Logic.int 1) else hypothesis
        else Costs.units amount
      in
      Costs.minus amount change
  | (At_most amount | Exactly amount), Units ->
      Costs.at_least_zero (Costs.minus (evaluate amount) change)
  | At_most amount, (At_most | Exactly) ->
      bounded_amount context frame (Costs.minus (evaluate amount) change)
  | Exactly amount, (At_most | Exactly) ->
      let amount = Costs.minus (evaluate amount) change in
      if exact_target then amount else bounded_amount context frame amount
  | (Order_of _ | Finite), _ -> unknown_amount context frame counter

(* How much a potential grew, or zero where it fell or cannot be read. *)
and growth change =
  try Costs.at_least_zero (change ()) with Unsupported _ | Foreign_unsupported _ -> Costs.zero

(* The cost on a counter of a call to a callee whose clauses are read: its
   clause about the counter's resource, from its first part that has one.
   A call back into the definition proven, through a cycle, assumes its
   [O(...)] bound. *)
and callee_amount ?ends_in context after ~path ~(parts : part list) ~(bound_frame : part -> frame)
    ~uses ~(values : passed list) ~change (counter : Costs.counter) =
  let is_recursive_call =
    counter.counting = Units
    && List.mem counter context.own_bounds
    && Call_graph.reaches context.database ~package:(Path.package context.current) ~from:path
         ~target:context.current
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
          ~evaluate:(fun amount -> snd (value context frame amount))
          ~is_recursive_call ~exact_target
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
        | clauses ->
            let amortized, plain =
              List.partition (fun (_, _, (cost : Core.cost)) -> cost.amortized) clauses
            in
            Some (if amortized_first then amortized @ plain else plain @ amortized))
      parts
  in
  match counter.resource with
  | Calls target when call_reaches context after uses values target = Logic.Boolean false ->
      Costs.zero
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
      | Some clauses
        when (not captured) && List.length clauses >= List.length receiving && receiving <> [] ->
          List.fold_left (fun total clause -> Costs.plus total (amount clause)) Costs.zero clauses
      | _ -> spent_where reaches (unknown_amount context after counter))
  | _ -> (
      (* [time(Types.method)] is the most one call takes plus the potential it
         makes, so a call that makes potential has paid for it. *)
      let within_time time =
        Costs.minus
          (Costs.plus time (Logic.int 1))
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
      Logic.disjunction
        (List.map
           (fun (passed : passed) ->
             if lambda_captures_target context passed.term term then Logic.Boolean true
             else may_be_target context frame passed.term passed.type_ term)
           values)
  | Capability path | Capability_method (path, _) ->
      Logic.Boolean
        (List.exists
           (function
             | Types.Capability used -> Path.equal used path
             | Types.Capability_parameter _ | Types.Capability_projection _
             | Types.Capability_variable _ ->
                 true)
           uses)

(* Whether a function value is a [calls] clause's target: the target
   itself, or a value of its sort that may equal it, as one chosen by [if]
   or read from a field may. *)
and may_be_target context frame term ty target =
  if term = target then Logic.Boolean true
  else
    match List.assoc_opt target context.call_targets with
    | Some local -> (
        match (ty, local_type context frame local) with
        | Types.Function _, Some target_type when sort_of context ty = sort_of context target_type
          ->
            Logic.equal term target
        | _ -> Logic.Boolean false)
    | None -> Logic.Boolean false

(* An amount spent only where [condition] holds. *)
and spent_where condition amount =
  match condition with
  | Logic.Boolean true -> amount
  | Logic.Boolean false -> Costs.zero
  | condition -> Logic.ite condition amount Costs.zero

and lambda_captures_target context lambda target =
  match
    (List.assoc_opt lambda context.lambda_captures, List.assoc_opt target context.call_targets)
  with
  | Some captured, Some local -> List.mem local captured
  | _ -> false

(* The cost of a call through a function value: its [time], which is one
   unit for a function type with an [O(...)] bound, and its type's clauses
   for other resources. *)
and function_value_amount context frame (function_type : Types.function_type) callee_term
    (counter : Costs.counter) =
  let clause resource =
    List.find_opt (fun (cost : Types.cost) -> cost.resource = resource) function_type.costs
  in
  let by_clause resource =
    match (clause resource, counter.counting) with
    | Some { bound = Order_of; _ }, Units -> Logic.int 1
    | Some { bound = No_more_than (Some limit) | Exactly_cost (Some limit); _ }, Units ->
        Logic.Integer limit
    | Some { bound = No_more_than (Some limit); _ }, (At_most | Exactly) ->
        bounded_amount context frame (Logic.Integer limit)
    | Some { bound = Exactly_cost (Some limit); _ }, (At_most | Exactly) -> Logic.Integer limit
    | _ -> unknown_amount context frame counter
  in
  match counter.resource with
  | Time -> time_of context frame (Types.Function function_type) callee_term
  | Allocations -> by_clause Types.Allocations
  | Allocated_bytes -> by_clause Types.Allocated_bytes
  | Calls (Through term) ->
      if lambda_captures_target context callee_term term then unknown_amount context frame counter
      else
        spent_where
          (may_be_target context frame callee_term (Types.Function function_type) term)
          (Logic.int 1)
  | Calls (Capability path | Capability_method (path, _)) ->
      if
        List.exists
          (function
            | Types.Capability used -> Path.equal used path
            | Types.Capability_parameter _ | Types.Capability_projection _
            | Types.Capability_variable _ ->
                true)
          (function_type.uses :> Types.capability list)
      then unknown_amount context frame counter
      else Costs.zero

(* The intrinsic storage and view operations, as the compiler declares
   them: a storage or a view is modeled as the sequence of its elements,
   and each operation reads or changes that sequence. An operation that
   stops the program on a bad index assumes on return that the index was
   valid. *)
and buffer_operation context frame ~(node : expression) (operation : Intrinsic.operation) element
    operands ~changed known =
  let length sequence = sequence_length context element sequence in
  (* No buffer is larger than C lets an object be, half the address space,
     so a buffer's length fits an [ISize] as well as a [USize]. *)
  let fits value =
    Logic.(Operation ("<=", [ int 0; value ]) &&& in_range (Types.builtin ISize) value)
  in
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
      Logic.(Operation ("<=", [ length sequence; capacity term ]) &&& fits (capacity term));
    sequence
  in
  let needs ?(requirement = "have the room it writes into") condition =
    oblige context frame Requires (at frame node)
      (Printf.sprintf "`%s` may not %s." (quote frame.source node.origin) requirement)
      condition
  in
  let keeps_capacity () =
    assume context frame (Logic.equal (capacity (List.hd changed)) (capacity (List.hd operands)))
  in
  let at = element_at context element in
  let bound () = fresh_name context "index" in
  let in_interval index low high =
    Logic.(Operation ("<=", [ low; index ]) &&& Operation ("<", [ index; high ]))
  in
  let all name low high body =
    Logic.Forall ([ (name, Logic.Int) ], Logic.(in_interval (Symbol name) low high ==> body))
  in
  let in_bounds index sequence = in_interval index (Logic.int 0) (length sequence) in
  let each_sum relation =
    let measure = fresh_name context "measure" in
    Logic.Forall
      ( [ (measure, sort_of context (Types.Function (measure_type element))) ],
        relation
          (fun sequence -> sequence_sum context element sequence (Logic.Symbol measure))
          (fun value -> applied context (measure_type element) (Logic.Symbol measure) [ value ]) )
  in
  let changed_storage () = storage (List.hd changed) in
  match (operation, operands) with
  | Storage_model, [ buffer ] -> storage buffer
  | View_model, [ buffer ] -> view buffer
  | Storage_empty, _ ->
      assume context frame (Logic.equal (length (storage known)) (Logic.int 0));
      known
  | Storage_with_capacity, [ room ] ->
      assume context frame
        Logic.(equal (length (storage known)) (int 0) &&& equal (capacity known) room);
      known
  | Storage_length, [ buffer ] -> length (storage buffer)
  | View_length, [ buffer ] -> length (view buffer)
  | Storage_capacity, [ buffer ] ->
      ignore (storage buffer);
      capacity buffer
  | Storage_set_capacity, [ buffer; room ] ->
      needs (Logic.Operation (">=", [ room; length (storage buffer) ]));
      assume context frame (Logic.equal (changed_storage ()) (storage buffer));
      assume context frame (Logic.equal (capacity (List.hd changed)) room);
      known
  | Storage_lengthen, [ buffer; by ] ->
      (* The elements the C library wrote into the spare capacity join the storage. *)
      let before = storage buffer and after = changed_storage () in
      needs
        (Logic.Operation ("<=", [ Logic.Operation ("+", [ length before; by ]); capacity buffer ]));
      keeps_capacity ();
      let limit = bound () in
      assume context frame
        (Logic.equal (length after) (Logic.Operation ("+", [ length before; by ])));
      assume context frame
        (all limit (Logic.int 0) (length before)
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      known
  | Storage_shorten, [ buffer; shorter ] ->
      (* The first [shorter] elements, in the same room. *)
      let before = storage buffer and after = changed_storage () in
      needs ~requirement:"be given a length at most the storage's"
        (Logic.Operation ("<=", [ shorter; length before ]));
      keeps_capacity ();
      let limit = bound () in
      assume context frame (Logic.equal (length after) shorter);
      assume context frame
        (all limit (Logic.int 0) shorter
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      known
  | Storage_push, [ buffer; value ] ->
      needs (Logic.Operation ("<", [ length (storage buffer); capacity buffer ]));
      keeps_capacity ();
      let longer = appended context frame element (storage buffer) value in
      assume context frame (Logic.equal (changed_storage ()) longer);
      known
  | Storage_pop, [ _ ] ->
      keeps_capacity ();
      let longer = appended context frame element (changed_storage ()) known in
      assume context frame (Logic.equal (storage (List.hd operands)) longer);
      known
  | Storage_insert, [ buffer; index; value ] ->
      let before = storage buffer and after = changed_storage () in
      needs (Logic.Operation ("<", [ length before; capacity buffer ]));
      keeps_capacity ();
      let limit = bound () in
      assume context frame
        (Logic.conjunction
           [
             Logic.Operation ("<=", [ Logic.int 0; index ]);
             Logic.Operation ("<=", [ index; length before ]);
             Logic.equal (length after) (Logic.Operation ("+", [ length before; Logic.int 1 ]));
             Logic.equal (at after index) value;
           ]);
      assume context frame
        (all limit (Logic.int 0) index
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      let limit = bound () in
      assume context frame
        (all limit index (length before)
           (Logic.equal
              (at after (Logic.Operation ("+", [ Logic.Symbol limit; Logic.int 1 ])))
              (at before (Logic.Symbol limit))));
      let limit = bound () in
      assume context frame
        (all limit
           (Logic.Operation ("+", [ index; Logic.int 1 ]))
           (length after)
           (Logic.equal (at after (Logic.Symbol limit))
              (at before (Logic.Operation ("-", [ Logic.Symbol limit; Logic.int 1 ])))));
      assume context frame
        (each_sum (fun sum measure ->
             Logic.equal (sum after) (Logic.Operation ("+", [ sum before; measure value ]))));
      known
  | Storage_remove, [ buffer; index ] ->
      keeps_capacity ();
      let before = storage buffer and after = changed_storage () in
      let limit = bound () in
      assume context frame
        (Logic.conjunction
           [
             in_bounds index before;
             Logic.equal (length after) (Logic.Operation ("-", [ length before; Logic.int 1 ]));
             Logic.equal known (at before index);
           ]);
      assume context frame
        (all limit (Logic.int 0) index
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      let limit = bound () in
      assume context frame
        (all limit index (length after)
           (Logic.equal (at after (Logic.Symbol limit))
              (at before (Logic.Operation ("+", [ Logic.Symbol limit; Logic.int 1 ])))));
      assume context frame
        (each_sum (fun sum measure ->
             Logic.equal (sum before) (Logic.Operation ("+", [ sum after; measure known ]))));
      known
  | (Storage_swap | View_swap), [ buffer; first; second ] ->
      let before, after =
        if operation = View_swap then (view buffer, view (List.hd changed))
        else begin
          keeps_capacity ();
          (storage buffer, changed_storage ())
        end
      in
      let limit = bound () in
      assume context frame
        (Logic.conjunction
           [
             in_bounds first before;
             in_bounds second before;
             Logic.equal (length after) (length before);
             Logic.equal (at after first) (at before second);
             Logic.equal (at after second) (at before first);
           ]);
      assume context frame
        (all limit (Logic.int 0) (length before)
           Logic.(
             not_ (equal (Symbol limit) first)
             &&& not_ (equal (Symbol limit) second)
             ==> equal (at after (Symbol limit)) (at before (Symbol limit))));
      assume context frame (each_sum (fun sum _ -> Logic.equal (sum after) (sum before)));
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
        Logic.(equal (view known) (storage buffer) &&& equal (changed_storage ()) (storage buffer));
      known
  | (Storage_take_view | View_take_view), [ owner; part; start ] ->
      (* The owner's elements from [start] are the view's, which changed
         them, and the owner is otherwise as it was. *)
      let before, after =
        if operation = View_take_view then (view owner, view (List.hd changed))
        else (storage owner, changed_storage ())
      in
      let run = view part in
      needs Logic.(Operation ("<=", [ Operation ("+", [ start; length run ]); length before ]));
      if operation = Storage_take_view then keeps_capacity ();
      run_replaced context frame element ~before ~after ~start
        ~stop:(Logic.Operation ("+", [ start; length run ]))
        ~run:(Some run);
      known
  | View_at, [ buffer; index ] ->
      assume context frame (in_bounds index (view buffer));
      at (view buffer) index
  | Storage_view, [ buffer ] ->
      assume context frame (Logic.equal (view known) (storage buffer));
      known
  | Compare_bytes, [ left; right ] -> byte_order context (view left) (view right)
  | View_slice, [ buffer; start; stop ] ->
      let whole = view buffer and part = view known in
      let limit = bound () in
      assume context frame
        (Logic.conjunction
           [
             Logic.Operation ("<=", [ Logic.int 0; start ]);
             Logic.Operation ("<=", [ start; stop ]);
             Logic.Operation ("<=", [ stop; length whole ]);
             Logic.equal (length part) (Logic.Operation ("-", [ stop; start ]));
           ]);
      assume context frame
        (all limit (Logic.int 0) (length part)
           (Logic.equal (at part (Logic.Symbol limit))
              (at whole (Logic.Operation ("+", [ start; Logic.Symbol limit ])))));
      known
  | _ -> known

(* [compare_bytes] of two byte sequences, as the compiler makes it: their
   lexicographic order, below zero, zero, or above zero, which is zero
   exactly when they are the same bytes, and is a total order. *)
and byte_order context left right =
  let sequence = sort_of context (sequence_type (Types.builtin UInt8)) in
  let symbol = Symbol.Compare_bytes_order in
  let first = not (Hashtbl.mem context.declared symbol) in
  declare context (Logic.Function (symbol, [ sequence; sequence ], Logic.Int));
  let order first_term second_term = Logic.Apply (symbol, [ first_term; second_term ]) in
  if first then begin
    let first_term = Logic.Symbol (variable "bytes.first")
    and second_term = Logic.Symbol (variable "bytes.second")
    and third_term = Logic.Symbol (variable "bytes.third") in
    let over names body = Logic.Forall (List.map (fun name -> (name, sequence)) names, body) in
    context.facts <-
      over
        [ variable "bytes.first"; variable "bytes.second" ]
        Logic.(
          Operation ("<=", [ int (-1); order first_term second_term ])
          &&& Operation ("<=", [ order first_term second_term; int 1 ])
          &&& (equal (order first_term second_term) (int 0) ==> equal first_term second_term)
          &&& equal (order second_term first_term)
                (Operation ("-", [ order first_term second_term ])))
      :: over [ variable "bytes.first" ] (Logic.equal (order first_term first_term) (Logic.int 0))
      :: over
           [ variable "bytes.first"; variable "bytes.second"; variable "bytes.third" ]
           Logic.(
             Operation ("<", [ order first_term second_term; int 0 ])
             &&& Operation ("<", [ order second_term third_term; int 0 ])
             ==> Operation ("<", [ order first_term third_term; int 0 ]))
      :: context.facts
  end;
  order left right

(* How many elements a storage has room for, as a function of it. *)
and buffer_capacity context element term =
  let ty =
    Types.Named { path = Intrinsic.builtin_path Storage; arguments = [ Types.Type element ] }
  in
  let symbol = Symbol.Capacity (type_key ty) in
  declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

(* The sequence a storage or a view holds, as a function of it. *)
and buffer_model context (builtin : Intrinsic.builtin) element term =
  let ty =
    Types.Named { path = Intrinsic.builtin_path builtin; arguments = [ Types.Type element ] }
  in
  let symbol = Symbol.Model (type_key ty) in
  declare context
    (Logic.Function (symbol, [ sort_of context ty ], sort_of context (sequence_type element)));
  Logic.Apply (symbol, [ term ])

(* Whether a call through a value of a function type is a function in the
   logic: it ends, uses no capabilities, changes none of its arguments, and
   returns its result. *)
and in_the_logic (function_type : Types.function_type) =
  Types.terminates function_type
  && function_type.uses = Types.no_capabilities
  && List.for_all (fun (mode, _) -> mode <> Types.Mut) function_type.inputs
  && match function_type.output with Returns _ -> true | _ -> false

(* A function value applied to its arguments, through the [apply] of its
   type's sorts. *)
and applied context (function_type : Types.function_type) callee arguments =
  let inputs = List.map (fun (_, input) -> sort_of context input) function_type.inputs in
  let output =
    sort_of context (match function_type.output with Returns output -> output | _ -> Types.unit)
  in
  let value_sort = sort_of context (Types.Function function_type) in
  let symbol = Symbol.Apply ((value_sort :: inputs) @ [ output ]) in
  declare context (Logic.Function (symbol, value_sort :: inputs, output));
  Logic.Apply (symbol, callee :: arguments)

(* Bound names for each input of a function type, at this depth of
   quantifiers. *)
and parameters_of context frame (function_type : Types.function_type) =
  let depth = List.length frame.bound in
  List.mapi
    (fun index (_, input) ->
      ( Symbol.Variable { label = "parameter"; numbers = [ depth; index ] },
        sort_of context (substituted context frame input) ))
    function_type.inputs

and time_of context frame (ty : Types.ty) term =
  let sort = sort_of context ty in
  let symbol = Symbol.Time sort in
  declare context (Logic.Function (symbol, [ sort ], Logic.Int));
  let time = Logic.Apply (symbol, [ term ]) in
  fact context frame (Logic.Operation ("<=", [ Logic.int 1; time ]));
  (match ty with
  | Types.Function { costs; _ }
    when List.exists
           (fun (cost : Types.cost) -> cost.resource = Types.Time && cost.bound = Order_of)
           costs ->
      fact context frame (Logic.equal time (Logic.int 1))
  | _ -> ());
  (match List.assoc_opt term context.lambda_times with
  | Some (bound, showing) ->
      (* The bound is used, so the obligations that show it are made. *)
      context.lambda_times <- List.remove_assoc term context.lambda_times;
      context.obligations <- List.rev_append showing context.obligations;
      fact context frame (Logic.equal time (Costs.larger (Logic.int 1) bound))
  | None -> ());
  time

(* The cost of building a record or a variant: one allocation, of its
   block, for a variant that is held by reference. *)
and construct_amount context frame (ty : Types.ty) variant (counter : Costs.counter) =
  match counter.resource with
  | (Allocations | Allocated_bytes) when not (indirect context ty variant) -> Costs.zero
  | Allocations -> Logic.int 1
  | Allocated_bytes when counter.counting = Units -> Logic.int 1
  | Allocated_bytes ->
      (* The size of the variant's block, which is fixed and not known
         here. *)
      let symbol = Symbol.Block_bytes { type_key = type_key ty; variant } in
      declare context (Logic.Constant (symbol, Logic.Int));
      fact context frame (Logic.Operation ("<=", [ Logic.int 1; Logic.Symbol symbol ]));
      Logic.Symbol symbol
  | Time | Calls _ -> Costs.zero

(* The cost of a call whose contract is not read. *)
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
                  | Types.Named { path; arguments = [ Types.Type element ] } -> (
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
              let amount_term =
                match amount with
                | Argument position ->
                    Option.map
                      (fun (passed : passed) -> passed.term)
                      (List.find_opt (fun (passed : passed) -> passed.position = position) values)
                | Generic name -> generic_argument context frame operation type_arguments name
              in
              match amount_term with
              | Some amount_term when resource = Allocations || counting = Units ->
                  Logic.ite
                    (Logic.Operation (">", [ amount_term; Logic.int 0 ]))
                    (Logic.int 1) (Logic.int 0)
              | _ -> unknown_amount context frame counter)
          | Unknown_allocations, _, _ -> unknown_amount context frame counter)
      | Calls _ -> Costs.zero)
  | Capability_method { capability; name } -> (
      let direct =
        match counter.resource with
        | Calls (Capability path) when Path.equal path capability -> Logic.int 1
        | Calls (Capability_method (path, method_))
          when Path.equal path capability && method_ = name ->
            Logic.int 1
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
                ~uses:(call_.uses :> Types.capability list)
                ~values ~change:None counter
          | None -> unknown_amount context frame counter))
  | Function _ | Trait_method _ | Indirect _ -> (
      match counter.resource with
      | Calls target ->
          spent_where
            (call_reaches context frame (call_.uses :> Types.capability list) values target)
            (unknown_amount context frame counter)
      | _ -> unknown_amount context frame counter)

and indirect context (ty : Types.ty) variant =
  match (ty, variant) with
  | Named { path; _ }, Some variant -> (
      match Query.demand context.database Interface.Environment.interface path with
      | Some (Interface.Environment.Type_interface { shape = Sum variants; _ }) ->
          List.exists
            (fun (written : Types.variant) -> written.variant_name = variant && written.indirect)
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
  | Log, [ log_argument ], [ argument ] ->
      let log = log_of context frame log_argument in
      (* [log] of a value of a bounded type is at most [log] of the type's
         largest value: its width, for an unsigned type. *)
      let rec unconverted (node : expression) =
        match node.kind with
        | Convert { conversion = To_integer; value = inner } -> unconverted inner
        | _ -> node
      in
      (match bounds (type_of context frame (unconverted argument)) with
      | Some (_, high) when not (Logic.mentions frame.bound log_argument) ->
          fact context frame
            Logic.(
              Operation ("<=", [ log_argument; Integer high ])
              ==> Operation ("<=", [ log; int (Z.numbits high) ]))
      | _ -> ());
      Some (frame, log)
  | Power, [ base; exponent ], _ -> Some (frame, power_of context frame base exponent)
  | Time, [ function_term ], [ function_value ] ->
      Some (frame, time_of context frame (type_of context frame function_value) function_term)
  | _ -> unsupported (at frame node) "this specification function"

and log_of context frame log_argument =
  declare context (Logic.Function (Symbol.Cost_log, [ Logic.Int ], Logic.Int));
  let rec add log_argument ~halving =
    match List.assoc_opt log_argument context.logs with
    | Some true -> ()
    | Some false when not halving -> ()
    | seen ->
        if seen = None then
          List.iter
            (fun (other, _) -> fact context frame (Costs.log_order log_argument other))
            context.logs;
        context.logs <- (log_argument, halving) :: List.remove_assoc log_argument context.logs;
        let facts, half = Costs.log_facts log_argument ~halving in
        List.iter (fact context frame) facts;
        Option.iter (fun half -> add half ~halving:false) half
  in
  if not (Logic.mentions frame.bound log_argument) then add log_argument ~halving:true;
  (* Of a number, it is the number's bit length: the smallest integer at
     least log2(n + 1). *)
  (match log_argument with
  | Logic.Integer limit ->
      fact context frame
        (Logic.equal
           (Logic.Apply (Symbol.Cost_log, [ log_argument ]))
           (Logic.int (if Z.sign limit <= 0 then 0 else Z.numbits limit)))
  | _ -> ());
  Logic.Apply (Symbol.Cost_log, [ log_argument ])

and power_of context frame base exponent =
  declare context (Logic.Function (Symbol.Cost_power, [ Logic.Int; Logic.Int ], Logic.Int));
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
  (if not (Logic.mentions frame.bound base || Logic.mentions frame.bound exponent) then
     match add exponent with
     | Some (step, previous) ->
         fact context frame step;
         ignore (add previous)
     | None -> ());
  (* Of two numbers, it is their power. *)
  (match (base, exponent) with
  | Logic.Integer base_value, Logic.Integer exponent_value
    when Z.sign exponent_value >= 0 && Z.leq exponent_value (Z.of_int 256) ->
      fact context frame
        (Logic.equal
           (Logic.Apply (Symbol.Cost_power, [ base; exponent ]))
           (Logic.Integer (Z.pow base_value (Z.to_int exponent_value))))
  | _ -> ());
  Logic.Apply (Symbol.Cost_power, [ base; exponent ])

(* [time(Types.method)]: the longest any one call of a trait's method on a type
   takes in this run, a constant of the run, at least one step. It is one
   symbol for each method and type, so a callee's bound and its caller's
   are about the same term. *)
and method_time context frame (callee : callee) =
  match callee with
  | Trait_method { trait; name; receiver; self_type; _ } ->
      trait_method_time context frame
        (Path.Method { owner = trait.trait; name; receiver })
        (substituted context frame self_type)
  | _ -> raise (Foreign_unsupported "the time of a function that is not a trait's method")

and trait_method_time context frame (method_ : Path.t) self_type =
  let symbol = Symbol.Method_time { method_; self_type = type_key self_type } in
  declare context (Logic.Constant (symbol, Logic.Int));
  fact context frame (Logic.Operation ("<=", [ Logic.int 1; Logic.Symbol symbol ]));
  (match method_time_bound context method_ self_type with
  | Some limit ->
      fact context frame
        (Logic.Operation ("<=", [ Logic.Symbol symbol; Logic.Integer (Z.max limit Z.one) ]))
  | None -> ());
  Logic.Symbol symbol

(* A bound on [time(Types.method)] for a known type: a copy of a [Plain] value
   that holds no potential takes one step, and the method of an [impl] whose
   time clause is a constant [O(k)] takes at most [k] counted as a call is,
   where it makes no potential, since nothing it changes or returns can
   hold any. *)
and method_time_bound context (method_ : Path.t) self_type =
  let holds ty = try has_potential context ty with Foreign_unsupported _ -> true in
  match method_ with
  | Method { owner = trait; name; receiver } -> (
      if Path.equal trait Interface.Impls.copyable_path then
        if
          Interface.Impls.plain context.database ~bounds:(current_bounds context) self_type
          && not (holds self_type)
        then Some Z.one
        else None
      else
        let reference : Types.trait_reference = { trait; trait_arguments = []; associated = [] } in
        match concrete_impl context reference self_type with
        | Some (impl, arguments) -> (
            let path = Path.Method { owner = impl; name; receiver } in
            let makes_no_potential =
              match Interface.Impls.signature context.database path with
              | Some (signature : Types.signature) -> (
                  List.for_all
                    (fun (parameter : Types.parameter_info) ->
                      parameter.mode <> Types.Mut || not (holds parameter.type_))
                    signature.parameters
                  && (match signature.receiver with Some (Mut, ty) -> not (holds ty) | _ -> true)
                  && match signature.output with Returns ty -> not (holds ty) | _ -> false)
              | None -> false
            in
            match
              method_contract ?reading_package:(reading_package context) context.database reference
                name receiver
                (Impl { impl; arguments })
            with
            | Some contract when makes_no_potential ->
                List.find_map
                  (fun (part : part) ->
                    List.find_map
                      (fun (cost : Core.cost) ->
                        match cost with
                        | {
                         resource = Time;
                         amortized = false;
                         bound = Order_of { kind = Integer limit; _ };
                         _;
                        } ->
                            Some limit
                        | _ -> None)
                      part.costs)
                  contract.parts
            | _ -> None)
        | None -> None)
  | _ -> None

(* A built-in copy: of a [Plain] value that holds no potential, a copy of
   its bits; of any other, a call of [Copyable.copy], which takes
   [time(Types.copy)] and pays for the potential the copy holds, as a trait's
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
            let copy_potential =
              try potential context frame ty term
              with Unsupported _ | Foreign_unsupported _ -> Costs.zero
            in
            Costs.minus (Costs.plus time (Logic.int 1)) copy_potential
        | _ -> unknown_amount context frame counter)

(* Loops' costs. A loop's [cost] clause about a counter bounds the loop's
   cost so far at its head, on entry and after each iteration, and after
   the loop the loop costs the clause's bound, as a call with that bound
   would. Any other counter is bounded by the iterations so far times a
   per-iteration bound, [per], which is inferred from the body's cost and
   then proven of each iteration.

   Where the values a loop changes hold potential, which amortized callees
   spend and save, a second bound, [per_held], bounds the loop's cost so far
   plus the potential it holds. That sum telescopes when each iteration
   spends potential that earlier ones saved. Both bounds are assumed at the
   head. The assumption is sound even before the bound is inferred, since
   each run of the loop has a last iteration. Only the bound an iteration's
   cost needs is inferred and proven. [held] maps a frame to the potential
   of the values the loop changes. *)
and loop_costs context frame (clauses : loop_clause list) ~held =
  List.map
    (fun (counter : Costs.counter) ->
      let entry =
        match List.assoc_opt counter frame.spent with Some term -> term | None -> Costs.zero
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
        | Some cost -> Clause_bound cost
        | None ->
            Per_iteration
              {
                per = fresh context frame "per" Logic.Int;
                per_held =
                  Option.map (fun held -> (fresh context frame "per" Logic.Int, held frame)) held;
              }
      in
      { counter; entry; rule; held })
    context.counters

and counting_of (cost : Core.cost) : Costs.counting =
  match cost.bound with Order_of _ | Finite -> Units | At_most _ -> At_most | Exactly _ -> Exactly

(* That a loop's [cost] clause bounds the loop's cost so far, at [at]. *)
and loop_clause_holds context (at : frame) (counter : Costs.counter) (cost : Core.cost) ~since =
  let amount =
    match cost.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (value context { at with checking = false } amount)
    | Finite -> Costs.zero
  in
  match counter.counting with
  | Units -> Costs.at_most since (Costs.bound amount)
  | Exactly -> Logic.equal since amount
  | At_most -> Costs.at_most since amount

and spent_at (frame : frame) key =
  match List.assoc_opt key frame.spent with Some spent_term -> spent_term | None -> Costs.zero

(* A counter's bounded term at the head and where the loop is left:
   its value, plus the potential the loop holds there, for [per_held]. *)
and counted_with ~(counter : Costs.counter) ~at ~bound =
  if counter.counting = Exactly then Logic.equal at bound else Costs.at_most at bound

(* The head of a loop: each counter takes a fresh value, within its
   clause, or within its iterations so far times its bounds on one. *)
and loop_head context head costs ~iterations =
  let iterations = Option.value iterations ~default:Costs.zero in
  let head =
    {
      head with
      spent = List.map (fun cost -> (cost.counter, fresh context head "spent" Logic.Int)) costs;
    }
  in
  List.iter
    (fun cost ->
      let at_head = spent_at head cost.counter in
      match cost.rule with
      | Clause_bound written ->
          assume context head
            (loop_clause_holds context head cost.counter written
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
      | Clause_bound written ->
          (* The bound is well defined, as every specification must be. *)
          (match written.bound with
          | Order_of amount | At_most amount | Exactly amount -> ignore (value context frame amount)
          | Finite -> ());
          oblige context frame Cost
            (span_of frame.source written.origin)
            (Printf.sprintf "The loop's `%s` may not hold on entry to the loop."
               (quote frame.source written.origin))
            (loop_clause_holds context frame cost.counter written ~since:Costs.zero)
      | Per_iteration _ -> ())
    costs

(* After the body: each per-iteration bound is inferred from the costs of
   the iterations that completed, and every iteration, completed or exited
   by [break], is proven to be within its counter's bound. An iteration that
   spends or saves potential is bounded with the potential the loop
   holds. *)
and loop_iterations context (loop : statement) head costs ~mark ~facts ~ends ~breaks =
  let span = span_of head.source loop.origin in
  List.iter
    (fun cost ->
      match cost.rule with
      | Clause_bound written_cost ->
          List.iter
            (fun (frame, when_) ->
              oblige context frame Cost
                (span_of frame.source written_cost.origin)
                (Printf.sprintf "The loop's `%s` may not hold %s."
                   (quote frame.source written_cost.origin)
                   when_)
                (loop_clause_holds context frame cost.counter written_cost
                   ~since:(Costs.minus (spent_at frame cost.counter) cost.entry)))
            (List.map (fun exit_frame -> (exit_frame, "after an iteration")) ends
            @ List.map (fun exit_frame -> (exit_frame, "where the loop is left")) breaks)
      | Per_iteration { per; per_held } -> (
          let frames = ends @ breaks in
          let plain (frame : frame) =
            Costs.since ~start:(spent_at head cost.counter) (spent_at frame cost.counter)
          in
          (* Where an iteration spends or saves potential, its cost is
             bounded with the potential the loop holds, which telescopes,
             or, where that is not found, by itself; otherwise by itself. *)
          let held_rule =
            match (per_held, cost.held) with
            | Some (per_held, _), Some held
              when List.exists (fun exit_frame -> mentions_potential (plain exit_frame)) frames ->
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
              (Costs.bound_on ~varies:(mentions_fresh_after context mark) ~facts most)
          in
          match List.find_map bounded (held_rule @ [ (per, plain) ]) with
          | Some (per, spent, bound) ->
              fact context head (Logic.equal per bound);
              List.iter2
                (fun (frame : frame) spent ->
                  oblige context frame Cost span
                    "The prover cannot show that this iteration of the loop costs no more than the \
                     per-iteration bound it inferred from the values the loop does not change: \
                     give the loop a `cost` clause."
                    (counted_with ~counter:cost.counter ~at:spent ~bound:per))
                frames spent
          | None ->
              oblige context head Cost span
                "The prover cannot bound the cost of one iteration of this loop by the values the \
                 loop does not change, so it cannot count the loop's cost: give the loop a `cost` \
                 clause."
                (Logic.Boolean false)))
    costs

(* Where the loop is left: a counter bounded by a clause counts as the
   clause, and one bounded by its iterations is also bounded by each upper
   bound [most] on them, which is arithmetic, so assumed. *)
and loop_exit context (exit_ : frame) costs ~iterations ~most =
  let iterations = Option.value iterations ~default:Costs.zero in
  let spent =
    List.map
      (fun cost ->
        let at = spent_at exit_ cost.counter in
        match cost.rule with
        | Clause_bound written ->
            let amount =
              match written.bound with
              | Order_of amount | At_most amount | Exactly amount ->
                  snd (value context { exit_ with checking = false } amount)
              | Finite -> Costs.zero
            in
            let counted =
              match cost.counter.counting with
              | Units -> Costs.units amount
              | At_most -> bounded_amount context exit_ amount
              | Exactly -> amount
            in
            (cost.counter, Costs.plus cost.entry counted)
        | Per_iteration { per; per_held } ->
            let bounded ~at ~start per =
              if cost.counter.counting <> Exactly then
                List.iter
                  (fun most ->
                    fact context exit_
                      Logic.(
                        conjunction
                          [
                            Costs.at_most at (Costs.plus start (Costs.times iterations per));
                            Operation ("<=", [ int 0; iterations ]);
                            Operation ("<=", [ iterations; most ]);
                            Operation ("<=", [ int 0; per ]);
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
            (cost.counter, at))
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
and potential_clause context (ty : Types.ty) =
  match type_source context ty with
  | Some ({ core = { definition = Type { potential = Some value; _ }; _ }; _ } as source) ->
      Some (source, value)
  | _ -> None

(* Whether a value of a type can hold potential: its type declares one, or
   a part of it can, whether or not this package sees its fields, or it is a
   growable buffer, a storage or a type whose model is the sequence one
   holds, which saves potential for growing. A type parameter may stand for
   such a type. *)
and has_potential context ?(seen = []) (ty : Types.ty) =
  if seen <> [] then holds_potential_type context ~seen ty
  else
    let key = type_key ty in
    match Hashtbl.find_opt context.holds_potential key with
    | Some holds -> holds
    | None ->
        let holds = holds_potential_type context ~seen ty in
        Hashtbl.replace context.holds_potential key holds;
        holds

and holds_potential_type context ~seen (ty : Types.ty) =
  if List.exists (Types.equal ty) seen then false
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
                  (List.map
                     (fun (generic : Types.generic) -> generic.generic)
                     interface.type_generics)
                  arguments
              with Invalid_argument _ -> []
            in
            let fields =
              match interface.shape with
              | Record fields -> fields
              | Sum variants ->
                  List.concat_map
                    (fun (variant : Types.variant) -> Option.value variant.fields ~default:[])
                    variants
              | Todo_type | Builtin_type _ | Error_shape _ -> []
            in
            List.exists
              (fun (field : Types.field) ->
                has_potential context ~seen:(ty :: seen)
                  (Types.substitute substitution field.field_type))
              fields
        | _ -> false)
    | Named { arguments; _ } ->
        if
          List.exists
            (function
              | Types.Type element -> has_potential context ~seen:(ty :: seen) element | _ -> false)
            arguments
        then raise (Foreign_unsupported "the potential of a collection's elements")
        else false
    | _ -> false

(* The potential a value holds: a function of it in the logic, at least
   zero for a valid value, as each type with a potential shows, and its
   type's own potential plus its parts', unfolded once for each value it is
   asked of. *)
and potential context frame ?(seen = []) (ty : Types.ty) term =
  if not (has_potential context ty) then Costs.zero
  else begin
    let held = held_symbol context ty term in
    if (not (List.mem held context.potentials)) && not (Logic.mentions frame.bound term) then begin
      context.potentials <- held :: context.potentials;
      fact context frame
        Logic.(validity context frame ~assuming:true ty term ==> Operation ("<=", [ int 0; held ]));
      match (potential_clause context ty, constructors context ty) with
      (* A type with visible fields holds its fields' potential; one with
         opaque fields, such as a [List] outside its package, is read as the
         buffer its model says it is. *)
      | None, None when Option.is_some (buffer_elements context ty) -> (
          (* A buffer's potential is its slack for growing, as a
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
                Logic.(
                  Operation ("<=", [ int 0; slack ])
                  &&& Operation ("<=", [ slack; Operation ("*", [ int 2; length ]) ]));
              (match ty with
              | Named { path; _ } when Intrinsic.builtin_of_path path = Some Storage ->
                  let saved =
                    Logic.Operation
                      ( "-",
                        [
                          Logic.Operation ("*", [ Logic.int 2; length ]);
                          buffer_capacity context element term;
                        ] )
                  in
                  fact context frame
                    (Logic.equal slack
                       (Logic.ite
                          (Logic.Operation (">=", [ saved; Logic.int 0 ]))
                          saved (Logic.int 0)))
              | Named { path; _ }
                when Intrinsic.builtin_of_path path = Some View
                     || Intrinsic.builtin_of_path path = Some Array ->
                  fact context frame (Logic.equal slack (Logic.int 0))
              | _ -> ());
              let elements =
                if has_potential context element then
                  sequence_sum context element sequence (potential_measure context element)
                else Costs.zero
              in
              fact context frame (Logic.equal held (Costs.plus slack elements))
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
                          Logic.ite
                            (Logic.Is (constructor_name ty variant, term))
                            (parts one) otherwise)
                        (parts last) earlier
                  | [] -> Costs.zero)
            in
            fact context frame (Logic.equal held (Costs.plus own parts))
          with Unsupported _ | Foreign_unsupported _ -> ())
      | _ -> ()
    end;
    (* A record that holds no potential of its own holds its parts' potential,
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
          (if List.exists (Types.equal field_type) (ty :: seen) then
             held_symbol context field_type part
           else potential context frame ~seen:(ty :: seen) field_type part)
      else total)
    Costs.zero fields

(* A growable buffer's elements and model: a storage, by its own model, or
   a type whose [Model] is the sequence of the storage it holds in its one
   field, as a [List] and a [String] are. *)
and buffer_elements context (ty : Types.ty) =
  let key = type_key ty in
  match Hashtbl.find_opt context.buffers key with
  | Some elements -> elements
  | None ->
      let elements = find_buffer_elements context ty in
      Hashtbl.replace context.buffers key elements;
      elements

and find_buffer_elements context (ty : Types.ty) =
  match ty with
  | Named { path; arguments = [ Types.Type element; Types.Value _ ] }
    when Intrinsic.builtin_of_path path = Some Array ->
      Option.map
        (fun model_of -> (element, model_of))
        (model_function context ty ~model:(sequence_type element))
  | Named { path; arguments = [ Types.Type element ] }
    when Intrinsic.builtin_of_path path = Some Storage ->
      Some (element, fun term -> buffer_model context Storage element term)
  | Named { path; arguments = [ Types.Type element ] }
    when Intrinsic.builtin_of_path path = Some View ->
      Some (element, fun term -> buffer_model context View element term)
  | Named { path; arguments } when builtin ty = None -> (
      match Query.demand context.database Interface.Environment.interface path with
      | Some (Interface.Environment.Type_interface { shape = Record [ field ]; type_generics; _ })
        -> (
          let substitution =
            try
              List.combine
                (List.map (fun (generic : Types.generic) -> generic.generic) type_generics)
                arguments
            with Invalid_argument _ -> []
          in
          match Types.substitute substitution field.field_type with
          | Named { path = field_path; arguments = [ Types.Type element ] }
            when Intrinsic.builtin_of_path field_path = Some Storage
                 || Intrinsic.builtin_of_path field_path = Some View ->
              Option.map
                (fun model_of -> (element, model_of))
                (model_function context ty ~model:(sequence_type element))
          | _ -> None)
      | _ -> None)
  | _ -> None

(* A buffer's slack for growing, as a function of it. *)
and buffer_slack context (ty : Types.ty) term =
  let symbol = Symbol.Slack (type_key ty) in
  declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

(* A value's potential as a measure, for a sum over a collection of such
   values: applied, it is the potential. *)
and potential_measure context element =
  let symbol = Symbol.Potential_measure (type_key element) in
  let measure = measure_type element in
  declare context (Logic.Constant (symbol, sort_of context (Types.Function measure)));
  let term = Logic.Symbol symbol in
  if not (List.mem term context.potentials) then begin
    context.potentials <- term :: context.potentials;
    let each = Symbol.Variable { label = "potential.element"; numbers = [] } in
    context.facts <-
      Logic.Forall
        ( [ (each, sort_of context element) ],
          Logic.equal
            (applied context measure term [ Logic.Symbol each ])
            (held_symbol context element (Logic.Symbol each)) )
      :: context.facts
  end;
  term

and held_symbol context ty term =
  let symbol = Symbol.Potential (type_key ty) in
  declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

(* The facts since a mark in the list, which is kept reversed. *)
and facts_since context count =
  let rec take count list =
    if count <= 0 then []
    else match list with [] -> [] | item :: rest -> item :: take (count - 1) rest
  in
  take (List.length context.facts - count) context.facts

(* Statements and blocks *)

and block_value context frame (body : block) =
  let rec value_after frame = function
    | [] -> (
        match body.value with
        | Some last -> expression context frame last
        | None -> Some (frame, Logic.Boolean true))
    | statement_ :: rest -> (
        match statement context frame statement_ with
        | Some frame -> value_after frame rest
        | None -> None)
  in
  match value_after frame body.statements with
  | Some (after, term) ->
      (* Locals declared inside the block end with it. *)
      Some (end_scope ~outer:frame after, term)
  | None -> None

and statement context frame (node : statement) : frame option =
  if frame.source.key = Some context.home then
    try statement_kind context frame node
    with Foreign_unsupported message ->
      raise (Unsupported (span_of frame.source node.origin, message))
  else statement_kind context frame node

(* A proof is ghost code, which a build leaves out: its facts are known
   after it, but the program continues from where it was, with nothing the
   proof changed, whichever way the proof ends, or if it never ends. A
   [todo] in it stands for the proof still to write, so the code after it is
   not proven on the paths that reach one, which this returns. *)
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
      Logic.disjunction context.unfinished)

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
      match block_value context (restrict frame (Logic.not_ matched)) otherwise with
      | Some (fallen, _) ->
          oblige context fallen Unreachable span
            "This `else` block may finish, but it must leave the path, since the pattern did not \
             match."
            (Logic.Boolean false);
          Some (restrict bound matched)
      | None -> Some (restrict bound matched))
  | Assign { target; value = assigned } ->
      let frame, new_value = value context frame assigned in
      with_target_keys context frame target (fun frame ->
          Some (store context frame target new_value))
  | Compound_assign { target; operand; bound; value = updated } ->
      let frame, right = operand_value context frame operand in
      let frame = { frame with locals = Locals.add bound right frame.locals } in
      with_target_keys context frame target (fun frame ->
          let frame, current = place_value context frame target in
          let after, new_value = value context { frame with updating = Some current } updated in
          Some (store context { after with updating = frame.updating } target new_value))
  | While { condition; clauses; body; _ } -> while_ context frame node condition clauses body
  | For { pattern; iteration; clauses; body; _ } ->
      (* A loop's iterations change disjoint places, so however they run, as
         tasks or at once, they can be read one after another. *)
      for_ context frame node pattern iteration clauses body
  | Assert { condition = { value = asserted; _ }; by_bit_vector } ->
      if by_bit_vector && not (is_test context) then bit_vector_assertion context frame asserted;
      let frame, term = value context frame asserted in
      if is_test context || by_bit_vector then assume context frame term
      else
        oblige context frame Assertion (at frame asserted)
          (Printf.sprintf "`%s` may not hold." (quote frame.source asserted.origin))
          term;
      Some frame
  | Proof block_ -> Some (restrict frame (Logic.not_ (ghost context frame block_)))
  | Parallel branches ->
      (* Branches are disjoint, so they can run in order. *)
      List.fold_left
        (fun frame branch ->
          match frame with Some frame -> statement context frame branch | None -> None)
        (Some frame) branches
  | Concurrent branches -> concurrent context frame node branches
  | Yield { mode; part } -> yield_part context frame node mode part

(* An [assert ... by bit_vector], proven in a query of its own: for every
   value of the integers and booleans it names, with its bitwise
   operations defined exactly. It holds of every value, so it holds of the
   values it is asserted of, and the caller assumes it. *)
and bit_vector_assertion context frame (asserted : expression) =
  let named = ref [] in
  Core_walk.expression
    (Core_walk.deep
       {
         Core_walk.ignore_all with
         place =
           (function
           | Local { local; type_; _ } when not (List.mem_assoc local !named) ->
               named := (local, type_) :: !named
           | _ -> ());
       })
    asserted;
  let saved_facts = context.facts and saved_decisions = context.decisions in
  let saved_stated = Hashtbl.copy context.stated in
  context.facts <- [];
  context.decisions <- [];
  let isolated =
    { frame with condition = Logic.Boolean true; bound = []; binders = []; checking = false }
  in
  let isolated =
    List.fold_left
      (fun (inside : frame) (local, ty) ->
        let symbol = fresh context inside "asserted" (sort_of context ty) in
        assume context inside (in_range ty symbol);
        match local with
        | Core.Self -> { inside with self = Some symbol }
        | _ -> { inside with locals = Locals.add local symbol inside.locals })
      isolated !named
  in
  let _, term = value context isolated asserted in
  let obligation =
    make_obligation context { isolated with checking = true } Assertion (at frame asserted)
      (Printf.sprintf "`%s` may not hold for every value of the variables it names."
         (quote frame.source asserted.origin))
      term
  in
  context.obligations <- { obligation with query = exactly obligation.query } :: context.obligations;
  context.facts <- saved_facts;
  context.decisions <- saved_decisions;
  Hashtbl.reset context.stated;
  Hashtbl.iter (Hashtbl.replace context.stated) saved_stated

(* A [concurrent] block. Its branches change disjoint places, and a
   capability call gives a fresh value whoever calls in between, so they
   are read one after another, as [parallel]'s are. An early exit from a
   branch takes effect where the block ends, after the other branches,
   which are cancelled and run to their own ends: each later branch runs
   from where the exit was as well as from where the branches before it
   ended, and each exit is then taken with its path's changes, or, if
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
                  (* The branch exited too, so either exit may be the one
                     taken, with the branch's effects before it exited. *)
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
(* [given], where the MIR gives the part: its value, whether it lends places,
   and how the caller's changes to it are written back to them. *)
and yield_part ?given context frame (node : statement) (mode : Types.mode) (part : operand) =
  let span = span_of frame.source node.origin in
  match (context.yielded_part, context.yield_ensures, frame.yielded_so_far) with
  | Some (part_type, kind), Some (each, at_end), Some before ->
      let frame, handed, lends, write_back =
        match given with
        | Some (handed, lends, write_back) -> (frame, handed, lends, write_back)
        | None ->
            let frame, handed = operand_value context frame part in
            ( frame,
              handed,
              Core_walk.lent_places part <> [],
              fun frame after -> written_back context frame part part_type after )
      in
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
        ~when_:"for the part yielded here";
      check_valid context frame span part_type handed ~deep:true ~when_:"for the part yielded here";
      (* The caller's changes to a part lent [mut] are written to each lent
         place. *)
      let frame, part_after =
        if mode = Types.Mut && lends then (
          let part_after = arrive context frame "lent" part_type in
          if kind = `Lends then
            context.lent_back <- (part_type, handed, part_after) :: context.lent_back;
          (write_back frame part_after, part_after))
        else (frame, handed)
      in
      let after = appended context frame part_type before part_after in
      let frame = { frame with yielded_so_far = Some after } in
      if kind = `Yields then begin
        show at_end ~at:frame ~result:None ~yielded:after ~finished:(Some (Logic.Boolean false))
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
                        Logic.ite
                          (Logic.Is (constructor_name ty variant, after))
                          selected
                          (arrive context frame "lent" field_type)
                  in
                  written_back context frame field field_type value
              | _ -> frame)
            frame fields
      | None -> raise (Foreign_unsupported (Printf.sprintf "the fields of `%s`" (Types.show ty))))
  | Value _ -> frame

(* A storage whose element at [index] is [part], and which is otherwise the
   one it was. *)
and storage_updated context frame element storage index part =
  let storage_type =
    Types.Named { path = Intrinsic.builtin_path Storage; arguments = [ Types.Type element ] }
  in
  let updated = arrive context frame "changed" storage_type in
  replaced context frame element
    ~before:(buffer_model context Storage element storage)
    ~after:(buffer_model context Storage element updated)
    index part;
  assume context frame
    (Logic.equal
       (buffer_capacity context element updated)
       (buffer_capacity context element storage));
  updated

(* An array whose element at [index] is [part], and which is otherwise the
   one it was. *)
and array_updated context frame (array_type : Types.ty) array index part =
  match array_type with
  | Named { arguments = Types.Type element :: _; _ } ->
      let updated = arrive context frame "changed" array_type in
      replaced context frame element
        ~before:(array_model context frame array_type array)
        ~after:(array_model context frame array_type updated)
        index part;
      updated
  | _ -> raise (Foreign_unsupported (Printf.sprintf "the elements of `%s`" (Types.show array_type)))

(* The owner of a slice lent to change, after the change: as long as it
   was, and the same outside the slice's run. *)
and sliced_owner_changed context frame (base : place) ~start ~stop =
  let owner_type = place_type context frame base in
  let element =
    match owner_type with
    | Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> raise (Foreign_unsupported (Printf.sprintf "a slice of `%s`" (Types.show owner_type)))
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
  | _ -> raise (Foreign_unsupported (Printf.sprintf "a slice of `%s`" (Types.show owner_type)))

(* That one sequence is another as long, the same outside the run from
   [start] to before [stop], and, where [run] is given, [run]'s elements in
   that run. *)
and run_replaced context frame element ~before ~after ~start ~stop ~run =
  let length sequence = sequence_length context element sequence in
  let at = element_at context element in
  let limit = fresh_name context "index" in
  let index = Logic.Symbol limit in
  let inside =
    match run with
    | Some run -> Logic.equal (at after index) (at run (Logic.Operation ("-", [ index; start ])))
    | None -> Logic.Boolean true
  in
  assume context frame (Logic.equal (length after) (length before));
  assume context frame
    (Logic.Forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           Operation ("<=", [ int 0; index ])
           &&& Operation ("<", [ index; length before ])
           ==> ite
                 (Operation ("<=", [ start; index ]) &&& Operation ("<", [ index; stop ]))
                 inside
                 (equal (at after index) (at before index))) ))

(* That one sequence is another with the element at [index] replaced by
   [part]. *)
and replaced context frame element ~before ~after index part =
  let length sequence = sequence_length context element sequence in
  let at = element_at context element in
  let limit = fresh_name context "index" in
  assume context frame
    (Logic.conjunction
       [ Logic.equal (length after) (length before); Logic.equal (at after index) part ]);
  assume context frame
    (Logic.Forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           Operation ("<=", [ int 0; Symbol limit ])
           &&& Operation ("<", [ Symbol limit; length before ])
           &&& not_ (equal (Symbol limit) index)
           ==> equal (at after (Symbol limit)) (at before (Symbol limit))) ))

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
            Logic.Apply
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
            (Foreign_unsupported
               (Printf.sprintf "assigning to a field of `%s`" (Types.show base_type))))
  | Lent
      {
        kind =
          Call
            {
              callee =
                Intrinsic { operation = Storage_at_mut; type_arguments = Types.Type element :: _ };
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
              callee =
                Intrinsic { operation = View_at_mut; type_arguments = Types.Type element :: _ };
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
  | Lent { kind = Call { lends = Some Types.Mut; _ }; _ } ->
      store_lent context frame place (fun _ -> new_value)
  | Lent _ | Temporary _ -> raise (Foreign_unsupported "assigning to this place")

(* Evaluates the index keys of an assignment's target, in order, and runs
   [f] with each key's term recorded, so that reading or storing the target
   in [f] evaluates no key again. A key evaluated twice would run its
   effects twice. *)
and with_target_keys context frame target work =
  let rec keys frame (place : place) =
    match place with
    | Local _ | Constant _ | Temporary _ -> (frame, [])
    | Field { base; _ } -> keys frame base
    | Lent { kind = Call { arguments = receiver :: indexes; _ }; _ } ->
        let frame, outer =
          match receiver with
          | Passed { value = Place base; _ } -> keys frame base
          | _ -> (frame, [])
        in
        List.fold_left
          (fun (frame, evaluated) (index : argument) ->
            match index with
            | Passed { value = Value key; _ } ->
                let frame, term = value context frame key in
                (frame, (key.id, term) :: evaluated)
            | Passed { value = Place key; _ } ->
                let frame, inner = keys frame key in
                (frame, inner @ evaluated)
            | Default -> (frame, evaluated))
          (frame, outer) indexes
    | Lent _ -> (frame, [])
  in
  let frame, evaluated = keys frame target in
  let outer = context.evaluated_keys in
  context.evaluated_keys <- evaluated @ outer;
  Fun.protect ~finally:(fun () -> context.evaluated_keys <- outer) (fun () -> work frame)

(* Whether a place is a part, through fields, of a call's [mut] lent
   result. *)
and lent_root (place : place) =
  match place with
  | Lent { kind = Call { lends = Some Types.Mut; callee; _ }; _ } -> (
      match callee with
      | Intrinsic { operation = Storage_at_mut | Array_at_mut | View_at_mut; _ } -> false
      | _ -> true)
  | Field { base; _ } -> lent_root base
  | _ -> false

(* Stores into a part of a call's [mut] lent result: the call is made once,
   and the part's final value is [leave] of the part, so a field's new value
   is built into the part as lent. *)
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
              Logic.Apply
                ( constructor_name base_type None,
                  List.map
                    (fun (name_, _) ->
                      let current = selected context base_type None name_ base_value in
                      if name_ = field then leave current else current)
                    fields ))
      | _ ->
          raise
            (Foreign_unsupported
               (Printf.sprintf "assigning to a field of `%s`" (Types.show base_type))))
  | _ -> store context frame place (leave (snd (place_value context frame place)))

(* The values a loop's body may change, which are havocked at its head: the local
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
                  | Passed { mode = Types.Mut; value = Place place; _ } -> note place
                  | Passed { mode = Types.Mut; value = Value { kind = Slice { call }; _ }; _ } ->
                      let base, _, _ = slice_parts call in
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
          | Yield { mode = Types.Mut; part } -> List.iter note (Core_walk.lent_places part)
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
        let ty =
          match local_type context frame local with Some ty -> ty | None -> Types.Integer
        in
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
and preserved_validity context (entry : frame) (changed : changed) =
  let obligation name ty before read =
    match validity context entry ~assuming:false ~deep:true ty before with
    | Logic.Boolean true -> None
    | valid -> Some (name, ty, valid, read)
  in
  List.filter_map
    (fun local ->
      match (local_type context entry local, Locals.find_opt local entry.locals) with
      | Some ty, Some before ->
          obligation
            (Option.value (Hashtbl.find_opt context.local_names local) ~default:"a local")
            ty before
            (fun (at : frame) -> Locals.find_opt local at.locals)
      | _ -> None)
    changed.changed_locals
  @
  match (changed.changes_self, entry.self, entry.self_type) with
  | true, Some before, Some ty ->
      Option.to_list (obligation "self" ty before (fun (at : frame) -> at.self))
  | _ -> []

and assume_preserved_validity context head preserved =
  List.iter
    (fun (_, ty, valid_on_entry, read) ->
      match read head with
      | Some term ->
          assume context head
            (Logic.( ==> ) valid_on_entry (validity context head ~assuming:true ~deep:true ty term))
      | None -> ())
    preserved

and check_preserved_validity context end_ span preserved =
  List.iter
    (fun (name, ty, valid_on_entry, read) ->
      match read end_ with
      | Some term ->
          oblige context end_ Invariant span
            (Printf.sprintf "The invariant of `%s` may not hold for `%s` after an iteration."
               (Types.show ty) name)
            (Logic.( ==> ) valid_on_entry
               (validity context end_ ~assuming:false ~deep:true ty term))
      | None -> ())
    preserved

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
  (* The condition runs at the head of each iteration, so its changes and
     its cost are the iteration's. *)
  let { loop_costs = costs; fresh_mark = mark; facts_mark; preserved; havocked = head } =
    enter_loop context frame ~entry:frame clauses
      ~changed:(changed_places ~condition frame body)
      body
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
       its changes. *)
      when is_functional_expression left && is_functional_expression right ->
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
        let _, left_value = value context { at with checking = false } left in
        let _, right_value = value context { at with checking = false } right in
        match compared with
        | Less -> Some [ Logic.Operation ("-", [ right_value; left_value ]) ]
        | Less_equal ->
            Some
              [
                Logic.Operation
                  ("+", [ Logic.Operation ("-", [ right_value; left_value ]); Logic.int 1 ]);
              ]
        | Greater -> Some [ Logic.Operation ("-", [ left_value; right_value ]) ]
        | _ ->
            Some
              [
                Logic.Operation
                  ("+", [ Logic.Operation ("-", [ left_value; right_value ]); Logic.int 1 ]);
              ])
    | `None -> None
  in
  let start_measures = if context.terminates then measure_terms inside else None in
  if context.terminates && start_measures = None then
    oblige context inside Termination span "This loop may not end: give it a `decreases` clause."
      (Logic.Boolean false);
  (* With one measure, which every iteration shows to start at or above
     zero and to decrease, the loop runs at most one more time than the
     measure on entry. A ghost [last] is the measure at the start of the
     latest iteration. *)
  let most =
    match (start_measures, measure_terms frame, iterations) with
    | Some [ at_head ], Some [ on_entry ], Some iterations ->
        let last = fresh context head "last" Logic.Int in
        assume context head
          Logic.(
            equal iterations (int 0)
            ==> Operation ("<=", [ at_head; on_entry ])
            &&& (Operation (">=", [ iterations; int 1 ])
                ==> (Operation ("<=", [ int 0; last ])
                    &&& Operation
                          ( "<=",
                            [
                              Operation ("+", [ Operation ("-", [ iterations; int 1 ]); last ]);
                              on_entry;
                            ] )
                    &&& Operation ("<", [ at_head; last ]))));
        [ Costs.at_least_zero (Costs.plus on_entry (Logic.int 1)) ]
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
      check_preserved_validity context end_ span preserved;
      match (start_measures, measure_terms end_) with
      | Some before, Some after ->
          oblige context end_ Termination span "This loop's measure may not decrease."
            (lexicographically_less before after)
      | _ -> ())
    ends;
  let exit_ =
    loop_exit context
      { (restrict head (Logic.not_ test)) with loop = frame.loop }
      costs ~iterations ~most
  in
  let left =
    List.map
      (fun (frame' : frame) ->
        loop_exit context { frame' with loop = frame.loop } costs
          ~iterations:(Option.map (fun count -> Costs.plus count (Logic.int 1)) iterations)
          ~most)
      exits.breaks
  in
  leave_loop context frame (exit_ :: left)

(* The start of a loop, from the frame before it and [entry], the frame its
   invariants are checked in on entry. *)
and enter_loop context frame ~entry clauses ~changed body =
  let costs = loop_costs context frame clauses ~held:(held_by context frame changed) in
  loop_entry context entry costs;
  let fresh_mark = context.fresh and facts_mark = List.length context.facts in
  let preserved = preserved_validity context frame changed in
  let head = havoc context frame changed in
  assume_preserved_validity context head preserved;
  let havocked =
    if contains_yield body then { head with yielded_so_far = havoc_parts context head } else head
  in
  { loop_costs = costs; fresh_mark; facts_mark; preserved; havocked }

(* The frame after a loop, from the frames that leave it, without the
   locals declared inside it. *)
and leave_loop context frame frames =
  Option.map (end_scope ~outer:frame) (join_frames context frames)

(* The checks at the end of each iteration of a loop that receives parts:
   its invariants and the validity it keeps, in the frames [with_through]
   gives, whose [yielded] is the parts received through the iteration. *)
and end_iterations context frame (node : statement) clauses (start : loop_start) ~head ~inside ~ends
    ~breaks ~with_through =
  loop_iterations context node head start.loop_costs ~mark:start.fresh_mark
    ~facts:(facts_since context start.facts_mark @ [ inside.condition ])
    ~ends:(List.map with_through ends) ~breaks:(List.map with_through breaks);
  List.iter
    (fun (end_ : frame) ->
      check_invariants context (with_through end_) clauses ~when_:"after an iteration";
      check_preserved_validity context end_ (span_of frame.source node.origin) start.preserved)
    ends

(* A ghost count of a loop's iterations so far, when the loop counts a
   cost by them. *)
and iterations_so_far context head costs =
  if
    List.exists
      (fun (cost : loop_cost) ->
        match cost.rule with Per_iteration _ -> true | Clause_bound _ -> false)
      costs
  then begin
    let iterations = fresh context head "iterations" Logic.Int in
    assume context head (Logic.Operation ("<=", [ Logic.int 0; iterations ]));
    Some iterations
  end
  else None

and one_step (counter : Costs.counter) =
  match counter.resource with Time -> Logic.int 1 | _ -> Costs.zero

and for_ ?driven context frame (node : statement) (pattern : pattern) (iteration : iteration)
    clauses body =
  let outer = context.iteration_returns in
  context.iteration_returns <- [];
  let ended = loop_over ?driven context frame node pattern iteration clauses body in
  let returning, others =
    List.partition (fun (loop, _) -> loop = node.origin) context.iteration_returns
  in
  context.iteration_returns <- outer @ others;
  match (ended, returning) with
  | Some ended, (_, ty) :: _ ->
      (* Where an iteration returned, the function returns once the loop has
         ended, on a path of its own. *)
      let returned = fresh context ended "returned" Logic.Bool in
      let value = Option.map (fun ty -> arrive context ended "result" ty) ty in
      context.returns <- (restrict ended returned, value) :: context.returns;
      Some (restrict ended (Logic.not_ returned))
  | _ -> ended

and loop_over ?driven context frame (node : statement) (pattern : pattern) (iteration : iteration)
    clauses body =
  let span = span_of frame.source node.origin in
  match iteration with
  | Integer_range { start; stop; inclusive } ->
      let element = substituted context frame pattern.type_ in
      let frame, low, high =
        match driven with
        | Some { range = Some (low, high); _ } -> (frame, low, high)
        | _ ->
            let frame, low = value context frame start in
            let frame, high = value context frame stop in
            (frame, low, high)
      in
      let outer_yielded = frame.yielded in
      (* In the loop's clauses, the pattern names the next index: [low] plus
         the iterations so far. *)
      let at_index (exit_frame : frame) next =
        snd (pattern_match context exit_frame pattern next element)
      in
      let entry = at_index { frame with yielded = Some (empty_parts context frame element) } low in
      check_invariants context entry clauses ~when_:"on entry to the loop";
      let start =
        enter_loop context frame ~entry clauses ~changed:(changed_places frame body) body
      in
      let costs = start.loop_costs and head = start.havocked in
      (* The [n]th iteration, from 0, has the index [low + n]. *)
      let count =
        Costs.normalize
          (if inclusive then Costs.plus (Costs.minus high low) (Logic.int 1)
           else Costs.minus high low)
      in
      let iterations = fresh context head "iterations" Logic.Int in
      assume context head
        Logic.(
          Operation ("<=", [ int 0; iterations ])
          &&& Operation ("<=", [ iterations; Costs.at_least_zero count ]));
      (* [yielded] is the indexes so far, from [low] up. *)
      let before = some_parts context head element in
      assume context head (Logic.equal (sequence_length context element before) iterations);
      (let position = fresh_name context "index" in
       match sequence_at context element before (Logic.Symbol position) with
       | Some yielded_index ->
           assume context head
             (Logic.Forall
                ( [ (position, Logic.Int) ],
                  Logic.(
                    Operation ("<=", [ int 0; Symbol position ])
                    &&& Operation ("<", [ Symbol position; iterations ])
                    ==> equal yielded_index (Operation ("+", [ low; Symbol position ]))) ))
       | None -> ());
      let index = Costs.plus low iterations in
      let head =
        loop_head context
          (at_index { head with yielded = Some before } index)
          costs ~iterations:(Some iterations)
      in
      assume_invariants context head clauses;
      let inside = restrict head (Logic.Operation ("<", [ iterations; count ])) in
      let through = appended context inside element before index in
      let inside = { inside with yielded = outer_yielded } in
      let inside = spend context inside one_step in
      let run_body =
        match driven with
        | Some driven -> driven.run_body
        | None -> core_loop_body context pattern element body
      in
      let ends, breaks = run_body inside index in
      let with_through (exit_frame : frame) =
        at_index
          { exit_frame with loop = frame.loop; yielded = Some through }
          (Costs.plus index (Logic.int 1))
      in
      end_iterations context frame node clauses start ~head ~inside ~ends ~breaks ~with_through;
      let most = [ Costs.at_least_zero count ] in
      let exit_ =
        loop_exit context
          { (restrict head (Logic.Operation (">=", [ iterations; count ]))) with loop = frame.loop }
          costs ~iterations:(Some iterations) ~most
      in
      let left =
        List.map
          (fun (exit_frame : frame) ->
            loop_exit context (with_through exit_frame) costs
              ~iterations:(Some (Costs.plus iterations (Logic.int 1)))
              ~most)
          breaks
      in
      leave_loop context frame
        (List.map
           (fun (exit_frame : frame) -> { exit_frame with yielded = outer_yielded })
           (exit_ :: left))
  | Yielding_call ({ kind = Call call_; _ } as yielding) ->
      each_loop ?driven context frame node pattern yielding call_ clauses body
  | Yielding_call _ -> unsupported span "this `for` loop"
  | Cursor { cursor; next = None } -> (
      match place_type context frame cursor with
      | Types.Cursor { method_; _ } as cursor_type ->
          pulled_loop ?driven context frame node pattern cursor clauses body ~cursor_type ~method_
      | _ -> unsupported span "this `for` loop")
  | Cursor { cursor; next = Some next } ->
      own_cursor_loop ?driven context frame node pattern cursor next clauses body
        ~cursor_type:(place_type context frame cursor)

(* A loop's body, read from its core form: the pattern binds the element,
   and the body runs. *)
and core_loop_body context (pattern : pattern) element_type body inside element =
  let exits = { breaks = []; continues = [] } in
  let _, inside =
    pattern_match context { inside with loop = Some exits } pattern element element_type
  in
  let finished = block_value context inside body in
  ((match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues, exits.breaks)

(* A [for] loop over a yielding method: each element is a fresh value
   that meets the method's clauses for each part, and the loop ends when
   the method has a [time] clause. *)
and each_loop ?driven context frame (node : statement) (pattern : pattern) (yielding : expression)
    (call_ : call) clauses body =
  let span = span_of frame.source node.origin in
  let frame, values =
    call_arguments
      ?given:(Option.bind driven (fun (driven : driven) -> driven.arguments))
      context frame yielding call_
      ~facts_for:(fun _ _ _ -> [])
  in
  let arguments = List.map (fun (passed : passed) -> (passed.position, passed.term)) values in
  let path, terminates, contract, substitution =
    match call_.callee with
    | Function { path; type_arguments } -> (
        let substitution =
          match Interface.Impls.signature context.database path with
          | Some (signature : Types.signature) -> callee_substitution frame signature type_arguments
          | None -> []
        in
        match Interface.Impls.signature context.database path with
        | Some signature ->
            ( Some path,
              signature.terminates,
              function_contract ?reading_package:(reading_package context) context.database path,
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
              List.map (Types.substitute_argument frame.substitution) trait.trait_arguments;
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
          method_contract ?reading_package:(reading_package context) context.database trait name
            receiver evidence,
          [ ({ Types.owner = trait.trait; name = "Self" }, Types.Type self_type) ] )
    | _ -> (None, false, None, [])
  in
  if context.terminates && not terminates then
    oblige context frame Termination span
      "This loop may not end: the method it loops over has no `time` clause." (Logic.Boolean false);
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
             ~uses:(call_.uses :> Types.capability list)
             ~values ~change:None)
    | _ -> spend context frame (unknown_amount context frame)
  in
  (* A loop over a collection [mut] changes the collection too. *)
  let changed =
    let in_body = changed_places frame body in
    List.fold_left
      (fun (changed : changed) (passed : passed) ->
        match (passed.mode, passed.operand) with
        | Types.Mut, Some (Place place) -> (
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
  receiving_loop ?driven context frame node pattern clauses body ~element_type ~changed
    ~start:(fun head -> some_parts context head element_type)
    ~receive:(fun head before ->
      (* Each time round, the method either yields another part or ends. *)
      let has_another = fresh context head "another" Logic.Bool in
      let element = arrive context head "element" element_type in
      let inside = restrict head has_another in
      assume_valid context inside element_type element;
      method_clauses inside ~each:true ~result:(Some element) ~yielded:before ~finished:None;
      let through = appended context inside element_type before element in
      method_clauses inside ~each:false ~result:None ~yielded:through
        ~finished:(Some (Logic.Boolean false));
      method_clauses
        (restrict head (Logic.not_ has_another))
        ~each:false ~result:None ~yielded:before ~finished:(Some (Logic.Boolean true));
      { has_another; element; through; advance = Fun.id })

(* A loop's changed values, with the local or [self] its cursor is in, which
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
   has yielded, before the loop too. *)
and pulled_loop ?driven context frame (node : statement) pattern (cursor_place : place) clauses body
    ~cursor_type ~method_ =
  let span = span_of frame.source node.origin in
  let cursor_access = cursor_access context driven cursor_place in
  let cursor = cursor_access.read frame in
  let cursor_method =
    match List.assoc_opt cursor context.cursors with
    | Some cursor_method -> cursor_method
    | None -> unsupported span "a loop over a cursor whose method the prover does not know"
  in
  if context.terminates && not (signature_terminates context method_) then
    oblige context frame Termination span
      "This loop may not end: the method its cursor comes from has no `time` clause."
      (Logic.Boolean false);
  let changed = with_cursor frame node (changed_places frame body) cursor_place in
  let at_head = ref cursor in
  receiving_loop ?driven context frame node pattern clauses body ~element_type:cursor_method.element
    ~changed
    ~start:(fun head ->
      let cursor = cursor_access.read head in
      context.cursors <- (cursor, cursor_method) :: context.cursors;
      at_head := cursor;
      cursor_yielded context cursor_type cursor_method.element cursor)
    ~receive:(fun head _ ->
      let pulled, later = pull context head cursor_method !at_head ~cursor_type in
      let option_type =
        Types.Named { path = option_path; arguments = [ Types.Type cursor_method.element ] }
      in
      {
        has_another = Logic.Is (constructor_name option_type (Some "Some"), pulled);
        element = Logic.Apply (selector_name option_type (Some "Some") "value", [ pulled ]);
        through = cursor_yielded context cursor_type cursor_method.element later;
        advance = (fun (frame : frame) -> cursor_access.write frame later);
      })

(* The place of a cursor a loop pulls: where the MIR gives it, or its core
   place. *)
and cursor_access context driven cursor_place =
  match driven with
  | Some { cursor = Some access; _ } -> access
  | _ -> core_place context cursor_place

(* A [for] loop over a value of a type's own [Cursor]: each iteration
   calls its [next] by the [impl]'s contract, and the loop ends at [None].
   Such a cursor promises no end, so in a function that must end, the loop
   needs a [decreases] clause, which each iteration decreases. *)
and own_cursor_loop ?driven context frame (node : statement) (pattern : pattern)
    (cursor_place : place) (next : callee) clauses body ~cursor_type =
  let span = span_of frame.source node.origin in
  let cursor_access = cursor_access context driven cursor_place in
  ignore (cursor_access.read frame);
  let element_type = substituted context frame pattern.type_ in
  let trait, evidence =
    match next with
    | Trait_method { trait; evidence = Impl _ as evidence; _ } -> (trait, evidence)
    | _ ->
        unsupported span "a loop over `%s`, whose `Cursor` the prover cannot find"
          (Types.show cursor_type)
  in
  let impl =
    match evidence with Impl { impl; _ } -> impl | _ -> bug "a cursor's evidence is not an impl"
  in
  let contract =
    match
      method_contract ?reading_package:(reading_package context) context.database trait "next" Mut
        evidence
    with
    | Some contract -> contract
    | None ->
        unsupported span "a loop over `%s`, whose `next` the prover cannot read"
          (Types.show cursor_type)
  in
  let path = Path.Method { owner = impl; name = "next"; receiver = Mut } in
  let option_type = Types.Named { path = option_path; arguments = [ Types.Type element_type ] } in
  let call_ : call =
    {
      callee = next;
      arguments = [ Passed { mode = Types.Mut; value = Place cursor_place; mark = None } ];
      lends = None;
      uses = Types.no_capabilities;
    }
  in
  let pulling : expression =
    { id = node.id; origin = node.origin; type_ = option_type; kind = Call call_ }
  in
  let measures = measures_of clauses in
  if context.terminates && not (signature_terminates context path) then
    oblige context frame Termination span
      (Printf.sprintf "This loop may not end: `%s`'s `next` has no `time` clause."
         (Types.show cursor_type))
      (Logic.Boolean false);
  if context.terminates && measures = None then
    oblige context frame Termination span
      "This loop may not end: a cursor of a type's own promises no end, so give the loop a \
       `decreases` clause."
      (Logic.Boolean false);
  let measured (at : frame) =
    Option.map
      (List.map (fun measure -> snd (value context { at with checking = false } measure)))
      measures
  in
  let changed = with_cursor frame node (changed_places frame body) cursor_place in
  receiving_loop ?driven context frame node pattern clauses body ~element_type ~changed
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
                      (lexicographically_less before after)
                | None -> ())
              ends
        | None -> ())
    ~start:(fun head -> some_parts context head element_type)
    ~receive:(fun head before ->
      let cursor = cursor_access.read head in
      let havoc_mut (frame : frame) =
        cursor_access.write frame (arrive context frame "changed" cursor_type)
      in
      let after, pulled =
        contract_call ~lent_final:None context head pulling call_ path contract
          [
            {
              position = 0;
              mode = Types.Mut;
              operand = Some (Place cursor_place);
              passed_place = Some cursor_access;
              type_ = cursor_type;
              term = cursor;
              run = None;
            };
          ]
          ~havoc_mut
          ~substitution_of:(fun _ ->
            [ ({ Types.owner = cursor_trait; name = "Self" }, Types.Type cursor_type) ])
          ~instance:[ type_key cursor_type ]
      in
      let has_another = Logic.Is (constructor_name option_type (Some "Some"), pulled) in
      let element = Logic.Apply (selector_name option_type (Some "Some") "value", [ pulled ]) in
      let inside = restrict after has_another in
      assume_valid context inside element_type element;
      {
        has_another;
        element;
        through = appended context inside element_type before element;
        advance =
          (fun (frame : frame) ->
            let now = cursor_access.read after in
            { (cursor_access.write frame now) with spent = after.spent });
      })

(* A [for] loop that receives parts one at a time: from a yielding method
   it calls, or from a cursor it pulls. [start] is the parts received before
   an iteration, at the head, and [receive] is the part an iteration
   receives, with the method's [ensures] for it assumed. *)
and receiving_loop ?(each_iteration = fun ~head:_ ~ends:_ -> ()) ?driven context frame
    (node : statement) (pattern : pattern) clauses body ~element_type ~changed ~start ~receive =
  let entry = { frame with yielded = Some (empty_parts context frame element_type) } in
  check_invariants context entry clauses ~when_:"on entry to the loop";
  let loop = enter_loop context frame ~entry clauses ~changed body in
  let costs = loop.loop_costs and head = loop.havocked in
  let before = start head in
  let iterations = sequence_length context element_type before in
  let head =
    loop_head context { head with yielded = Some before } costs ~iterations:(Some iterations)
  in
  assume_invariants context head clauses;
  let ended_mark = List.length context.facts in
  let received = receive head before in
  let through = received.through in
  let inside = received.advance (restrict head received.has_another) in
  let inside = { (spend context inside one_step) with yielded = frame.yielded } in
  let run_body =
    match driven with
    | Some (driven : driven) -> driven.run_body
    | None -> core_loop_body context pattern element_type body
  in
  let ends, breaks = run_body inside received.element in
  each_iteration ~head ~ends;
  let with_through (exit_frame : frame) =
    { exit_frame with loop = frame.loop; yielded = Some through }
  in
  end_iterations context frame node clauses loop ~head ~inside ~ends ~breaks ~with_through;
  let ended = received.advance (restrict head (Logic.not_ received.has_another)) in
  let varies = mentions_fresh_after context loop.fresh_mark in
  let ended_facts = facts_since context ended_mark @ facts_since context loop.facts_mark in
  let exit_ =
    loop_exit context
      { ended with loop = frame.loop; yielded = Some before }
      costs ~iterations:(Some iterations)
      ~most:(Costs.upper_bounds ~varies ~facts:ended_facts iterations)
  in
  let left =
    List.map
      (fun (exit_frame : frame) ->
        loop_exit context (with_through exit_frame) costs
          ~iterations:(Some (Costs.plus iterations (Logic.int 1)))
          ~most:
            (Costs.upper_bounds ~varies ~facts:ended_facts
               (sequence_length context element_type through)))
      breaks
  in
  leave_loop context frame
    (List.map
       (fun (exit_frame : frame) -> { exit_frame with yielded = frame.yielded })
       (exit_ :: left))

(* Whether a loop's body yields. *)
and contains_yield body =
  Core_walk.block_exists
    ~statement:(fun (node : statement) -> match node.kind with Yield _ -> true | _ -> false)
    body

and havoc_parts context frame =
  match context.yielded_part with
  | Some (part, _) -> Some (some_parts context frame part)
  | None -> frame.yielded_so_far

(* The MIR

   The body of the definition proven runs forward from its MIR, which has
   decided the order of evaluation, the scope of each temporary and
   binding, and the flow of patterns and early exits, as code generation
   and the ownership check read them. Each computation that the core form
   names, such as a call, an operator, or a constructor, is read through
   the same functions as in a specification, given the values of its
   operands, so code and specification give the same term. A body that
   uses a form the MIR's reading does not cover yet is read from its core
   form. *)

(* The core form's nodes of the definition proven, by what the MIR names
   them by. *)
type core_index = {
  expressions : (Core.id, expression) Hashtbl.t;
  statements : (Core.origin, statement) Hashtbl.t;
  conditions : (Core.origin, unit) Hashtbl.t;  (** The condition of each [if], by its origin *)
  unreachable : (Core.origin, unit) Hashtbl.t;  (** Each [unreachable] written *)
  enclosing : (Core.id, expression) Hashtbl.t;
      (** The slice or the tagged template around each call that is one's *)
  names : (Core.local, string) Hashtbl.t;  (** Each binding's name *)
}

let core_index (definition : Core.definition) =
  let index =
    {
      expressions = Hashtbl.create 64;
      statements = Hashtbl.create 16;
      conditions = Hashtbl.create 8;
      unreachable = Hashtbl.create 2;
      enclosing = Hashtbl.create 4;
      names = Hashtbl.create 16;
    }
  in
  Core_walk.definition
    (Core_walk.deep
       {
         Core_walk.ignore_all with
         expression =
           (fun (node : expression) ->
             Hashtbl.replace index.expressions node.id node;
             match node.kind with
             | If { condition; _ } -> Hashtbl.replace index.conditions condition.origin ()
             | Unreachable -> Hashtbl.replace index.unreachable node.origin ()
             | Slice { call } | Template { call; _ } -> Hashtbl.replace index.enclosing call.id node
             | _ -> ());
         statement = (fun (node : statement) -> Hashtbl.replace index.statements node.origin node);
         pattern =
           (fun (pattern : pattern) ->
             match pattern.kind with
             | Bind { local; name; _ } -> Hashtbl.replace index.names local name
             | _ -> ());
       })
    definition;
  index

(* Whether the MIR's reading covers every form of a body. *)
let mir_covers (index : core_index) (parameters : Core.parameter list) (mir : Mir.t) =
  let core_call (call : Mir.call) =
    match Hashtbl.find_opt index.expressions call.node with
    | Some { kind = Call { callee; _ }; _ } -> (
        match (callee, call.callee) with
        | Indirect _, Indirect _ -> true
        | Indirect _, _ | _, Indirect _ -> false
        | _ -> true)
    | _ -> false
  in
  let rvalue (value : Mir.rvalue) ~node =
    match value with
    | Operand _ | Compare _ | Not _ | Is_variant _ | Copy _ | Value_parameter _ -> true
    | Operation _ | Construct _ | Convert _ | Function_value _ | To_any _ -> (
        match Option.bind node (Hashtbl.find_opt index.expressions) with
        | Some { kind = Operator _ | Construct _ | Convert _ | Function_value _ | To_any _; _ } ->
            true
        | _ -> false)
    | Array _ -> (
        match Option.bind node (Hashtbl.find_opt index.expressions) with
        | Some { kind = Collection_literal _; _ } -> true
        | _ -> false)
    | Lambda _ -> (
        match Option.bind node (Hashtbl.find_opt index.expressions) with
        | Some { kind = Lambda _; _ } -> true
        | _ -> false)
  in
  let statement (statement : Mir.statement) =
    match statement.kind with
    | Assign { value; node; _ } -> rvalue value ~node
    | Call { call; _ } -> core_call call
    | Live _ | Dead _ | Loan_start _ | Loan_end _ | Echo _ | Proof _ | Matched _ -> true
    | Assert _ | Ghost_assert _ -> (
        match Hashtbl.find_opt index.statements statement.origin with
        | Some { kind = Assert _; _ } -> true
        | _ -> false)
    | Lend { call; _ } -> core_call call
    | Slice { call; _ } | Template { call; _ } -> Hashtbl.mem index.enclosing call.node
    | Pull _ | Provide _ | Provide_end -> true
    | Fork_start { concurrent; _ } -> not concurrent
    | Fork_end _ -> true
  in
  let terminator (ending : Mir.terminator) =
    match ending with
    | Goto _ | Branch _ | Switch_variant _ | Return _ | Unreachable | Todo | Iteration_end -> true
    | For { loop; _ } -> (
        match Hashtbl.find_opt index.statements loop.origin with
        | Some { kind = For _; _ } -> true
        | _ -> false)
    | Yield _ -> true
    | Exit_tasks _ -> false
  in
  ignore parameters;
  Array.for_all
    (fun (block : Mir.basic_block) ->
      (match block.Mir.header with
        | None -> true
        | Some natural -> (
            match Hashtbl.find_opt index.statements natural.loop.origin with
            | Some { kind = While _; _ } -> true
            | _ -> false))
      && List.for_all statement block.Mir.statements
      && terminator block.Mir.terminator)
    mir.body.blocks

(* Where a body's run is: the core form's nodes, the body, and the locals
   that are a place they were bound to, to be changed there. *)
type run = {
  index : core_index;
  body : Mir.body;
  places : (Mir.local, Mir.place) Hashtbl.t;
  lends : (Mir.local, frame -> Logic.term -> frame) Hashtbl.t;
      (** For each part lent to change, how its final value goes back where it was lent from, as the
          lend ends *)
  constructs : (Mir.local, string option * (string * Mir.operand option) list) Hashtbl.t;
      (** The constructor each temporary is built by, for a [yield] of places it holds *)
  passed_lambdas : (Core.id, unit) Hashtbl.t;
      (** The lambdas written as a call's arguments, which the call reads with its parameter's facts
      *)
  slices : (Mir.local, expression * Mir.place * Logic.term * Logic.term) Hashtbl.t;
      (** Each temporary that holds a slice: its core node, the collection it views, and its run's
          start and stop, for a callee that changes the slice *)
  provides : (Core.origin, Mir.provided list) Hashtbl.t;
      (** Each [provide]'s implementations, by its origin, which its end on its normal path carries
      *)
}

(* The key of a local of the MIR in a frame's locals: a parameter's or a
   binding's own core local, which specifications name, and for a
   temporary, a synthetic local numbered below zero, which no core form
   has. *)
let mir_key run local =
  match run.body.locals.(local).kind with
  | Source { local = core; _ } -> core
  | Temporary | Lent _ -> Core.Synthetic (-1 - local)

let rec mir_place_type context frame run (place : Mir.place) =
  match place.Mir.projections with
  | [] -> (
      match place.Mir.root with
      | Local local -> substituted context frame run.body.locals.(local).type_
      | Constant path ->
          raise
            (Foreign_unsupported (Printf.sprintf "a field of the constant `%s`" (Path.show path))))
  | _ -> (
      let base =
        { place with Mir.projections = List.rev (List.tl (List.rev place.Mir.projections)) }
      in
      let base_type = mir_place_type context frame run base in
      let variant, field =
        match List.nth place.Mir.projections (List.length place.Mir.projections - 1) with
        | Field field -> (None, field)
        | Variant_field { variant; field } -> (Some variant, field)
      in
      match Option.bind (declared_fields context base_type variant) (List.assoc_opt field) with
      | Some field_type -> substituted context frame field_type
      | None -> raise (Foreign_unsupported (Printf.sprintf "the field `%s`" field)))

(* A place with each local that is a place it was bound to replaced by that
   place. *)
let rec expanded run (place : Mir.place) =
  match place.Mir.root with
  | Local local -> (
      match Hashtbl.find_opt run.places local with
      | Some bound ->
          let bound = expanded run bound in
          { bound with Mir.projections = bound.Mir.projections @ place.Mir.projections }
      | None -> place)
  | Constant _ -> place

let read_root context frame run (root : Mir.root) =
  match root with
  | Constant path -> constant_value context frame path
  | Local local -> (
      match mir_key run local with
      | Self -> (
          match frame.self with
          | Some self -> self
          | None -> raise (Foreign_unsupported "`self` outside a method"))
      | key -> (
          (* A function-typed parameter read other than to be called or passed
             on keeps its [requires]. *)
          if frame.checking && not context.reading_callback then escaping_callback context frame key;
          match Locals.find_opt key frame.locals with
          | Some term -> term
          | None -> raise (Foreign_unsupported "a local the prover did not bind")))

(* The value at a place of the MIR. *)
let read_place context frame run (place : Mir.place) =
  let place = expanded run place in
  let _, term =
    List.fold_left
      (fun (prefix, term) (projection : Mir.projection) ->
        let base = { place with Mir.projections = prefix } in
        let base_type = mir_place_type context frame run base in
        let variant, field =
          match projection with
          | Field field -> (None, field)
          | Variant_field { variant; field } -> (Some variant, field)
        in
        let projected = { place with Mir.projections = prefix @ [ projection ] } in
        if constructors context base_type = None then
          raise
            (Foreign_unsupported
               (Printf.sprintf "a field of `%s`, whose fields the prover does not see"
                  (Types.show base_type)));
        ignore (sort_of context base_type);
        ( prefix @ [ projection ],
          field_of context frame base_type variant field
            (mir_place_type context frame run projected)
            term ))
      ([], read_root context frame run place.Mir.root)
      place.Mir.projections
  in
  term

(* The frame after a place of the MIR takes a new value: a local, [self],
   or a field, which rebuilds each value it is in. *)
let write_place context frame run (place : Mir.place) new_value =
  let place = expanded run place in
  let rec rebuilt prefix whole = function
    | [] -> new_value
    | (projection : Mir.projection) :: rest -> (
        let base_type = mir_place_type context frame run { place with Mir.projections = prefix } in
        let variant, field =
          match projection with
          | Field field -> (None, field)
          | Variant_field { variant; field } -> (Some variant, field)
        in
        let field_type =
          mir_place_type context frame run { place with Mir.projections = prefix @ [ projection ] }
        in
        let part = field_of context frame base_type variant field field_type whole in
        let changed = rebuilt (prefix @ [ projection ]) part rest in
        match constructors context base_type with
        | Some shape ->
            let shaped = Option.value (List.assoc_opt variant shape) ~default:[] in
            Logic.Apply
              ( constructor_name base_type variant,
                List.map
                  (fun (other, _) ->
                    if other = field then changed
                    else selected context base_type variant other whole)
                  shaped )
        | None ->
            raise (Foreign_unsupported (Printf.sprintf "the fields of `%s`" (Types.show base_type)))
        )
  in
  match place.Mir.root with
  | Constant _ -> raise (Foreign_unsupported "assigning to a constant")
  | Local local -> (
      let whole =
        if place.Mir.projections = [] then new_value
        else rebuilt [] (read_root context frame run place.Mir.root) place.Mir.projections
      in
      match mir_key run local with
      | Self -> { frame with self = Some whole }
      | key -> bind frame key (substituted context frame run.body.locals.(local).type_) whole)

let mir_operand context frame run (operand : Mir.operand) =
  match operand with
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> read_place context frame run place
  | Constant { value; type_ } -> (
      let ty = substituted context frame type_ in
      match value with
      | Unit ->
          ignore (sort_of context Types.unit);
          Logic.Apply (Symbol.Unit, [])
      | Integer number -> Logic.Integer number
      | Float number -> (
          match float_format ty with
          | Some format -> float_literal format number
          | None -> raise (Foreign_unsupported "a float literal without a float type"))
      | Boolean truth -> Logic.Boolean truth
      | String text -> text_value context frame ty text)

let mir_operand_type context frame (operand : Mir.operand) =
  match operand with
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } | Constant { type_; _ } ->
      substituted context frame type_

(* The value an rvalue computes, and the frame after it. *)
let mir_rvalue context frame run (value : Mir.rvalue) ~node ~span =
  let core_node () =
    match Option.bind node (Hashtbl.find_opt run.index.expressions) with
    | Some node -> node
    | None -> bug "a computation of the MIR whose core node is not known"
  in
  let operand = mir_operand context frame run in
  match value with
  | Operand value -> (frame, operand value)
  | Compare { comparison = compared; left; right } -> (
      let left_term = operand left and right_term = operand right in
      ( frame,
        if float_format (mir_operand_type context frame left) <> None then
          match compared with
          | Equal -> float_equal left_term right_term
          | Not_equal -> Logic.not_ (float_equal left_term right_term)
          | Less -> float_less left_term right_term
          | Less_equal ->
              Logic.( ||| ) (float_less left_term right_term) (float_equal left_term right_term)
          | Greater -> float_less right_term left_term
          | Greater_equal ->
              Logic.( ||| ) (float_less right_term left_term) (float_equal left_term right_term)
        else
          match comparison compared with
          | Some _ when compared = Equal -> Logic.equal left_term right_term
          | Some symbol -> Logic.Operation (symbol, [ left_term; right_term ])
          | None -> Logic.not_ (Logic.equal left_term right_term) ))
  | Not inner -> (frame, Logic.not_ (operand inner))
  | Is_variant { place; variant } ->
      let ty = mir_place_type context frame run place in
      ignore (sort_of context ty);
      if constructors context ty = None then
        unsupported span "a variant of `%s`, which the prover does not see" (Types.show ty);
      (frame, Logic.Is (constructor_name ty (Some variant), read_place context frame run place))
  | Copy copied_operand ->
      let ty = mir_operand_type context frame copied_operand in
      let term = operand copied_operand in
      (copied context frame ty term, term)
  | Convert { conversion = Widen; value } ->
      (* A named function's costs are checked where it is passed, and a
         lambda's where it is written. *)
      (match Option.bind node (Hashtbl.find_opt run.index.expressions) with
      | Some ({ kind = Convert { value = converted; _ }; _ } as written) -> (
          match
            (converted.kind, type_of context frame converted, type_of context frame written)
          with
          | (Function_value _ | Lambda _), _, _ -> ()
          | _, Types.Function actual, Types.Function expected
            when not (List.for_all (fun cost -> List.mem cost actual.costs) expected.costs) ->
              unsupported (at frame written) "a function value's costs"
          | _ -> ())
      | _ -> ());
      (frame, operand value)
  | Value_parameter parameter -> (frame, value_term context frame (Value_parameter parameter))
  | Convert { conversion = To_integer; value } -> (frame, operand value)
  | Convert { conversion = From_integer; value } ->
      let node = core_node () in
      let ty = type_of context frame node in
      let term = operand value in
      oblige context frame Out_of_range (at frame node)
        (Printf.sprintf "`%s` may not fit in `%s`." (quote frame.source node.origin) (Types.show ty))
        (in_range ty term);
      (frame, term)
  | Function_value { path; type_arguments } ->
      let node = core_node () in
      (frame, global_value context frame node path type_arguments)
  | To_any _ ->
      (* A value of [any Trait], known through the trait's contracts: one
         allocation, of the block that holds the value. *)
      let node = core_node () in
      let frame =
        spend context frame (fun (counter : Costs.counter) ->
            match (counter.resource, counter.counting) with
            | Allocations, _ -> Logic.int 1
            | Allocated_bytes, Units -> Logic.int 1
            | Allocated_bytes, (At_most | Exactly) -> unknown_amount context frame counter
            | (Time | Calls _), _ -> Costs.zero)
      in
      (frame, arrive context frame "any" (type_of context frame node))
  | Operation { operation; operands; _ } -> (
      let node = core_node () in
      match node.kind with
      | Operator { arguments; _ } ->
          let ty = type_of context frame node in
          ( frame,
            primitive_operation context frame ~node operation [ ty ] (List.map operand operands)
              ~arguments:(List.map Option.some arguments) ~fallback:(fun () ->
                if float_format ty <> None then arrive context frame "operator" ty
                else unsupported (at frame node) "this operator") )
      | _ -> bug "a primitive operation whose core node is no operator")
  | Construct { variant; fields } -> (
      let node = core_node () in
      match node.kind with
      | Construct { fields = written; _ } ->
          let given name =
            match List.assoc_opt name fields with
            | Some (Some value) -> Some (operand value)
            | _ -> None
          in
          construct ~given context frame node variant written
      | _ -> bug "a constructor whose core node is no constructor")
  | Array elements -> (
      let node = core_node () in
      match node.kind with
      | Collection_literal { elements = written; _ } ->
          list_literal ~given:(List.map operand elements) context frame node written
      | _ -> bug "an array whose core node is no literal")
  | Lambda _ -> (
      let node = core_node () in
      match node.kind with
      | Lambda { parameters; captures; body; _ } ->
          if Hashtbl.mem run.passed_lambdas node.id then
            (* The call reads it, with its parameter's facts. *)
            (frame, arrive context frame "lambda" (type_of context frame node))
          else lambda context frame node parameters captures body ~facts:(fun _ -> [])
      | _ -> bug "a lambda whose core node is no lambda")

(* A place of the MIR as the place of a [mut] argument. *)
let mir_passed_place context run place =
  {
    read = (fun frame -> read_place context { frame with checking = false } run place);
    write = (fun frame term -> write_place context frame run place term);
  }

(* A slice of the MIR's collection [base] from [low] to [high], with the
   facts about its elements. *)
let mir_slice context frame run (node : expression) (base : Mir.place) low high =
  slice_run
    ~given:(mir_place_type context frame run base, read_place context frame run base, low, high)
    context frame node (Temporary node) ~start:None ~stop:None ~inclusive:false

(* The values of a call's arguments that the MIR has evaluated, by position,
   with the place of each passed [mut]. A slice passed [mut] gives its run,
   and is read again after the call as a view of its collection's new
   run. *)
let mir_arguments context frame run (arguments : Mir.argument list) position =
  match List.nth_opt arguments position with
  | Some (Passed { value; mode; _ }) -> (
      let term = reading_callback context (fun () -> mir_operand context frame run value) in
      match (mode, value) with
      | Types.Mut, Borrow { place = { root = Local local; projections = [] }; _ }
        when Hashtbl.mem run.slices local ->
          let node, base, low, high = Hashtbl.find run.slices local in
          let reread frame =
            let _, viewed, _, _ =
              mir_slice context { frame with checking = false } run node base low (Some high)
            in
            viewed
          in
          Some (term, Some { read = reread; write = (fun frame _ -> frame) }, Some (low, high))
      | Types.Mut, Borrow { place; _ } ->
          Some (term, Some (mir_passed_place context run place), None)
      | _ -> Some (term, None, None))
  | Some Default | None -> None

(* A call, through the callee's contract, with the arguments the MIR has
   evaluated. Gives [None] where the call never returns. *)
let mir_call context frame run (call : Mir.call) =
  match Hashtbl.find_opt run.index.expressions call.node with
  | Some ({ kind = Call called; _ } as node) -> (
      let given = mir_arguments context frame run call.arguments in
      let callee =
        match call.callee with
        | Indirect callee ->
            Some (reading_callback context (fun () -> mir_operand context frame run callee))
        | _ -> None
      in
      match resolved_call ~given ?callee context frame node called with
      | Some _ when Types.equal (type_of context frame node) Types.Never -> None
      | translated -> translated)
  | _ -> bug "a call of the MIR whose core call is not known"

(* A lending call, whose part [part] holds. A part lent to change takes the
   callee's contract at its end too, given its final value: a method lent
   from is called again then, which writes the receiver back, and spends the
   call's cost then, and the part of a storage, an array, or a view goes back
   into it at its index. *)
let mir_lend context frame run part (call : Mir.call) =
  match Hashtbl.find_opt run.index.expressions call.node with
  | Some ({ kind = Call called; _ } as node) -> (
      let given = mir_arguments context frame run call.arguments in
      let receiver =
        match call.arguments with
        | Passed { value = Borrow { place; _ }; _ } :: _ -> Some place
        | _ -> None
      in
      let index_term () =
        match given 1 with
        | Some (term, _, _) -> term
        | None -> bug "a lend at an index with no index"
      in
      let lent =
        match (called.lends, called.callee, receiver) with
        | ( Some Types.Mut,
            Intrinsic { operation = Storage_at_mut; type_arguments = Types.Type element :: _ },
            Some receiver ) ->
            let index = index_term () in
            Hashtbl.replace run.lends part (fun frame final ->
                let element = substituted context frame element in
                let buffer = read_place context { frame with checking = false } run receiver in
                write_place context frame run receiver
                  (storage_updated context frame element buffer index final));
            resolved_call ~given context frame node called
        | Some Types.Mut, Intrinsic { operation = Array_at_mut; _ }, Some receiver ->
            let index = index_term () in
            Hashtbl.replace run.lends part (fun frame final ->
                let array_type = mir_place_type context frame run receiver in
                let before = read_place context { frame with checking = false } run receiver in
                write_place context frame run receiver
                  (array_updated context frame array_type before index final));
            resolved_call ~given context frame node called
        | ( Some Types.Mut,
            Intrinsic { operation = View_at_mut; type_arguments = Types.Type element :: _ },
            Some receiver ) ->
            let index = index_term () in
            Hashtbl.replace run.lends part (fun frame final ->
                let element = substituted context frame element in
                let before = read_place context { frame with checking = false } run receiver in
                let updated =
                  arrive context frame "changed" (mir_place_type context frame run receiver)
                in
                replaced context frame element
                  ~before:(buffer_model context View element before)
                  ~after:(buffer_model context View element updated)
                  index final;
                write_place context frame run receiver updated);
            resolved_call ~given context frame node called
        | Some Types.Mut, Intrinsic _, _ -> unsupported (at frame node) "this lend"
        | Some Types.Mut, _, _ ->
            Hashtbl.replace run.lends part (fun frame final ->
                match
                  resolved_call ~lent_final:(fun _ -> final) ~given context frame node called
                with
                | Some (after, _) -> after
                | None -> frame);
            without_costs context (fun () -> resolved_call ~given context frame node called)
        | _ -> resolved_call ~given context frame node called
      in
      match lent with
      | Some (after, term) ->
          Some (write_place context after run { root = Local part; projections = [] } term)
      | None -> None)
  | _ -> bug "a lend of the MIR whose core call is not known"

(* Whether a yielded operand lends places: it is a place, or a constructor
   applied to places, to any depth. *)
let rec mir_lends_places run (operand : Mir.operand) =
  match operand with
  | Borrow _ -> true
  | Use { place = { root = Local local; projections = [] }; _ } -> (
      match Hashtbl.find_opt run.constructs local with
      | Some (_, fields) ->
          List.exists
            (function _, Some field -> mir_lends_places run field | _, None -> false)
            fields
      | None -> false)
  | Use _ | Take _ | Constant _ -> false

(* The frame after the caller's changes to a part lent [mut] come back, as
   [after]: each place the part lends has its part of [after]. A variant's
   field is its part only where [after] is still that variant, and is
   otherwise a value nothing more is known about. *)
let rec mir_written_back context run ty (operand : Mir.operand) frame after =
  match operand with
  | Borrow { place; _ } -> write_place context frame run place after
  | Use { place = { root = Local local; projections = [] }; _ } -> (
      match (Hashtbl.find_opt run.constructs local, constructors context ty) with
      | Some (variant, fields), Some shape ->
          let shaped = Option.value (List.assoc_opt variant shape) ~default:[] in
          List.fold_left
            (fun frame (name, field) ->
              match (field, List.assoc_opt name shaped) with
              | Some field, Some field_type when mir_lends_places run field ->
                  let field_type = substituted context frame field_type in
                  let selected = field_of context frame ty variant name field_type after in
                  let value =
                    match variant with
                    | None -> selected
                    | Some _ ->
                        Logic.ite
                          (Logic.Is (constructor_name ty variant, after))
                          selected
                          (arrive context frame "lent" field_type)
                  in
                  mir_written_back context run field_type field frame value
              | _ -> frame)
            frame fields
      | Some _, None ->
          raise (Foreign_unsupported (Printf.sprintf "the fields of `%s`" (Types.show ty)))
      | None, _ -> frame)
  | Use _ | Take _ | Constant _ -> frame

let mir_statement context frame run (statement : Mir.statement) =
  let span = span_of frame.source statement.origin in
  match statement.kind with
  | Assign
      {
        target = { root = Local local; projections = [] };
        value = Operand (Borrow { place; mode = Mut; _ });
        _;
      } ->
      (* A binding of a part to change is the part itself. *)
      Hashtbl.replace run.places local place;
      Some frame
  | Assign { target; value; node } ->
      let frame, term = mir_rvalue context frame run value ~node ~span in
      (match target.root with
      | Local local -> (
          match mir_key run local with
          | (Named _ | Synthetic _) as key ->
              Option.iter
                (Hashtbl.replace context.local_names key)
                (Hashtbl.find_opt run.index.names key)
          | Self -> ())
      | Constant _ -> ());
      Some (write_place context frame run target term)
  | Call { destination; call } -> (
      match mir_call context frame run call with
      | Some (after, term) -> (
          match destination with
          | Some destination -> Some (write_place context after run destination term)
          | None -> Some after)
      | None -> None)
  | Live _ | Loan_start _ | Loan_end _ | Echo _ -> Some frame
  | Dead locals ->
      (* A part lent to change goes back as its lend ends: a part lent from
         another part first. *)
      let frame =
        List.fold_left
          (fun frame local ->
            match Hashtbl.find_opt run.lends local with
            | Some finish ->
                Hashtbl.remove run.lends local;
                finish frame
                  (read_place context { frame with checking = false } run
                     { root = Local local; projections = [] })
            | None -> frame)
          frame (List.rev locals)
      in
      Some
        {
          frame with
          locals =
            List.fold_left
              (fun locals local -> Locals.remove (mir_key run local) locals)
              frame.locals locals;
        }
  | Lend { part; call } -> mir_lend context frame run part call
  | Assert asserted -> (
      match Hashtbl.find_opt run.index.statements statement.origin with
      | Some { kind = Assert { condition = { value = written; _ }; by_bit_vector }; _ } ->
          if by_bit_vector && not (is_test context) then bit_vector_assertion context frame written;
          let term = mir_operand context frame run asserted in
          if is_test context || by_bit_vector then assume context frame term
          else
            oblige context frame Assertion (at frame written)
              (Printf.sprintf "`%s` may not hold." (quote frame.source written.origin))
              term;
          Some frame
      | _ -> bug "an assertion of the MIR whose core statement is not known")
  | Ghost_assert _ -> (
      match Hashtbl.find_opt run.index.statements statement.origin with
      | Some core_statement -> statement_kind context frame core_statement
      | None -> bug "an assertion of the MIR whose core statement is not known")
  | Proof block -> Some (restrict frame (Logic.not_ (ghost context frame block)))
  | Matched { patterns } ->
      if frame.checking then
        context.decisions <-
          ( Printf.sprintf "the arm `%s` is taken"
              (String.concat ", " (List.map (quote frame.source) patterns)),
            None,
            frame.condition,
            Logic.Boolean true )
          :: context.decisions;
      Some frame
  | Slice { destination; base; call } -> (
      match Hashtbl.find_opt run.index.enclosing call.node with
      | Some node ->
          let given = mir_arguments context frame run call.arguments in
          let low = match given 1 with Some (term, _, _) -> term | None -> Logic.int 0 in
          let high = Option.map (fun (term, _, _) -> term) (given 2) in
          let frame, viewed, low, high = mir_slice context frame run node base low high in
          (match destination with
          | { root = Local local; projections = [] } ->
              Hashtbl.replace run.slices local (node, base, low, high)
          | _ -> ());
          Some (write_place context frame run destination viewed)
      | None -> bug "a slice of the MIR whose core slice is not known")
  | Template { destination; literals; call } -> (
      match Hashtbl.find_opt run.index.enclosing call.node with
      | Some ({ kind = Template { call = template_call; _ }; _ } as node) ->
          let template =
            match mir_arguments context frame run call.arguments 0 with
            | Some (term, _, _) -> term
            | None -> bug "a tagged template with no template"
          in
          let frame, tagged =
            tagged_template ~given:template context frame node literals template_call
          in
          Some (write_place context frame run destination tagged)
      | _ -> bug "a tagged template of the MIR whose core template is not known")
  | Pull { destination; cursor } -> (
      (* A pull of a cursor whose method the prover knows. *)
      let cursor_type = mir_place_type context frame run cursor in
      let cursor_term = read_place context frame run cursor in
      match List.assoc_opt cursor_term context.cursors with
      | Some cursor_method ->
          let pulled, later = pull context frame cursor_method cursor_term ~cursor_type in
          let frame = write_place context frame run cursor later in
          Some (write_place context (spend context frame one_step) run destination pulled)
      | None -> unsupported span "a pull of a cursor whose method the prover does not know")
  | Provide { provided; _ } ->
      (* The body runs with the implementations, which the prover never
         models, so a capability call in it gives a fresh value by its
         contract. *)
      Hashtbl.replace run.provides statement.origin provided;
      Some frame
  | Provide_end -> (
      (* Where the body ends, each implementation handed over [mut] holds a
         fresh value of its type, which meets its type's invariants. *)
      match Hashtbl.find_opt run.provides statement.origin with
      | Some provided ->
          Some
            (List.fold_left
               (fun frame (implementation : Mir.provided) ->
                 match (implementation.mode, implementation.value) with
                 | Types.Mut, Borrow { place; _ } ->
                     let root = { (expanded run place) with Mir.projections = [] } in
                     let ty = mir_place_type context frame run root in
                     let fresh_value = arrive context frame "changed" ty in
                     let frame = write_place context frame run root fresh_value in
                     assume_valid context frame ty fresh_value;
                     frame
                 | _ -> frame)
               frame provided)
      | None -> Some frame)
  | Fork_start { concurrent = false; _ } | Fork_end _ ->
      (* Branches are disjoint, so they can run in order. *)
      Some frame
  | Fork_start { concurrent = true; _ } -> bug "a form the MIR's reading does not cover"

(* The MIR of the body of a function proven, with its core form's nodes,
   where the MIR's reading covers it. A function for specifications only,
   and a proof, never runs, so it has no MIR. *)
let mir_of context (source : source) parameters ~runs =
  if runs && source.key = Some context.home then
    match Mir.of_definition source.core.definition with
    | Some mir ->
        let index = core_index source.core.definition in
        if mir_covers index parameters mir then Some (index, mir) else None
    | None -> None
  else None

(* The blocks a set of blocks reaches, the set included, without entering
   [avoid]. *)
let reached (body : Mir.body) ~from ~avoid =
  let seen = Hashtbl.create 16 in
  let rec visit block =
    if (not (Hashtbl.mem seen block)) && not (avoid block) then begin
      Hashtbl.replace seen block ();
      List.iter visit (Mir.successors body.blocks.(block).terminator)
    end
  in
  List.iter visit from;
  seen

(* The blocks of a [while] loop: those its header reaches without leaving
   by its exit, and from which the header is reached again. *)
let loop_blocks (body : Mir.body) header (natural : Mir.natural_loop) =
  let forward = reached body ~from:[ header ] ~avoid:(fun block -> block = natural.after) in
  let blocks = Hashtbl.create 16 in
  Hashtbl.replace blocks header ();
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter
      (fun block () ->
        if
          (not (Hashtbl.mem blocks block))
          && List.exists (Hashtbl.mem blocks) (Mir.successors body.blocks.(block).terminator)
        then begin
          Hashtbl.replace blocks block ();
          changed := true
        end)
      forward
  done;
  blocks

(* Runs a body of the MIR forward from [start]. Each [return] joins
   [context.returns]. Its blocks are in reverse postorder, so each block
   runs once every block that jumps to it has, but for a loop's back edges:
   a [while] loop runs as the core form's does, with its changes havocked
   at its head and its invariants checked at the end of each iteration. *)
let mir_run context start index (body : Mir.body) =
  (* A named function passed directly as an argument is checked against the
     parameter's function type at the call, as the core form's reading does,
     and not as a value used on its own. *)
  Hashtbl.iter
    (fun _ (node : expression) ->
      match node.kind with
      | Call called ->
          List.iter
            (function
              | Passed { value = Value argument; _ } -> (
                  let rec unwidened (node : expression) =
                    match node.kind with
                    | Convert { conversion = Widen; value = inner } -> unwidened inner
                    | _ -> node
                  in
                  match unwidened argument with
                  | { kind = Function_value _; id; _ } ->
                      context.passed_values <- id :: context.passed_values
                  | _ -> ())
              | Passed _ | Default -> ())
            called.arguments
      | _ -> ())
    index.expressions;
  let passed_lambdas = Hashtbl.create 2 in
  Hashtbl.iter
    (fun _ (node : expression) ->
      match node.kind with
      | Call called ->
          List.iter
            (function
              | Passed { value = Value { kind = Lambda _; id; _ }; _ } ->
                  Hashtbl.replace passed_lambdas id ()
              | Passed _ | Default -> ())
            called.arguments
      | _ -> ())
    index.expressions;
  let constructs = Hashtbl.create 4 in
  Array.iter
    (fun (block : Mir.basic_block) ->
      List.iter
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Assign
              {
                target = { root = Local local; projections = [] };
                value = Construct { variant; fields };
                _;
              } ->
              Hashtbl.replace constructs local (variant, fields)
          | _ -> ())
        block.statements)
    body.blocks;
  let run =
    {
      index;
      body;
      places = Hashtbl.create 4;
      lends = Hashtbl.create 4;
      constructs;
      slices = Hashtbl.create 2;
      provides = Hashtbl.create 2;
      passed_lambdas;
    }
  in
  let count = Array.length body.blocks in
  let incoming = Array.make count [] in
  let ran = Array.make count false in
  let rec terminator frame (block : Mir.basic_block) ~jump ~iteration_end =
    let span = span_of frame.source block.terminator_origin in
    match block.terminator with
    | Goto target -> jump target frame
    | Branch { condition; yes; no } ->
        let test = mir_operand context frame run condition in
        if frame.checking && Hashtbl.mem index.conditions block.terminator_origin then begin
          let text = quote frame.source block.terminator_origin in
          context.decisions <-
            ( Printf.sprintf "`%s` is true" text,
              Some (Printf.sprintf "`%s` is false" text),
              frame.condition,
              test )
            :: context.decisions
        end;
        jump yes (restrict frame test);
        jump no (restrict frame (Logic.not_ test))
    | Switch_variant { place; cases } ->
        let ty = mir_place_type context frame run place in
        let term = read_place context frame run place in
        List.iter
          (fun (variant, target) ->
            jump target (restrict frame (Logic.Is (constructor_name ty (Some variant), term))))
          cases
    | Return returned ->
        context.returns <-
          (frame, Option.map (mir_operand context frame run) returned) :: context.returns
    | Unreachable ->
        if Hashtbl.mem index.unreachable block.terminator_origin then
          oblige context frame Unreachable span "This `unreachable` may be reached."
            (Logic.Boolean false)
    | Todo ->
        if context.proving then begin
          context.holes <- (context.home, span) :: context.holes;
          context.unfinished <- frame.condition :: context.unfinished
        end
    | Iteration_end -> iteration_end frame
    | For { iteration; part; body = first; after; loop } -> (
        match Hashtbl.find_opt index.statements loop.origin with
        | Some
            ({ kind = For { pattern; iteration = written; clauses; body = written_body; _ }; _ } as
             node) -> (
            let body_blocks = reached body ~from:[ first ] ~avoid:(fun block -> block = after) in
            (* An iteration: the part takes the element, and the body's blocks
               run, each once, to the end of the iteration or a [break]. *)
            let run_body inside element =
              let inside =
                bind inside (mir_key run part)
                  (substituted context inside body.locals.(part).type_)
                  element
              in
              let ends = ref [] and breaks = ref [] in
              incoming.(first) <- [ inside ];
              run_region ~inside:(Hashtbl.mem body_blocks)
                ~jump:(fun target frame ->
                  if target = after then breaks := frame :: !breaks else jump target frame)
                ~iteration_end:(fun frame -> ends := frame :: !ends);
              (List.rev !ends, List.rev !breaks)
            in
            let operand = mir_operand context frame run in
            let driven =
              {
                run_body;
                range =
                  (match iteration with
                  | Range { start; stop; _ } -> Some (operand start, operand stop)
                  | Yielding _ | Pull _ -> None);
                arguments =
                  (match iteration with
                  | Yielding call -> Some (mir_arguments context frame run call.arguments)
                  | Range _ | Pull _ -> None);
                cursor =
                  (match iteration with
                  | Pull { cursor; _ } -> Some (mir_passed_place context run cursor)
                  | Range _ | Yielding _ -> None);
              }
            in
            match for_ ~driven context frame node pattern written clauses written_body with
            | Some ended -> jump after ended
            | None -> ())
        | _ -> bug "a loop of the MIR whose core loop is not known")
    | Yield { mode; part; resume } -> (
        match Hashtbl.find_opt index.statements block.terminator_origin with
        | Some ({ kind = Yield { part = written; _ }; _ } as node) -> (
            let handed = mir_operand context frame run part in
            let part_type = mir_operand_type context frame part in
            match
              yield_part
                ~given:
                  ( handed,
                    mir_lends_places run part,
                    fun frame after -> mir_written_back context run part_type part frame after )
                context frame node mode written
            with
            | Some after -> jump resume after
            | None -> ())
        | _ -> bug "a yield of the MIR whose core yield is not known")
    | Exit_tasks _ -> bug "a form the MIR's reading does not cover"
  and run_block position frame ~jump ~iteration_end =
    let block = body.blocks.(position) in
    let ended =
      List.fold_left
        (fun frame statement ->
          Option.bind frame (fun frame -> mir_statement context frame run statement))
        (Some frame) block.statements
    in
    Option.iter (fun frame -> terminator frame block ~jump ~iteration_end) ended
  (* Runs the blocks of a region, each once, in order, from the frames that
     reach them. A jump to a block outside the region leaves by [jump], and
     the end of an iteration of the innermost [for] by [iteration_end]. *)
  and run_region ~inside ~jump ~iteration_end =
    for position = 0 to count - 1 do
      if inside position && not ran.(position) then begin
        ran.(position) <- true;
        let frames = List.rev incoming.(position) in
        incoming.(position) <- [];
        match join_frames context frames with
        | None -> ()
        | Some entry -> (
            let local_jump target frame =
              if inside target && not ran.(target) then
                incoming.(target) <- frame :: incoming.(target)
              else jump target frame
            in
            match body.blocks.(position).header with
            | Some natural -> run_loop position natural entry ~jump:local_jump ~iteration_end
            | None -> run_block position entry ~jump:local_jump ~iteration_end)
      end
    done
  (* A [while] loop, from the frame on entry to its header. *)
  and run_loop header (natural : Mir.natural_loop) frame ~jump ~iteration_end =
    let node, condition, clauses, loop_body =
      match Hashtbl.find_opt index.statements natural.loop.origin with
      | Some ({ kind = While { condition; clauses; body; _ }; _ } as node) ->
          (node, condition, clauses, body)
      | _ -> bug "a loop of the MIR whose core loop is not known"
    in
    let span = span_of frame.source node.origin in
    check_invariants context frame clauses ~when_:"on entry to the loop";
    let { loop_costs = costs; fresh_mark = mark; facts_mark; preserved; havocked = head } =
      enter_loop context frame ~entry:frame clauses
        ~changed:(changed_places ~condition frame loop_body)
        loop_body
    in
    let iterations = iterations_so_far context head costs in
    let head = loop_head context head costs ~iterations in
    assume_invariants context head clauses;
    let top = head in
    let blocks = loop_blocks body header natural in
    let in_loop block = Hashtbl.mem blocks block in
    (* The condition's blocks: those the header reaches before the body. *)
    let tested =
      reached body ~from:[ header ] ~avoid:(fun block ->
          block = natural.body || not (in_loop block))
    in
    (* The blocks from which the loop's exit is reached, so that a jump to
       one leaves the loop, as a [return] does not. *)
    let toward_exit =
      let reaching = Hashtbl.create 8 in
      Hashtbl.replace reaching natural.after ();
      let changed = ref true in
      while !changed do
        changed := false;
        Array.iteri
          (fun position (block : Mir.basic_block) ->
            if
              (not (in_loop position))
              && (not (Hashtbl.mem reaching position))
              && List.exists (Hashtbl.mem reaching) (Mir.successors block.terminator)
            then begin
              Hashtbl.replace reaching position ();
              changed := true
            end)
          body.blocks
      done;
      reaching
    in
    let ends = ref [] and failed = ref [] and breaks = ref [] and inside = ref [] in
    let leaving_from = ref header in
    let loop_jump target frame =
      if target = header then ends := frame :: !ends
      else if target = natural.body then incoming.(target) <- frame :: incoming.(target)
      else if in_loop target then incoming.(target) <- frame :: incoming.(target)
      else if Hashtbl.mem toward_exit target then
        if Hashtbl.mem tested !leaving_from then failed := (target, frame) :: !failed
        else breaks := (target, frame) :: !breaks
      else jump target frame
    in
    (* The body's entry takes one step, as each iteration does. *)
    let enter_body () =
      let frames = List.rev incoming.(natural.body) in
      incoming.(natural.body) <-
        (match join_frames context frames with
        | Some entry ->
            let entry = spend context entry one_step in
            inside := [ entry ];
            [ entry ]
        | None -> [])
    in
    ran.(header) <- true;
    leaving_from := header;
    run_block header head ~jump:loop_jump ~iteration_end;
    for position = 0 to count - 1 do
      if in_loop position && not ran.(position) then begin
        if position = natural.body then enter_body ();
        ran.(position) <- true;
        leaving_from := position;
        let frames = List.rev incoming.(position) in
        incoming.(position) <- [];
        match join_frames context frames with
        | None -> ()
        | Some entry -> (
            match body.blocks.(position).header with
            | Some inner ->
                run_loop position inner entry ~iteration_end ~jump:(fun target frame ->
                    leaving_from := position;
                    loop_jump target frame)
            | None -> run_block position entry ~jump:loop_jump ~iteration_end)
      end
    done;
    let inside =
      match !inside with [ entry ] -> entry | _ -> restrict head (Logic.Boolean false)
    in
    let measures =
      match (measures_of clauses, condition.kind) with
      | Some measures, _ -> `Written measures
      | ( None,
          Compare
            { comparison = (Less | Less_equal | Greater | Greater_equal) as compared; left; right }
        )
        when is_functional_expression left && is_functional_expression right ->
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
          let _, left_value = value context { at with checking = false } left in
          let _, right_value = value context { at with checking = false } right in
          match compared with
          | Less -> Some [ Logic.Operation ("-", [ right_value; left_value ]) ]
          | Less_equal ->
              Some
                [
                  Logic.Operation
                    ("+", [ Logic.Operation ("-", [ right_value; left_value ]); Logic.int 1 ]);
                ]
          | Greater -> Some [ Logic.Operation ("-", [ left_value; right_value ]) ]
          | _ ->
              Some
                [
                  Logic.Operation
                    ("+", [ Logic.Operation ("-", [ left_value; right_value ]); Logic.int 1 ]);
                ])
      | `None -> None
    in
    let start_measures = if context.terminates then measure_terms inside else None in
    if context.terminates && start_measures = None then
      oblige context inside Termination span "This loop may not end: give it a `decreases` clause."
        (Logic.Boolean false);
    let most =
      match (start_measures, measure_terms frame, iterations) with
      | Some [ at_head ], Some [ on_entry ], Some iterations ->
          let last = fresh context head "last" Logic.Int in
          assume context head
            Logic.(
              equal iterations (int 0)
              ==> Operation ("<=", [ at_head; on_entry ])
              &&& (Operation (">=", [ iterations; int 1 ])
                  ==> (Operation ("<=", [ int 0; last ])
                      &&& Operation
                            ( "<=",
                              [
                                Operation ("+", [ Operation ("-", [ iterations; int 1 ]); last ]);
                                on_entry;
                              ] )
                      &&& Operation ("<", [ at_head; last ]))));
          [ Costs.at_least_zero (Costs.plus on_entry (Logic.int 1)) ]
      | _ -> []
    in
    let ends = List.rev !ends in
    let breaks = List.rev !breaks in
    loop_iterations context node top costs ~mark
      ~facts:(facts_since context facts_mark @ [ inside.condition ])
      ~ends ~breaks:(List.map snd breaks);
    List.iter
      (fun (end_ : frame) ->
        check_invariants context end_ clauses ~when_:"after an iteration";
        check_preserved_validity context end_ span preserved;
        match (start_measures, measure_terms end_) with
        | Some before, Some after ->
            oblige context end_ Termination span "This loop's measure may not decrease."
              (lexicographically_less before after)
        | _ -> ())
      ends;
    List.iter
      (fun (target, (failing : frame)) ->
        jump target (loop_exit context failing costs ~iterations ~most))
      (List.rev !failed);
    List.iter
      (fun (target, (leaving : frame)) ->
        jump target
          (loop_exit context leaving costs
             ~iterations:(Option.map (fun count -> Costs.plus count (Logic.int 1)) iterations)
             ~most))
      breaks
  in
  incoming.(0) <- [ start ];
  run_region
    ~inside:(fun _ -> true)
    ~jump:(fun target frame -> incoming.(target) <- frame :: incoming.(target))
    ~iteration_end:(fun _ -> bug "the end of an iteration outside a loop")

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
    datatypes = Hashtbl.create 16;
    stated = Hashtbl.create 64;
    facts = [];
    scopes = [];
    quantifier_facts = Hashtbl.create 16;
    quantifier_symbols = [];
    obligations = [];
    fresh = 0;
    values = [];
    local_names = Hashtbl.create 16;
    returns = [];
    leaving = [];
    lent_back = [];
    instantiating = [];
    yielded_part = None;
    yield_ensures = None;
    parameters = [];
    counters = [];
    own_bounds = [];
    fresh_order = Hashtbl.create 64;
    logs = [];
    powers = [];
    lambda_times = [];
    lambda_captures = [];
    lambda_definitions = Hashtbl.create 8;
    potentials = [];
    models = Hashtbl.create 16;
    holds_potential = Hashtbl.create 16;
    buffers = Hashtbl.create 16;
    equalities = [];
    known_calls = [];
    decisions = [];
    iteration_returns = [];
    entry = [];
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
    evaluated_keys = [];
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
    condition = Logic.Boolean true;
    checking = true;
    bound = [];
    binders = [];
    loop = None;
    substitution = [];
    self_type = None;
    yielded = None;
    finished = None;
    yielded_so_far = None;
    updating = None;
    spent = [];
  }

(* The span of the whole definition, for an obligation about how it
   returns. *)
let definition_span (source : source) =
  let spans = Lazy.force source.spans in
  match Array.length spans with 0 -> Syntax.Span.make 0 0 | count -> spans.(count - 1)

(* A cost clause, as a promise about one counter, shown at each way its
   definition returns. A trait's clause, which an [impl]'s method keeps, is
   read in the trait's form. *)
type promise = {
  counter : Costs.counter;
  clause : Core.cost;
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
              (match (cost.resource, resource) with
              | Calls (Function_parameter local), Calls (Through term) ->
                  context.call_targets <- (term, local) :: context.call_targets
              | _ -> ());
              if counter.counting = Units && not (List.mem counter context.own_bounds) then
                context.own_bounds <- counter :: context.own_bounds;
              Some { counter; clause = cost; written_in = source; inherited }))
    costs

(* The source of a method's inherited clauses, for messages: its trait,
   or its capability. *)
let promised_by database (source : source) =
  match source.key with
  | Some { path = Method { owner; _ }; _ }
    when Interface.Summary.kind_of database owner = Some Names.Capability ->
      "capability"
  | _ -> "trait"

(* A promise shown where its definition returns: the cost within
   its bound, read with the parameters as they were on entry. *)
let keep_promise context (frame : frame) (promise : promise) ~(at : frame) ~span ~change =
  let spent =
    match List.assoc_opt promise.counter frame.spent with Some term -> term | None -> Costs.zero
  in
  (* An amortized bound is on the cost plus the change in potential of the
     definition's result and changed values. *)
  let spent = if promise.clause.amortized then Costs.plus spent (change ()) else spent in
  let amount =
    match promise.clause.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (value context { at with checking = false } amount)
    | Finite -> Costs.zero
  in
  let goal =
    match promise.counter.counting with
    | Units -> Costs.at_most spent (Costs.bound amount)
    | Exactly -> Logic.equal spent amount
    | At_most -> Costs.at_most spent amount
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
let function_ ?(proof = false) ?(updating_helper = false) ?inherited ?(substitution = []) database
    (source : source) ~path =
  let parameters, contract, body =
    match source.core.definition with
    | Function { parameters; contract; body = Some body } -> (parameters, contract, body)
    | _ -> unsupported (definition_span source) "a function without a body"
  in
  let signature =
    Option.map
      (Types.map_signature (Types.substitute substitution))
      (Interface.Impls.signature database path)
  in
  let terminates =
    proof
    ||
    match signature with
    | Some (signature : Types.signature) -> signature.terminates
    | None -> false
  in
  let home = home source in
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
            (match self with
            | Logic.Symbol symbol -> context.entry <- symbol :: context.entry
            | _ -> ());
            (* A step of an update may be given a value in the middle of
               one. *)
            if not updating_helper then assume_valid context frame self_type self;
            { frame with self = Some self; self_type = Some self_type }
        | local ->
            let ty = substituted context frame parameter.type_ in
            let term = arrive context frame ("parameter." ^ parameter.name) ty in
            (match term with
            | Logic.Symbol symbol ->
                context.values <- (symbol, parameter.name) :: context.values;
                context.entry <- symbol :: context.entry
            | _ -> ());
            assume_valid context frame ty term;
            bind frame local ty term)
      { (empty_frame source) with substitution }
      parameters
  in
  let start = { start with old_locals = start.locals; old_self = start.self } in
  (* A lending or yielding method yields parts: its postconditions that
     mention [result] hold at each [yield], and its others where it ends. *)
  let start =
    match signature with
    | Some { output = (Yields (_, part) | Lends (_, part)) as output; _ } ->
        let kind = match output with Lends _ -> `Lends | _ -> `Yields in
        context.yielded_part <- Some (part, kind);
        context.yield_ensures <-
          Some
            ( List.filter mentions_result contract.ensures,
              List.filter (fun clause -> not (mentions_result clause)) contract.ensures );
        { start with yielded_so_far = Some (empty_parts context start part) }
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
  (* An [impl]'s method also keeps its trait's or its capability's contract.
     Callers through a bound or the capability prove that precondition, so
     it is assumed and must imply the method's own. They assume that
     postcondition, so it is proven. *)
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
              self_type = Option.map (fun (_, ty) -> Types.substitute substitution ty) self;
              result;
              checking = false;
              loop = None;
              updating = None;
              substitution;
            } )
    | _ -> None
  in
  let own_requires = List.map (fun (clause : condition) -> clause.value) contract.requires in
  (* The trait's precondition, on entry, under which its postcondition and
     cost clauses are promised. *)
  let trait_requires =
    match trait_frame start ~result:None with
    | Some (part, inside) ->
        Logic.conjunction
          (List.map (fun clause -> snd (clause_value context inside clause)) part.requires)
    | None -> Logic.Boolean true
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
    { start with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
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
        | Order_of amount | At_most amount | Exactly amount ->
            let result = Option.map (arrive context start "result") output in
            ignore (value context { start with result } amount)
        | Finite -> ())
    promised;
  let finished =
    match
      mir_of context source parameters
        ~runs:
          ((not proof)
          &&
          match signature with
          | Some (signature : Types.signature) -> not signature.specification_only
          | None -> false)
    with
    | Some (index, mir) ->
        mir_run context start index mir.body;
        None
    | None -> block_value context start body
  in
  let returns =
    (match finished with Some (frame, term) -> [ (frame, Some term) ] | None -> [])
    @ List.rev context.returns
  in
  let mut_parameters =
    List.filter
      (fun (parameter : Core.parameter) -> parameter.mode = Types.Mut && parameter.local <> Self)
      parameters
  in
  let mut_self =
    List.exists
      (fun (parameter : Core.parameter) -> parameter.mode = Types.Mut && parameter.local = Self)
      parameters
  in
  List.iter
    (fun ((frame : frame), returned) ->
      let frame = { frame with result = returned } in
      (* The values other code sees again: the result, each [mut] parameter, and
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
      (match (context.yield_ensures, frame.yielded_so_far) with
      | Some (_, at_end), Some yielded_so_far ->
          (* The postconditions about how a lending or yielding method ends,
             with everything it yielded, having run to its end. *)
          List.iter
            (fun (ensured : expression) ->
              let _, term =
                value context
                  { frame with yielded = Some yielded_so_far; finished = Some (Logic.Boolean true) }
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
      (* For an amortized bound: the potential of the result and the [mut]
         parameters on return, less that of the [mut] and [own] parameters
         on entry. *)
      let change () =
        let potential_change =
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
              | (Types.Mut | Types.Own), Some entry, Some ty ->
                  let potential_after =
                    match (parameter.mode, later) with
                    | Types.Mut, Some later -> potential context frame ty later
                    | _ -> Costs.zero
                  in
                  Costs.plus total (Costs.minus potential_after (potential context frame ty entry))
              | _ -> total)
            Costs.zero parameters
        in
        (* The caller pays for its changes to a part lent to it [mut], so the
           part's change in potential is not the method's. *)
        let potential_change =
          List.fold_left
            (fun total (ty, handed, back) ->
              Costs.minus total
                (Costs.minus (potential context frame ty back) (potential context frame ty handed)))
            potential_change context.lent_back
        in
        match (returned, output) with
        | Some term, Some output ->
            Costs.plus potential_change (potential context frame output term)
        | _ -> potential_change
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
          begin match (inherited, returned) with
          | Some (_, _, Some provided), Some returned ->
              if is_functional_block provided then
                begin match block_value context inside provided with
                | Some (_, defined) ->
                    oblige context frame Ensures returns_span
                      "This method overrides its trait's default body, so it must return the same \
                       value, and it may not."
                      (Logic.equal returned defined)
                | None -> ()
                end
              else
                oblige context frame Ensures returns_span
                  "This method overrides its trait's default body, which is not functional, so \
                   there is no definition to prove it equal to."
                  (Logic.Boolean false)
          | _ -> ()
          end
      | _ -> ())
    returns;
  outcome context

(* The laws of a trait an [impl] writes by hand, each shown for fresh
   values of its parameters, after the bodies of the [proof]s written for
   it. *)
let laws database (source : source) ~impl ~trait ~for_type ~proofs ~at =
  let home = home source in
  let context = new_context database ~home ~current:impl ~terminates:false ~measures:[] in
  let start = empty_frame source in
  let substitution = trait_substitution database trait for_type in
  List.iter
    (fun (law_source, (law : law)) ->
      let types = law_parameter_types ~substitution law in
      if not (List.exists (fun ty -> Types.is_error ty) types) then begin
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
                      Locals.add parameter.local (Types.substitute renaming parameter.type_) types
                    ))
                  (start.locals, start.types) parameters
                  (List.filteri (fun index _ -> index < List.length parameters) terms)
              in
              restrict start
                (Logic.not_
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
        match without_costs context (fun () -> block_value context inside law.body) with
        | Some (_, holds) ->
            oblige context start Law at
              (Printf.sprintf "The law `%s.%s` may not hold for `%s`." (Types.show_trait trait)
                 law.name (Types.show for_type))
              holds
        | None -> ()
      end)
    (laws_of context trait.trait);
  outcome context

(* A type's own clauses. Each invariant is well defined for a value whose
   fields meet their own types' invariants, given the invariants before
   it. The type's [cost potential] is well defined and never below zero
   for a value that meets its invariants, which makes each
   potential a fact about every valid value. *)
let type_ database (source : source) ~path =
  let home = home source in
  let context = new_context database ~home ~current:path ~terminates:false ~measures:[] in
  (match source.core.definition with
  | Type { invariants; potential; _ } ->
      let ty =
        match Query.demand database Interface.Environment.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            Types.Named { path; arguments = Types.generic_arguments interface.type_generics }
        | _ -> Types.Named { path; arguments = [] }
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
               (Types.show ty))
            (Logic.Operation ("<=", [ Logic.int 0; own ])))
        potential
  | _ -> ());
  outcome context

let test database (source : source) ~path =
  let home = home source in
  let context = new_context database ~home ~current:path ~terminates:false ~measures:[] in
  (match source.core.definition with
  | Test body -> ignore (block_value context (empty_frame source) body)
  | _ -> ());
  outcome context

(* A constant's value is well defined, as any expression is: its
   arithmetic stays in range, and its shifts and divisions are valid. *)
let constant database (source : source) ~path =
  let home = home source in
  let context = new_context database ~home ~current:path ~terminates:false ~measures:[] in
  (match source.core.definition with
  | Constant defined -> ignore (value context (empty_frame source) defined)
  | _ -> ());
  outcome context

let theorem database source ~path = function_ ~proof:true database source ~path
