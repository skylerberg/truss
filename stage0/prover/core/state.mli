(** The state of a proof of a checked definition: its types.

    Every body is read from the MIR: the code of the definition proven, and each formula that it or
    a callee states.

    A body is executed symbolically, forward, in passive form: every value is a term, every fact is
    guarded by the condition of the path it holds on, and where paths join, each local that differs
    gets a fresh symbol that each path defines. So the verification condition grows with the body,
    not with its number of paths. A formula is no body: it is mapped to a term by structural
    recursion, and joins no paths.

    Each obligation becomes one query: the facts gathered before it, and its goal, guarded by its
    path. Once made, an obligation is a fact for the rest of the body, since its own query proves
    it.

    Anything the prover cannot translate soundly raises [Unsupported], and the definition's
    obligations are not proven at all: an obligation is never assumed because the prover could not
    read the code around it. *)

module Symbol = Logic.Symbol
module Names = Resolve.Names
module Code = Diagnostic.Code
module Span = Syntax.Span
module Locals = Locals

type span = Syntax.span

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
  evaluation : evaluation option;  (** Running code that decides it, where there is any. *)
  known_calls : known_call list;  (** The calls its query mentions that running code can give. *)
  decisions : (string * string option * Logic.term * Logic.term) list;
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
  spans : span array Lazy.t;
  text : string Lazy.t;
}

(* The definition being proven from [source]. *)
(* One form's clauses about a callee: its own, or, for a method of an
   [impl], its trait's. Its parameters are in the order a call's arguments
   are, a method's receiver first. *)
type part = {
  callee : source;
  parameters : Mir.parameter list;
  requires : Mir.requirement list;
  ensures : Mir.formula list;
  decreases : Mir.formula list;
  costs : Mir.cost list;  (** Its cost clauses, but [cost time finite]. *)
  callbacks : (int * Mir.callback) list;
      (** The clauses of each function-typed parameter that states them, by its position. *)
  inherited : bool;  (** The trait's, which an [impl]'s method keeps. *)
}

type contract = {
  parts : part list;  (** The callee's own first. *)
  pure : bool;  (** Pure and terminating, so a function in the logic. *)
  result_kind : [ `Returns | `Lends ];
  definition : (part * Mir.formula) option;
      (** A functional body, which is the callee's definition, as a formula. *)
}

(* Where a path is: the value of each local, the values on entry for
   [old], the path's condition, and the values of [self] and [result]. *)
type frame = {
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
  substitution : Types.substitution;
      (** The type arguments of the callee whose clauses are read here, for its generic types. *)
  self_type : Types.ty option;  (** The type of [self], whose fields an invariant names. *)
  yielded : Logic.term option;
      (** The value of [yielded] here: the part a lending callee lent, or the values a [for] loop's
          earlier iterations received. *)
  yielded_so_far : Logic.term option;
      (** In a lending method's own body, the part it has lent, once it has. *)
  spent : (Costs.counter * Logic.term) list;
      (** Each counter's cost so far in the definition being proven. *)
}

(* The locals, and whether [self], a loop's body may mutate. *)
type changed = { changed_locals : Core.local list; changes_self : bool }

type loop_rule =
  | Clause_bound of Mir.cost
  | Per_iteration of { per : Logic.term; per_held : (Logic.term * Logic.term) option }

type loop_cost = {
  counter : Costs.counter;
  entry : Logic.term;  (** The counter on entry to the loop. *)
  rule : loop_rule;
  held : (frame -> Logic.term) option;  (** The potential of the values the loop mutates. *)
  held_on_entry : Logic.term option;  (** That potential on entry to the loop. *)
  gained_at_head : Logic.term option;
      (** For a [cost] clause of a loop whose changed values hold potential: what the clause counts
          at the head beside the cost so far. It is the potential gained if an iteration spends or
          saves potential, and zero otherwise, which is known once the body is read. *)
  mutable counts_potential : bool;
      (** Whether the loop's [cost] clause bounds its cost so far plus the potential gained. *)
}

(* Which elements an index or a range reaches: one, or the run from a start
   to before a stop. *)
type place_value = One of Logic.term | Run of Logic.term * Logic.term

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
   mode, what it is, its type, and its value. *)
type passed = {
  position : int;
  mode : Types.mode;
  shape : Invocation.shape;
  origin : Core.origin option;  (** Where the argument is written, for a fix that names it. *)
  passed_place : passed_place option;
      (** For an argument that is a place, the place. A slice passed [mut] writes its run back into
          the collection it views. *)
  type_ : Types.ty;
  term : Logic.term;
}

(* A lambda as the MIR holds it: its body, the bodies that its body names,
   its captures, whether its body is functional, and the type of its body's
   value before any conversion to [Integer]. *)
type lambda_code = {
  code : Mir.body;
  lambdas : Mir.body array;
  captures : Mir.capture list;
  definition : Mir.formula option;
  value_type : Types.ty option;
}

type given =
  | Given_value of passed
  | Given_lambda of {
      position : int;
      mode : Types.mode;
      site : Invocation.site;
      lambda : lambda_code;
    }

(* What a [for] loop iterates over, as the code evaluated it: a range's
   bounds, or the place of a cursor with its type's [next]. *)
type looped =
  | Over_range of { low : Logic.term; high : Logic.term; inclusive : bool }
  | Over_cursor of { cursor : passed_place; cursor_type : Types.ty; next : Invocation.callee }

type driven = {
  loop_at : Core.origin;
  loop_clauses : Mir.loop_clause list;
  looped : looped;
  element_type : Types.ty;
  lent_element : Types.ty option;
      (** In a loop over the elements of a collection, the type of the element each iteration is
          lent. The loop is then over the positions of the elements, and [yielded] holds the
          elements. *)
  kept_count : Mir.formula option;
      (** In a loop that mutates the elements of a collection, the call of the collection's [count],
          whose value every iteration keeps. *)
  collection : (frame -> Types.ty * Logic.term) option;
      (** In a loop over the elements of a collection, the collection's type and value. *)
  element_call : Mir.formula option;
      (** In a loop that reads the elements of a collection, the call of the collection's [element]
          at the loop's position. The loop borrows the collection, so the element at a position is
          the same value in every iteration, and [yielded] holds those values. *)
  bind_element : frame -> Logic.term -> frame;
  changed_in : frame -> changed;
      (** The values the loop mutates: those its body mutates, and a cursor it pulls. *)
  changed_by_body : frame -> changed;
  run_body : frame -> Logic.term -> frame list * frame list;
  bindings : frame -> frame;
}

(* The values a quantifier ranges over, once read. *)
type quantified_range =
  | Range_of_type of Types.ty
  | Range_of_integers of { low : Logic.term; high : Logic.term; inclusive : bool; type_ : Types.ty }
  | Range_of_collection of {
      collection_type : Types.ty;
      collected : Logic.term;
      element : Types.ty;
      span : span;
    }

(* A fact stated once in a definition's proof, by its subject. *)
type stated =
  | In_range of Logic.symbol  (** That a symbol's values are in its type's range. *)
  | Value_of of Logic.symbol  (** A constant's value. *)
  | Definition_of of Logic.symbol  (** A pure function's definition, for every argument. *)
  | Contract_of of Logic.symbol  (** A pure function's [ensures], for every valid argument. *)
  | Limited_link of Logic.symbol  (** That a function equals its limited copy where applied. *)
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
  mutable callbacks : (Core.local * string * Mir.callback) list;
      (** Each function-typed parameter of the definition that states clauses: its local, its name,
          and the clauses. *)
  measures : Mir.formula list;  (** Its [decreases], for its recursive calls. *)
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
  mutable lent_back : (Types.ty * Logic.term * Logic.term) list;
      (** Each part a lending method lends [mut]: its type, as it was lent, and as it came back. *)
  mutable instantiating : Path.t list;  (** Contracts being assumed, to stop at recursion. *)
  mutable axiomatizing : Logic.symbol list;
      (** The pure functions whose definition or contract is being stated over their parameters: a
          call to one of them inside is its limited copy. *)
  axiom_clauses : (Logic.symbol * string * Core.origin, unit) Hashtbl.t;
  defined_by_axiom : (Logic.symbol, bool) Hashtbl.t;
      (** Whether each pure function's definition is stated as an axiom, once it is decided. *)
  mutable open_axioms : open_axiom list;  (** The axioms being stated, innermost first. *)
  axioms_of : (Logic.symbol, open_axiom) Hashtbl.t;
  disjoint : (int * int) list;
      (** The ownership check's pairs of indexes, by the origin of each, that must differ. *)
  mutable indexes : (int * (place_value * span)) list;
      (** The value of each such index or range, once read. *)
  mutable evaluated_keys : (Core.id * Logic.term) list;
      (** The terms of the index keys of the target of the assignment being translated, by node.
          Reading and storing the target look them up, so that no key is evaluated twice. *)
  mutable yielded_part : Types.ty option;
      (** In a lending method's body, the type of the part it lends. *)
  mutable yield_ensures : (Mir.formula list * Mir.formula list) option;
      (** Its [ensures]: the clauses that mention [result], which hold where the method lends, and
          the others, which hold where the lend ends. *)
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
  mutable potentials : Logic.term list;
  models : (string, (Logic.term -> Logic.term) option) Hashtbl.t;
  holds_potential : (string, bool) Hashtbl.t;  (** Whether each type can hold potential. *)
  buffers : (string, (Types.ty * (Logic.term -> Logic.term)) option) Hashtbl.t;
      (** Each type's elements and model as a buffer's, where it is one. *)
  mutable equalities : Logic.term list;  (** Each derived [==] whose definition is a fact. *)
  mutable known_calls : known_call list;  (** Each call running code can give a value. *)
  mutable decisions : (string * string option * Logic.term * Logic.term) list;
      (** Each [if] and [match] arm read so far, reversed. *)
  mutable entry : Logic.symbol list;
      (** The symbols of the definition's parameters and [self] as they arrive. *)
  mutable proving : bool;
      (** In a theorem, a [proof] block, or a law's proof, where a [todo] is a hole. *)
  mutable holes : (Names.key * span) list;  (** Reversed. *)
  mutable unfinished : Logic.term list;
      (** The condition of each path a [todo] ends in the [proof] block being read. *)
  mutable call_targets : (Logic.term * Core.local) list;
      (** Each function-typed parameter a [calls] clause counts, with its local. *)
  mutable reading_callback : bool;
  ranking : bool;
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
  run_body : frame -> lambdas:Mir.body array -> Mir.body -> unit;
      (** Runs a body of the MIR from a frame: each value it returns joins [returns]. *)
  formula_term : frame -> Mir.formula -> arguments:Logic.term list -> frame * Logic.term;
      (** The value of a formula read from a frame, with [arguments] for its parameters, or none
          where it reads them from the frame: the term, and the frame as it was but for what reading
          the formula spent. *)
}

and open_axiom = {
  parameters : Logic.symbol list;
  mutable hypotheses : Logic.term list;
  mutable at_calls : (frame -> (Logic.term -> Logic.term) -> unit) list;
}

(* The package a callee is read from, for [source_at]: the definition's. *)
