module Symbol = Logic.Symbol
module Names = Resolve.Names
module Code = Diagnostic.Code
module Span = Syntax.Span

type span = Syntax.span

module Locals : Map.S with type key = Core.local

exception Unsupported of span * string
exception Foreign_unsupported of string

type evaluation = { from_template : Path.t; texts : string list; clause : int }

type known_call = {
  function_ : Path.t;
  arguments : Z.t list;
  term : Logic.term;
  result_is_bool : bool;
}

type obligation = {
  code : Code.prover;
  span : span;
  message : string;
  cited : (Names.key * span) option;
  fixes : Syntax.span Diagnostic.fix list;
  query : Logic.query;
  values : (Logic.symbol * string) list;
  locals : (Logic.symbol * string) list;
  evaluation : evaluation option;
  known_calls : known_call list;
  decisions : (string * string option * Logic.term * Logic.term) list;
}

type outcome = { obligations : obligation list; holes : (Names.key * span) list }

type source = {
  key : Names.key option;
  name : string;
  core : Core.t;
  spans : span array Lazy.t;
  text : string Lazy.t;
}

type part = {
  callee : source;
  parameters : Core.parameter list;
  requires : Core.expression list;
  ensures : Core.expression list;
  decreases : Core.expression list;
  costs : Core.cost list;
  inherited : bool;
}

type contract = {
  parts : part list;
  pure : bool;
  result_kind : [ `Lends | `Returns | `Yields ];
  definition : (part * Core.block) option;
}

type loop_exits = { mutable breaks : frame list; mutable continues : frame list }
and leaving = { tasks : Core.task list; at : frame; exit : exit_ }
and exit_ = Returning of Logic.term option | Breaking | Continuing

and frame = {
  source : source;
  locals : Logic.term Locals.t;
  types : Types.ty Locals.t;
  old_locals : Logic.term Locals.t;
  self : Logic.term option;
  old_self : Logic.term option;
  result : Logic.term option;
  condition : Logic.term;
  checking : bool;
  bound : Logic.symbol list;
  binders : (Logic.symbol * Logic.sort * Logic.term) list;
  loop : loop_exits option;
  substitution : Types.substitution;
  self_type : Types.ty option;
  yielded : Logic.term option;
  finished : Logic.term option;
  yielded_so_far : Logic.term option;
  updating : Logic.term option;
  spent : (Costs.counter * Logic.term) list;
}

type changed = { changed_locals : Core.local list; changes_self : bool }

type loop_rule =
  | Clause_bound of Core.cost
  | Per_iteration of { per : Logic.term; per_held : (Logic.term * Logic.term) option }

type loop_cost = {
  counter : Costs.counter;
  entry : Logic.term;
  rule : loop_rule;
  held : (frame -> Logic.term) option;
}

type place_value = One of Logic.term | Run of Logic.term * Logic.term
type cursor = { method_frame : frame; own : part; element : Types.ty }

type received = {
  has_another : Logic.term;
  element : Logic.term;
  through : Logic.term;
  advance : frame -> frame;
}

type passed = {
  position : int;
  mode : Types.mode;
  operand : Core.operand option;
  type_ : Types.ty;
  term : Logic.term;
  run : (Logic.term * Logic.term) option;
}

type stated =
  | In_range of Logic.symbol
  | Value_of of Logic.symbol
  | Definition_of of Logic.symbol
  | Contract_of of Logic.symbol
  | Limited_link of Logic.symbol
  | Exclusive of Logic.symbol
  | Array_length of Logic.symbol
  | Ranked_model of Logic.symbol
  | Ranked_elements of string

type context = {
  database : Query.context;
  current : Path.t;
  mutable terminates : bool;
  mutable parameters : Core.parameter list;
  measures : Core.expression list;
  mutable declarations : Logic.declaration list;
  declared : (Logic.symbol, unit) Hashtbl.t;
  datatypes : (string, unit) Hashtbl.t;
  stated : (stated, unit) Hashtbl.t;
  mutable facts : Logic.term list;
  mutable obligations : obligation list;
  mutable fresh : int;
  mutable values : (Logic.symbol * string) list;
  local_names : (Core.local, string) Hashtbl.t;
  mutable returns : (frame * Logic.term option) list;
  mutable leaving : leaving list;
  mutable lent_back : (Types.ty * Logic.term * Logic.term) list;
  mutable instantiating : Path.t list;
  mutable axiomatizing : Logic.symbol list;
  axiom_clauses : (Logic.symbol * string * Core.origin, unit) Hashtbl.t;
  defined_by_axiom : (Logic.symbol, bool) Hashtbl.t;
  mutable open_axioms : open_axiom list;
  axioms_of : (Logic.symbol, open_axiom) Hashtbl.t;
  disjoint : (int * int) list;
  mutable indexes : (int * (place_value * span)) list;
  mutable evaluated_keys : (Core.id * Logic.term) list;
  mutable yielded_part : (Types.ty * [ `Lends | `Yields ]) option;
  mutable yield_ensures : (Core.expression list * Core.expression list) option;
  home : Names.key;
  mutable laws_assumed : string list;
  mutable counters : Costs.counter list;
  mutable own_bounds : Costs.counter list;
  fresh_order : (Logic.symbol, int) Hashtbl.t;
  mutable logs : (Logic.term * bool) list;
  mutable powers : (Logic.term * Logic.term) list;
  mutable lambda_times : (Logic.term * (Logic.term * obligation list)) list;
  mutable lambda_captures : (Logic.term * Core.local list) list;
  lambda_definitions : (Logic.symbol, Logic.term) Hashtbl.t;
  mutable potentials : Logic.term list;
  models : (string, (Logic.term -> Logic.term) option) Hashtbl.t;
  holds_potential : (string, bool) Hashtbl.t;
  buffers : (string, (Types.ty * (Logic.term -> Logic.term)) option) Hashtbl.t;
  mutable equalities : Logic.term list;
  mutable known_calls : known_call list;
  mutable decisions : (string * string option * Logic.term * Logic.term) list;
  mutable iteration_returns : (Core.origin * Types.ty option) list;
  mutable entry : Logic.symbol list;
  mutable cursors : (Logic.term * cursor) list;
  mutable proving : bool;
  mutable holes : (Names.key * span) list;
  mutable unfinished : Logic.term list;
  mutable call_targets : (Logic.term * Core.local) list;
  mutable passed_values : int list;
  mutable reading_callback : bool;
  ranking : bool;
  mutable scopes : (Logic.symbol * Logic.term list ref) list;
  quantifier_facts : (Logic.term, Logic.term list) Hashtbl.t;
  mutable quantifier_symbols : Logic.symbol list;
  mutable validating : Types.ty list;
}

and open_axiom = {
  parameters : Logic.symbol list;
  mutable hypotheses : Logic.term list;
  mutable at_calls : (frame -> (Logic.term -> Logic.term) -> unit) list;
}

val quote : source -> int -> string
val source_at_key : Query.context -> Names.key -> source option

type form_origin = Written | Derived | Provided

val law_proofs :
  Query.context ->
  Path.package ->
  Types.trait_reference ->
  Types.ty ->
  (string * (source * Types.substitution * Core.parameter list * Core.block)) list

val impl_unfinished : Query.context -> Names.key -> bool
val trait_part : Query.context -> Path.t -> string -> Path.receiver -> part option
val capability_part : Query.context -> Path.t -> string -> part option
val provided_body : Query.context -> Path.t -> string -> Path.receiver -> Core.block option
val is_updating_helper : Query.context -> Path.t -> bool
val definition_span : source -> Span.t

type promise = {
  counter : Costs.counter;
  clause : Core.cost;
  written_in : source;
  inherited : bool;
}

val function_ :
  ?proof:bool ->
  ?updating_helper:bool ->
  ?inherited:part * Types.substitution * Core.block option ->
  ?substitution:Types.substitution ->
  Query.context ->
  source ->
  path:Path.t ->
  outcome
(** The obligations of a function. With [substitution], its type parameters are those types, for a
    function proven once for each type a bound allows. *)

val laws :
  Query.context ->
  source ->
  impl:Path.t ->
  trait:Types.trait_reference ->
  for_type:Types.ty ->
  proofs:(string * (source * Types.substitution * Core.parameter list * Core.block)) list ->
  at:span ->
  outcome

val type_ : Query.context -> source -> path:Path.t -> outcome
val test : Query.context -> source -> path:Path.t -> outcome
val constant : Query.context -> source -> path:Path.t -> outcome
val theorem : Query.context -> source -> path:Path.t -> outcome
