module T = Types
module L = Logic
module S = Logic.Symbol
module Names = Resolve.Names
module Code = Diagnostic.Code
module Span = Syntax.Span

type span = Syntax.span

module Locals : Map.S with type key = Core.local

exception Unsupported of span * string
exception Foreign_unsupported of string

type evaluation = { from_template : Path.t; texts : string list; clause : int }
type known_call = { function_ : Path.t; arguments : Z.t list; term : L.term; result_is_bool : bool }

type obligation = {
  code : Code.prover;
  span : span;
  message : string;
  cited : (Names.key * span) option;
  fixes : Diagnostic.fix list;
  query : L.query;
  contracts_alone : L.query option;
  values : (S.t * string) list;
  locals : (S.t * string) list;
  constants : Costs.constants list;
  evaluation : evaluation option;
  known_calls : known_call list;
  decisions : (string * string option * L.term * L.term) list;
  hidden : (string * bool) list;
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
and exit_ = Returning of L.term option | Breaking | Continuing

and frame = {
  source : source;
  locals : L.term Locals.t;
  types : T.ty Locals.t;
  old_locals : L.term Locals.t;
  self : L.term option;
  old_self : L.term option;
  result : L.term option;
  condition : L.term;
  checking : bool;
  bound : S.t list;
  binders : (S.t * L.sort * L.term) list;
  loop : loop_exits option;
  substitution : T.substitution;
  self_type : T.ty option;
  yielded : L.term option;
  finished : L.term option;
  handed_out : L.term option;
  updating : L.term option;
  spent : (string * L.term) list;
}

type changed = { changed_locals : Core.local list; changes_self : bool }

type loop_rule =
  | Clause_bound of Core.cost * Costs.constants option
  | Per_iteration of { per : L.term; per_held : (L.term * L.term) option }

type loop_cost = {
  counter : Costs.counter;
  key : string;
  entry : L.term;
  rule : loop_rule;
  held : (frame -> L.term) option;
}

type place_value = One of L.term | Run of L.term * L.term
type cursor = { method_frame : frame; own : part; element : T.ty }
type received = { another : L.term; element : L.term; through : L.term; advance : frame -> frame }

type passed = {
  position : int;
  mode : T.mode;
  operand : Core.operand option;
  type_ : T.ty;
  term : L.term;
  run : (L.term * L.term) option;
}

type stated =
  | In_range of S.t
  | Value_of of S.t
  | Definition_of of S.t
  | Contract_of of S.t
  | Exclusive of S.t
  | Array_length of S.t
  | Ranked_model of S.t
  | Ranked_elements of string

type context = {
  database : Query.context;
  current : Path.t;
  mutable terminates : bool;
  mutable parameters : Core.parameter list;
  measures : Core.expression list;
  mutable declarations : L.declaration list;
  declared : (S.t, unit) Hashtbl.t;
  datatypes : (string, unit) Hashtbl.t;
  stated : (stated, unit) Hashtbl.t;
  mutable facts : L.term list;
  unfolded : (L.term, unit) Hashtbl.t;
  mutable obligations : obligation list;
  mutable fresh : int;
  mutable values : (S.t * string) list;
  local_names : (Core.local, string) Hashtbl.t;
  mutable returns : (frame * L.term option) list;
  mutable leaving : leaving list;
  mutable lent_back : (T.ty * L.term * L.term) list;
  mutable instantiating : Path.t list;
  disjoint : (int * int) list;
  mutable indexes : (int * (place_value * span)) list;
  mutable hands_out : (T.ty * [ `Lends | `Yields ]) option;
  mutable handing : (Core.expression list * Core.expression list) option;
  home : Names.key;
  mutable laws_assumed : string list;
  mutable counters : Costs.counter list;
  mutable own_constants : (string * Costs.constants) list;
  mutable groups : Costs.constants list;
  fresh_order : (S.t, int) Hashtbl.t;
  mutable logs : (L.term * bool) list;
  mutable powers : (L.term * L.term) list;
  mutable lambda_times : (L.term * (L.term * obligation list)) list;
  mutable lambda_captures : (L.term * Core.local list) list;
  lambda_definitions : (S.t, L.term) Hashtbl.t;
  mutable potentials : L.term list;
  models : (string, (L.term -> L.term) option) Hashtbl.t;
  holds_potential : (string, bool) Hashtbl.t;
  buffers : (string, (T.ty * (L.term -> L.term)) option) Hashtbl.t;
  mutable equalities : L.term list;
  mutable known_calls : known_call list;
  mutable decisions : (string * string option * L.term * L.term) list;
  mutable iteration_returns : (Core.origin * T.ty option) list;
  reveal : bool;
  mutable entry : S.t list;
  mutable hidden_bodies : (S.t * (string * bool)) list;
  mutable cursors : (L.term * cursor) list;
  mutable proving : bool;
  mutable holes : (Names.key * span) list;
  mutable unfinished : L.term list;
  mutable call_targets : (L.term * Core.local) list;
  mutable passed_values : int list;
  mutable reading_callback : bool;
  ranking : bool;
  mutable scopes : (S.t * L.term list ref) list;
  quantifier_facts : (L.term, L.term list) Hashtbl.t;
  mutable quantifier_symbols : S.t list;
  mutable validating : T.ty list;
}

val quote : source -> int -> string
val source_at_key : Query.context -> Names.key -> source option

type found = Written | Derived | Provided

val law_proofs :
  Query.context ->
  Path.package ->
  T.trait_reference ->
  T.ty ->
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
  constants : Costs.constants option;
  written_in : source;
  inherited : bool;
}

val function_ :
  ?reveal:bool ->
  ?proof:bool ->
  ?updating_helper:bool ->
  ?inherited:part * T.substitution * Core.block option ->
  Query.context ->
  source ->
  path:Path.t ->
  outcome

val laws :
  ?reveal:bool ->
  Query.context ->
  source ->
  impl:Path.t ->
  trait:T.trait_reference ->
  for_type:T.ty ->
  proofs:(string * (source * T.substitution * Core.parameter list * Core.block)) list ->
  at:span ->
  outcome

val type_ : ?reveal:bool -> Query.context -> source -> path:Path.t -> outcome
val test : ?reveal:bool -> Query.context -> source -> path:Path.t -> outcome
val constant : ?reveal:bool -> Query.context -> source -> path:Path.t -> outcome
val theorem : ?reveal:bool -> Query.context -> source -> path:Path.t -> outcome
