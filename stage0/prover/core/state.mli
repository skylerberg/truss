module Symbol = Logic.Symbol
module Names = Resolve.Names
module Code = Diagnostic.Code
module Span = Syntax.Span
module Locals = Locals

type span = Syntax.span
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
  fixes : span Diagnostic.fix list;
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
  spans : span array Lazy.t;
  text : string Lazy.t;
}

type part = {
  callee : source;
  parameters : Mir.parameter list;
  requires : Mir.requirement list;
  ensures : Mir.formula list;
  decreases : Mir.formula list;
  costs : Mir.cost list;
  callbacks : (int * Mir.callback) list;
  inherited : bool;
}

type contract = {
  parts : part list;
  is_logic_function : bool;
  result_kind : [ `Returns | `Lends ];
  definition : (part * Mir.t) option;
}

type slice = {
  made_at : Invocation.site;
  collection : Mir.place;
  start : Logic.term;
  stop : Logic.term;
}

type held_slice = Slices of (Logic.term * slice) list | Unknown_slice

type frame = {
  source : source;
  locals : Logic.term Locals.t;
  types : Types.ty Locals.t;
  old_locals : Logic.term Locals.t;
  self : Logic.term option;
  old_self : Logic.term option;
  result : Logic.term option;
  condition : Logic.term;
  makes_obligations : bool;
  bound : Logic.symbol list;
  binders : (Logic.symbol * Logic.sort * Logic.term) list;
  substitution : Types.substitution;
  self_type : Types.ty option;
  yielded : Logic.term option;
  yielded_so_far : Logic.term option;
  spent : (Costs.counter * Logic.term) list;
  aliases : (Logic.term * Mir.place) list Locals.t;
  slices : held_slice Locals.t;
  lends : (Logic.term * (frame -> Logic.term -> frame)) list Locals.t;
}

type changed = {
  changed_locals : Core.local list;
  changes_self : bool;
  reassigned : Core.local list;
}

type place_value = One of Logic.term | Run of Logic.term * Logic.term
type passed_place = { read : frame -> Logic.term; write : frame -> Logic.term -> frame }

type passed = {
  position : int;
  mode : Types.mode;
  shape : Invocation.shape;
  origin : Core.origin option;
  passed_place : passed_place option;
  type_ : Types.ty;
  term : Logic.term;
}

type lambda_code = { code : Mir.body; lambdas : Mir.body array }

type call_argument =
  | Value_argument of passed
  | Lambda_argument of {
      position : int;
      mode : Types.mode;
      site : Invocation.site;
      lambda : lambda_code;
    }

type stated =
  | In_range of Logic.symbol
  | Value_of of Logic.symbol
  | Contract_of of Logic.symbol
  | Limited_link of Logic.symbol
  | Exclusive of Logic.symbol
  | Array_length of Logic.symbol
  | Ranked_model of Logic.symbol
  | Ranked_elements of Types.ty

type context = {
  database : Query.context;
  current : Path.t;
  mutable terminates : bool;
  mutable callbacks : (Core.local * string * Mir.callback) list;
  measures : Mir.formula list;
  mutable declarations : Logic.declaration list;
  declared : (Logic.symbol, unit) Hashtbl.t;
  datatypes : (Types.ty, unit) Hashtbl.t;
  stated : (stated, unit) Hashtbl.t;
  mutable facts : Logic.term list;
  mutable obligations : obligation list;
  mutable fresh : int;
  mutable values : (Logic.symbol * string) list;
  local_names : (Core.local, string) Hashtbl.t;
  mutable returns : (frame * Logic.term option) list;
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
  mutable yielded_part : Types.ty option;
  mutable yield_ensures : (Mir.formula list * Mir.formula list) option;
  home : Names.key;
  mutable laws_assumed : (Types.trait_reference * Types.ty) list;
  mutable counters : Costs.counter list;
  mutable own_bounds : Costs.counter list;
  fresh_order : (Logic.symbol, int) Hashtbl.t;
  mutable logs : (Logic.term * bool) list;
  mutable powers : (Logic.term * Logic.term) list;
  mutable lambda_times : (Logic.term * (Logic.term * obligation list)) list;
  mutable lambda_captures : (Logic.term * Core.local list) list;
  lambda_definitions : (Logic.symbol, Logic.term) Hashtbl.t;
  mutable potentials : Logic.term list;
  models : (Types.ty * Types.ty, (Logic.term -> Logic.term) option) Hashtbl.t;
  holds_potential : (Types.ty, bool) Hashtbl.t;
  buffers : (Types.ty, (Types.ty * (Logic.term -> Logic.term)) option) Hashtbl.t;
  mutable equalities : Logic.term list;
  mutable known_calls : known_call list;
  mutable decisions : (string * string option * Logic.term * Logic.term) list;
  mutable entry : Logic.symbol list;
  mutable proving : bool;
  mutable holes : (Names.key * span) list;
  mutable unfinished : Logic.term list;
  mutable call_targets : (Logic.term * Core.local) list;
  mutable reading_callback : bool;
  ranking : bool;
  mutable scopes : (Logic.symbol * Logic.term list ref) list;
  quantifier_facts : (Logic.term, Logic.term list) Hashtbl.t;
  mutable quantifier_symbols : Logic.symbol list;
  mutable validating : Types.ty list;
  run_body : frame -> lambdas:Mir.body array -> Mir.body -> unit;
  formula_term : frame -> Mir.formula -> arguments:Logic.term list -> frame * Logic.term;
}

and open_axiom = {
  parameters : Logic.symbol list;
  mutable hypotheses : Logic.term list;
  mutable at_calls : (frame -> (Logic.term -> Logic.term) -> unit) list;
}
