type template_check = { from_template : Path.t; literals : string list; clauses : int list }
type template_clause = { check : template_check; clause : int }

type piece =
  | Text of string
  | Quote of Resolve.Names.key * Core.origin
  | Substituted of {
      key : Resolve.Names.key;
      clause : Core.origin;
      replacements : (Core.origin * string) list;
      type_names : (string * string) list;
    }

type message = piece list
type location = Node of Core.origin | Whole_definition
type edit = { at : Source.Definition_span.t; replacement : message }
type fix = { title : message; edits : edit list }

type obligation = {
  code : Diagnostic.Code.prover;
  location : location;
  message : message;
  cited : (Resolve.Names.key * Core.origin) option;
  fixes : fix list;
  query : Logic.query;
  values : (Logic.symbol * string) list;
  locals : (Logic.term * string) list;
  template_clause : template_clause option;
  decisions : (string * string option * Logic.term * Logic.term) list;
}

type outcome = { obligations : obligation list; holes : (Resolve.Names.key * location) list }
type source = { key : Resolve.Names.key option; name : string }

type clauses = {
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
  callee_clauses : clauses;
  trait_clauses : clauses option;
  is_logic_function : bool;
  result_kind : [ `Returns | `Lends ];
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
  binder_facts : (Logic.symbol * Logic.term list ref) list;
  open_axioms : open_axiom list;
  substitution : Types.substitution;
  self_type : Types.ty option;
  yielded : Logic.term option;
  yielded_so_far : Logic.term option;
  spent : (Costs.counter * Logic.term) list;
  aliases : (Logic.term * Mir.place) list Locals.t;
  slices : held_slice Locals.t;
  lends : (Logic.term * (frame -> Logic.term -> frame)) list Locals.t;
}

and open_axiom = {
  parameters : Logic.symbol list;
  mutable hypotheses : Logic.term list;
  mutable at_calls : (frame -> (Logic.term -> Logic.term) -> unit) list;
}

type changed = {
  changed_locals : Locals.local list;
  changes_self : bool;
  reassigned : Locals.local list;
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

type stated = Tables.stated =
  | In_range of Logic.symbol
  | Value_of of Logic.symbol
  | Contract_of of Logic.symbol
  | Limited_link of Logic.symbol
  | Exclusive of Logic.symbol
  | Array_length of Logic.symbol
  | Ranked_model of Logic.symbol
  | Ranked_elements of Types.ty

type definition = {
  lookups : Lookups.t;
  home : Resolve.Names.key;
  current : Path.t;
  node : Path.t;
  measures : Mir.formula list;
  disjoint : (int list * int list) list;
  ranking : bool;
  inherits_precondition : bool;
  callbacks : (Core.local * string * Mir.callback) list;
  yielded_part : Types.ty option;
  yield_ensures : (Mir.formula list * Mir.formula list) option;
}

type vocabulary = {
  mutable declarations : Logic.declaration list;
  declared : unit Tables.Symbol_table.t;
  definitions : unit Tables.Symbol_table.t;
  datatypes : unit Tables.Type_table.t;
  mutable fresh : int;
  fresh_order : int Tables.Symbol_table.t;
  models : (Logic.term -> Logic.term) option Tables.Model_table.t;
  holds_potential : bool Tables.Type_table.t;
  buffers : (Types.ty * (Logic.term -> Logic.term)) option Tables.Type_table.t;
  lambda_definitions : Logic.term Tables.Symbol_table.t;
  mutable lambda_costs : ((Logic.term * Metric.t) * (Logic.term * obligation list)) list;
  mutable lambda_captures : (Logic.term * Core.local list) list;
}

type assertions = {
  mutable facts : Logic.term list;
  stated : unit Tables.Stated_table.t;
  mutable decisions : (string * string option * Logic.term * Logic.term) list;
  quantifier_facts : Logic.term list Tables.Term_table.t;
  mutable quantifier_symbols : Logic.symbol list;
  mutable equalities : Logic.term list;
  mutable logs : (Logic.term * bool) list;
  mutable powers : (Logic.term * Logic.term) list;
  mutable indexes : (int * place_value) list;
  mutable potentials : Logic.term list;
  axiom_clauses : unit Tables.Axiom_clause_table.t;
  axioms_of : open_axiom Tables.Symbol_table.t;
  mutable laws_assumed : (Types.trait_reference * Types.ty) list;
}

type report = {
  mutable obligations : obligation list;
  mutable holes : (Resolve.Names.key * location) list;
  local_names : string Tables.Local_table.t;
  local_origins : Core.origin Tables.Local_table.t;
}

type entry = {
  parameters : Logic.symbol list;
  parameter_names : (Logic.symbol * string) list;
  bounded_counters : Costs.counter list;
  call_targets : (Logic.term * Core.local) list;
}

type ghost_run = { mutable unfinished : Logic.term list }
type proving = Not_proving | Proving_theorem | Running_ghost_code of ghost_run

type scope = {
  mutable terminates : bool;
  mutable counters : Costs.counter list;
  mutable proving : proving;
  mutable is_reading_callback : bool;
  mutable validating : Types.ty list;
  mutable instantiating : Path.t list;
  mutable axiomatizing : Logic.symbol list;
}

type context = {
  definition : definition;
  vocabulary : vocabulary;
  assertions : assertions;
  report : report;
  entry : entry;
  scope : scope;
  reader : reader;
}

and reader = {
  read_lambda_body :
    context -> frame -> lambdas:Mir.body array -> Mir.body -> (frame * Logic.term option) list;
  read_formula : context -> frame -> Mir.formula -> arguments:Logic.term list -> frame * Logic.term;
}
