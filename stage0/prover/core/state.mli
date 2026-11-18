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
  panic_clause : Interface.Impls.declaring_clause option;
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
type panic = Declared | Undeclared of Interface.Impls.declaring_clause | Undeclarable

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
  panic : panic;
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

type context = {
  lookups : Lookups.t;
  current : Path.t;
  node : Path.t;
  mutable terminates : bool;
  mutable callbacks : (Core.local * string * Mir.callback) list;
  measures : Mir.formula list;
  mutable declarations : Logic.declaration list;
  declared : unit Tables.Symbol_table.t;
  definitions : unit Tables.Symbol_table.t;
  datatypes : unit Tables.Type_table.t;
  stated : unit Tables.Stated_table.t;
  mutable facts : Logic.term list;
  mutable obligations : obligation list;
  mutable fresh : int;
  mutable values : (Logic.symbol * string) list;
  local_names : string Tables.Local_table.t;
  local_origins : Core.origin Tables.Local_table.t;
  mutable returns : (frame * Logic.term option) list;
  mutable lent_back : (Types.ty * Logic.term * Logic.term) list;
  mutable instantiating : Path.t list;
  mutable axiomatizing : Logic.symbol list;
  axiom_clauses : unit Tables.Axiom_clause_table.t;
  mutable open_axioms : open_axiom list;
  axioms_of : open_axiom Tables.Symbol_table.t;
  disjoint : (int list * int list) list;
  mutable indexes : (int * place_value) list;
  mutable yielded_part : Types.ty option;
  mutable yield_ensures : (Mir.formula list * Mir.formula list) option;
  home : Resolve.Names.key;
  mutable laws_assumed : (Types.trait_reference * Types.ty) list;
  mutable counters : Costs.counter list;
  mutable bounded_counters : Costs.counter list;
  fresh_order : int Tables.Symbol_table.t;
  mutable logs : (Logic.term * bool) list;
  mutable powers : (Logic.term * Logic.term) list;
  mutable lambda_costs : ((Logic.term * Metric.t) * (Logic.term * obligation list)) list;
  mutable lambda_captures : (Logic.term * Core.local list) list;
  lambda_definitions : Logic.term Tables.Symbol_table.t;
  mutable potentials : Logic.term list;
  models : (Logic.term -> Logic.term) option Tables.Model_table.t;
  holds_potential : bool Tables.Type_table.t;
  buffers : (Types.ty * (Logic.term -> Logic.term)) option Tables.Type_table.t;
  mutable equalities : Logic.term list;
  mutable decisions : (string * string option * Logic.term * Logic.term) list;
  mutable entry : Logic.symbol list;
  mutable proving : bool;
  inherits_precondition : bool;
  mutable holes : (Resolve.Names.key * location) list;
  mutable unfinished : Logic.term list;
  mutable call_targets : (Logic.term * Core.local) list;
  mutable reading_callback : bool;
  ranking : bool;
  mutable scopes : (Logic.symbol * Logic.term list ref) list;
  quantifier_facts : Logic.term list Tables.Term_table.t;
  mutable quantifier_symbols : Logic.symbol list;
  mutable validating : Types.ty list;
  run_body : frame -> lambdas:Mir.body array -> Mir.body -> unit;
  read_formula : frame -> Mir.formula -> arguments:Logic.term list -> frame * Logic.term;
}

and open_axiom = {
  parameters : Logic.symbol list;
  mutable hypotheses : Logic.term list;
  mutable at_calls : (frame -> (Logic.term -> Logic.term) -> unit) list;
}
