type source = { key : Resolve.Names.key; definition : Path.t }

type clauses = {
  callee : source;
  parameters : Mir.parameter list;
  panics_unless : Mir.requirement list;
  requires : Mir.requirement list;
  ensures : Mir.formula list;
  decreases : Mir.formula list;
  costs : Mir.cost list;
  callbacks : (int * Mir.callback) list;
  inherited : bool;
  bindings : Types.substitution;
}

type contract = {
  callee_clauses : clauses;
  trait_clauses : clauses option;
  restated_clauses : clauses list;
  is_logic_function : bool;
  result_kind : [ `Returns | `Lends ];
}

type known_callee = {
  known_signature : Types.signature option Lazy.t;
  known_clauses : (Interface.form_origin * clauses option) option Lazy.t;
}

type known_function =
  | Named of {
      path : Path.t;
      contract : contract;
      substitution_of : clauses -> Types.substitution;
      type_arguments : Types.argument list;
      group_member : Path.t option;
      may_abort : bool;
    }
  | Own of { name : string; callback : Mir.callback }

type obligation_policy = {
  panic_condition : Catalog.Prover.quoted list option;
  keeps_termination : bool;
  keeps_failures : bool;
}

type environment = {
  lookups : Lookups.t;
  current : Path.t;
  node : Path.t;
  home : Resolve.Names.key;
  condition : Types.condition;
  bounds : Interface.Impls.bounds;
  disjoint : (Core.id list * Core.id list) list;
  inherits_precondition : bool;
  ranking : bool;
  policy : obligation_policy;
  visible_types : (Types.type_interface * Types.substitution) option Tables.Type_table.t;
  callees : known_callee Tables.Path_table.t;
}

type frame = {
  environment : environment;
  query : Query.t;
  source : source;
  locals : Logic.term Locals.t;
  types : Types.ty Locals.t;
  old_locals : Logic.term Locals.t;
  self : Logic.term option;
  old_self : Logic.term option;
  result : Logic.term option;
  condition : Logic.term;
  makes_obligations : bool;
  is_ghost : bool;
  bound : Logic.symbol list;
  binders : (Logic.symbol * Logic.sort * Logic.term) list;
  substitution : Types.substitution;
  self_type : Types.ty option;
  visited : Logic.term option;
  final_result : Logic.term option;
  spent : (Costs.counter * Logic.term) list;
  aliases : (Logic.term * Mir.place) list Locals.t;
  lends : (Logic.term * (frame -> Logic.term -> frame)) list Locals.t;
  callbacks : (Logic.term * (Types.function_type * known_function)) list;
  requires_being_read : Core.origin option;
  callees_whose_requires_are_read : Path.t list;
  provided : Mir.provided list list;
  panics : bool;
  can_declare_panic : bool;
  instantiating : (Path.t * int) list;
  obligation_condition : Types.condition;
  is_reading_callback : bool;
  validating : Types.ty list;
}

type changed_part = { root : Locals.local; declared_root_type : Types.ty; fields : string list }
type place_value = One of Logic.term | Run of Logic.term * Logic.term
type noted_place = { origin : Core.origin; value : place_value }
type function_exit = { frame : frame; returned : Logic.term option; return_origin : Core.origin }

type passed_place = {
  read : frame -> Logic.term;
  write : frame -> is_valid:bool -> Logic.term -> frame * (frame -> unit);
}

type passed = {
  position : int;
  mode : Language.Mode.t;
  origin : Core.origin option;
  passed_place : passed_place option;
  is_step_self : bool;
  type_ : Types.ty;
  declared_type : Types.ty;
  term : Logic.term;
}

type lambda_code = { code : Mir.body; lambdas : Mir.body array }

type call_argument =
  | Value_argument of passed
  | Lambda_argument of {
      position : int;
      mode : Language.Mode.t;
      site : Invocation.site;
      lambda : lambda_code;
    }

type call_amount = {
  call : Catalog.Prover.quoted;
  callee : Path.t;
  states_cost : bool;
  counts_potential : bool;
  counter : Costs.counter;
  amount : Logic.term;
}

type buffer = {
  kind : Language.Builtin_type.t;
  element : Types.ty;
  model_of : Logic.term -> Logic.term;
}

type cost_state = {
  mutable counters : Costs.counter list;
  mutable conditional_counters : Costs.counter list;
  mutable bounded_counters : Costs.counter list;
  mutable recursive_costs_assumed : int;
  mutable lambdas_assuming_recursive_costs : Logic.term list;
  mutable lambda_costs : ((Logic.term * Language.Metric.t) * (Logic.term * Obligation.t list)) list;
  mutable lambda_bounds :
    (Logic.term * ((Language.Metric.t * Logic.term) list * Core.local list)) list;
  mutable lambda_captures : (Logic.term * Core.local list) list;
  mutable call_targets : (Logic.term * Core.local) list;
  mutable call_amounts : call_amount list;
  mutable potentials : Logic.term list;
  mutable credited_holders : string list;
  mutable blocked_holders : string list;
  holds_potential : bool Tables.Type_table.t;
  buffers : buffer option Tables.Type_table.t;
}

type lent_part = { lent_frame : frame; lent_origin : Core.origin }
type lending_state = { mutable part_type : Types.ty option; mutable lent_parts : lent_part list }

type open_axiom = {
  parameters : Logic.symbol list;
  mutable hypotheses : Logic.term list;
  mutable at_calls : (frame -> (Logic.term -> Logic.term) -> unit) list;
}

type axiom_state = {
  mutable axiomatizing : Logic.symbol list;
  axiom_clauses : unit Tables.Axiom_clause_table.t;
  mutable open_axioms : open_axiom list;
  axioms_of : open_axiom Tables.Symbol_table.t;
}

type definition_entry = { entry_frame : frame; entry_measures : Logic.term list }

type termination_state = {
  mutable terminates : bool;
  measures : Mir.formula list;
  mutable definition_entry : definition_entry option;
}

type validity_state = {
  type_clauses : (source * Mir.type_clauses option Lazy.t) option Tables.Path_table.t;
  valid_values : (Types.ty * Logic.term) list Tables.Term_table.t;
}

type callback_state = { mutable named : (Logic.term * (Types.function_type * known_function)) list }

type context = {
  environment : environment;
  mutable parameter_names : (Logic.symbol * string) list;
  local_names : string Tables.Local_table.t;
  local_origins : Core.origin Tables.Local_table.t;
  mutable returns : function_exit list;
  query : Query.t;
  axioms : axiom_state;
  termination : termination_state;
  validity : validity_state;
  callbacks : callback_state;
  mutable indexes : (Core.id * noted_place) list;
  lending : lending_state;
  mutable laws_assumed : (Types.trait_reference * Types.ty) list;
  cost : cost_state;
  mutable logs : (Logic.term * bool) list;
  mutable powers : (Logic.term * Logic.term) list;
  lambda_definitions : Logic.term Tables.Symbol_table.t;
  models : (Logic.term -> Logic.term) option Tables.Model_table.t;
  mutable equalities : Logic.term list;
  mutable entry : Logic.symbol list;
  mutable holes : (Resolve.Names.key * Obligation.location) list;
  mutable unfinished : Logic.term list;
  mutable skipped_conditions : Types.condition list;
  run_body : frame -> lambdas:Mir.body array -> Mir.body -> unit;
  read_formula : frame -> Mir.formula -> arguments:Logic.term list -> frame * Logic.term;
}
