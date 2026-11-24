type source = { key : Resolve.Names.key; definition : Path.t; name : string }

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
  is_ghost : bool;
  bound : Logic.symbol list;
  binders : (Logic.symbol * Logic.sort * Logic.term) list;
  substitution : Types.substitution;
  self_type : Types.ty option;
  yielded : Logic.term option;
  yielded_so_far : Logic.term option;
  spent : (Costs.counter * Logic.term) list;
  aliases : (Logic.term * Mir.place) list Locals.t;
  lends : (Logic.term * (frame -> Logic.term -> frame)) list Locals.t;
}

type changed_part = { root : Locals.local; fields : string list }
type place_value = One of Logic.term | Run of Logic.term * Logic.term
type noted_place = { origin : Core.origin; value : place_value }

type passed_place = {
  read : frame -> Logic.term;
  write : frame -> Logic.term -> frame;
  note_changed_in_place : unit -> unit;
}

type passed = {
  position : int;
  mode : Language.Mode.t;
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
      mode : Language.Mode.t;
      site : Invocation.site;
      lambda : lambda_code;
    }

type stated = Tables.stated =
  | In_range of Logic.symbol
  | Field_in_range of Logic.term
  | Value_of of Logic.symbol
  | Contract_of of Logic.symbol
  | Limited_link of Logic.symbol
  | Exclusive of Logic.symbol
  | Array_length of Logic.symbol
  | Ranked_model of Logic.symbol
  | Ranked_elements of Types.ty
  | Range_elements of Types.ty
  | Non_negative_rank of Types.ty
  | Method_cost_bound of Logic.symbol

type call_amount = {
  call : Obligation.piece;
  callee : Path.t;
  states_cost : bool;
  counter : Costs.counter;
  amount : Logic.term;
}

type lending = {
  part_type : Types.ty;
  part_postconditions : Mir.formula list;
  return_postconditions : Mir.formula list;
}

type context = {
  lookups : Lookups.t;
  current : Path.t;
  node : Path.t;
  mutable terminates : bool;
  mutable callbacks : (Core.local * string * Mir.callback) list;
  measures : Mir.formula list;
  mutable declarations : Logic.declaration list;
  declared : Logic.sort list Tables.Symbol_table.t;
  definitions : unit Tables.Symbol_table.t;
  datatypes : unit Tables.Type_table.t;
  visible_types : (Types.type_interface * Types.substitution) option Tables.Type_table.t;
  type_clauses : (source * Mir.type_clauses option Lazy.t) option Tables.Path_table.t;
  callees : known_callee Tables.Path_table.t;
  stated : unit Tables.Stated_table.t;
  mutable facts : Logic.term list;
  mutable obligations : Obligation.t list;
  mutable fresh : int;
  mutable values : (Logic.symbol * string) list;
  local_names : string Tables.Local_table.t;
  local_origins : Core.origin Tables.Local_table.t;
  mutable returns : (frame * Logic.term option) list;
  mutable enclosing_provides : Mir.provided list list;
  mutable lent_back : (Types.ty * Logic.term * Logic.term) list;
  mutable instantiating : Path.t list;
  mutable axiomatizing : Logic.symbol list;
  axiom_clauses : unit Tables.Axiom_clause_table.t;
  mutable open_axioms : open_axiom list;
  axioms_of : open_axiom Tables.Symbol_table.t;
  disjoint : (Core.id list * Core.id list) list;
  mutable indexes : (Core.id * noted_place) list;
  mutable lending : lending option;
  home : Resolve.Names.key;
  mutable laws_assumed : (Types.trait_reference * Types.ty) list;
  mutable counters : Costs.counter list;
  mutable bounded_counters : Costs.counter list;
  mutable recursive_costs_assumed : int;
  fresh_order : int Tables.Symbol_table.t;
  mutable logs : (Logic.term * bool) list;
  mutable powers : (Logic.term * Logic.term) list;
  mutable lambda_costs : ((Logic.term * Language.Metric.t) * (Logic.term * Obligation.t list)) list;
  mutable lambda_captures : (Logic.term * Core.local list) list;
  mutable call_amounts : call_amount list;
  lambda_definitions : Logic.term Tables.Symbol_table.t;
  mutable potentials : Logic.term list;
  models : (Logic.term -> Logic.term) option Tables.Model_table.t;
  holds_potential : bool Tables.Type_table.t;
  buffers : (Types.ty * (Logic.term -> Logic.term)) option Tables.Type_table.t;
  mutable equalities : Logic.term list;
  mutable path_notes : (string * Logic.term) list;
  mutable entry : Logic.symbol list;
  inherits_precondition : bool;
  mutable holes : (Resolve.Names.key * Obligation.location) list;
  mutable unfinished : Logic.term list;
  mutable call_targets : (Logic.term * Core.local) list;
  mutable reading_callback : bool;
  ranking : bool;
  mutable scopes : (Logic.symbol * Logic.term list ref) list;
  quantifier_facts : Logic.term list Tables.Term_table.t;
  written_quantifiers : unit Tables.Term_table.t;
  mutable quantifier_symbols : Logic.symbol list;
  mutable validating : Types.ty list;
  condition : Types.condition;
  bounds : Interface.Impls.bounds;
  keeps_termination : bool;
  keeps_failures : bool;
  mutable panics : bool;
  mutable can_declare_panic : bool;
  panic_condition : Obligation.message option;
  mutable obligation_condition : Types.condition;
  mutable skipped_conditions : Types.condition list;
  run_body : frame -> lambdas:Mir.body array -> Mir.body -> unit;
  read_formula : frame -> Mir.formula -> arguments:Logic.term list -> frame * Logic.term;
}

and open_axiom = {
  parameters : Logic.symbol list;
  mutable hypotheses : Logic.term list;
  mutable at_calls : (frame -> (Logic.term -> Logic.term) -> unit) list;
}
