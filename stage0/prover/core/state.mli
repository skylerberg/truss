type source = { key : Resolve.Names.key; definition : Path.t }

type clauses = {
  callee : source;
  parameters : Mir.parameter list;
  conditional_uses : Mir.conditional_use list;
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

type ruled_out = { capability : Types.capability; condition : Catalog.Prover.quoted list }
type kept = Every_capability | Capabilities of Types.capability list
type obligation_policy = { keeps : kept; ruled_out : ruled_out option }

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
  terminates : bool;
  measures : Mir.formula list;
  termination : Mir.Size_change.verdict Lazy.t;
  blocked_holders : string list;
  proven_laws : (Types.trait_reference * Types.ty) option;
  policy : obligation_policy;
  memos : Private_state.t;
  read_formula : frame -> Mir.formula -> arguments:Logic.term list -> frame * Logic.term;
  run_body : frame -> lambdas:Mir.body array -> Mir.body -> body_exits;
}

and frame = {
  environment : environment;
  query : Query.t;
  source : source;
  entry : (Logic.symbol * string option) list;
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
  conditional_counters : Costs.counter list;
  aliases : (Logic.term * Mir.place) list Locals.t;
  lends : (Logic.term * (frame -> Logic.term -> frame)) list Locals.t;
  callbacks : (Logic.term * (Types.function_type * known_function)) list;
  requires_being_read : Core.origin option;
  callees_whose_requires_are_read : Path.t list;
  provided : Mir.provided list list;
  available : Types.capability_set;
  declared_uses : Types.capability_set option;
  instantiating : (Path.t * int) list;
  obligation_condition : Types.condition;
  is_reading_callback : bool;
  validating : Types.ty list;
  terminates : bool;
  lent_part_type : Types.ty option;
  definition_entry : definition_entry option;
}

and definition_entry = { entry_measures : Logic.term list; entry_ranks : ranked_value list }
and ranked_value = { position : int; type_ : Types.ty; value : Logic.term }
and function_exit = { frame : frame; returned : Logic.term option; return_origin : Core.origin }
and lent_part = { lent_frame : frame; lent_origin : Core.origin }
and body_exits = { returns : function_exit list; lends : lent_part list }

type changed_part = {
  root : Locals.local;
  root_description : Catalog.Prover.value;
  declared_root_type : Types.ty;
  fields : string list;
}

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
