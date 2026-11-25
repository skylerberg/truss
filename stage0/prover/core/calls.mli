val add_restated_clauses :
  State.context ->
  self_type:Types.ty ->
  bind:(Types.trait_reference -> Path.t -> Types.substitution) ->
  Path.t ->
  string ->
  Path.receiver ->
  State.contract ->
  State.contract

type called =
  | Named of Path.t
  | Through of {
      name : string option;
      function_type : Types.function_type;
      term : Logic.term;
      enclosing : State.frame;
    }

val call_contract :
  ?passed_for:Catalog.Prover.through ->
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  called ->
  State.contract ->
  State.passed list ->
  recursive_callee:Path.t option ->
  lent_final:(Logic.term -> Logic.term) option ->
  substitution_of:(State.clauses -> Types.substitution) ->
  type_arguments:Types.argument list ->
  State.frame * Logic.term

val make_callback_cost :
  State.context -> State.frame -> Language.Metric.t -> Types.ty -> Logic.term -> Logic.term

val apply_call :
  ?leave_lent:(Logic.term -> Logic.term) ->
  ?passed_for:string ->
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  through:(Types.ty * Logic.term * Invocation.shape) option ->
  State.passed list ->
  (State.frame * Logic.term) option
