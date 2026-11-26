val make_state : unit -> State.axiom_state
val assume_typed : State.context -> State.frame -> Logic.term -> unit

val map_each_value :
  State.context -> State.frame -> Logic.term -> (State.frame -> Logic.term -> unit) -> unit

type application = {
  symbol : Logic.symbol;
  sorts : Logic.sort list;
  term : Logic.term;
  is_limited : bool;
}

val declare_function :
  State.context ->
  path:Path.t ->
  type_arguments:Types.argument list ->
  sorts:Logic.sort list ->
  result_type:Types.ty ->
  Logic.symbol

val apply :
  State.context ->
  State.frame ->
  path:Path.t ->
  type_arguments:Types.argument list ->
  sorts:Logic.sort list ->
  result_type:Types.ty ->
  arguments:Logic.term list ->
  is_on_bound_values:bool ->
  application

val state :
  State.context ->
  State.frame ->
  application ->
  State.contract ->
  substitution_of:(State.clauses -> Types.substitution) ->
  result_type:Types.ty ->
  group_member:Path.t option ->
  is_on_bound_values:bool ->
  unit

val states : State.context -> application -> State.clauses -> Mir.formula -> bool

val assume_hypotheses :
  State.context -> State.frame -> application -> arguments:Logic.term list -> unit

val find_definition : application -> Logic.term -> Logic.term option
