val assume_typed : State.frame -> Logic.term -> unit
val map_each_value : State.frame -> Logic.term -> (State.frame -> Logic.term -> unit) -> unit

type application = {
  symbol : Logic.symbol;
  sorts : Logic.sort list;
  term : Logic.term;
  is_limited : bool;
}

val declare_function :
  Query.t ->
  path:Path.t ->
  type_arguments:Types.argument list ->
  sorts:Logic.sort list ->
  result_type:Types.ty ->
  Logic.symbol

val run_limiting : Query.t -> Logic.symbol list -> (unit -> 'a) -> 'a

val apply :
  State.frame ->
  path:Path.t ->
  type_arguments:Types.argument list ->
  sorts:Logic.sort list ->
  result_type:Types.ty ->
  arguments:Logic.term list ->
  is_on_bound_values:bool ->
  application

val state :
  State.frame ->
  application ->
  State.contract ->
  substitution_of:(State.clauses -> Types.substitution) ->
  result_type:Types.ty ->
  group_member:Path.t option ->
  is_on_bound_values:bool ->
  unit

val states : Query.t -> application -> State.clauses -> Mir.formula -> bool
val assume_hypotheses : State.frame -> application -> arguments:Logic.term list -> unit
val find_definition : application -> Logic.term -> Logic.term option
