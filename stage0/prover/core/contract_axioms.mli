val is_typing_fact : State.frame -> Logic.term -> bool
val assume_typed : State.frame -> Logic.term -> unit
val assume_ground_facts : State.frame -> Logic.term -> (unit -> Logic.term list) -> unit

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
val assume_can_call : State.frame -> application -> arguments:Logic.term list -> unit
val find_definition : application -> Logic.term -> Logic.term option
