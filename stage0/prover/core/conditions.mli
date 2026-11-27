type decision = Always | In_run of Types.condition | Elsewhere

val implies : Lookups.t -> current:Path.t -> Types.condition -> Types.condition -> bool

val may_use_for_every_value :
  Lookups.t ->
  current:Path.t ->
  condition:Types.condition ->
  Types.capability ->
  Types.capability_set ->
  bool

val decide_available :
  Lookups.t ->
  current:Path.t ->
  condition:Types.condition ->
  Types.capability_set ->
  Types.capability_set

val list_undecided : Query.t -> Types.condition list

val decide :
  State.environment -> Query.t -> substitution:Types.substitution -> Types.condition -> decision

val holds_here :
  State.environment -> Query.t -> ?substitution:Types.substitution -> Types.condition -> bool

val find_obligation_condition : decision -> Types.condition option

val keep_holding :
  State.environment -> Query.t -> substitution:Types.substitution -> State.clauses -> State.clauses
