val is_available : State.frame -> Types.capability -> bool
val find_ruled_out : State.frame -> State.ruled_out option
val set_available : State.frame -> Types.capability_set -> State.frame

val oblige :
  ?cited:Resolve.Names.key * Core.origin ->
  ?fixes:Catalog.Prover.fix list ->
  ?can_be_required:bool ->
  ?is_proven_by_evaluation:bool ->
  ?holds_when:Types.condition ->
  State.frame ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  unit

val make_closed_obligation :
  State.frame ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  Obligation.t option

val make_obligation :
  State.frame -> Obligation.location -> Catalog.Prover.obligation -> Logic.term -> Obligation.t
