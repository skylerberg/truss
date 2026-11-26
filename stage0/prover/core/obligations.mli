val make_policy :
  keeps_termination:bool ->
  keeps_failures:bool ->
  panic_condition:Catalog.Prover.quoted list option ->
  State.obligation_policy

val find_ruled_out_panic : State.frame -> Catalog.Prover.quoted list option
val set_panics : State.frame -> panics:bool -> State.frame

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
