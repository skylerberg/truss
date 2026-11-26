val make_policy :
  keeps_termination:bool ->
  keeps_failures:bool ->
  panics:bool ->
  can_declare_panic:bool ->
  panic_condition:Catalog.Prover.quoted list option ->
  State.obligation_policy

val may_panic : State.context -> bool
val find_ruled_out_panic : State.context -> Catalog.Prover.quoted list option
val run_with_panics : State.context -> panics:bool -> (unit -> 'a) -> 'a
val with_condition : State.context -> Types.condition -> (unit -> 'a) -> 'a

val oblige :
  ?cited:Resolve.Names.key * Core.origin ->
  ?fixes:Catalog.Prover.fix list ->
  ?can_be_required:bool ->
  ?is_proven_by_evaluation:bool ->
  ?holds_when:Types.condition ->
  State.context ->
  State.frame ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  unit

val make_closed_obligation :
  State.context ->
  State.frame ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  Obligation.t option

val make_obligation :
  State.context ->
  State.frame ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  Obligation.t
