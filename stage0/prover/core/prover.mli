module State = State
module Facts = Facts
module Contracts = Contracts
module Lookups = Lookups

type proof =
  | Obligations of State.outcome
  | Unsupported of State.location * string
  | Not_proven_here

val proof : Lookups.t -> Resolve.Names.key -> proof

val resolve_location :
  Resolve.Names.lookups -> Resolve.Names.key -> State.location -> Source.Definition_span.t

type 'span state = {
  code : Diagnostic.Code.prover;
  span : 'span;
  shows : string;
  failure : 'span Diagnostic.diagnostic option;
  trusts_compiled_code : bool;
}

type verdicts

val decide :
  runs:(State.template_check * (bool list, string) result) list ->
  Lookups.t ->
  Solver.t ->
  (Resolve.Names.key * proof) list ->
  verdicts

val list_states : verdicts -> Path.file -> Source.span state list
val list_diagnostics : verdicts -> Path.file -> Diagnostic.t list
