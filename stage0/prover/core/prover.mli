module State = State
module Facts = Facts
module Contracts = Contracts
module Lookups = Lookups

type proof = Obligations of State.outcome | Unsupported of Syntax.span * string | Not_proven_here

val proof : Lookups.t -> Resolve.Names.key -> proof

type run_result = Ran of bool | Timed_out | Not_run
type evaluator = State.evaluation -> run_result

type 'span state = {
  code : Diagnostic.Code.prover;
  span : 'span;
  shows : string;
  failure : 'span Diagnostic.diagnostic option;
  trusts_compiled_code : bool;
}

type verdict = (Syntax.span state * (Resolve.Names.key * Syntax.span) option) list

val verdicts :
  ?evaluator:evaluator ->
  Lookups.t ->
  Solver.t ->
  (Resolve.Names.key * proof) list ->
  (Resolve.Names.key * verdict) list

val states :
  Lookups.t -> verdict:(Resolve.Names.key -> verdict) -> Path.file -> Diagnostic.span state list

val diagnostics :
  Lookups.t -> verdict:(Resolve.Names.key -> verdict) -> Path.file -> Diagnostic.t list
