module Obligation = Obligation
module Lookups = Lookups

type proof =
  | Obligations of Obligation.outcome
  | Unsupported of Obligation.location * string
  | Not_proven_here

val prove : Lookups.t -> Resolve.Names.key -> proof

val resolve_location :
  Resolve.Names.lookups -> Resolve.Names.key -> Obligation.location -> Source.Definition_span.t

type 'span state = {
  code : Diagnostic.Code.prover;
  span : 'span;
  shows : string;
  failure : 'span Diagnostic.diagnostic option;
  trusts_compiled_code : bool;
}

type verdicts

val decide :
  runs:(Obligation.template_check * (bool list, string) result) list ->
  Lookups.t ->
  Solver.t ->
  (Resolve.Names.key * proof) list ->
  verdicts

val list_states : verdicts -> Path.file -> Source.span state list
val list_diagnostics : verdicts -> Path.file -> Diagnostic.t list

module For_testing : sig
  type query = { code : Diagnostic.Code.prover; span : Source.span; shows : string; input : string }

  val list_queries : Lookups.t -> (Resolve.Names.key * proof) list -> Path.file -> query list
end
