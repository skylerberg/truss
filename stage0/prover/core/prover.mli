module Obligation = Obligation
module Lookups = Lookups

type proof =
  | Obligations of Obligation.outcome
  | Unsupported of {
      location : Obligation.location;
      construct : Catalog.Prover.construct;
      foreign : string option;
    }
  | Not_proven_here

val prove : Lookups.t -> Resolve.Names.key -> proof
val list_evaluations : proof -> Obligation.evaluation list

val resolve_location :
  Resolve.Names.lookups -> Resolve.Names.key -> Obligation.location -> Source.Definition_span.t

type site = { code : Diagnostic.Code.prover; shows : Catalog.Prover.t }

type state = {
  site : site;
  is_proven : bool;
  trusts_compiled_code : bool;
  failure : Catalog.Prover.t option;
}

type posed

val pose : runs:(Obligation.evaluation * Obligation.run) list -> proof -> posed
val list_requests : posed -> (Solver.request * Logic.query) list
val list_refutation_requests : posed -> Solver.answer list -> (Solver.request * Logic.query) list

val list_states :
  posed -> answers:Solver.answer list -> refutations:Solver.answer list -> state list

module For_testing : sig
  val list_queries : posed -> (site * string) list
end
