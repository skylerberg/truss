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

type state = {
  site : Catalog.Prover.t;
  is_proven : bool;
  trusts_compiled_code : bool;
  failure : Catalog.Prover.t option;
}

type posed

val pose : runs:(Obligation.evaluation * Obligation.run) list -> proof -> posed
val list_requests : posed -> Solver.request list
val list_refutation_requests : posed -> Solver.answer list -> Solver.request list

val list_states :
  posed -> answers:Solver.answer list -> refutations:Solver.answer list -> state list

module For_testing : sig
  val list_queries : posed -> (Catalog.Prover.t * string) list
end
