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

type site = { code : Diagnostic.Code.prover; span : Source.Definition_span.t; shows : string }
type citation = { cited : Resolve.Names.key; clause : Source.Definition_span.t }

type state = {
  site : site;
  is_proven : bool;
  trusts_compiled_code : bool;
  failure : Source.Definition_span.t Diagnostic.diagnostic option;
  citation : citation option;
}

type posed

val pose :
  Lookups.t ->
  runs:(Obligation.evaluation * Obligation.run) list ->
  Resolve.Names.key ->
  proof ->
  posed

val list_requests : posed -> (Solver.request * Logic.query) list
val list_refutation_requests : posed -> Solver.answer list -> (Solver.request * Logic.query) list

val list_states :
  Lookups.t -> posed -> answers:Solver.answer list -> refutations:Solver.answer list -> state list

val note_cited_clause :
  Source.span Diagnostic.diagnostic -> Source.span -> Source.span Diagnostic.diagnostic

val name_cited_clause :
  Source.span Diagnostic.diagnostic -> path:string -> line:int -> Source.span Diagnostic.diagnostic

module For_testing : sig
  val list_queries : posed -> (site * string) list
end
