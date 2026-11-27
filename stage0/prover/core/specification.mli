type clause = Catalog.Prover.quoted * Logic.term

type t = {
  list_requires : Logic.term list -> clause list;
  list_ensures :
    entries:Logic.term list -> exits:Logic.term list -> result:Logic.term -> clause list;
  has_ensures : bool;
}

val oblige_requires :
  State.frame ->
  Obligation.location ->
  t ->
  Logic.term list ->
  describe:(Catalog.Prover.quoted -> Catalog.Prover.obligation) ->
  Logic.term

val assume_ensures :
  State.frame -> t -> entries:Logic.term list -> exits:Logic.term list -> result:Logic.term -> unit

val refine :
  State.frame ->
  Obligation.location ->
  by:((State.frame -> t) * (Catalog.Prover.quoted -> Catalog.Prover.obligation)) option ->
  t ->
  Logic.term list ->
  havoc:(unit -> Logic.term list * Logic.term) ->
  describe_ensures:(Catalog.Prover.quoted -> Catalog.Prover.obligation) ->
  unit
