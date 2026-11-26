type t

val create : unit -> t
val make_variable : ?numbers:int list -> string -> 'a Logic.Symbol.t
val declare : t -> Logic.declaration -> unit
val find_argument_sorts : t -> Logic.symbol -> Logic.sort list option
val list_defined_symbols : t -> Logic.symbol list
val add_fact : t -> Logic.term -> unit
val define : t -> Logic.term -> Logic.term -> unit

type mark

val mark : t -> mark
val list_facts_since : t -> mark -> Logic.term list
val list_declarations_since : t -> mark -> Logic.declaration list
val is_made_between : t -> mark -> mark -> Logic.symbol -> bool option
val mentions_fresh_since : t -> mark -> Logic.term -> bool
val holds : t -> under:Logic.term -> Logic.term -> bool
val run_dropping_facts : t -> drop:(Logic.term -> bool) -> (unit -> 'a) -> 'a
val run_once : t -> Tables.stated -> (unit -> unit) -> unit
val run_without_facts : t -> (unit -> 'a) -> 'a
val run_in_scope : t -> Logic.symbol list -> (unit -> 'a) -> 'a * Logic.term list
val add_scoped_fact : t -> bound:Logic.symbol list -> Logic.term -> unit
val list_scope_facts : t -> Logic.symbol list -> Logic.term list
val run_under_binder : t -> Logic.symbol -> (unit -> 'a) -> 'a * (Logic.term -> Logic.term)
val note_written_quantifier : t -> Logic.term -> unit
val add_quantifier_facts : t -> binders:Logic.symbol list -> Logic.term -> Logic.term
val take_fresh_number : t -> int
val make_fresh_name : t -> string -> 'a Logic.Symbol.t
val make_ordered_fresh_name : t -> string -> 'a Logic.Symbol.t

val make_obligation :
  t ->
  find_signature:(Logic.symbol -> (Logic.sort list * Logic.sort) option) ->
  list_axioms:(Logic.symbol -> Logic.term list) ->
  list_constructors:(Types.ty -> (Logic.symbol * (Logic.symbol * Logic.sort) list) list option) ->
  condition:Logic.term ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  Obligation.t

val add_obligation : t -> Obligation.t -> unit
val note_withheld : t -> Logic.symbol -> Path.t -> unit
val list_obligations : t -> Obligation.t list
