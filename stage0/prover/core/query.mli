type t

val create : unit -> t
val make_variable : ?numbers:int list -> string -> 'a Logic.Symbol.t
val declare : t -> Logic.declaration -> unit
val has_datatype : t -> Types.ty -> bool

val declare_datatype :
  t -> Types.ty -> (unit -> (Logic.symbol * (Logic.symbol * Logic.sort) list) list) -> unit

val find_argument_sorts : t -> Logic.symbol -> Logic.sort list option
val is_declared : t -> Logic.symbol -> bool
val list_defined_symbols : t -> Logic.symbol list
val count_declarations : t -> int
val list_declarations_since : t -> count:int -> Logic.declaration list
val add_fact : t -> Logic.term -> unit
val count_facts : t -> int
val list_facts_since : t -> count:int -> Logic.term list
val holds : t -> under:Logic.term -> Logic.term -> bool
val run_dropping_facts : t -> drop:(Logic.term -> bool) -> (unit -> 'a) -> 'a
val run_once : t -> Tables.stated -> (unit -> unit) -> unit
val run_without_facts : t -> (unit -> 'a) -> 'a
val run_in_scope : t -> Logic.symbol list -> (unit -> 'a) -> 'a * Logic.term list
val add_scoped_fact : t -> bound:Logic.symbol list -> Logic.term -> unit
val list_scope_facts : t -> Logic.symbol list -> Logic.term list
val add_quantifier_symbol : t -> Logic.symbol -> unit
val attach_quantifier_facts : t -> Logic.term -> Logic.term list -> unit
val note_written_quantifier : t -> Logic.term -> unit
val add_quantifier_facts : t -> binders:Logic.symbol list -> Logic.term -> Logic.term
val take_fresh_number : t -> int
val count_fresh : t -> int
val make_fresh_name : t -> string -> 'a Logic.Symbol.t
val make_ordered_fresh_name : t -> string -> 'a Logic.Symbol.t
val find_fresh_order : t -> Logic.symbol -> int option
val mentions_fresh_after : t -> int -> Logic.term -> bool

val make_obligation :
  t ->
  condition:Logic.term ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  Obligation.t

val add_obligation : t -> Obligation.t -> unit
val list_obligations : t -> Obligation.t list
