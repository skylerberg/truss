val make_variable : ?numbers:int list -> string -> 'a Logic.Symbol.t

type unsupported = {
  location : Obligation.location;
  construct : Catalog.Prover.construct;
  foreign_definition : Path.t option;
}

exception Unsupported of unsupported

val raise_unsupported : Obligation.location -> Catalog.Prover.construct -> 'a
val run_in_source : State.context -> State.source -> (unit -> 'a) -> 'a
val raise_bug : ('a, unit, string, 'b) format4 -> 'a

val list_method_type_arguments :
  Types.trait_reference -> self_type:Types.ty -> Types.argument list -> Types.argument list

val read_parameter_name : Mir.parameter -> string
val list_clauses : Mir.requirement list -> Mir.formula list
val declare : State.context -> Logic.declaration -> unit
val find_argument_sorts : State.context -> Logic.symbol -> Logic.sort list option
val add_fact : State.context -> Logic.term -> unit
val declare_value_symbol : State.context -> State.frame -> Logic.symbol -> Logic.sort -> Logic.term
val make_fresh_name : State.context -> string -> 'a Logic.Symbol.t
val declare_fresh : State.context -> State.frame -> string -> Logic.sort -> Logic.term
val mentions_fresh_after : State.context -> int -> Logic.term -> bool
val close_over_binders : State.frame -> Logic.term -> Logic.term option
val add_frame_fact : State.context -> State.frame -> Logic.term -> unit
val assume : State.context -> State.frame -> Logic.term -> unit
val remove_panic_condition : Types.capability_set -> Types.capability_set
val locate : State.context -> State.source -> Core.origin -> Obligation.location
val add_hole : State.context -> Resolve.Names.key * Obligation.location -> unit
val quote : State.source -> Core.origin -> Catalog.Prover.quoted
val describe_local : State.context -> State.frame -> Locals.local -> Catalog.Prover.value
val is_home : State.context -> State.source -> bool
val is_in_home_package : State.context -> State.source -> bool
val run_once : State.context -> State.stated -> (unit -> unit) -> unit
val bind : State.frame -> Locals.key -> Types.ty -> Logic.term -> State.frame
val restrict : State.frame -> Logic.term -> State.frame
