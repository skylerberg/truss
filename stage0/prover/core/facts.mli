type unsupported = {
  location : Obligation.location;
  construct : Catalog.Prover.construct;
  foreign_definition : Path.t option;
}

exception Unsupported of unsupported

val raise_unsupported : Obligation.location -> Catalog.Prover.construct -> 'a
val run_in_source : State.frame -> (unit -> 'a) -> 'a
val raise_bug : ('a, unit, string, 'b) format4 -> 'a

val list_method_type_arguments :
  Types.trait_reference -> self_type:Types.ty -> Types.argument list -> Types.argument list

val read_parameter_name : Mir.parameter -> string
val list_clauses : Mir.requirement list -> Mir.formula list
val declare_value_symbol : State.frame -> Logic.symbol -> Logic.sort -> Logic.term
val declare_fresh : State.frame -> string -> Logic.sort -> Logic.term
val close_over_binders : State.frame -> Logic.term -> Logic.term option
val add_axiom : State.frame -> Logic.term -> unit
val define : State.frame -> Logic.term -> Logic.term -> unit
val assume : State.frame -> Logic.term -> unit
val remove_panic : Types.capability_set -> Types.capability_set
val locate : State.frame -> Core.origin -> Obligation.location
val locate_source : State.environment -> State.source -> Core.origin -> Obligation.location
val quote : State.source -> Core.origin -> Catalog.Prover.quoted
val is_home : State.frame -> bool
val is_in_home_package : State.frame -> bool
val bind : State.frame -> Locals.key -> Types.ty -> Logic.term -> State.frame
val restrict : State.frame -> Logic.term -> State.frame
val restrict_unless_proven : State.frame -> Logic.term -> State.frame
val suppose : State.frame -> string -> Logic.term * State.frame
