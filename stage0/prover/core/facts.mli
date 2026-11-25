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
val list_method_type_arguments : self_type:Types.ty -> Types.argument list -> Types.argument list
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

val add_requires :
  State.context -> State.frame -> Catalog.Prover.required list -> Catalog.Prover.fix list

val find_value_code : State.context -> Logic.term -> Catalog.Code.t option
val remove_panic_condition : Types.capability_set -> Types.capability_set
val find_counter_condition : State.context -> Costs.counter -> Types.condition

val oblige :
  ?cited:Resolve.Names.key * Core.origin ->
  ?fixes:Catalog.Prover.fix list ->
  ?can_be_required:bool ->
  ?holds_when:Types.condition ->
  State.context ->
  State.frame ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  unit

val reject_recursion_through_supplied_code :
  State.context -> State.frame -> Obligation.location -> Mir.statement -> unit

val find_recursive_callee :
  State.context -> State.frame -> Obligation.location -> 'operand Core.target -> Path.t option

val is_evaluated_constant : State.context -> Path.t -> Mir.t -> bool
val reject_constant_cycle : State.context -> State.frame -> Mir.t -> unit

type circular_proof

val list_circular_clauses : State.context -> State.frame -> type_:Types.ty -> circular_proof list
val list_circular_contracts : State.context -> State.frame -> circular_proof list
val reject_circular_proof : State.context -> State.frame -> circular_proof -> unit

val reject_uncompared_recursion :
  State.context -> State.frame -> Obligation.location -> Path.t option -> unit

val make_closed_obligation :
  State.context ->
  State.frame ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  Obligation.t option

val make_obligation :
  State.context ->
  State.frame ->
  Obligation.location ->
  Catalog.Prover.obligation ->
  Logic.term ->
  Obligation.t

val locate : State.context -> State.source -> Core.origin -> Obligation.location
val add_hole : State.context -> Resolve.Names.key * Obligation.location -> unit
val quote : State.source -> Core.origin -> Catalog.Prover.quoted
val is_home : State.context -> State.source -> bool
val is_in_home_package : State.context -> State.source -> bool
val find_bounds : Types.ty -> (Z.t * Z.t) option
val find_float_format : Types.ty -> (int * int) option
val make_constructor_symbol : Types.ty -> string option -> 'a Logic.Symbol.t
val make_selector_symbol : Types.ty -> string option -> string -> 'a Logic.Symbol.t
val is_standard_equal : Path.t -> bool

val find_visible_type :
  State.context -> Types.ty -> (Types.type_interface * Types.substitution) option

val find_constructors :
  State.context -> Types.ty -> (string option * (string * Types.ty) list) list option

val declare_sort : State.context -> Types.ty -> Logic.sort
val is_equality_identity : State.context -> ?seen:Types.ty list -> Types.ty -> bool
val make_in_range : Types.ty -> Logic.term -> Logic.term
val run_once : State.context -> State.stated -> (unit -> unit) -> unit
val arrive : State.context -> State.frame -> string -> Types.ty -> Logic.term

val read_or_arrive :
  State.context -> State.frame -> string -> Types.ty -> (State.frame -> Logic.term) -> Logic.term

val bind : State.frame -> Locals.key -> Types.ty -> Logic.term -> State.frame

val list_definition_bounds :
  Lookups.t -> current:Path.t -> condition:Types.condition -> Interface.Impls.bounds

val substitute_declared_type : State.context -> State.frame -> Types.ty -> Types.ty
val substitute_type : State.context -> State.frame -> Types.ty -> Types.ty

val find_impl :
  State.context -> Types.trait_reference -> Types.ty -> (Path.t * Types.substitution) option

val find_local_type : State.context -> State.frame -> Locals.key -> Types.ty option
val mentions_potential : Logic.term -> bool
val list_potentials : Logic.term -> Logic.term list
val take_potential_as_zero : Logic.term -> Logic.term
val restrict : State.frame -> Logic.term -> State.frame
val name_path_condition : State.context -> State.frame -> Logic.term -> Logic.term

val merge :
  State.context ->
  ?value_type:Types.ty ->
  condition:Logic.term ->
  (Logic.term * State.frame * Logic.term option) list ->
  State.frame * Logic.term option

val join :
  State.context ->
  ?value_type:Types.ty ->
  (State.frame * Logic.term option) list ->
  (State.frame * Logic.term option) option

val join_frames : State.context -> State.frame list -> State.frame option
