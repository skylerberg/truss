val core_of : Definitions.context -> Path.t -> Core.parameter list * Core.block
(** The parameters of a function or a method, and its body as Core. *)

val expression_into :
  ?arguments:(Core.parameter * Lir.place) list ->
  Lowering.state ->
  Core.expression ->
  Lir.place ->
  unit
(** Evaluates a core expression that runs on its own, such as a default or a constant's value, and
    writes its value to the place, which holds nothing. [arguments] are the parameters of the code
    around that it reads, with their places. *)

val fill_defaults :
  Lowering.state -> Lir.local -> (Core.parameter * Lir.place) list -> Lir.place list
(** Fills in each parameter whose argument the caller omitted, as the bits of the mask say, and
    gives each parameter's place: a parameter with a default that the function owns has a place of
    its own. *)

val lower_code : Lowering.state -> Path.t -> parameters:Lir.place list -> unit
(** Lowers the MIR of the code at the path in the current frame, with the places of its parameters,
    in order. Leaves a block that nothing reaches. *)
