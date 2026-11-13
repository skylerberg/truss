val core_of : Definitions.context -> Path.t -> Core.parameter list * Core.block
(** The parameters of a function or a method, and its body as Core. *)

val bind_core : Lowering.state -> Core.local -> Lir.place -> unit

val expression_into :
  ?parameters:Core.parameter list -> Lowering.state -> Core.expression -> Lir.place -> unit
(** Evaluates a core expression that runs on its own, such as a default or a constant's value, and
    writes its value to the place, which holds nothing. [parameters] are the locals of the code
    around that it reads, which are bound already. *)

val fill_defaults : Lowering.state -> Lir.local -> Core.parameter list -> unit
(** Fills in each parameter whose argument the caller omitted, as the bits of the mask say. *)

val lower_code : Lowering.state -> Path.t -> unit
(** Lowers the MIR of the code at the path in the current frame, whose parameters are bound. Leaves
    a block that nothing reaches. *)
