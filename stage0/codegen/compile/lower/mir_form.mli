val mir_of : Definitions.context -> Path.t -> Mir.t
(** The MIR of a function or a method. *)

val parameter_of : Mir.body -> Mir.local -> Types.mode * string * Types.ty
(** A parameter's mode, name, and type, from its local. *)

val mir_into : ?arguments:Lowered.place list -> Lowering.state -> Mir.t -> Lowered.place -> unit
(** Lowers the MIR of one expression, with its parameters bound to [arguments], into a place. *)

val expression_into :
  ?arguments:(Core.parameter * Lowered.place) list ->
  Lowering.state ->
  Core.expression ->
  Lowered.place ->
  unit
(** Evaluates a core expression that runs on its own, such as a default or a constant's value, and
    writes its value to the place, which holds nothing. [arguments] are the parameters of the code
    around that it reads, with their places. *)

val fill_defaults :
  Lowering.state -> Lowered.place -> Mir.body -> Lowered.place list -> Lowered.place list
(** Fills in each parameter whose argument the caller omitted, as the bits of the mask say, and
    gives each parameter's place: a parameter with a default that the function owns has a place of
    its own. *)

val lower_code : Lowering.state -> Path.t -> parameters:Lowered.place list -> unit
(** Lowers the MIR of the code at the path in the current frame, with the places of its parameters,
    in order. Leaves a block that nothing reaches. *)

(* The field of a pulled method's cursor that holds its state: 0 before
   the method starts, 1 once it has returned, and [k + 1] after its [k]th
   [yield]. *)
val cursor_state : Lowering.cursor -> Lowered.place

(* Ends a call of a pulled method's [next], which gives [value] in [Some],
   or [None]. *)
val give_option : Lowering.state -> Lowered.operand option -> unit
