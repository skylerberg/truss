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

val fill_defaults :
  Lowering.state -> Lowered.place -> Mir.body -> Lowered.place list -> Lowered.place list

val lower_code :
  Lowering.state ->
  Path.t ->
  parameters:Lowered.place list ->
  ?lending:Lowering.lending ->
  unit ->
  unit
(** Lowers the body of a function or a method. [lending] is a lending method's trailing parameters.
*)
