val mir_of : Definitions.context -> Path.t -> Mir.t
(** The MIR of a function or a method. *)

val parameter_defaults : Definitions.context -> Path.t -> (int * Mir.t) list
(** The MIR of each default of the parameters of the function or method at a path, by the
    parameter's position. *)

val parameter_of : Mir.body -> Mir.local -> Types.mode * string * Types.ty
(** A parameter's mode, name, and type, from its local. *)

val mir_into : ?arguments:Lowered.place list -> Lowering.state -> Mir.t -> Lowered.place -> unit
(** Lowers the MIR of one expression, with its parameters bound to [arguments], into a place. *)

val fill_defaults :
  Lowering.state ->
  Lowered.place ->
  Mir.body ->
  defaults:(int * Mir.t) list ->
  Lowered.place list ->
  Lowered.place list

val lower_code : Lowering.state -> Path.t -> parameters:Lowered.place list -> unit
