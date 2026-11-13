(** A computation and a call as the prover reads them, whichever form they are read from: a
    specification's core expressions, or code's MIR. One reading of each then serves both forms. *)

type site = { id : Core.id; origin : Core.origin; type_ : Types.ty }
(** The computation: its node's id, which keys what the prover records about it, its origin, and its
    type before the frame's substitution. *)

val site_of : Core.expression -> site

(** The callee of a call. *)
type callee =
  | Function of { path : Path.t; type_arguments : Types.argument list }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;
      evidence : Core.evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
  | Indirect  (** A call through a function value, whose value the caller gives. *)

type t = { callee : callee; lends : Types.mode option; uses : Types.capability_set }
(** A call: its callee, the mode of the part it lends, if it lends one, and the capabilities it
    uses. *)

val of_core : Core.call -> t
val of_core_callee : Core.callee -> callee
val of_mir : Mir.call -> lends:Types.mode option -> t
val of_mir_callee : Mir.callee -> callee

val core_callee : callee -> Core.callee option
(** The callee as the call graph names it, for a direct call. *)

(** What an argument is, for the checks of a callback it passes and the text of a fix that names it.
*)
type shape =
  | Named_function of { id : Core.id; origin : Core.origin; path : Path.t }
      (** A named function passed as a value. *)
  | Forwarded of Core.local  (** A local passed on, such as a callback parameter. *)
  | Other
