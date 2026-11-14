(** A computation and a call of the MIR, as the prover's rules take them. *)

type site = { id : Core.id; origin : Core.origin; type_ : Types.ty }
(** The computation: its node's id, which keys what the prover records about it, its origin, and its
    type before the frame's substitution. *)

type callee = unit Core.target
(** A call's callee. A call through a function value carries nothing: the caller gives the value. *)

type t = { callee : callee; lends : Types.mode option; uses : Types.capability_set }
(** A call: its callee, the mode of the part it lends, if it lends one, and the capabilities it
    uses. *)

val unit_callee : 'a Core.target -> callee
val of_mir : Mir.call -> lends:Types.mode option -> t

type shape =
  | Named_function of { id : Core.id; origin : Core.origin; path : Path.t }
      (** A named function passed as a value. *)
  | Forwarded of Core.local  (** A local passed on, such as a callback parameter. *)
  | Other
