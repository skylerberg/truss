(* The statements that code generation writes and the C builder prints at
   once: typed places, operands, calls, and terminators.

   Locals are mutable slots, not SSA. Every choice about how a value is
   passed is already explicit: a parameter that arrives as a pointer has a
   [Pointer] type, an argument passed by address is an [Address] operand,
   and a result too large to return comes back through a pointer parameter.
   The builder only prints. *)

include module type of struct
  include Lowered_types
end

(* A local as a place, with no projections. *)
val local_place : local -> place

(* The type of a projection of a place of the given type, or [None] where it
   has zero size and so is erased. [environment] gives the fields of a
   nested function's environment. *)
val projection_type :
  Memory_layout.env -> environment:(int -> (string * ty) list) -> ty -> projection -> ty option

(* The blocks a terminator may go to, in order. *)
val successors : terminator -> block list

(* Whether a local of the type takes no room, so that no code names it. *)
val erased : Memory_layout.env -> ty -> bool
