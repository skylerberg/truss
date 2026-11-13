(* The lowered IR: a small typed control-flow graph for each instance, which
   yield lowering transforms and the C emitter prints.

   Locals are mutable slots, not SSA. Every choice about how a value is
   passed is already explicit: a parameter that arrives as a pointer has a
   [Pointer] type, an argument passed by address is an [Address] operand,
   and a result too large to return comes back through a pointer parameter.
   The emitter only prints. *)

include module type of struct
  include Ir_types
end

val signature : function_ -> signature

(* A local as a place, with no projections. *)
val local_place : local -> place

(* The type of a projection of a place of the given type, or [None] where it
   has zero size and so is erased. [environment] gives the fields of a
   nested function's environment. *)
val projection_type :
  Memory_layout.env -> environment:(int -> (string * ty) list) -> ty -> projection -> ty option

(* The type of a place in a function, or [None] where it has zero size. *)
val place_type :
  Memory_layout.env -> environment:(int -> (string * ty) list) -> function_ -> place -> ty option

(* A statement or terminator with every place rewritten by [place], each
   after the places inside its indexes, and every block number by [block]. *)
val map_statement : place:(place -> place) -> block:(block -> block) -> statement -> statement
val map_terminator : place:(place -> place) -> block:(block -> block) -> terminator -> terminator

(* Visits every place and every operand of a statement or a terminator,
   each after the places and operands inside it. *)
type visitor = { place : place -> unit; operand : operand -> unit }

val visit_statement : visitor -> statement -> unit
val visit_terminator : visitor -> terminator -> unit

(* The blocks a terminator may go to, in order. *)
val successors : terminator -> block list

(* Whether a local of the type takes no room, so that no code names it. *)
val erased : Memory_layout.env -> ty -> bool

(* The operands a call's target reads, beyond its arguments. *)
val target_operands : target -> operand list

(* The same function in canonical form: blocks in reverse postorder from
   the entry, with unreachable blocks removed, and locals numbered with the
   parameters first and then by first use, with unused locals removed. Two
   lowerings of one definition that differ only in numbering give equal
   canonical forms. *)
val canonical_instance : t -> t

(* A compact text form, for tests. *)

module For_testing : sig
  val canonical : function_ -> function_
  val to_string : t -> string
  val function_to_string : function_ -> string
end
