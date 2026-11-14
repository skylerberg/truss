(* Lowering the operations of [standard::intrinsic].

   Every operation is written into the caller's code, never called: the
   arithmetic as primitive operations, which the C compiler sees whole, and
   the operations on [Storage] and [View] as a few statements over their
   fields. Growing storage is the one call, into the runtime, since it does
   not depend on the element type beyond its size.

   Storage with capacity 0 and a nonzero length is static, as a string
   literal's is. Every operation that writes the buffer in place first gives
   such storage a buffer of its own, so static bytes are never written. *)

(* An argument: a place, for an operation on [Storage] or [View], which reads
   or changes it there, or a value. *)
type argument = Place of Lowered.place | Value of Lowered.operand

(* The ground types the lowering needs. *)
type types = { usize : Ground.ty; string_slice : Ground.ty }

(* The positions of the arguments an operation passed by place takes as its
   own, moving their values out of their places. *)
val consumed_places : Intrinsic.operation -> int list

(* Writes the operation, with its type arguments in the order the intrinsic
   module declares them, into the builder. [value_arguments] are its generic
   value arguments, such as an array's length, in the same order. The
   result, if any, goes to [destination]. A lending operation instead
   returns the place it lends. An operation that never returns, [crash],
   leaves the builder in a new block that nothing reaches. *)
val lower :
  ?checks:bool ->
  ?value_arguments:Z.t list ->
  Memory_layout.env ->
  Emit_c.Builder.t ->
  types ->
  Intrinsic.operation ->
  type_arguments:Ground.ty list ->
  argument list ->
  destination:Lowered.place option ->
  site:Lowered.site ->
  Lowered.place option
