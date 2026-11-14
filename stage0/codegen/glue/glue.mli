(* Glue, as rustc names it: the functions the compiler writes for every
   type rather than the program, here drop, copy, debug output and encoding.

   Each is an instance of its own, keyed by the type, so it is compiled once
   and shared. Its code follows the type's shape. [Storage[Element]], the
   one built-in type that owns a buffer of elements, has code of its own:
   dropping drops its live elements and frees the buffer, and copying makes
   one allocation, and for plain elements one memory copy. *)

(* How a type's debug output is written: from its structure, as Truss would
   build it, such as [Point(x: 1.0, y: 2.0)] or [Some(3)]; as quoted text,
   for a record whose one field is storage or a view of bytes, such as
   [String]; or as a list, for a record whose one field is storage or a view
   of elements, such as [List]. *)
type debug_form = Structure | Text | Sequence
type t

(* [usize] is the ground type [USize]. [debug_form] defaults to [Structure]
   for every type. *)
val create :
  Memory_layout.env ->
  representation:(Ground.ty -> Memory_layout.representation) ->
  usize:Ground.ty ->
  ?debug_form:(Ground.ty -> debug_form) ->
  unit ->
  t

(* Whether a type has nothing to drop and copies with a memory copy: it
   holds no storage and no [indirect] variant anywhere. Drops of such types
   are removed, and copying one copies its bytes. *)
val trivial : t -> Ground.ty -> bool

(* The drop function of a type: [Instance.Drop ty], taking a writable
   pointer to the value. *)
val drop : t -> Ground.ty -> Emit_c.Builder.instance

(* The copy function of a type: [Instance.Copy ty], taking the value as a
   read-only parameter and returning the copy. *)
val copy : t -> Ground.ty -> Emit_c.Builder.instance

(* Slot 0 of an [any] table: [Instance.Any_drop ty], which takes the value's
   pointer untyped and drops the value. *)
val any_drop : t -> Ground.ty -> Emit_c.Builder.instance

(* The buffer a debug or an encode function appends to: storage of bytes, which
   its caller owns. Each takes the address of one to change, after the
   value. *)
val output_ty : Ground.ty

(* The function that appends a value of a type in its binary form:
   [Instance.Encode ty], taking a read-only pointer to the value, and the
   output. *)
val encode : t -> Ground.ty -> Emit_c.Builder.instance

(* Writes, with the builder, a call to the encode function of the type on
   the value at the place, to append to [output]; nothing for a type of
   zero size. *)
val encode_call :
  t -> Emit_c.Builder.t -> output:Lowered.operand -> Ground.ty -> Lowered.place -> unit

(* Writes, with the builder, a copy of the value at [source] to
   [destination], both of the type: a memory copy for a trivial type, and
   otherwise a call to its copy function. *)
val copy_into :
  t -> Emit_c.Builder.t -> destination:Lowered.place -> source:Lowered.place -> Ground.ty -> unit

(* The debug output function of a type: [Instance.Debug ty], which takes a
   read-only pointer to the value, unless the type has zero size, and the
   output, and appends the value's text with the standard library's
   functions that write numbers and quoted text. *)
val debug : t -> Ground.ty -> Emit_c.Builder.instance
val debug_signature : t -> Ground.ty -> Lowered.signature

module For_testing : sig
  val copy_signature : t -> Ground.ty -> Lowered.signature
end
