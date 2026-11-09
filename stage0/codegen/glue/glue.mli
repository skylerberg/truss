(* The functions the compiler writes for every type: drop and copy. See
   CODEGEN.md, "Generated functions for each type".

   Each is an instance of its own, keyed by the type, so it is compiled once
   and shared. Its code follows the type's shape. [Storage[Element]], the
   one built-in type that owns a buffer of elements, has code of its own:
   dropping drops its live elements and frees the buffer, and copying makes
   one allocation, and for plain elements one memory copy. *)

(* What a type is, for glue: made of fields, or the built-in storage of
   elements of a type. *)
type kind =
  | Shape of Memory_layout.shape
  | Storage of Ground.ty
  | Handle  (** An operating system's descriptor, in a [descriptor] field, closed when dropped *)

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
  kind_of:(Ground.ty -> kind) ->
  usize:Ground.ty ->
  ?debug_form:(Ground.ty -> debug_form) ->
  unit ->
  t

(* Whether a type has nothing to drop and copies with a memory copy: it
   holds no storage and no [indirect] variant anywhere. Drops of such types
   are removed, and copying one copies its bytes. *)
val trivial : t -> Ground.ty -> bool

(* The drop function of a type: [Instance.Drop ty], taking a writable
   pointer to the value, as [Convention.drop_signature] says. *)
val drop : t -> Ground.ty -> Lir.t

(* The copy function of a type: [Instance.Copy ty], taking the value as a
   read-only parameter and returning the copy. *)
val copy : t -> Ground.ty -> Lir.t
val copy_signature : t -> Ground.ty -> Lir.signature

(* Slot 0 of an [any] table: [Instance.Any_drop ty], which takes the value's
   pointer untyped and drops the value. *)
val any_drop : t -> Ground.ty -> Lir.t

(* The function that writes a value of a type in its binary form to the
   debug buffer: [Instance.Encode ty], taking a read-only pointer to the
   value. See CODEGEN.md, "Code run while compiling". *)
val encode : t -> Ground.ty -> Lir.t
val encode_signature : t -> Ground.ty -> Lir.signature

(* Writes, with the builder, a call to the encode function of the type on
   the value at the place; nothing for a type of zero size. *)
val encode_call : t -> Lir_builder.t -> Ground.ty -> Lir.place -> unit

(* Writes, with the builder, a copy of the value at [source] to
   [destination], both of the type: a memory copy for a trivial type, and
   otherwise a call to its copy function. *)
val copy_into : t -> Lir_builder.t -> destination:Lir.place -> source:Lir.place -> Ground.ty -> unit

(* The debug output function of a type: [Instance.Debug ty], which takes a
   read-only pointer to the value, or nothing for a type of zero size, and
   appends the value's text to the runtime's debug buffer. *)
val debug : t -> Ground.ty -> Lir.t
val debug_signature : t -> Ground.ty -> Lir.signature
