(* The functions the compiler writes for every type: drop and copy. See
   CODEGEN.md, "Generated functions for each type".

   Each is an instance of its own, keyed by the type, so it is compiled once
   and shared. Its code follows the type's shape. [Storage[Element]], the
   one built-in type that owns a buffer of elements, has code of its own:
   dropping drops its live elements and frees the buffer, and copying makes
   one allocation, and for plain elements one memory copy. *)

(* What a type is, for glue: made of fields, or the built-in storage of
   elements of a type. *)
type kind = Shape of Memory_layout.shape | Storage of Ground.ty
type t

(* [usize] is the ground type [USize]. *)
val create : Memory_layout.env -> kind_of:(Ground.ty -> kind) -> usize:Ground.ty -> t

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
