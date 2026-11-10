(* [Storage[Element]] and [View[Element]], the two built-in types that hold
   a buffer of elements: what each is made of, the states a storage can be
   in, and the places and values the rest of code generation makes of them.
   Nothing else names their fields.

   A storage is in one of three states, which its capacity and length say:
   - empty: no elements and no buffer. Its capacity and length are 0.
   - static: elements in memory it does not own, as a string literal's are.
     Its capacity is 0 and its length is not.
   - owning: a buffer on the heap, which it frees. Its capacity is not 0.

   So a storage owns a buffer exactly when its capacity is not 0, and one
   that does not is never written in place or freed. A constant's storage
   is the one case apart: its elements are static and its capacity is its
   length, so that a copy of it is a real copy, and nothing writes or drops
   a constant. *)

(* The types of a storage and of a view of elements of a type, and the
   element type of a storage and of a view. *)
val of_elements : Ground.ty -> Ground.ty
val view_of_elements : Ground.ty -> Ground.ty
val elements_of : Ground.ty -> Ground.ty option
val viewed : Ground.ty -> Ground.ty option

(* What each is made of, where [usize] is the type of a length. *)
val shape : usize:Ground.ty -> Ground.ty -> Memory_layout.shape
val view_shape : usize:Ground.ty -> Ground.ty -> Memory_layout.shape

(* The names of a storage's fields, for the emitter's static data. *)
val buffer_field : string
val length_field : string
val capacity_field : string

(* The parts of a storage at a place, and its element at an index. *)
val buffer : Lir.place -> Lir.place
val length : Lir.place -> Lir.place
val capacity : Lir.place -> Lir.place
val at : Lir.place -> Lir.operand -> Lir.place

(* The parts of a view at a place, and its element at an index. *)
val view_elements : Lir.place -> Lir.place
val view_length : Lir.place -> Lir.place
val view_at : Lir.place -> Lir.operand -> Lir.place

(* An empty storage, of a storage type. Its buffer points at nothing, and is
   not null, so an [Option] of a storage has a niche. *)
val empty : Ground.ty -> Lir.rvalue

(* A static storage, of a storage type: [length] elements at [elements],
   which it does not own. *)
val static : Ground.ty -> elements:Lir.operand -> length:Lir.operand -> Lir.rvalue

(* An owning storage, of a storage type: a buffer on the heap with room for
   [capacity] elements, of which the first [length] are there. *)
val owning :
  Ground.ty -> buffer:Lir.operand -> length:Lir.operand -> capacity:Lir.operand -> Lir.rvalue

(* A view, of a view type, of [length] elements at [elements]. *)
val view : Ground.ty -> elements:Lir.operand -> length:Lir.operand -> Lir.rvalue

(* Writes a test of whether the storage at a place owns a buffer, and gives
   its result, a [Bool]. *)
val owns_buffer : Lir_builder.t -> Lir.place -> Lir.operand

(* Writes a test of whether the storage at a place has no elements. *)
val is_empty : Lir_builder.t -> Lir.place -> Lir.operand
