(* How Truss parameters and results become C parameters and results. Lowering
   and the C emitter both follow these rules, so a caller and its callee
   always agree. *)

(* How a parameter of a type and mode arrives: by value, or as a pointer,
   [writable] for [mut] and large [own] parameters. A read-only value that
   holds an array's elements in its own bytes arrives as a pointer whatever
   its size, since a view of the elements must be a view of the caller's.
   [None] for a type of zero size, which is not passed at all. *)
val parameter : Memory_layout.env -> Ground.mode -> Ground.ty -> Lowered.ty option

type result =
  | Nothing  (** Zero size or [Never]: the C function returns [void] *)
  | Returned of Lowered.ty
  | Through_pointer of Lowered.ty
      (** Too large to return: written through a writable pointer, the first parameter *)

val result : Memory_layout.env -> Ground.ty -> result
val signature : ?returns:bool -> Lowered.ty list -> result -> Lowered.signature
val destination : result -> Lowered.place -> Lowered.destination

(* The C signature of the code behind a function value of a type: its
   environment first, then its parameters, then one evidence pointer for
   each capability in its [uses]. *)
val function_value : Memory_layout.env -> Ground.function_type -> Lowered.signature

(* The shape of a function value: its code and its environment. *)
val function_value_shape : Ground.function_type -> Memory_layout.shape

(* A type's drop function takes a writable pointer to the value. *)
val drop_signature : Ground.ty -> Lowered.signature

(* An evidence pointer, as a parameter. *)
val evidence : Lowered.ty
