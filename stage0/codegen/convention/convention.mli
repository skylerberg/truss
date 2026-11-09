(* How Truss parameters and results become C parameters and results. See
   CODEGEN.md, "Calling convention". Lowering and the C emitter both follow
   these rules, so a caller and its callee always agree. *)

(* Values up to this many bytes are passed and returned by value. *)
val by_value_limit : int

(* How a parameter of a type and mode arrives: by value, or as a pointer,
   [writable] for [mut] and large [own] parameters. [None] for a type of
   zero size, which is not passed at all. *)
val parameter : Memory_layout.env -> Ground.mode -> Ground.ty -> Lir.ty option

type result =
  | Nothing  (** Zero size or [Never]: the C function returns [void] *)
  | Returned of Lir.ty
  | Through_pointer of Lir.ty
      (** Too large to return: written through a writable pointer, the first parameter *)

val result : Memory_layout.env -> Ground.ty -> result

(* The C signature of the code behind a function value of a type: its
   environment first, then its parameters, then one evidence pointer for
   each capability in its [uses]. *)
val function_value : Memory_layout.env -> Ground.function_type -> Lir.signature

(* The shape of a function value: its code and its environment. *)
val function_value_shape : Ground.function_type -> Memory_layout.shape

(* A type's drop function takes a writable pointer to the value. *)
val drop_signature : Ground.ty -> Lir.signature

(* An evidence pointer, as a parameter. *)
val evidence : Lir.ty
