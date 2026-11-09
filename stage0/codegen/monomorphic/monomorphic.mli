(* From the type checker's types to code generation's ground types and
   shapes. See CODEGEN.md, "Instances" and "Data layout".

   An instance's code is lowered with its type arguments substituted, so
   every type in it must come out ground: no generic parameter, no
   projection, and nothing the checker left undecided. A type that is not
   ground here is a compiler bug, and raises [Invalid_argument]. *)

(* What the conversion reads about other definitions, each one of the type
   checker's queries. *)
type context = {
  type_interface : Path.t -> Types.type_interface option;
  normalize : Types.ty -> Types.ty;
      (** Replaces each projection whose base is known by the associated type its [impl] chooses *)
  capabilities : Types.parameter -> Path.t list;
      (** The capabilities a capability parameter stands for in this instance *)
  cursor_fields : Ground.yielding -> (string * Memory_layout.member) list;
      (** The fields of a pulled method's cursor, from its lowered body *)
}

val ground : context -> Types.substitution -> Types.ty -> Ground.ty
val ground_argument : context -> Types.substitution -> Types.argument -> Ground.argument
val ground_function : context -> Types.substitution -> Types.function_type -> Ground.function_type
val mode : Types.mode -> Ground.mode

(* The ground type of a built-in. *)
val builtin : Intrinsic.builtin -> Ground.ty

(* What a ground type is made of, for its layout. *)
val shape : context -> Ground.ty -> Memory_layout.shape

(* What a ground type is, for its generated drop and copy. *)
val kind : context -> Ground.ty -> Glue.kind
