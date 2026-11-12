(* From the type checker's types to code generation's ground types and
   shapes.

   An instance's code is lowered with its type arguments substituted, so
   every type in it must come out ground: no generic parameter, no
   projection, and nothing the checker left undecided. A type that is not
   ground here is a compiler bug. *)

(* The type checker's queries that the conversion reads about other
   definitions. *)
type context = {
  type_interface : Path.t -> Types.type_interface option;
  normalize : Types.ty -> Types.ty;
      (** Replaces each projection whose base is known by the associated type its [impl] chooses *)
  normalize_capabilities : Types.capability_set -> Types.capability_set;
      (** Replaces each associated capability set whose base is known by the capabilities that its
          [impl] defines *)
  cursor_fields : Ground.yielding -> (string * Memory_layout.member) list;
      (** The fields of a pulled method's cursor, from its lowered body *)
}

val ground : context -> Types.substitution -> Types.ty -> Ground.ty
val ground_argument : context -> Types.substitution -> Types.argument -> Ground.argument
val mode : Types.mode -> Ground.mode

(* The capabilities that a function takes evidence for in an instance, in
   path order: those that its [uses] clause names after substitution,
   except [Panic]. An associated capability set is replaced by the set
   that the [impl] defines for the type that the instance substitutes for
   its base, so a function that uses [Source.Uses] takes the evidence that
   its instance's [Source] needs. *)
val evidence_for : context -> Types.substitution -> Types.capability_set -> Path.t list

(* A ground type, written back as the checker's, so that the checker's own
   substitution and its lookups apply to it, and the substitution of
   generic parameters by ground arguments. *)
val back : Ground.ty -> Types.ty
val substitution : Types.generic list -> Ground.argument list -> Types.substitution

(* The ground type of a built-in. *)
val builtin : Intrinsic.builtin -> Ground.ty

(* [Panic], the one capability with no evidence: [Panic.crash] ends the
   process, so no function takes evidence for it and no ground function
   type lists it. *)
val panic_capability : Path.t

(* What a ground type is made of, for its layout. *)
val shape : context -> Ground.ty -> Memory_layout.shape

(* How a ground type holds its value: its shape, or a built-in representation. *)
val representation : context -> Ground.ty -> Memory_layout.representation
