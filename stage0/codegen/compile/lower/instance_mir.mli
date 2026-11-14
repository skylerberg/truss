type callee = { path : Path.t; type_arguments : Types.argument list; mir : Mir.t }
(** A method a call reaches: its path, its type arguments as the instance has them, and its MIR with
    them substituted. *)

val substituted : Types.substitution -> Mir.t -> Mir.t
(** A MIR with type arguments substituted for its generic parameters. *)

val inlined : resolve:(Mir.callee -> callee option) -> enclosing:Path.t list -> Mir.t -> Mir.t
