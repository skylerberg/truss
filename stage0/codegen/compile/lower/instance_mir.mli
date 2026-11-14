type callee = {
  path : Path.t;
  type_arguments : Types.argument list;
  mir : Mir.t;
  defaults : (int * Mir.t) list;
}
(** A method a call reaches: its path, its type arguments as the instance has them, and, with them
    substituted, its MIR and the MIR of each of its parameters' defaults, by the parameter's
    position. *)

val substituted : Types.substitution -> Mir.t -> Mir.t
(** A MIR with type arguments substituted for its generic parameters. *)

val inlined : resolve:(Mir.callee -> callee option) -> enclosing:Path.t list -> Mir.t -> Mir.t
