(** The MIR an instance runs: its body with each lending and yielding method it calls inlined. A
    loop over a yielding method becomes the method's body, with a copy of the loop's body at each
    [yield]; a lending call becomes the method's body up to its [yield], with the rest of the method
    where the part it lends ends. *)

type callee = { path : Path.t; type_arguments : Types.argument list; mir : Mir.t }
(** A method a call reaches: its path, its type arguments as the instance has them, and its MIR with
    them substituted. *)

val substituted : Types.substitution -> Mir.t -> Mir.t
(** A MIR with type arguments substituted for its generic parameters. *)

val inlined : resolve:(Mir.callee -> callee option) -> enclosing:Path.t list -> Mir.t -> Mir.t
(** The MIR with each lending and yielding method that [resolve] finds inlined, but those in
    [enclosing], the code's own method and those inlined around it, which are never inlined again. A
    loop over one of those pulls a cursor over it instead, as a [concurrent for] does over a method
    that does not yield by position. *)
