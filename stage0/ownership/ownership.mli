(** Moves, loans, and views, within each function. See TYPECHECKER.md, "Ownership: moves, loans, and
    views". *)

type result = {
  diagnostics : Diagnostic.t list;  (** In the definition's own offsets. *)
  moves : Syntax.id list;
      (** The id of every expression that moves a place, in order, so code generation knows what not
          to release. *)
  obligations : Checked.obligation list;
      (** The [Disjoint] obligations of [parallel] branches and of places lent together. *)
}

val ownership : (Resolve.Names.key, result option) Query.query
(** A definition's ownership, or [None] if there is no such definition or it has no checked form. *)

val pullable : (Path.t, bool) Query.query
(** Whether a [yields] method can be pulled as a cursor: one whose yields go through a recursive
    call cannot, and drives only [for] loops. *)

val diagnostics : Query.database -> Path.module_ -> Diagnostic.t list
(** Every ownership error of a file, in its offsets and in order. *)
