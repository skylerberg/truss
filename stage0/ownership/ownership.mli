(** Moves, loans, and views, within each function. *)

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

(** Whether a [yields] method can be pulled as a cursor, and if not, why. *)
type pulling =
  | Pullable
  | Yields_mut  (** A cursor would store [mut] access between pulls. *)
  | Recursive
      (** In its own cycle of yielding through, as a tree's [each] that loops over its subtrees, so
          its cursor would need a stack of its own. *)
  | Yields_places
      (** It yields read-only views of named places, such as [self[index]] or a local, which a pull
          hands out as owned values: only a [Plain] element can be pulled, since anything else would
          be copied unasked. A pull of a non-[Plain] element is reported where it happens. *)

val pullable : (Path.t, pulling) Query.query

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every ownership error of a file, in its offsets and in order. *)

(** The ownership check on the core form. It is not used yet: the tests compare it with the check
    above. *)
module On_core : sig
  type result = {
    diagnostics : Diagnostic.t list;
    moves : Core.id list;  (** The [Use] nodes that move a place. *)
    disjoint : (Core.origin * Core.origin) list;
        (** Pairs of index calls or slices of one collection, by origin, that must select different
            elements. The prover shows that they do. *)
  }

  val check : Query.context -> Resolve.Names.key -> result option
end
