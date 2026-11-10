(** Moves, loans, and views, within each function. *)

type result = {
  diagnostics : Diagnostic.t list;  (** In the definition's own offsets. *)
  moves : Core.id list;  (** The [Use] nodes of the core form that move a place. *)
  obligations : Checked.obligation list;
      (** The [Disjoint] obligations: pairs of index calls or slices of one collection, by origin,
          that must select different elements. They come from places passed to one call and from the
          branches of a [parallel] or [concurrent] block. The prover shows that they hold. *)
}

val ownership : (Resolve.Names.key, result option) Query.query
(** The ownership check of a definition. [None] if the definition has no core form. *)

(** Whether a yielding method can be pulled as a cursor, and if not, why. *)
type pulling =
  | Pullable
  | Yields_mut  (** A cursor would store [mut] access between pulls. *)
  | Recursive
      (** The method yields through itself, as a tree's [each] that loops over its subtrees. Its
          cursor would need a stack of its own. *)
  | Yields_places
      (** The method yields read-only views of places, such as [self[index]]. A pull hands out an
          owned value, so only a [Plain] element can be pulled. A pull of any other element is
          reported where it happens. *)

val pullable : (Path.t, pulling) Query.query

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every ownership error of a file, in its offsets and in order. *)
