(** The ownership check: moves, loans, and views, within each function. It prevents use after move,
    dangling views, mutation of a borrowed place, and data races. *)

type result = {
  diagnostics : Syntax.diagnostic list;
  moves : Core.id list;  (** The [Use] nodes of the core form that move a place. *)
  disjoint : (Core.origin * Core.origin) list;
      (** The [Disjoint] obligations: pairs of index calls or slices of one collection, by origin,
          that must select disjoint elements. They come from arguments of one call that may alias,
          and from the branches of a [parallel] or [concurrent] block. The prover discharges them.
      *)
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
      (** The method yields read-only views of places, such as [self[index]]. A pull returns an
          owned value, so only a [Plain] element can be pulled. A cursor over any other element is
          reported where the cursor is created. *)

val pullable : (Path.t, pulling) Query.query

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** Every ownership error of a file, in its offsets and in order. *)
