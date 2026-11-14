(** The ownership check: moves, loans, and views, within each function. It prevents use after move,
    dangling views, mutation of a borrowed place, and data races. *)

type result = {
  diagnostics : Syntax.diagnostic list;
  disjoint : (Core.origin * Core.origin) list;
      (** The [Disjoint] obligations: pairs of index calls or slices of one collection, by origin,
          that must select disjoint elements. They come from arguments of one call that may alias,
          and from the branches of a [parallel] or [concurrent] block. The prover discharges them.
      *)
}

val ownership : (Resolve.Names.key, result option) Query.query
(** The ownership check of a definition. [None] if the definition has no core form. *)

val diagnostics : Query.context -> Path.file -> Diagnostic.t list
(** Every ownership error of a file, in its offsets and in order. *)
