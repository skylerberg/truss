(** The prover's entry point: the obligations of each definition, proven one query at a time. See
    PROVER.md, "What the prover does".

    Stage0's prover is being built. What it proves so far is listed in PROVER.md, "What is built"; a
    definition that uses anything else is reported as [prover.unsupported], and none of its
    obligations count as proven. *)

module Translate = Translate

type proof =
  | Obligations of Translate.outcome
  | Unsupported of Syntax.span * string
      (** The definition uses something the prover cannot translate yet, at this span. *)
  | Not_proven_here
      (** A definition with nothing to prove, or one whose earlier errors stop the prover. *)

val proof : (Resolve.Names.key, proof) Query.query
(** A definition's obligations, each a canonical query, stored with its trace like every stage's
    results. *)

val diagnostics : Query.database -> Solver.t -> Path.module_ -> Diagnostic.t list
(** Every obligation of a file's definitions that the solver could not prove, and every definition
    the prover could not read, in the file's offsets and in order. *)

val holes : Query.database -> Path.module_ -> Source.span list
(** Each [todo] in a file's theorems, [proof] blocks, and laws' proofs, in the file's offsets and in
    order: what follows one on its path is not shown, so a build of a program refuses one that can
    reach it. Holes are not errors; tests run regardless. See PROVER.md, "Holes". *)
