(** The prover's entry point: the obligations of each definition, proven one query at a time.

    A definition that uses what the prover cannot read yet is reported as [prover.unsupported], and
    none of its obligations count as proven. *)

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

(** What running the code that decides a clause gave: that it holds, that it does not, or that it
    ran past its time limit. *)
type evaluated = Holds | Fails | Too_long

val diagnostics :
  ?evaluate:(Translate.evaluation -> evaluated option) ->
  Query.context ->
  Solver.t ->
  Path.module_ ->
  Diagnostic.t list
(** Every obligation of a file's definitions that the solver could not prove, and every definition
    the prover could not read, in the file's offsets and in order. [evaluate] decides a clause by
    running compiled code, as code generation's [Compile.check_template] does, where it can; the
    prover does not depend on code generation, so the caller gives it. *)
