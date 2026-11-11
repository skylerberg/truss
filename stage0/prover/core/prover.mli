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

type running = {
  template : Translate.evaluation -> evaluated option;
  call : Translate.known_call -> Z.t option;
}
(** Running compiled code, which the caller gives through code generation: a template's check, and a
    call whose arguments are known, whose result is a [Bool] as 0 or 1. *)

type told
(** What the world outside the prover said of something it asked: the solver of a query, or running
    code of a template's check or a call's value. *)

val told : (string, told) Query.input
(** What each thing asked was told, by what was asked. A definition's outcome is a saved result
    worked out from these, so one whose reads have not changed is neither translated nor asked
    anything again. *)

val solve_ahead :
  ?running:running ->
  ?tell:((string * told) list -> unit) ->
  Query.context ->
  Solver.t ->
  Path.module_ list ->
  unit
(** Decides every definition of the modules: what their outcomes wait for is asked together, the
    solver's queries several at once, one for each core, and [tell] sets {!told} to the answers,
    which by default sets them in the context's engine. A caller that will ask for many modules'
    proofs calls it once with all of them, which keeps every core busy where one module's queries
    are few. *)

type state = {
  code : Diagnostic.Code.prover;
  span : Diagnostic.span;  (** In the file's offsets. *)
  shows : string;  (** What the obligation is to show, as its diagnostic first says it. *)
  failure : Diagnostic.t option;  (** Why it was not shown, or [None] where it was. *)
}
(** An obligation's state, as a language server shows it at its position. *)

val states :
  ?running:running ->
  ?tell:((string * told) list -> unit) ->
  Query.context ->
  Solver.t ->
  Path.module_ ->
  state list
(** Every obligation of a file's definitions, shown or not, and every definition the prover could
    not read, in the file's offsets and in order. *)

val diagnostics :
  ?running:running ->
  ?tell:((string * told) list -> unit) ->
  Query.context ->
  Solver.t ->
  Path.module_ ->
  Diagnostic.t list
(** Every obligation of a file's definitions that the solver could not prove, and every definition
    the prover could not read, in the file's offsets and in order. [running] runs compiled code, as
    code generation's [Compile.check_template] and [Compile.evaluate_call] do, where it can; the
    prover does not depend on code generation, so the caller gives it. *)
