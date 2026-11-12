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

(** A run of compiled code that decides part of a proof: a template's check, or a call whose
    arguments are known. *)
type run = Template_check of Translate.evaluation | Call of Translate.known_call

(** What a run gave: an integer, or a [Bool] as 0 or 1; that it timed out; or that it was not run,
    since its code cannot be built. *)
type run_result = Returned of Z.t | Timed_out | Not_run

type evaluator = { code_key : run -> string option; run : run -> run_result }
(** Runs compiled code, through code generation, which the caller gives, since the prover does not
    depend on code generation. [code_key] is the key of everything a run's code can reach, which
    changes exactly when what the run gives may, and [None] where the code cannot be built. *)

type oracle_response
(** An oracle's response to a request: the solver's to a query, or the evaluator's to a run, with
    the key of the code that ran. *)

val oracle_response : (string, oracle_response) Query.input
(** Each oracle's response, by the request's key. A definition's outcome is a saved result derived
    from these, so one whose reads have not changed is neither translated nor asked anything again.
*)

val solve_ahead :
  ?evaluator:evaluator ->
  record:((string * oracle_response) list -> unit) ->
  Query.context ->
  Solver.t ->
  Path.module_ list ->
  unit
(** Decides every definition of the modules. Each run whose code key changed since it ran, or that
    timed out, is run again, so that no proof keeps a value the current code would not give. Then
    the requests the outcomes are pending on are sent together, the solver's queries several at
    once, one for each core, and [record] sets {!oracle_response} to the responses, which the driver
    does, since only the database sets a session's inputs. A caller that will ask for many modules'
    proofs calls it once with all of them, which keeps every core busy where one module's queries
    are few. *)

type 'span state = {
  code : Diagnostic.Code.prover;
  span : 'span;
  shows : string;  (** What the obligation is to show, as its diagnostic first says it. *)
  failure : 'span Diagnostic.diagnostic option;
      (** Why it was not shown, or [None] where it was. *)
  trusts_compiled_code : bool;
      (** It was shown by running compiled code, or with a fact that running a call gave. *)
}
(** An obligation's state, as a language server shows it at its position. *)

val states :
  ?evaluator:evaluator ->
  record:((string * oracle_response) list -> unit) ->
  Query.context ->
  Solver.t ->
  Path.module_ ->
  Diagnostic.span state list
(** Every obligation of a file's definitions, shown or not, and every definition the prover could
    not read, in the file's offsets and in order. *)

val diagnostics :
  ?evaluator:evaluator ->
  record:((string * oracle_response) list -> unit) ->
  Query.context ->
  Solver.t ->
  Path.module_ ->
  Diagnostic.t list
(** Every obligation of a file's definitions that the solver could not prove, and every definition
    the prover could not read, in the file's offsets and in order. [evaluator] runs compiled code,
    as code generation's [Compile.check_template] and [Compile.evaluate_call] do, where it can. *)
