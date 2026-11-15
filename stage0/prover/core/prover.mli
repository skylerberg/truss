module State = State
module Facts = Facts
module Contracts = Contracts

type proof = Obligations of State.outcome | Unsupported of Syntax.span * string | Not_proven_here

val proof : (Resolve.Names.key, proof) Query.query

type run = Template_check of State.evaluation | Call of State.known_call
type run_result = Returned of Z.t | Timed_out | Not_run
type evaluator = { code_key : run -> string option; run : run -> run_result }
type oracle_response

val oracle_response : (string, oracle_response) Query.input

val solve_ahead :
  ?evaluator:evaluator ->
  record:((string * oracle_response) list -> unit) ->
  Query.context ->
  Solver.t ->
  Path.file list ->
  unit

type 'span state = {
  code : Diagnostic.Code.prover;
  span : 'span;
  shows : string;
  failure : 'span Diagnostic.diagnostic option;
  trusts_compiled_code : bool;
}

val states :
  ?evaluator:evaluator ->
  record:((string * oracle_response) list -> unit) ->
  Query.context ->
  Solver.t ->
  Path.file ->
  Diagnostic.span state list

val diagnostics :
  ?evaluator:evaluator ->
  record:((string * oracle_response) list -> unit) ->
  Query.context ->
  Solver.t ->
  Path.file ->
  Diagnostic.t list
