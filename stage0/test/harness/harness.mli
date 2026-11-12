(** Running the tests of one test executable. When the executable exits, it prints the result, and
    exits with status 1 if any test failed. *)

val test : string -> (unit -> unit) -> unit
(** Runs a test now. An exception it raises is a failure, and so is a result that an engine the test
    made holds and a new engine with the same inputs computes differently. *)

val always : string -> (unit -> unit) -> unit
(** Runs a test whatever [TRUSS_TEST] names, for a step that every test of the executable needs,
    such as building the program they run in. *)

val wanted : string -> bool
(** Whether a test of this name runs: every test does, or with [TRUSS_TEST] set, the tests whose
    names contain it. *)

val fail : ('a, unit, string, unit) format4 -> 'a
(** Reports a failure of the test that is running. *)

val expect_not_recomputed :
  Engine.t ->
  first:(unit -> unit) ->
  again:(unit -> unit) ->
  ('key, 'value) Query.query ->
  'key list ->
  unit
(** Fails the test unless [first] computes the query's result for each key and [again] computes none
    of them. A key that [first] does not compute fails, so the check cannot pass on a result nothing
    computes. *)

val workspace_path : string -> string
(** The path of a file of the repository, given from the workspace root, such as ["SYNTAX.md"],
    whatever directory the executable runs in. *)
