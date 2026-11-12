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
  Engine.t -> first:(unit -> unit) -> again:(unit -> unit) -> string list -> unit
(** Fails the test unless [first] computes each result that a label names, as ["name(key)"], and
    [again] computes none of them. A label that names no result fails, so a renamed query or key
    cannot pass the check unnoticed. *)

val workspace_path : string -> string
(** The path of a file of the repository, given from the workspace root, such as ["SYNTAX.md"],
    whatever directory the executable runs in. *)
