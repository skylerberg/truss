(** Running the tests of one test executable. *)

val test : string -> (unit -> unit) -> unit
(** Runs a test now. An exception it raises is a failure, and so is a result that an engine the test
    made holds and a new engine with the same inputs computes differently. *)

val wanted : string -> bool
(** Whether a test of this name runs: every test does, or with [TRUSS_TEST] set, the tests whose
    names contain it. *)

val fail : ('a, unit, string, unit) format4 -> 'a
(** Reports a failure of the test that is running. *)

val finish : unit -> unit
(** Prints the result and exits with status 1 if any test failed. *)
