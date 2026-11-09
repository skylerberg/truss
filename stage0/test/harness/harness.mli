(** Running the tests of one test executable. See IMPLEMENTATION.md, "Testing". *)

val test : string -> (unit -> unit) -> unit
(** Runs a test now. An exception it raises is a failure. *)

val fail : ('a, unit, string, unit) format4 -> 'a
(** Reports a failure of the test that is running. *)

val finish : unit -> unit
(** Prints the result and exits with status 1 if any test failed. *)
