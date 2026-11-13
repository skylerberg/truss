(* The C that every program links with: the runtime's few functions, and
   the generated [main].

   The runtime is one fixed file per target, compiled once and cached, so
   unlike generated code it includes the system's headers: its declarations
   of signals and alternate stacks differ between systems, and parsing the
   headers costs nothing on an edit. Failures go through it: a panic, a
   failed [assert], a [todo] reached, running out of memory, and
   overflowing the stack, each reported to the test runner when in a test,
   and otherwise on standard error. *)

(* With [tests], the runtime of a test program: it counts the blocks that
   are allocated and not freed, and holds the program's table of tests,
   which the runner runs by number. A program that is not a test program has
   neither. With [in_order], the runtime runs the branches of a fork one
   after another and has no threads, as a test program and code run while
   compiling have it. *)
val runtime : Memory_layout.target -> tests:bool -> in_order:bool -> string

(* A C [main] that installs the stack-overflow handler, calls the C
   function [entry], which takes nothing and returns an [Int32], and exits
   with the status it returns. *)

(* A C [main] of a test program: it gives the runtime the table of the
   tests, each a C function [void name(void)], and calls [runner], the
   standard library's test runner, with how many there are and the most
   milliseconds one may run, and exits with the status it returns. The
   runner runs the tests in worker processes, and prints a line as it hands
   each test to a worker, and each result as soon as its test ends: its
   blocks, then a line with the test's number in the table, its outcome, and
   how many microseconds it ran, which ends the record:

   {v
   start 0
   start 1
   message 20
   values differ ...
   test 1 failed 212
   test 0 passed 87
   v}

   An outcome is [passed], [failed], [panicked], [incomplete] (a [todo] was
   reached), [timed_out], or [crashed]. A [message] block, and an [echo]
   block of the test's echo output, give their length in bytes and then the
   bytes. Results come in the order tests end, which depends on the
   workers. The program exits with 1 if any test did not pass. *)
val tests_calling : time_limit:int -> runner:string -> string list -> string

(* A C [main] that installs the stack-overflow handler and calls [entry]
   with the program's arguments, the generated Truss side of startup, and
   exits with the status it returns. *)
(* The startup of code run while compiling, which calls the evaluator. *)
val evaluator_calling : string -> string
val program_calling : string -> string

module For_testing : sig
  val main_calling : string -> string
end
