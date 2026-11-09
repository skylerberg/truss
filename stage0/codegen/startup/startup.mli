(* The C that every program links with: the runtime's few functions, and
   the generated [main]. See CODEGEN.md, "Program startup and failure".

   The runtime is one fixed file per target, compiled once and cached, so
   unlike generated code it includes the system's headers: its declarations
   of signals and alternate stacks differ between systems, and parsing the
   headers costs nothing on an edit. Failures go through it: a panic, a
   failed [assert], a [todo] reached, running out of memory, and
   overflowing the stack, each reported to the test runner when in a test,
   and otherwise on standard error. *)

val runtime : Memory_layout.target -> string

(* A C [main] that installs the stack-overflow handler, calls the C
   function [entry], which takes nothing and returns an [Int32], and exits
   with the status it returns. *)
val main_calling : string -> string

(* A C [main] that runs the tests, each a C function [void name(void)], in
   worker processes, killing any that runs longer than [time_limit]
   milliseconds, and prints each result in order:

   {v
   test 0 passed
   test 1 failed
   message 20
   values differ ...
   v}

   An outcome is [passed], [failed], [panicked], [incomplete] (a [todo] was
   reached), [timed_out], or [crashed]. A [message] block, and an [echo]
   block of the test's echo output, give their length in bytes and then the
   bytes. The program exits with 1 if any test did not pass. *)
val tests_calling : time_limit:int -> string list -> string
