(* Compiling a program or a test run from a database of checked
   definitions: lowering each instance a root reaches, elaborating its
   drops, building it through the object cache, and running it. See
   CODEGEN.md, "Instances" and "Tests". *)

type t

(* With [checks], the default, the program checks at run time what the
   prover would prove: [requires] clauses that can run, integer overflow,
   and division. Stage0 has no prover, so its builds check, as CODEGEN.md's
   [--check-proofs] does. *)
val create :
  ?checks:bool ->
  Query.database ->
  Memory_layout.target ->
  Toolchain.t ->
  Build.cache ->
  Build.settings ->
  t

(* What an instance compiles to: its LIR, lowered or generated, with its
   drops elaborated, in canonical form, or a constant's static data. Each
   is made once. *)
val compiled : t -> Instance.key -> Lir.compiled

(* Builds a program that runs the tests, each named by its path, and runs
   it, returning its exit status and its output, as [Startup.tests_calling]
   describes it. *)
(* With [results], a directory, each test that passes with nothing to show
   is kept there under the key of the code it can run, as CODEGEN.md's "Test
   results" says, and is not built or run again until that code changes;
   the report is the same either way. *)
val run_tests :
  ?results:string -> t -> time_limit:int -> Path.t list -> (int * string, string) result

(* Builds the program whose [main] is at that path, and runs it with the
   arguments, and [input] as its standard input if given, returning its exit
   status, its output, and its errors. *)
(* Builds the program whose [main] is at that path into an executable at
   [output]. *)
val build_program : t -> main:Path.t -> output:string -> (unit, string) result

val run_program :
  ?input:string ->
  t ->
  main:Path.t ->
  arguments:string list ->
  (int * string * string, string) result
