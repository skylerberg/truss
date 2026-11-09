(* Compiling a program or a test run from a database of checked
   definitions: lowering each instance a root reaches, elaborating its
   drops, building it through the object cache, and running it. See
   CODEGEN.md, "Instances" and "Tests". *)

type t

val create :
  Query.database -> Memory_layout.target -> Toolchain.t -> Build.cache -> Build.settings -> t

(* What an instance compiles to: its LIR, lowered or generated, with its
   drops elaborated, in canonical form, or a constant's static data. Each
   is made once. *)
val compiled : t -> Instance.key -> Lir.compiled

(* Builds a program that runs the tests, each named by its path, and runs
   it, returning its exit status and its output, as [Startup.tests_calling]
   describes it. *)
val run_tests : t -> time_limit:int -> Path.t list -> (int * string, string) result

(* Builds the program whose [main] is at that path, and runs it with the
   arguments, and [input] as its standard input if given, returning its exit
   status, its output, and its errors. *)
val run_program :
  ?input:string ->
  t ->
  main:Path.t ->
  arguments:string list ->
  (int * string * string, string) result
