(* Compiling a program or a test run from a database of checked
   definitions: lowering each instance a root reaches, building it through
   the object cache, and running it.

   A step that fails for a reason that is not the compiler's gives [Error]
   with a message: the C compiler or the linker refused, a program run
   while compiling ended badly, or the program is one stage0 cannot build
   yet. A bug in the compiler is raised as [Compiler_bug.Bug], which
   nothing here catches, for the command to report. *)

type t

(* How instances are lowered: for which target, and whether the build has
   run-time checks. *)
type lowering

(* The instances whose keys have been asked for, for each way of lowering.
   Finding the instances that reach each other starts from these, so a
   driver's [want] adds to this input before a key is asked for. Only the
   database sets it. *)
val roots : (lowering, Instance.key list) Query.input

val add_roots : Query.context -> lowering -> Instance.key list -> Instance.key list
(** The roots with more wanted, which a driver sets {!roots} to before it asks for those instances'
    keys: a query cannot set an input. *)

(* Where the results of runs are kept, by the key of the code that ran:
   each test that passed with nothing to show, and the output of each run
   of code while compiling. The database keeps them in its store. *)
type results = { find : string -> string option; add : string -> string -> unit }

(* The result of a run of code while compiling, or that it ran past the
   compiler's time limit. *)
type 'a ran = Ran of 'a | Ran_too_long

(* With [checks], the default, the program checks at run time each
   primitive operation that is undefined or wrong where its precondition
   does not hold: an index, a slice, arithmetic, a shift, and a call of
   the C library. It evaluates no [requires] clause. A build with checks
   does not wait for proofs. [file_name] names the file of each position the
   program reports, and is [Path.show_file] unless a
   driver shows files another way. [want] is told which instances' keys are
   about to be asked for, and adds them to [roots]. [worked_on] says whether a package is one of the
   project's own, whose code a development build never copies into
   another's file; without it, every package but the standard library is.
   [results] keeps the results of runs between compilers.
   [evaluation_time_limit], in milliseconds, stops each run of code while
   compiling, and is 10 seconds by default. [programs] is the directory each
   built program is written to, and is the system's temporary directory by
   default. *)
val create :
  ?checks:bool ->
  ?file_name:(Path.file -> string) ->
  ?results:results ->
  ?evaluation_time_limit:int ->
  ?programs:string ->
  want:(lowering -> Instance.key list -> unit) ->
  ?worked_on:(Path.package -> bool) ->
  Query.context ->
  Memory_layout.target ->
  Toolchain.t ->
  Build.cache ->
  Build.settings ->
  t

(* An instance's C, lowered or generated, or a constant's
   static data. Each is made once. *)

(* How a test ended, as the runner names it. *)
type outcome = Passed | Failed | Panicked | Incomplete | Timed_out | Crashed

(* As the runner names it: ["passed"], ["timed_out"], and so on. *)
val show_outcome : outcome -> string

(* One test's result: its outcome, its message and echo output, if any, how
   many microseconds it ran in its worker, and whether it came from the
   kept results, in which case the duration is that of the run that kept
   it. *)
type record = {
  outcome : outcome;
  message : string option;
  echo : string option;
  microseconds : int;
  cached : bool;
}

(* A test program's whole report, one record a test, in the order of the tests however they ended, or why
   it cannot be read. *)

(* How a test run is getting on: lowering the instances the tests reach, compiling
   the C files that are not cached, out of how many, running the tests that
   have no kept result, and each test's start and end, by its place in the
   list given. A test with a kept result is reported as ended before any
   test runs. *)
type progress =
  | Lowering
  | Compiling of { compiled : int; total : int }
  | Running of { tests : int }
  | Started of { test : int }
  | Ended of { test : int; record : record }

(* Builds a program that runs the tests, each named by its path, runs it,
   and returns each test's record in the order given. With the compiler's
   results, each test that passes with nothing to show is kept there under
   the key of the code it can run, and is not built or run again until that
   code changes; with [rerun], every test runs, and passes are kept again.
   [progress] is told of each step as it happens. *)
val run_tests :
  ?rerun:bool ->
  ?progress:(progress -> unit) ->
  t ->
  time_limit:int ->
  Path.t list ->
  (record list, string) result

(* Builds, at [output], a program that runs tests that are instances made
   by hand, in order, as [run_tests] builds one of tests in source. It is
   for testing the runner on code no source compiles to, such as a test
   that leaves a block allocated. *)

(* Each test's key: the hash of the code it can run and of the build's
   added C flags, which changes exactly when the test's outcome may. A test
   that cannot be lowered has none. *)
val test_keys : t -> Path.t list -> (Path.t * string) list

(* A [todo] or an [echo] that a program can reach, which a release build
   refuses: its file and position, as the program would report them,
   and the definitions on the way from [main] to the one that holds it. *)
type unshippable = {
  failure : [ `Todo | `Echo ];
  file : string;
  line : int;
  column : int;
  way : Path.t list;
}

(* Every [todo] and [echo] the program whose [main] is at that path can
   reach, once each, in order of position. *)
val unshippable : t -> main:Path.t -> (unshippable list, string) result

(* A path in the compiler's directory of programs that no other program
   has, for a program to build. *)
val fresh_program : t -> string

(* Builds the program whose [main] is at that path into an executable at
   [output]. *)
val build_program : t -> main:Path.t -> output:string -> (unit, string) result

(* Builds the program whose [main] is at that path, and runs it with the
   arguments, and [input] as its standard input if given, returning its exit
   status, its output, and its errors. With [in_order], the program is
   linked with the runtime that starts no threads, as a test program is, so
   its tasks and [parallel] branches run sequentially. *)

(* The key a run of code while compiling is kept under: the hash of the
   code the root can reach, code generation's version, the target, and the
   build's added C flags, which changes exactly when the run's result
   may. *)
val run_key : t -> Instance.key -> (string, string) result

(* Evaluates a tagged template's check by running it: each of the tag's
   [from_template]'s clauses that can run, for a template of these literal
   texts and no parts, by its position among the clauses, with whether it
   holds. The prover asks it only of clauses that read the template's
   literals alone. *)
val check_template :
  t -> from_template:Path.t -> texts:string list -> ((int * bool) list ran, string) result

(* Evaluates a call of a function that is not generic, whose arguments are
   known integers, or [Bool]s as 0 or 1, by running it: its result as static
   data. *)
val evaluate_call :
  t -> function_:Path.t -> arguments:Z.t list -> (Lir.static_value ran, string) result

(** Code generation's own passes, for their tests. *)
module For_testing : sig
  module Lower : sig
    type context
    type constant = Lower.constant = Folded of Lir.data | Run of Ground.ty

    val context :
      ?checks:bool ->
      cursor_fields:(context -> Ground.yielding -> (string * Memory_layout.member) list) ->
      constant:(context -> Path.t -> Lir.static_value option) ->
      Query.context ->
      Memory_layout.target ->
      context

    val constant : context -> Path.t -> constant

    val constant_value : context -> Path.t -> Lir.static_value option
    (** Another constant's value, where it folds. *)
  end

  module Intrinsics = Intrinsics

  val parse_report : string -> (record list, string) result

  val build_supplied_tests :
    t ->
    time_limit:int ->
    (Memory_layout.env -> Emit_c.Builder.instance) list ->
    output:string ->
    (unit, string) result

  val compiled : t -> Instance.key -> Emit_c.fragment

  val run_program :
    ?input:string ->
    ?in_order:bool ->
    t ->
    main:Path.t ->
    arguments:string list ->
    (int * string * string, string) result
end
