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

val roots : (lowering, Instance.key list) Query.input
val add_roots : Query.context -> lowering -> Instance.key list -> Instance.key list

type results = { find : string -> string option; add : string -> string -> unit }

(* The result of a run of code while compiling, or that it ran past the
   compiler's time limit. *)
type 'a ran = Ran of 'a | Ran_too_long

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

type progress =
  | Lowering
  | Compiling of { compiled : int; total : int }
  | Running of { tests : int }
  | Started of { test : int }
  | Ended of { test : int; record : record }

val run_tests :
  ?rerun:bool ->
  ?progress:(progress -> unit) ->
  t ->
  time_limit:int ->
  Path.t list ->
  (record list, string) result

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

val check_template :
  t -> from_template:Path.t -> texts:string list -> ((int * bool) list ran, string) result

(* Evaluates a call of a function that is not generic, whose arguments are
   known integers, or [Bool]s as 0 or 1, by running it: its result as static
   data. *)
val evaluate_call :
  t -> function_:Path.t -> arguments:Z.t list -> (Lowered.static_value ran, string) result

(** Code generation's own passes, for their tests. *)
module For_testing : sig
  module Lower : sig
    type context
    type constant = Lower.constant = Folded of Lowered.data | Run of Ground.ty

    val context :
      ?checks:bool ->
      cursor_fields:(context -> Ground.yielding -> (string * Memory_layout.member) list) ->
      constant:(context -> Path.t -> Lowered.static_value option) ->
      Query.context ->
      Memory_layout.target ->
      context

    val constant : context -> Path.t -> constant

    val constant_value : context -> Path.t -> Lowered.static_value option
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
