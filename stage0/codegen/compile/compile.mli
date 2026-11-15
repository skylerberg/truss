module Lookups = Lookups

type t
type results = { find : string -> string option; add : string -> string -> unit }
type 'a ran = Ran of 'a | Ran_too_long

val create :
  ?checks:bool ->
  ?file_name:(Path.file -> string) ->
  ?results:results ->
  ?evaluation_time_limit_ms:int ->
  ?programs:string ->
  ?worked_on:(Path.package -> bool) ->
  Lookups.t ->
  Libc.system ->
  Toolchain.t ->
  Build.cache ->
  Build.settings ->
  t

type outcome = Passed | Failed | Panicked | Incomplete | Timed_out | Crashed

val show_outcome : outcome -> string

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
  time_limit_ms:int ->
  Path.t list ->
  (record list, string) result

type unshippable = {
  failure : [ `Todo | `Echo ];
  file : string;
  line : int;
  column : int;
  way : Path.t list;
}

val unshippable : t -> main:Path.t -> (unshippable list, string) result
val reached_definitions : t -> main:Path.t -> (Path.t list, string) result
val fresh_program : t -> string
val build_program : t -> main:Path.t -> output:string -> (unit, string) result

val check_template :
  t -> from_template:Path.t -> texts:string list -> ((int * bool) list ran, string) result

val evaluate_call :
  t -> function_:Path.t -> arguments:Z.t list -> (Lowered.static_value ran, string) result

module For_testing : sig
  val is_folded : t -> Path.t -> bool

  module Intrinsics = Intrinsics

  val parse_report : string -> (record list, string) result

  val build_supplied_tests :
    t ->
    time_limit_ms:int ->
    (Memory_layout.env -> Emit_c.Builder.instance) list ->
    output:string ->
    (unit, string) result

  val compiled : t -> Instance.key -> Emit_c.fragment

  val run_program :
    ?input:string ->
    t ->
    main:Path.t ->
    arguments:string list ->
    (int * string * string, string) result
end
