type profile = Profile.t = Development | Release
type t
type results = { find : string -> string option; add : string -> string -> unit }
type 'a ran = Ran of 'a | Unfinished of string | Stopped of string

val create :
  ?show_file:(Path.file -> string) ->
  ?results:results ->
  ?evaluation_cpu_time_limit_ms:int ->
  ?programs:string ->
  ?is_worked_on:(Path.package -> bool) ->
  Lowering.lowered_lookups ->
  C_compiler.t ->
  profile ->
  t

module Test_report : sig
  type outcome = Test_report.outcome =
    | Passed
    | Failed
    | Panicked
    | Incomplete
    | Timed_out
    | Crashed

  val show_outcome : outcome -> string

  type record = Test_report.record = {
    outcome : outcome;
    message : string option;
    echo : string option;
    output : string option;
    microseconds : int;
    cached : bool;
  }

  module For_testing : sig
    val parse : tests:int -> string -> (record list, string) result
    val list_records_by_piece : tests:int -> string list -> (int * record) list
  end
end

type progress =
  | Lowering
  | Compiling of { compiled : int; total : int }
  | Running of { tests : int }
  | Started of { test : int }
  | Ended of { test : int; record : Test_report.record }

val run_tests :
  ?rerun:bool ->
  ?report_progress:(progress -> unit) ->
  t ->
  time_limit_ms:int ->
  Path.t list ->
  (Test_report.record list, string) result

type location = { file : Path.file; line : int; column : int }
type unshippable = { failure : [ `Todo | `Echo ]; location : location; way : Path.t list }

val list_unshippable : Lowering.lowered_lookups -> main:Path.t -> unshippable list
val list_reached_definitions : Lowering.lowered_lookups -> Path.t -> Path.t list
val list_reached_todo_types : Lowering.lowered_lookups -> Path.t -> Path.t list
val make_program_path : t -> string
val build_program : t -> main:Path.t -> output:string -> is_kept:bool -> (unit, string) result
val evaluate : t -> Lowered.Item.t list -> Lowered.static_value ran list

module For_testing : sig
  val is_folded : t -> Path.t -> bool

  val build_supplied_tests :
    t ->
    time_limit_ms:int ->
    (Memory_layout.env -> Emit_c.fragment) list ->
    output:string ->
    (unit, string) result

  val compile_fragment : t -> Lowered.Item.t -> Emit_c.fragment
  val render_unit : t -> Lowered.Item.t -> string
  val count_built_programs : unit -> int
end
