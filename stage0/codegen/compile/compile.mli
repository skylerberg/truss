module Lookups = Lookups

type unsupported = { construct : string; at : Lowered.site option }
type lowered

type requests = {
  settings : Lookups.settings;
  read_source : Path.file -> Source.t;
  interface : Interface.Lookups.t;
  mir : Mir.lookups;
  find_lowered : Instance.key -> (lowered, unsupported) result option;
  read_test_key : Instance.key -> (string, unsupported) result;
  list_reached_todo_types : Instance.key -> Path.t list;
}

exception Todo_type of Ground.ty
exception Infinite_size of Ground.ty

type t
type results = { find : string -> string option; add : string -> string -> unit }
type 'a ran = Ran of 'a | Ran_too_long | Stopped of string

val create :
  ?show_file:(Path.file -> string) ->
  ?results:results ->
  ?evaluation_time_limit_ms:int ->
  ?programs:string ->
  ?is_worked_on:(Path.package -> bool) ->
  requests ->
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
  output : string option;
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
  ?report_progress:(progress -> unit) ->
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

val list_unshippable : t -> main:Path.t -> unshippable list
val list_reached_definitions : t -> Path.t -> Path.t list
val list_reached_todo_types : t -> Path.t -> Path.t list
val make_program_path : t -> string
val build_program : t -> main:Path.t -> output:string -> (unit, string) result
val run_literal_check : t -> Instance.literal_check -> (bool list, string) result
val list_roots : tests:Path.t list -> mains:Path.t list -> Instance.key list
val lower : Lookups.settings -> Lookups.t -> Instance.key -> (lowered, unsupported) result
val list_references : lowered -> Instance.key list

val check_calls :
  Interface.Lookups.t ->
  find_call_edges:(Path.t -> Path.t list option) ->
  Instance.key ->
  lowered ->
  unit

val derive_test_keys :
  read_lowered:(Instance.key -> lowered) ->
  read_known_key:(Instance.key -> string) ->
  Instance.key list ->
  (Instance.key * string) list

module For_testing : sig
  val is_folded : t -> Path.t -> bool
  val make_lowered : Emit_c.fragment -> lowered

  module Intrinsics = Intrinsics

  val parse_report : string -> (record list, string) result

  val build_supplied_tests :
    t ->
    time_limit_ms:int ->
    (Memory_layout.env -> Emit_c.Builder.instance) list ->
    output:string ->
    (unit, string) result

  val compile_fragment : t -> Instance.key -> Emit_c.fragment

  val evaluate_call :
    t -> function_:Path.t -> arguments:Z.t list -> (Lowered.static_value ran, string) result

  val run_program :
    ?input:string ->
    t ->
    main:Path.t ->
    arguments:string list ->
    (int * string * string, string) result

  val drop_and_copy : Memory_layout.env -> Drop_and_copy.t
  val is_trivial : Drop_and_copy.t -> Ground.ty -> bool
  val drop : Drop_and_copy.t -> Ground.ty -> Emit_c.Builder.instance
  val copy : Drop_and_copy.t -> Ground.ty -> Emit_c.Builder.instance
  val copy_signature : Drop_and_copy.t -> Ground.ty -> Lowered.signature
end
