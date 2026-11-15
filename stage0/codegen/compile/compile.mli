module Lookups = Lookups

type unsupported = { construct : string; at : Lowered.site option }
type lowered
type ground_types = { types : Ground.ty list; folded_constants : Path.t list }

type requests = {
  settings : Lookups.settings;
  source : Path.file -> Source.t;
  interface : Interface.Lookups.t;
  mir : Mir.lookups;
  lowered : Instance.key -> (lowered, unsupported) result;
  test_key : Instance.key -> (string, unsupported) result;
  layouts : Instance.key list -> Ground.ty -> Memory_layout.t;
}

type t
type results = { find : string -> string option; add : string -> string -> unit }
type 'a ran = Ran of 'a | Ran_too_long

val create :
  ?file_name:(Path.file -> string) ->
  ?results:results ->
  ?evaluation_time_limit_ms:int ->
  ?programs:string ->
  ?worked_on:(Path.package -> bool) ->
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

val roots : tests:Path.t list -> mains:Path.t list -> Instance.key list
val ground_types : Lookups.settings -> Lookups.t -> Instance.key -> ground_types

val lower :
  Lookups.settings ->
  Lookups.t ->
  layout_of:(Ground.ty -> Memory_layout.t) ->
  lowered:(Instance.key -> (lowered, unsupported) result) ->
  Instance.key ->
  (lowered, unsupported) result

val references : lowered -> Instance.key list

val check_calls :
  Interface.Lookups.t ->
  successors:(Path.t -> Path.t list option) ->
  Instance.key ->
  lowered ->
  unit

val test_keys :
  lowered:(Instance.key -> lowered) ->
  known:(Instance.key -> string) ->
  Instance.key list ->
  (Instance.key * string) list

val layout :
  Interface.Lookups.t -> layout_of:(Ground.ty -> Memory_layout.t) -> Ground.ty -> Memory_layout.t

val stored_in_place : Interface.Lookups.t -> Ground.ty -> Ground.ty list

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

  val evaluate_call :
    t -> function_:Path.t -> arguments:Z.t list -> (Lowered.static_value ran, string) result

  val run_program :
    ?input:string ->
    t ->
    main:Path.t ->
    arguments:string list ->
    (int * string * string, string) result
end
