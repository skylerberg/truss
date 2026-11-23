type t = {
  store : Store.t;
  records_reads : bool;
  bugs : (int * int, Compiler_bug.t) Hashtbl.t;
  broken : (int * int, unit) Hashtbl.t;
}

val create : Store.t -> records_reads:bool -> t
val with_failing_unit : ?raising:exn -> Kind.stage -> int -> (unit -> 'result) -> 'result
val fail_for_test : Kind.stage -> int list -> unit
val reset_broken : t -> unit
val is_broken : t -> Kind.stage -> int -> bool
val record_bug : t -> Kind.stage -> int list -> Compiler_bug.t -> unit

type recorder = { note : Kind.marker -> Kind.target -> int -> string -> unit }

val untracked : recorder
val locate : Kind.target -> int -> string -> Store.endpoint
val locate_unit : Kind.stage -> int -> Store.endpoint

type observation =
  | Computed of { stage : Kind.stage; ids : int list; reads : int; distinct_reads : int }
  | Unchanged of { stage : Kind.stage; id : int }
  | Written of { stage : Kind.stage; id : int; is_removal : bool }

val with_observer : (observation -> unit) -> (unit -> 'result) -> 'result
val record : t -> ?package:int -> Kind.stage -> int -> (recorder -> 'result) -> 'result

val record_observed :
  t ->
  ?package:int ->
  Kind.stage ->
  int ->
  (recorder -> 'result) ->
  'result * Store.edge_change list

val record_group :
  t -> Kind.stage -> int list -> own:Kind.fact list -> (recorder -> 'result) -> 'result

val mark_stale : t -> Kind.stage -> int -> unit
val mark_readers : t -> Kind.target -> int -> string -> unit
val mark_readers_of_all : t -> (Kind.target * int * string) list -> unit
val make_call_graph : visible:string list -> Store.call_graph
val mark_callers_to_group : t -> seeds:int list -> unit
val mark_position_holders : t -> Kind.target -> int -> string -> unit

type 'value outcome = Value of 'value | Failed | Blocked
type state = Has_value | Has_failed | Is_blocked

exception Reads_failed_fact

type 'value view

type 'value fact = {
  whole : 'value view;
  groups : (Kind.fact * int) list;
  encode : 'value -> Store.cell list;
}

type any_fact = Any : 'value fact -> any_fact

val guard_view :
  'value view ->
  stage:Kind.stage ->
  target:Kind.fact ->
  table:string ->
  id_column:string ->
  'value view

val make_fact :
  stage:Kind.stage ->
  table:string ->
  id_column:string ->
  fixed:(string * Store.cell) list ->
  groups:(Kind.fact * string list) list ->
  encode:('value -> Store.cell list) ->
  decode:(Store.cell array -> 'value) ->
  'value fact

val make_view :
  stage:Kind.stage ->
  table:string ->
  id_column:string ->
  fixed:(string * Store.cell) list ->
  target:Kind.fact ->
  columns:string list ->
  decode:(Store.cell array -> 'value) ->
  'value view

type description = { table : string; id_column : string; targets : Kind.fact list }

val describe : any_fact -> description
val marshal : 'value -> Store.cell
val unmarshal : Store.cell -> 'value
val find : t -> recorder -> 'value view -> Path.package -> id:int -> 'value outcome option
val find_settled : t -> recorder -> 'value view -> Path.package -> id:int -> 'value outcome option
val read : t -> recorder -> 'value view -> Path.package -> id:int -> 'value outcome
val read_value : t -> recorder -> 'value view -> Path.package -> id:int -> 'value
val find_value : t -> recorder -> 'value view -> Path.package -> id:int -> 'value option
val write : t -> 'value fact -> id:int -> 'value outcome option -> state option
val report : Kind.stage -> int -> is_changed:bool -> unit
val report_computed : Kind.stage -> int list -> unit
val list_facts : Kind.stage -> any_fact list
val forget : t -> Kind.stage -> int -> unit

val replace_file_diagnostics :
  t -> Kind.stage -> package:Path.package -> file:int -> Diagnostic.t list -> bool

val replace_placed_diagnostics :
  t ->
  Kind.stage ->
  package:Path.package ->
  unit:int ->
  (int * Diagnostic.in_definition) list ->
  bool

val replace_definition_diagnostics :
  t -> Kind.stage -> package:Path.package -> definition:int -> Diagnostic.in_definition list -> unit
