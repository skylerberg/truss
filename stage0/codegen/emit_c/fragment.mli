type kind =
  | Functions of { nested : int; weight : int }
  | Static_data
  | Table_entries of Path.t option

type t = {
  item : Lowered.Item.t;
  kind : kind;
  functions : (string * string) list;
  definition : string;
  types : C_types.key list;
  environments : (C_types.key * C_types.defined) list;
  prototypes : (string * string) list;
  statics : string list;
  sites : Lowered.site list;
  helpers : string list;
  references : Lowered.Item.t list;
  calls : (Path.t * int) list;
  called : Lowered.Item.t list;
  failures : (C_runtime.failure * Lowered.site) list;
}

val iter_identifiers : string -> on_identifier:(string -> unit) -> on_other:(char -> unit) -> unit

val make :
  C_types.context ->
  item:Lowered.Item.t ->
  kind:kind ->
  functions:(string * string) list ->
  definition:string ->
  t
