val encode_entry :
  source:int ->
  module_:Path.module_ ->
  file_name:string ->
  int ->
  Resolve.Names.entry ->
  Store.entry

type impl_entry = { declared_in : Path.module_; entry : (Path.t * Path.t) * Path.t }

val make_lookups :
  Store.t ->
  note:(Kind.lookup -> int -> string -> unit) ->
  is_package:(Path.package -> bool) ->
  list_dependency_names:(Path.package -> Path.package list) ->
  Resolve.Names.lookups

type change = { lookup : Kind.lookup; scope : int; name : string; is_spans_only : bool }

val list_replaced_lookups :
  Store.t ->
  before:Store.schema option ->
  after:Store.schema option ->
  (Kind.lookup * int * string) list

type written = {
  changes : change list;
  added : Store.definition list;
  removed : Store.definition list;
}

val written_origin : int
val derived_impl_origin : int
val inherited_method_origin : int
val derived_method_origin : int

val encode_supplied :
  origin:int ->
  kind:Resolve.Names.kind ->
  Resolve.Names.key ->
  supplied_from:int ->
  container:int option ->
  Store.definition

val decode_key : string -> Resolve.Names.key
val decode_file : string -> Path.file
val decode_kind : int -> Resolve.Names.kind
val rank_kind : Resolve.Names.kind -> int

val write_module :
  Store.t ->
  Path.module_ ->
  files:(Path.file * string) list ->
  Resolve.Namespace.module_declarations ->
  written
