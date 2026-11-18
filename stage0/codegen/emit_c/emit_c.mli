type profile = Development | Release
type linkage = External | Internal
type failure = C_runtime.failure = Echo | Todo

module Builder = Builder

val make_symbol : Lowered.Item.t -> string
val version : int

type fragment = Fragment.t

val make_data_fragment : Memory_layout.env -> Lowered.data -> fragment
val make_table_fragment : Memory_layout.env -> Lowered.table -> fragment
val item : fragment -> Lowered.Item.t
val references : fragment -> Lowered.Item.t list
val called : fragment -> Lowered.Item.t list
val list_linked : lookup:(Lowered.Item.t -> fragment) -> Lowered.Item.t list -> fragment list

val trace_reachable :
  lookup:(Lowered.Item.t -> fragment option) ->
  Lowered.Item.t list ->
  (fragment * Lowered.Item.t list) list

val is_small : fragment -> bool
val failures : fragment -> (failure * Lowered.site) list
val render_fragment : fragment -> string
val render_file : Memory_layout.env -> profile -> (fragment * linkage) list -> string
val shared_structs : string

type position = { file : string; line : int; column : int }

val render_sites_file : resolve_position:(Lowered.site -> position) -> fragment list -> string

module For_testing : sig
  val render_c : fragment -> string
end
