type linkage = External | Internal
type failure = C_runtime.failure = Echo | Todo

module Ir_builder = Ir_builder

val make_symbol : Lowered.Item.t -> string
val version : int

type fragment = Fragment.t

val make_data_fragment : Memory_layout.env -> Lowered.data -> fragment
val make_table_fragment : Memory_layout.env -> Lowered.table -> fragment
val item : fragment -> Lowered.Item.t
val references : fragment -> Lowered.Item.t list
val called : fragment -> Lowered.Item.t list
val sites : fragment -> Lowered.site list

val trace_reachable :
  lookup:(Lowered.Item.t -> fragment option) ->
  Lowered.Item.t list ->
  (fragment * Lowered.Item.t list) list

val failures : fragment -> (failure * Lowered.site) list
val hash : fragment -> string

type position = { file : string; line : int; column : int }

val render_file :
  Memory_layout.env ->
  Profile.t ->
  resolve_position:(Lowered.site -> position) ->
  (fragment * linkage) list ->
  string

val render_unit :
  Memory_layout.env ->
  Profile.t ->
  resolve_position:(Lowered.site -> position) ->
  is_worked_on:(Path.package -> bool) ->
  find_fragment:(Lowered.Item.t -> fragment option) ->
  fragment ->
  string

val shared_structs : string
val render_sites_file : resolve_position:(Lowered.site -> position) -> Lowered.site list -> string

module For_testing : sig
  val render_c : fragment -> string
end
