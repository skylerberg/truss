type profile = Development | Release
type linkage = External | Internal
type failure = C_runtime.failure = Echo | Todo

module Builder = Builder

type compiled = Code of Builder.instance | Data of Lowered.data | Table of Lowered.table

val version : int

type fragment

val make_fragment : Memory_layout.env -> compiled -> fragment
val key : fragment -> Instance.key
val references : fragment -> Instance.key list
val called : fragment -> Instance.key list
val list_linked : lookup:(Instance.key -> fragment) -> Instance.key list -> fragment list

val trace_reachable :
  lookup:(Instance.key -> fragment option) ->
  Instance.key list ->
  (fragment * Instance.key list) list

val is_small : fragment -> bool
val failures : fragment -> (failure * Lowered.site) list
val render_fragment : fragment -> string
val render_file : Memory_layout.env -> profile -> (fragment * linkage) list -> string
val site_struct : string

type position = { file : string; line : int; column : int }

val render_sites_file : resolve_position:(Lowered.site -> position) -> fragment list -> string

module For_testing : sig
  val render_c : fragment -> string
end
