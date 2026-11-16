type build = Development | Release
type linkage = External | Internal
type failure = C_runtime.failure = Echo | Todo

module Builder = Builder

type compiled = Code of Builder.instance | Data of Lowered.data | Table of Lowered.table

val version : int

type fragment

val fragment : Memory_layout.env -> compiled -> fragment
val key : fragment -> Instance.key
val references : fragment -> Instance.key list
val calls : fragment -> (Path.t * int) list
val called : fragment -> Instance.key list
val table : fragment -> Path.t option option
val is_small : fragment -> bool
val failures : fragment -> (failure * Lowered.site) list
val text : fragment -> string
val file : Memory_layout.env -> build -> (fragment * linkage) list -> string
val site_struct : string

type position = { file : string; line : int; column : int }

val sites_file : position:(Lowered.site -> position) -> fragment list -> string

module For_testing : sig
  val c : fragment -> string
end
