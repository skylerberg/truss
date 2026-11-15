type build = Development | Release
type linkage = External | Internal
type site = C_runtime.site = { definition : Path.t; line : int; column : int }
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
val anchors : fragment -> Path.t list
val failures : fragment -> (failure * site) list
val text : fragment -> string
val file : Memory_layout.env -> build -> (fragment * linkage) list -> string
val anchor_struct : string
val runtime_declarations : string
val anchor_symbol : Path.t -> string

module For_testing : sig
  val c : fragment -> string
end
