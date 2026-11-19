type key =
  | Type of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Environment of Lowered.Item.t * int
  | Evidence of int
  | Capabilities of int

type reference =
  | Item of Lowered.Item.t
  | Type_name of key
  | Site of Lowered.site
  | Local of Lowered.local
  | Byte_constant of int
  | Nested_function of int
  | Static of int
  | Helper of C_runtime.helper
  | Capability of Path.t

type t =
  | Text of string
  | Name of reference
  | Concat of t list
  | Line_control of Lowered.site option

type segment = { site : Lowered.site option; text : string }

val empty : t
val ( ++ ) : t -> t -> t
val join : string -> t list -> t
val render_braces : t list -> t
val render_key_name : key -> string
val render : t -> resolve:(reference -> string) -> string
val render_segments : t -> site:Lowered.site option -> resolve:(reference -> string) -> segment list
