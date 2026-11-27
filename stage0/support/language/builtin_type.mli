type t =
  | Int8
  | Int16
  | Int32
  | Int64
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | Float32
  | Float64
  | Bool
  | Character
  | Unit
  | Never
  | Integer
  | Array
  | Storage
  | View
  | Handle
  | Shared

val all : t list
val show : t -> string
val find_scalar_literal : t -> string -> int option
