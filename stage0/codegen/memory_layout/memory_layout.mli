type integer = Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64

type pointee =
  | Data of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Opaque

type scalar =
  | Integer of integer
  | Float32
  | Float64
  | Bool
  | Character
  | Pointer of pointee
  | Nullable_pointer of pointee

type member = Typed of Ground.ty | Raw of scalar

type shape =
  | Scalar of scalar
  | Record of (string * member) list
  | Sum of variant_shape list
  | Array of Ground.ty * int

and variant_shape = { name : string; indirect : bool; fields : (string * member) list }

type representation = Shape of shape | Storage of Ground.ty | Handle | Shared of Ground.ty

type t = { size : int; alignment : int; form : form; niche : niche option }

and form =
  | Zero_size
  | Scalar of scalar
  | Struct of field list
  | Array of { element : Ground.ty; element_layout : t; count : int }
  | Tag_only of { tag : integer; variants : string list }
  | Tagged of { tag : integer; payload_offset : int; variants : variant list }
  | Niche_encoded of { dataful : variant; others : (string * Z.t) list; encoding : niche option }

and field = { name : string; member : member; layout : t; offset : int }
and variant = { name : string; index : int; payload : t }
and niche = { path : step list; scalar : scalar; start : Z.t; count : Z.t }
and step = Field of string | Tag

type env

val create : Libc.system -> shape_of:(Ground.ty -> shape) -> env
val system : env -> Libc.system
val shape : env -> Ground.ty -> shape
val of_type : env -> Ground.ty -> t
val has_zero_size : env -> Ground.ty -> bool
val block : env -> Ground.ty -> string -> t
val scalar_size : scalar -> int
val integer_size : integer -> int
val integer_range : integer -> Z.t * Z.t

type discriminant = Only | Tag_value of Z.t | Niche_value of Z.t | Not_niche

val discriminant : t -> string -> discriminant

module For_testing : sig
  val to_string : t -> string
end
