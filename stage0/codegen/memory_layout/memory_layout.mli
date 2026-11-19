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

type t = { size : int; alignment : int; form : form; niche : niche option }

and form =
  | Zero_size
  | Scalar of scalar
  | Struct of field list
  | Array of { element : Ground.ty; element_layout : t; count : int }
  | Tag_only of { tag : integer; variants : string list }
  | Tagged of { tag : integer; payload_offset : int; variants : variant list }
  | Niche_encoded of { dataful : variant; dataless : dataless option }

and field = { name : string; member : member; layout : t; offset : int }
and variant = { name : string; index : int; payload : t }
and dataless = { niche : niche; niche_values : (string * Z.t) list }
and niche = { path : step list; scalar : scalar; start : Z.t; count : Z.t }
and step = Field of string | Tag

type env

exception Infinite_size of Ground.ty

val create : Libc.system -> compute_shape:(Ground.ty -> shape) -> env
val system : env -> Libc.system
val compute_shape : env -> Ground.ty -> shape
val of_type : env -> Ground.ty -> t
val has_zero_size : env -> Ground.ty -> bool
val lay_out_block : env -> Ground.ty -> string -> t
val compute_scalar_size : scalar -> int
val compute_integer_size : integer -> int
val compute_integer_range : integer -> Z.t * Z.t

type tag = { at : step list; integer : integer }

type discriminant =
  | Only
  | Tag_value of { tag : tag; value : Z.t }
  | Niche_value of { niche : niche; value : Z.t }
  | Not_niche of { niche : niche; stop : Z.t }

type 'case dispatch =
  | Switch of { tag : tag; cases : (Z.t * 'case) list }
  | Tests of (discriminant * 'case) list

val compute_discriminant : t -> string -> discriminant
val dispatch : t -> (string * 'case) list -> 'case dispatch

module For_testing : sig
  val to_string : t -> string
end
