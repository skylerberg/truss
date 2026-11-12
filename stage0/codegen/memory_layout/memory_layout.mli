(* The memory layout of every ground type: its size, its alignment, where its
   fields go, how its variants are told apart, and which of its values are
   spare for an enclosing type to use.

   No program can observe a layout, so the compiler is free to choose it.
   The rules are: fields placed by alignment, largest first, then by name; sum types as a tag and a union of
   their variants; and niches that remove the tag where a field has spare
   values. *)

(* The target code is built for: the width of the pointers of the machine it runs
   on, the width of [USize] and [ISize], and the system whose C library it
   calls. The widths differ only for code built to run while compiling for
   a target whose [USize] is narrower than the host's pointers: such code
   runs on the host, with the target's [USize], so that it computes the
   target's results. *)
type target = { pointer_bytes : int; usize_bytes : int; system : Libc.system }

val target_64 : Libc.system -> target

type integer = Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64 | USize | ISize

(* A pointer's target, which matters only to the C that is emitted: a
   value of a type, the heap block of an [indirect] variant, code, or
   something the C does not name, such as an [any] value's contents. *)
type pointee =
  | Data of Ground.ty
  | Block of Ground.ty * string  (** The type and the variant's name *)
  | Code of Ground.function_type
  | Opaque

type scalar =
  | Integer of integer
  | Float32
  | Float64
  | Bool  (** One byte, 0 or 1 *)
  | Character  (** A [UInt32] no greater than [0x10FFFF] *)
  | Pointer of pointee  (** Never null *)
  | Nullable_pointer of pointee

(* A field holds a value of a Truss type, or a raw scalar that no Truss type
   names, such as the code pointer of a function value. *)
type member = Typed of Ground.ty | Raw of scalar

(* A type's shape, which the code that knows the type checker's type
   shapes provides, after substituting type arguments. Fields and variants
   are in declaration order. [Unit] and every record with no fields are
   [Record []]; [Never] is [Sum []]. *)
type shape =
  | Scalar of scalar
  | Record of (string * member) list
  | Sum of variant_shape list
  | Array of Ground.ty * int

and variant_shape = { name : string; indirect : bool; fields : (string * member) list }

(* How a type holds its value: inline as its shape, or as one of the
   built-in types whose drop and copy are not derived from fields. *)
type representation =
  | Shape of shape
  | Storage of Ground.ty  (** [Storage[Element]], the built-in buffer of elements *)
  | Handle  (** An operating system's descriptor, in a [descriptor] field, closed when dropped *)
  | Shared of Ground.ty
      (** A reference to a reference-counted heap block that holds a value of the type. The [value]
          field is the address of the value in the block. *)

type t = { size : int; alignment : int; form : form; niche : niche option }

and form =
  | Zero_size  (** No bytes: erased from parameters, fields, and locals *)
  | Scalar of scalar
  | Struct of field list
      (** A record, or a variant's fields: every field that has a size, in placement order *)
  | Array of { element : Ground.ty; element_layout : t; count : int }
  | Tag_only of { tag : integer; variants : string list }
      (** A sum type with no fields, numbered in order *)
  | Tagged of { tag : integer; payload_offset : int; variants : variant list }
      (** A tag, then a union of every variant's payload *)
  | Niche_encoded of { dataful : variant; others : (string * Z.t) list; encoding : niche option }
      (** The payload of the one variant with fields, whose spare values at [encoding] stand for the
          other variants, given with the value each one is stored as *)

and field = { name : string; member : member; layout : t; offset : int }

(* A variant's payload is its fields as a [Struct], [Zero_size] when it has
   none with a size, or for an [indirect] variant one pointer to its block. *)
and variant = { name : string; index : int; payload : t }

(* Spare values: [count] values starting at [start], as unsigned values of
   the scalar at [path], the steps from the start of the value to it: a
   field, or a tagged sum's tag. [[]] is the value itself. *)
and niche = { path : step list; scalar : scalar; start : Z.t; count : Z.t }
and step = Field of string | Tag

(* Computes layouts, each once, from the shapes [shape_of] gives. *)
type env

val create : target -> shape_of:(Ground.ty -> shape) -> env
val target : env -> target

(* A type's shape, from which the layouts are computed. *)
val shape : env -> Ground.ty -> shape
val of_type : env -> Ground.ty -> t

val has_zero_size : env -> Ground.ty -> bool
(** Whether values of a type take no bytes, so that code generation erases them. *)

(* The heap block of the [indirect] variant [variant] of [ty]: its fields as
   a [Struct]. Asked for separately, because a block may hold the type
   itself, which is why the variant is [indirect]. *)
val block : env -> Ground.ty -> string -> t
val scalar_size : target -> scalar -> int
val integer_size : target -> integer -> int

val integer_range : target -> integer -> Z.t * Z.t
(** The least and the greatest value of an integer kind on a target. *)

(* The index of a variant in a sum type's layout, and how it is told apart:
   by its tag value, or by the value stored at the niche. *)
type discriminant =
  | Only  (** The type has one variant, or none with a size: nothing to test *)
  | Tag_value of Z.t
  | Niche_value of Z.t
  | Not_niche  (** The dataful variant of a niche-encoded type: no other value is there *)

val discriminant : t -> string -> discriminant

(* A compact, one-line description, for tests. *)
val scalar_to_string : scalar -> string

module For_testing : sig
  val target_32 : Libc.system -> target
  val to_string : t -> string
end
