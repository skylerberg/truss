(** The module [standard::intrinsic], which exists in no source file. The compiler declares what is
    in it: the built-in types, whose rules no definition could state, and the operations the
    standard library is written on top of. See TYPECHECKER.md, "The prelude", and CODEGEN.md, "The
    system interface". Only the [standard] package can import it. *)

val module_ : Path.module_

type builtin =
  | Int8
  | Int16
  | Int32
  | Int64
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | USize
  | ISize
  | Float32
  | Float64
  | Bool
  | Character
  | Unit
  | Never
  | Integer  (** The mathematical integers, in specifications only. *)
  | Array  (** [Array[Element, count: USize]] *)

val builtins : builtin list
val builtin_name : builtin -> string
val builtin_path : builtin -> Path.t
val builtin_of_path : Path.t -> builtin option
