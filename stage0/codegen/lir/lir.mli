(* The lowered IR: a small typed control-flow graph for each instance, which
   drop elaboration and yield lowering transform and the C emitter prints.
   See CODEGEN.md, "The lowered IR".

   Locals are mutable slots, not SSA. Every choice about how a value is
   passed is already explicit: a parameter that arrives as a pointer has a
   [Pointer] type, an argument passed by address is an [Address] operand,
   and a result too large to return comes back through a pointer parameter.
   The emitter only prints. *)

type local = int
type block = int

(* The type of a local, a parameter, or a result. *)
type ty =
  | Value of Ground.ty
  | Pointer of { target : ty; writable : bool }
      (** A [restrict] pointer: to a [mut] or large parameter, or to a part of one *)
  | Raw of Memory_layout.scalar  (** A scalar no Truss type names, such as a drop flag *)
  | Environment of int
      (** The environment [struct] of nested function [n] of this instance, whose fields its
          [environment] lists *)

(* A place: a local or a constant's static data, then fields, elements, and
   dereferences. *)
type root = Local of local | Static of { key : Instance.key; ty : Ground.ty }

type place = { root : root; projections : projection list }

and projection =
  | Field of string  (** A record's field *)
  | Variant_field of { variant : string; field : string }
      (** A field of a sum type's variant, which must be the variant the value holds. For an
          [indirect] variant this reaches into its block. *)
  | Index of operand  (** An element of an [Array] or of the buffer a pointer points at *)
  | Deref

and operand =
  | Copy of place  (** For a value that copies implicitly *)
  | Move of place  (** Leaves the place with nothing to drop *)
  | Constant of constant
  | Address of { place : place; writable : bool }

and constant =
  | Integer of Memory_layout.integer * Z.t
  | Float32 of int32  (** The bits *)
  | Float64 of int64  (** The bits *)
  | Bool of bool
  | Character of int
  | Bytes of string  (** The address of static bytes, such as a string literal's *)
  | Null

and function_ref =
  | Instance of Instance.key
  | Nested of int  (** A lambda or loop body of this instance *)

(* How a function is called, which the caller needs to declare it. *)
type signature = { parameters : ty list; result : ty option; returns : bool }
(** [returns] is false for a function whose result type is [Never] *)

type unary = Negate | Not | Complement

type binary =
  | Add
  | Subtract
  | Multiply
  | Divide
  | Remainder
  | Bit_and
  | Bit_or
  | Bit_xor
  | Shift_left  (** The amount is masked to the width of the value *)
  | Shift_right  (** Arithmetic on signed integers, logical on unsigned *)
  | Equal  (** On floats, every NaN equals every NaN, as DESIGN.md's lawful equality says *)
  | Not_equal
  | Less  (** On floats, NaN comes after every number *)
  | Less_equal
  | Greater
  | Greater_equal
  | Ieee_equal  (** The IEEE comparisons, on floats only *)
  | Ieee_less
  | Ieee_less_equal

(* The operations the intrinsic module lowers to directly. See CODEGEN.md,
   "The system interface". Operating-system calls are added with the
   standard library's real implementations. *)
type intrinsic =
  | Allocate
      (** [(size: USize, alignment: USize) -> pointer]; ends the process when memory runs out *)
  | Reallocate  (** [(pointer, old size, new size, alignment) -> pointer] *)
  | Free  (** [(pointer)] *)
  | Copy_bytes  (** [(destination, source, count)], which must not overlap *)
  | Move_bytes  (** [(destination, source, count)] *)
  | Compare_bytes  (** [(first, second, count) -> Int32] *)
  | Add_overflow  (** [(left, right, result pointer) -> Bool], true when it overflowed *)
  | Subtract_overflow
  | Multiply_overflow
  | Leading_zeros
  | Trailing_zeros
  | Count_ones
  | Swap_bytes
  | Rotate_left
  | Rotate_right
  | Multiply_high  (** The upper half of the full-width product *)
  | Square_root
  | Fused_multiply_add
  | Floor
  | Ceiling
  | Truncate
  | Round_even
  | Float_bits  (** A float's bits, with every NaN replaced by one canonical NaN *)
  | Float_from_bits
  | Grow
      (** [(buffer pointer's address, length, capacity's address, element size, alignment, minimum)]:
          gives storage room for at least [minimum] elements. Storage with capacity 0 and a nonzero
          length is static, and is copied to the heap, never freed. *)
  | System_write  (** [(descriptor, bytes, count) -> ISize], -1 on error *)
  | System_read  (** [(descriptor, bytes, count) -> ISize], -1 on error *)
  | Clock_now  (** [() -> Int64], nanoseconds since the Unix epoch *)
  | Random_fill  (** [(bytes, count)] *)

type target =
  | Direct of { function_ : function_ref; signature : signature }
  | Indirect of { value : operand; signature : signature }
      (** A call through a function value: its code with its environment first *)
  | Intrinsic of intrinsic

type rvalue =
  | Use of operand
  | Unary of unary * operand
  | Binary of binary * operand * operand
  | Convert of operand * Memory_layout.scalar
      (** A conversion between built-in numbers, which the type checker or the prover has shown
          keeps the value *)
  | Build of { ty : Ground.ty; variant : string option; fields : (string * operand) list }
      (** A record or a variant. Building an [indirect] variant allocates its block. *)
  | Is_variant of place * string  (** Whether a sum type's value holds the variant *)
  | Function_value of { code : function_ref; environment : operand option }

(* A position within a definition, which the definition's anchor turns into
   a file and line. See CODEGEN.md, "Positions". It names its definition,
   rather than taking the instance's, because code can come from another
   definition: a trait's provided method compiled for an [impl] reports
   positions in the trait. *)
type site = { definition : Path.t; line : int; column : int }

(* Why a [fail] ends the run: a panic, a failed [assert] in a test, or a
   [todo] that was reached. *)
type failure = Panic | Assertion | Todo

type statement =
  | Assign of place * rvalue
  | Call of { target : target; arguments : operand list; result : place option }
  | Drop of place  (** Runs the type's drop code *)
  | Echo of { text : operand; length : operand; site : site }
      (** Records the debug output of a value: a pointer to UTF-8 bytes and their length *)
  | Free_block of { place : place; variant : string }
      (** Frees the block of an [indirect] variant whose fields have all been moved out or dropped
      *)

type terminator =
  | Goto of block
  | Switch of { value : operand; cases : (Z.t * block) list; default : block option }
      (** On an integer, a [Bool], or a [Character]; with no default, the cases cover every value *)
  | Switch_variant of { place : place; cases : (string * block) list; default : block option }
  | Return of operand option
  | Unreachable  (** A point the prover has shown is never reached *)
  | Fail of { failure : failure; message : operand; length : operand; site : site }
      (** Ends a test or the process: the message is a pointer to UTF-8 bytes and their length *)
  | Yield of { value : operand; resume : block; stop : block option }
      (** Before yield lowering only. [stop] runs when the caller leaves the loop at this [yield]; a
          lending method's [yield] has none, since it always continues. *)

type basic_block = { statements : statement list; terminator : terminator }
type local_info = { ty : ty; name : string option }

type function_ = {
  parameters : local list;  (** Locals that arrive as the parameters, in order *)
  result : ty option;
  returns : bool;
  locals : local_info array;
  blocks : basic_block array;  (** Block 0 is the entry *)
  environment : (string * ty) list;
      (** For a nested function, the fields of its environment: a pointer to each local of the
          function around it that it reads, and for a loop body the slots it reports through *)
}

type t = { key : Instance.key; main : function_; nested : function_ array }

val signature : function_ -> signature

(* The type of a projection of a place of the given type, or [None] where it
   has zero size and so is erased. [environment] gives the fields of a
   nested function's environment. Raises [Invalid_argument] for a projection
   that does not fit the type, which is a compiler bug. *)
val projection_type :
  Memory_layout.env -> environment:(int -> (string * ty) list) -> ty -> projection -> ty option

(* The type of a place in a function, or [None] where it has zero size. *)
val place_type :
  Memory_layout.env -> environment:(int -> (string * ty) list) -> function_ -> place -> ty option

(* A statement or terminator with every place rewritten by [place], each
   after the places inside its indexes, and every block number by [block]. *)
val map_statement : place:(place -> place) -> block:(block -> block) -> statement -> statement
val map_terminator : place:(place -> place) -> block:(block -> block) -> terminator -> terminator

(* The blocks a terminator may go to, in order. *)
val successors : terminator -> block list

(* The same function in canonical form: blocks in reverse postorder from
   the entry, with unreachable blocks removed, and locals numbered with the
   parameters first and then by first use, with unused locals removed. Two
   lowerings of one definition that differ only in numbering give equal
   canonical forms. *)
val canonical : function_ -> function_
val canonical_instance : t -> t

(* The version of code generation, part of every key built from the LIR. *)
val version : int

(* The canonical encoding, in deterministic CBOR. Each path, in a type or a
   site, is written by [path], and each reference to another instance by
   [instance], which by default encode them; test keys pass ones that
   number them instead, so that no name is in them. See CODEGEN.md, "Test
   results". *)
val encode : ?path:(Path.t -> Cbor.t) -> ?instance:(Instance.key -> Cbor.t) -> t -> Cbor.t

(* The BLAKE3 hash of the canonical form's encoding and [version], which
   early cutoff compares. *)
val hash : t -> string

(* A compact text form, for tests. *)
val to_string : t -> string
val function_to_string : function_ -> string
