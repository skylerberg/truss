(* The lowered IR's types. *)

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
  | Evidence of int
      (** Evidence a [provide] builds on the stack, with room for [n] pointers to the evidence its
          implementation captured *)

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
  | Moved_address of place
      (** The address of a place whose value the callee takes, for a large [own] argument: the place
          holds nothing after the call *)

and constant =
  | Integer of Memory_layout.integer * Z.t
  | Float32 of int32  (** The bits *)
  | Float64 of int64  (** The bits *)
  | Bool of bool
  | Character of int
  | Bytes of string  (** The address of static bytes, such as a string literal's *)
  | Null
  | Symbol_address of Instance.key  (** The address of static evidence or a table *)
  | Size_of of Ground.ty  (** A [USize]: how many bytes a value of the type takes *)
  | Alignment_of of Ground.ty  (** A [USize]: the alignment of a value of the type *)

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
  | Equal  (** On floats, every NaN equals every NaN *)
  | Not_equal
  | Less  (** On floats, NaN comes after every number *)
  | Less_equal
  | Greater
  | Greater_equal
  | Ieee_equal  (** The IEEE comparisons, on floats only *)
  | Ieee_less
  | Ieee_less_equal

(* The operations the intrinsic module lowers to directly. Operating-system
   calls are added with the standard library's real implementations. *)
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
  | System_environment
      (** [(name, name length, value length's address) -> bytes]: an environment variable's value,
          null when it is unset *)
  | System_open
      (** [(path, path length, flags, error's address) -> Int32]: a descriptor, -1 with the error
          number written when it fails *)
  | System_run
      (** [(program, length, arguments, length, error's address) -> Int32]: as [run_process] *)
  | Float_text
      (** [(value, bytes) -> USize]: writes the shortest decimal that reads back as the float, at
          most [float_text_limit] bytes, as [Display] shows it *)
  | Clock_now  (** [() -> Int64], nanoseconds since the Unix epoch *)
  | Random_fill  (** [(bytes, count)] *)
  | Debug_begin  (** Empties the debug output buffer *)
  | Debug_text  (** [(bytes, count)]: appends text as it is *)
  | Debug_signed  (** [(Int64)] *)
  | Debug_unsigned  (** [(UInt64)] *)
  | Debug_float32
  | Debug_float64  (** The shortest decimal that reads back as the same float *)
  | Debug_bool
  | Debug_character  (** As [Character"x"] *)
  | Debug_string  (** [(bytes, count)]: as a quoted string with escapes *)
  | Debug_bytes  (** [() -> pointer] to the buffer's bytes *)
  | Debug_length  (** [() -> USize] *)
  | Evidence_implementation  (** [(evidence) -> pointer] to the value that implements it *)
  | Evidence_outer  (** [(evidence, index) -> evidence] the implementation captured *)
  | Program_argument
      (** [(arguments, index, length pointer) -> bytes]: a program argument as UTF-8, with bad
          sequences replaced by U+FFFD *)
  | Evidence_fill
      (** [(evidence's address, implementation, table, captured evidence...)]: fills evidence a
          [provide] builds *)

let float_text_limit = 32

type target =
  | Direct of { function_ : function_ref; signature : signature }
  | Indirect of { value : operand; signature : signature }
      (** A call through a function value: its code, given its environment first *)
  | Intrinsic of intrinsic
  | Foreign of Libc.declaration
      (** A function of the C library, given each argument converted to its parameter's C type *)
  | Evidence_call of { evidence : operand; slot : int; signature : signature }
      (** A capability's method: entry [slot] of the evidence's table, given the evidence first *)
  | Table_call of { table : operand; value : operand; slot : int; signature : signature }
      (** Entry [slot] of a table of code, such as an [any] value's, given the value first *)

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
   a file and line. It names its definition, rather than taking the
   instance's, because code can come from another definition: a trait's
   provided method compiled for an [impl] reports positions in the trait. *)
type site = { definition : Path.t; line : int; column : int }

(* Why a [fail] ends the run: a panic, a failed [assert] in a test, or a
   [todo] that was reached. *)
type failure = Panic | Assertion | Todo

(* Where a call's result goes. A target that is given something first, such
   as a function value's environment, is given it before the result's
   pointer. *)
type destination =
  | Discarded  (** There is no result, or nothing reads it *)
  | Returned of place  (** Returned by value, and written to the place *)
  | Written of place
      (** Written by the callee through a pointer to the place, the call's first argument, for a
          result too large to return *)

type statement =
  | Assign of place * rvalue
  | Call of { target : target; arguments : operand list; result : destination }
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

type local_info = {
  ty : ty;
  name : string option;
  borrowed : bool;
      (** Holds the bits of a value that something else owns, as a read-only parameter passed by
          value does: nothing here drops it *)
}

type function_ = {
  parameters : local list;  (** Locals that arrive as the parameters, in order *)
  written_result : local option;
      (** The parameter pointing to where a result too large to return is written, which holds no
          value until the function writes it *)
  result : ty option;
  returns : bool;
  locals : local_info array;
  blocks : basic_block array;  (** Block 0 is the entry *)
  environment : (string * ty) list;
      (** For a nested function, the fields of its environment: a pointer to each local of the
          function around it that it reads, and for a loop body the slots it reports through *)
}

type t = { key : Instance.key; main : function_; nested : function_ array }

(* Static data: a constant's value, which the emitter writes as C
   initializers in a read-only place. *)
type static_value =
  | Static_scalar of constant
  | Static_record of (string * static_value) list
  | Static_variant of string * (string * static_value) list
  | Static_array of static_value list
  | Static_storage of { element : Ground.ty; elements : static_value list; owned : bool }
      (** Elements in static memory, with the capacity recorded as the length when [owned], and as 0
          otherwise, as for a string's static bytes *)

type data = { data_key : Instance.key; ty : Ground.ty; value : static_value }

(* A capability [impl]'s table: its entries, in the order of the
   capability's methods. *)
type table = { table_key : Instance.key; entries : (Instance.key * signature) list }

(* Static evidence: its implementation, a value of zero size here, its
   table, and the evidence the implementation captured. *)
type evidence = { evidence_key : Instance.key; table : Instance.key; outer : Instance.key list }

(* What an instance compiles to: code, static data, a table of entries, or
   static evidence. *)
type compiled = Code of t | Data of data | Table of table | Evidence of evidence
