type local = int
type block = int

type ty = Ir_types.ty =
  | Value of Ground.ty
  | Pointer of { target : ty; writable : bool }
  | Raw of Memory_layout.scalar
  | Environment of int
  | Evidence of int

type root = Ir_types.root = Local of local | Static of { key : Instance.key; ty : Ground.ty }

type place = Ir_types.place = { root : root; projections : projection list }

and projection = Ir_types.projection =
  | Field of string
  | Variant_field of { variant : string; field : string }
  | Index of operand
  | Deref

and operand = Ir_types.operand =
  | Copy of place
  | Move of place
  | Constant of constant
  | Address of { place : place; writable : bool }
  | Moved_address of place

and constant = Ir_types.constant =
  | Integer of Memory_layout.integer * Z.t
  | Float32 of int32
  | Float64 of int64
  | Bool of bool
  | Character of int
  | Bytes of string
  | Null
  | Symbol_address of Instance.key
  | Size_of of Ground.ty
  | Alignment_of of Ground.ty

and function_ref = Ir_types.function_ref = Instance of Instance.key | Nested of int

type signature = Ir_types.signature = { parameters : ty list; result : ty option; returns : bool }
type unary = Ir_types.unary = Negate | Not | Complement

type binary = Ir_types.binary =
  | Add
  | Subtract
  | Multiply
  | Divide
  | Remainder
  | Bit_and
  | Bit_or
  | Bit_xor
  | Shift_left
  | Shift_right
  | Equal
  | Not_equal
  | Less
  | Less_equal
  | Greater
  | Greater_equal
  | Ieee_equal
  | Ieee_less
  | Ieee_less_equal

type intrinsic = Ir_types.intrinsic =
  | Allocate
  | Reallocate
  | Free
  | Copy_bytes
  | Move_bytes
  | Compare_bytes
  | Add_overflow
  | Subtract_overflow
  | Multiply_overflow
  | Leading_zeros
  | Trailing_zeros
  | Count_ones
  | Swap_bytes
  | Rotate_left
  | Rotate_right
  | Multiply_high
  | Square_root
  | Fused_multiply_add
  | Floor
  | Ceiling
  | Truncate
  | Round_even
  | Float_bits
  | Float_from_bits
  | Run_test
  | Report_tests_to
  | Live_blocks
  | Environment
  | Terminated_length
  | Evidence_implementation
  | Evidence_outer
  | Program_argument
  | Evidence_fill
  | Coroutine_start
  | Coroutine_resume
  | Coroutine_suspend
  | Tasks_spawn
  | Shared_allocate
  | Shared_retain
  | Shared_release
  | Shared_free
  | Shared_lock
  | Shared_unlock
  | Blocking_begin
  | Blocking_end

type target = Ir_types.target =
  | Direct of { function_ : function_ref; signature : signature }
  | Indirect of { value : operand; signature : signature }
  | Intrinsic of intrinsic
  | Foreign of Libc.declaration
  | Evidence_call of { evidence : operand; capability : Path.t; slot : int; signature : signature }
  | Table_call of { table : operand; value : operand; slot : int; signature : signature }

type rvalue = Ir_types.rvalue =
  | Use of operand
  | Unary of unary * operand
  | Binary of binary * operand * operand
  | Convert of operand * Memory_layout.scalar
  | Build of { ty : Ground.ty; variant : string option; fields : (string * operand) list }
  | Is_variant of place * string
  | Function_value of { code : function_ref; environment : operand option }

type site = Ir_types.site = { definition : Path.t; line : int; column : int }
type failure = Ir_types.failure = Panic | Assertion | Todo
type destination = Ir_types.destination = Discarded | Returned of place | Written of place

type statement = Ir_types.statement =
  | Assign of place * rvalue
  | Call of { target : target; arguments : operand list; result : destination }
  | Drop of place
  | Echo of { text : operand; length : operand; site : site }
  | Free_block of { place : place; variant : string }
  | Fork of { branches : (int * operand) list }
  | Fork_range of { body : int; environment : operand; first : operand; last : operand }

type terminator = Ir_types.terminator =
  | Goto of block
  | Switch of { value : operand; cases : (Z.t * block) list; default : block option }
  | Switch_variant of { place : place; cases : (string * block) list; default : block option }
  | Return of operand option
  | Unreachable
  | Fail of { failure : failure; message : operand; length : operand; site : site }

type basic_block = Ir_types.basic_block = { statements : statement list; terminator : terminator }
type local_info = Ir_types.local_info = { ty : ty; name : string option }

type function_ = Ir_types.function_ = {
  parameters : local list;
  written_result : local option;
  result : ty option;
  returns : bool;
  locals : local_info array;
  blocks : basic_block array;
  environment : (string * ty) list;
}

type t = Ir_types.t = { key : Instance.key; main : function_; nested : function_ array }

type static_value = Ir_types.static_value =
  | Static_scalar of constant
  | Static_record of (string * static_value) list
  | Static_variant of string * (string * static_value) list
  | Static_array of static_value list
  | Static_storage of { element : Ground.ty; elements : static_value list; owned : bool }

type data = Ir_types.data = { data_key : Instance.key; ty : Ground.ty; value : static_value }

type table = Ir_types.table = {
  table_key : Instance.key;
  capability : Path.t option;
  entries : (Instance.key * signature) list;
}

type compiled = Ir_types.compiled = Code of t | Data of data | Table of table

val local_place : local -> place
val signature : function_ -> signature
val erased : Memory_layout.env -> ty -> bool

val projection_type :
  Memory_layout.env -> environment:(int -> (string * ty) list) -> ty -> projection -> ty option

val place_type :
  Memory_layout.env -> environment:(int -> (string * ty) list) -> function_ -> place -> ty option

val target_operands : target -> operand list

type visitor = { place : place -> unit; operand : operand -> unit }

val visit_statement : visitor -> statement -> unit
val visit_terminator : visitor -> terminator -> unit
val successors : terminator -> block list
val map_statement : place:(place -> place) -> block:'a -> statement -> statement
val map_terminator : place:(place -> place) -> block:(block -> block) -> terminator -> terminator
val canonical : function_ -> function_
val canonical_instance : t -> t
