type local = int
type block = int

type ty =
  | Value of Ground.ty
  | Pointer of { target : ty; writable : bool }
  | Raw of Memory_layout.scalar
  | Environment of int
  | Evidence of int

type site = { definition : Path.t; line : int; column : int }
type root = Local of local | Static of { key : Instance.key; ty : Ground.ty }

type place = { root : root; projections : projection list }

and projection =
  | Field of string
  | Variant_field of { variant : string; field : string }
  | Index of operand
  | Deref

and operand =
  | Copy of place
  | Move of place
  | Constant of constant
  | Address of { place : place; writable : bool }
  | Moved_address of place

and constant =
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
  | Site of site

and function_ref = Instance of Instance.key | Nested of int

type signature = { parameters : ty list; result : ty option; returns : bool }
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

type intrinsic =
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

type target =
  | Direct of { function_ : function_ref; signature : signature }
  | Indirect of { value : operand; signature : signature }
  | Intrinsic of intrinsic
  | Foreign of Libc.declaration
  | Evidence_call of { evidence : operand; capability : Path.t; slot : int; signature : signature }
  | Table_call of { table : operand; value : operand; slot : int; signature : signature }

type rvalue =
  | Use of operand
  | Unary of unary * operand
  | Binary of binary * operand * operand
  | Convert of operand * Memory_layout.scalar
  | Build of { ty : Ground.ty; variant : string option; fields : (string * operand) list }
  | Is_variant of place * string
  | Function_value of { code : function_ref; environment : operand option }

type failure = Panic | Assertion | Todo
type destination = Discarded | Returned of place | Written of place

type region =
  | Branch
  | Chunk of { first : local; last : local }
  | Task of { function_value : local; item : local }

type statement =
  | Assign of place * rvalue
  | Call of { target : target; arguments : operand list; result : destination }
  | Drop of place
  | Echo of { text : operand; length : operand; site : site }
  | Free_block of { place : place; variant : string }
  | Region of { fork : int; region : region }
  | Regions_end of { fork : int }
  | Loop_body of { loop : int; part : local option }
  | Loop_exit of { loop : int }
  | Fork of { branches : (int * operand) list }
  | Fork_range of { body : int; environment : operand; first : operand; last : operand }

type terminator =
  | Goto of block
  | Switch of { value : operand; cases : (Z.t * block) list; default : block option }
  | Switch_variant of { place : place; cases : (string * block) list; default : block option }
  | Return of operand option
  | Unreachable
  | Fail of {
      failure : failure;
      message : operand;
      length : operand;
      site : site;
      caller : operand option;
    }
  | Yield of { value : operand; resume : block; stop : block option }
  | Loop_call of {
      loop : int;
      target : target;
      arguments : operand list;
      go_on : ty;
      body : block;
      after : block;
      exit : local;
    }
  | Loop_next of { loop : int; body : block; after : block }

type basic_block = { statements : statement list; terminator : terminator }
type local_info = { ty : ty; name : string option; borrowed : bool }

type function_ = {
  parameters : local list;
  written_result : local option;
  result : ty option;
  returns : bool;
  locals : local_info array;
  blocks : basic_block array;
  environment : (string * ty) list;
}

type t = { key : Instance.key; main : function_; nested : function_ array }

type static_value =
  | Static_scalar of constant
  | Static_record of (string * static_value) list
  | Static_variant of string * (string * static_value) list
  | Static_array of static_value list
  | Static_storage of { element : Ground.ty; elements : static_value list; owned : bool }

type data = { data_key : Instance.key; ty : Ground.ty; value : static_value }

type table = {
  table_key : Instance.key;
  capability : Path.t option;
  entries : (Instance.key * signature) list;
}

type compiled = Code of t | Data of data | Table of table
