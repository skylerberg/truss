type local = private int
type block = private int
type nested_function = private int

type ty =
  | Value of Ground.ty
  | Pointer of { target : ty; writable : bool }
  | Raw of Memory_layout.scalar
  | Environment of nested_function
  | Evidence of int
  | Capabilities of int
  | Trace
  | Lend
  | Lend_mark

type site = { definition : Path.t; offset : int }
type root = Local of local | Static of { item : Item.t; ty : Ground.ty }

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
  | Symbol_address of Item.t
  | Site of site
  | Capability of Path.t
  | Size_of of Ground.ty
  | Alignment_of of Ground.ty

and function_ref = Item of Item.t | Nested of nested_function

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

type comparison =
  | Equal
  | Not_equal
  | Less
  | Less_equal
  | Greater
  | Greater_equal
  | Ieee_equal
  | Ieee_less
  | Ieee_less_equal

type test = comparison * operand * operand

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
  | Capabilities_fill
  | Capability_find
  | Trace_link
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
  | Lend_begin
  | Lend_called
  | Lend_release
  | Lend_transfer
  | Lend_allocate
  | Lend_defer_drop
  | Lend_defer_write_back

type target =
  | Direct of { function_ : function_ref; signature : signature }
  | Indirect of { code : operand; environment : operand; signature : signature }
  | Intrinsic of intrinsic
  | Foreign of Libc.declaration
  | Evidence_call of { evidence : operand; capability : Path.t; slot : int; signature : signature }
  | Table_call of { table : operand; value : operand; slot : int; signature : signature }

type rvalue =
  | Use of operand
  | Unary of unary * operand
  | Binary of binary * operand * operand
  | Compare of test
  | Convert of operand * Memory_layout.scalar
  | Build of { ty : Ground.ty; variant : string option; fields : (string * operand) list }
  | Is_variant of place * string
  | Function_value of { code : function_ref; environment : operand option }

type failure = Panic | Assertion | Todo
type destination = Discarded | Returned of place | Written of place

type statement =
  | Assign of place * rvalue
  | Call of { target : target; arguments : operand list; result : destination }
  | Drop of place
  | Echo of { text : operand; length : operand; site : site }
  | Fail_obligation_when of {
      test : test;
      message : operand;
      length : operand;
      site : site;
      reported : operand option;
      trace : operand option;
    }
  | Free_block of { place : place; variant : string }
  | Defer_free_block of { lend : operand; place : place; variant : string }
  | Fork of { branches : (nested_function * operand) list }
  | Fork_range of { body : nested_function; environment : operand; first : operand; last : operand }

type terminator =
  | Goto of block
  | Branch of { test : test; yes : block; no : block }
  | Switch of { value : operand; cases : (Z.t * block) list; default : block }
  | Switch_variant of { place : place; cases : (string * block) list; default : block option }
  | Return of operand option
  | Unreachable
  | Fail of {
      failure : failure;
      message : operand;
      length : operand;
      site : site;
      reported : operand option;
      trace : operand option;
    }

type static_value =
  | Static_scalar of constant
  | Static_record of (string * static_value) list
  | Static_variant of string * (string * static_value) list
  | Static_array of static_value list
  | Static_storage of { element : Ground.ty; elements : static_value list }
  | Static_view of { element : Ground.ty; elements : static_value list }

type data = { data_item : Item.t; ty : Ground.ty; value : static_value }

type table = {
  table_item : Item.t;
  capability : Path.t option;
  entries : (Item.t * signature) list;
}

val add_local : 'a Dynarray.t -> 'a -> local
val add_block : 'a Dynarray.t -> 'a -> block
val list_blocks : 'a Dynarray.t -> block list

type nested_function_counter

val create_nested_function_counter : unit -> nested_function_counter
val allocate_nested_function : nested_function_counter -> nested_function

module For_testing : sig
  val make_local : int -> local
  val make_block : int -> block
  val make_nested_function : int -> nested_function
end
