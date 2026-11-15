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

val builtins : builtin list
val builtin_name : builtin -> string
val builtin_path : builtin -> Path.t
val builtin_of_path : Path.t -> builtin option
val libc_builtin : Libc.scalar -> builtin

type operation =
  | Add
  | Subtract
  | Multiply
  | Divide
  | Remainder
  | Negate
  | Wrapping_add
  | Wrapping_subtract
  | Wrapping_multiply
  | Add_overflows
  | Subtract_overflows
  | Multiply_overflows
  | Equal
  | Less
  | Ieee_equal
  | Ieee_less
  | Bit_and
  | Bit_or
  | Bit_xor
  | Complement
  | Shift_left
  | Shift_right
  | Convert
  | Fits
  | Square_root
  | Fused_multiply_add
  | Floor
  | Ceiling
  | Truncate
  | Round_to_even
  | To_bits
  | From_bits
  | Is_nan
  | Leading_zeros
  | Trailing_zeros
  | Count_ones
  | Swap_bytes
  | Rotate_left
  | Rotate_right
  | Multiply_high
  | Compare_bytes
  | Storage_empty
  | Storage_with_capacity
  | Storage_length
  | Storage_capacity
  | Storage_set_capacity
  | Storage_lengthen
  | Storage_shorten
  | Storage_push
  | Storage_pop
  | Storage_insert
  | Storage_remove
  | Storage_swap
  | Storage_from_array
  | Array_from_storage
  | Array_view
  | Array_at_mut
  | Storage_at
  | Storage_at_mut
  | Storage_view
  | View_length
  | View_at
  | View_at_mut
  | View_swap
  | View_slice
  | Storage_model
  | View_model
  | Array_model
  | View_address
  | Crash
  | Handle_from
  | Handle_descriptor
  | Handle_release
  | Run_test
  | Report_tests_to
  | Live_blocks
  | Environment_entry
  | Coroutine_start
  | Coroutine_resume
  | Coroutine_suspend
  | Tasks_spawn
  | Shared_new
  | Shared_update
  | Holds_invariant
  | Shared_key
  | System_is_os of Libc.os
  | System_is_architecture of Libc.architecture
  | Libc of Libc.function_
  | Libc_number of Libc.number

val operations : operation list
val primitive : operation -> bool
val operation_name : operation -> string
val operation_path : operation -> Path.t
val operation_of_path : Path.t -> operation option
val uses : operation -> Path.t list
