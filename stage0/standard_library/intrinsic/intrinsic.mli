val convert_libc_scalar : Libc.scalar -> Language.Builtin_type.t

type scalar =
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

type buffer =
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
  | Storage_view
  | View_length
  | View_swap
  | View_slice
  | Storage_model
  | View_model
  | Array_model
  | View_address

type lend = Storage_at | View_at

type runtime =
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

type operation = Scalar of scalar | Buffer of buffer | Lend of lend | Runtime of runtime

val operations : operation list
val show_operation : operation -> string
val make_operation_path : operation -> Path.t
val find_operation : Path.t -> operation option
