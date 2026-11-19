let convert_libc_scalar : Libc.scalar -> Language.Builtin_type.t = function
  | UInt8 -> UInt8
  | Int32 -> Int32
  | UInt32 -> UInt32
  | Int64 -> Int64
  | UInt64 -> UInt64
  | Float32 -> Float32
  | Float64 -> Float64

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

let list_scalar_operations =
  [
    Add;
    Subtract;
    Multiply;
    Divide;
    Remainder;
    Negate;
    Wrapping_add;
    Wrapping_subtract;
    Wrapping_multiply;
    Add_overflows;
    Subtract_overflows;
    Multiply_overflows;
    Equal;
    Less;
    Ieee_equal;
    Ieee_less;
    Bit_and;
    Bit_or;
    Bit_xor;
    Complement;
    Shift_left;
    Shift_right;
    Convert;
    Fits;
    Square_root;
    Fused_multiply_add;
    Floor;
    Ceiling;
    Truncate;
    Round_to_even;
    To_bits;
    From_bits;
    Is_nan;
    Leading_zeros;
    Trailing_zeros;
    Count_ones;
    Swap_bytes;
    Rotate_left;
    Rotate_right;
    Multiply_high;
  ]

let list_buffer_operations =
  [
    Compare_bytes;
    Storage_empty;
    Storage_with_capacity;
    Storage_length;
    Storage_capacity;
    Storage_set_capacity;
    Storage_lengthen;
    Storage_shorten;
    Storage_push;
    Storage_pop;
    Storage_insert;
    Storage_remove;
    Storage_swap;
    Storage_from_array;
    Array_from_storage;
    Array_view;
    Storage_view;
    View_length;
    View_swap;
    View_slice;
    Storage_model;
    View_model;
    Array_model;
    View_address;
  ]

let list_lend_operations = [ Storage_at; View_at ]

let list_runtime_operations =
  [
    Crash;
    Handle_from;
    Handle_descriptor;
    Handle_release;
    Run_test;
    Report_tests_to;
    Live_blocks;
    Environment_entry;
    Coroutine_start;
    Coroutine_resume;
    Coroutine_suspend;
    Tasks_spawn;
    Shared_new;
    Shared_update;
    Holds_invariant;
    Shared_key;
  ]
  @ List.map (fun os -> System_is_os os) Libc.oses
  @ List.map (fun architecture -> System_is_architecture architecture) Libc.architectures
  @ List.map (fun function_ -> Libc function_) Libc.functions
  @ List.map (fun number -> Libc_number number) Libc.numbers

let operations =
  List.map (fun operation -> Scalar operation) list_scalar_operations
  @ List.map (fun operation -> Buffer operation) list_buffer_operations
  @ List.map (fun operation -> Lend operation) list_lend_operations
  @ List.map (fun operation -> Runtime operation) list_runtime_operations

let show_scalar : scalar -> string = function
  | Add -> "add"
  | Subtract -> "subtract"
  | Multiply -> "multiply"
  | Divide -> "divide"
  | Remainder -> "remainder"
  | Negate -> "negate"
  | Wrapping_add -> "wrapping_add"
  | Wrapping_subtract -> "wrapping_subtract"
  | Wrapping_multiply -> "wrapping_multiply"
  | Add_overflows -> "add_overflows"
  | Subtract_overflows -> "subtract_overflows"
  | Multiply_overflows -> "multiply_overflows"
  | Equal -> "equal"
  | Less -> "less"
  | Ieee_equal -> "ieee_equal"
  | Ieee_less -> "ieee_less"
  | Bit_and -> "bit_and"
  | Bit_or -> "bit_or"
  | Bit_xor -> "bit_xor"
  | Complement -> "complement"
  | Shift_left -> "shift_left"
  | Shift_right -> "shift_right"
  | Convert -> "convert"
  | Fits -> "fits"
  | Square_root -> "square_root"
  | Fused_multiply_add -> "fused_multiply_add"
  | Floor -> "floor"
  | Ceiling -> "ceiling"
  | Truncate -> "truncate"
  | Round_to_even -> "round_to_even"
  | To_bits -> "to_bits"
  | From_bits -> "from_bits"
  | Is_nan -> "is_nan"
  | Leading_zeros -> "leading_zeros"
  | Trailing_zeros -> "trailing_zeros"
  | Count_ones -> "count_ones"
  | Swap_bytes -> "swap_bytes"
  | Rotate_left -> "rotate_left"
  | Rotate_right -> "rotate_right"
  | Multiply_high -> "multiply_high"

let show_buffer : buffer -> string = function
  | Compare_bytes -> "compare_bytes"
  | Storage_empty -> "storage_empty"
  | Storage_with_capacity -> "storage_with_capacity"
  | Storage_length -> "storage_length"
  | Storage_capacity -> "storage_capacity"
  | Storage_set_capacity -> "storage_set_capacity"
  | Storage_lengthen -> "storage_lengthen"
  | Storage_shorten -> "storage_shorten"
  | Storage_push -> "storage_push"
  | Storage_pop -> "storage_pop"
  | Storage_insert -> "storage_insert"
  | Storage_remove -> "storage_remove"
  | Storage_swap -> "storage_swap"
  | Storage_from_array -> "storage_from_array"
  | Array_from_storage -> "array_from_storage"
  | Array_view -> "array_view"
  | Storage_view -> "storage_view"
  | View_length -> "view_length"
  | View_swap -> "view_swap"
  | View_slice -> "view_slice"
  | Storage_model -> "storage_model"
  | View_model -> "view_model"
  | Array_model -> "array_model"
  | View_address -> "view_address"

let show_lend : lend -> string = function Storage_at -> "storage_at" | View_at -> "view_at"

let show_runtime : runtime -> string = function
  | Crash -> "crash"
  | Handle_from -> "handle_from"
  | Handle_descriptor -> "handle_descriptor"
  | Handle_release -> "handle_release"
  | Run_test -> "run_test"
  | Report_tests_to -> "report_tests_to"
  | Live_blocks -> "live_blocks"
  | Environment_entry -> "environment_entry"
  | Coroutine_start -> "coroutine_start"
  | Coroutine_resume -> "coroutine_resume"
  | Coroutine_suspend -> "coroutine_suspend"
  | Tasks_spawn -> "tasks_spawn"
  | Shared_new -> "shared_new"
  | Shared_update -> "shared_update"
  | Holds_invariant -> "holds_invariant"
  | Shared_key -> "shared_key"
  | System_is_os Linux -> "system_is_linux"
  | System_is_os Macos -> "system_is_macos"
  | System_is_architecture X86_64 -> "system_is_x86_64"
  | System_is_architecture Arm64 -> "system_is_arm64"
  | Libc function_ ->
      (if Libc.is_runtime_function function_ then "runtime_" else "libc_")
      ^ Libc.show_function function_
  | Libc_number number ->
      let name = Libc.show_number number in
      let unprefixed =
        if String.starts_with ~prefix:"_" name then String.drop_first 1 name else name
      in
      "libc_" ^ String.lowercase_ascii unprefixed

let show_operation = function
  | Scalar operation -> show_scalar operation
  | Buffer operation -> show_buffer operation
  | Lend operation -> show_lend operation
  | Runtime operation -> show_runtime operation

let make_operation_path operation =
  Path.Top { module_ = Well_known.intrinsic_module; name = show_operation operation }

let operations_by_path =
  Path.Map.of_seq
    (List.to_seq
       (List.map (fun operation -> (make_operation_path operation, operation)) operations))

let find_operation path = Path.Map.find_opt path operations_by_path
