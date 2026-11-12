let module_ = Path.standard_module [ "intrinsic" ]

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
  | Integer
  | Array
  | Storage
  | View
  | Handle
  | Shared

let builtins =
  [
    Int8;
    Int16;
    Int32;
    Int64;
    UInt8;
    UInt16;
    UInt32;
    UInt64;
    USize;
    ISize;
    Float32;
    Float64;
    Bool;
    Character;
    Unit;
    Never;
    Integer;
    Array;
    Storage;
    View;
    Handle;
    Shared;
  ]

let builtin_name = function
  | Int8 -> "Int8"
  | Int16 -> "Int16"
  | Int32 -> "Int32"
  | Int64 -> "Int64"
  | UInt8 -> "UInt8"
  | UInt16 -> "UInt16"
  | UInt32 -> "UInt32"
  | UInt64 -> "UInt64"
  | USize -> "USize"
  | ISize -> "ISize"
  | Float32 -> "Float32"
  | Float64 -> "Float64"
  | Bool -> "Bool"
  | Character -> "Character"
  | Unit -> "Unit"
  | Never -> "Never"
  | Integer -> "Integer"
  | Array -> "Array"
  | Storage -> "Storage"
  | View -> "View"
  | Handle -> "Handle"
  | Shared -> "Shared"

let builtin_path builtin = Path.Top { module_; name = builtin_name builtin }

let builtin_of_path = function
  | Path.Top { module_ = m; name } when m = module_ ->
      List.find_opt (fun builtin -> builtin_name builtin = name) builtins
  | _ -> None

let libc_builtin : Libc.scalar -> builtin = function
  | UInt8 -> UInt8
  | Int32 -> Int32
  | UInt32 -> UInt32
  | Int64 -> Int64
  | UInt64 -> UInt64
  | USize -> USize
  | ISize -> ISize
  | Float32 -> Float32
  | Float64 -> Float64

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
  | Storage_view_mut
  | View_length
  | View_at
  | View_at_mut
  | View_swap
  | Storage_take_view
  | View_take_view
  | Array_take_view
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
  | Shared_key
  | System_is_os of Libc.os
  | System_is_architecture of Libc.architecture
  | Libc of Libc.function_
  | Libc_number of Libc.number

let primitive = function
  | Add | Subtract | Multiply | Divide | Remainder | Negate | Wrapping_add | Wrapping_subtract
  | Wrapping_multiply | Add_overflows | Subtract_overflows | Multiply_overflows | Equal | Less
  | Ieee_equal | Ieee_less | Bit_and | Bit_or | Bit_xor | Complement | Shift_left | Shift_right
  | Convert | Fits | Square_root | Fused_multiply_add | Floor | Ceiling | Truncate | Round_to_even
  | To_bits | From_bits | Is_nan | Leading_zeros | Trailing_zeros | Count_ones | Swap_bytes
  | Rotate_left | Rotate_right | Multiply_high ->
      true
  | _ -> false

let operations =
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
    Array_at_mut;
    Storage_at;
    Storage_at_mut;
    Storage_view;
    Storage_view_mut;
    View_length;
    View_at;
    View_at_mut;
    View_swap;
    Storage_take_view;
    View_take_view;
    Array_take_view;
    View_slice;
    Storage_model;
    View_model;
    Array_model;
    View_address;
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
    Shared_key;
  ]
  @ List.map (fun os -> System_is_os os) Libc.oses
  @ List.map (fun architecture -> System_is_architecture architecture) Libc.architectures
  @ List.map (fun function_ -> Libc function_) Libc.functions
  @ List.map (fun number -> Libc_number number) Libc.numbers

let operation_name = function
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
  | Array_at_mut -> "array_at_mut"
  | Storage_at -> "storage_at"
  | Storage_at_mut -> "storage_at_mut"
  | Storage_view -> "storage_view"
  | Storage_view_mut -> "storage_view_mut"
  | View_length -> "view_length"
  | View_at -> "view_at"
  | View_at_mut -> "view_at_mut"
  | View_swap -> "view_swap"
  | Storage_take_view -> "storage_take_view"
  | View_take_view -> "view_take_view"
  | Array_take_view -> "array_take_view"
  | View_slice -> "view_slice"
  | Storage_model -> "storage_model"
  | Array_model -> "array_model"
  | View_model -> "view_model"
  | View_address -> "view_address"
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
  | Shared_key -> "shared_key"
  | System_is_os Linux -> "system_is_linux"
  | System_is_os Macos -> "system_is_macos"
  | System_is_architecture X86_64 -> "system_is_x86_64"
  | System_is_architecture Arm64 -> "system_is_arm64"
  | Libc function_ ->
      (if Libc.is_runtime_function function_ then "runtime_" else "libc_")
      ^ Libc.function_name function_
  | Libc_number number ->
      (* A name does not start with an underscore, as some of C's do. *)
      let name = Libc.number_name number in
      let from = if String.starts_with ~prefix:"_" name then 1 else 0 in
      "libc_" ^ String.lowercase_ascii (String.sub name from (String.length name - from))

let operation_path operation = Path.Top { module_; name = operation_name operation }

let uses : operation -> Path.t list = function
  | Shared_update | Shared_key -> [ Well_known.path Tasks ]
  | _ -> []

let operation_of_path = function
  | Path.Top { module_ = m; name } when m = module_ ->
      List.find_opt (fun operation -> operation_name operation = name) operations
  | _ -> None
