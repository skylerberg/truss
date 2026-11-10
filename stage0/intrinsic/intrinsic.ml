let module_ : Path.module_ = { package = "standard"; modules = [ "intrinsic" ] }

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

let builtin_path builtin = Path.Top { module_; name = builtin_name builtin }

let builtin_of_path = function
  | Path.Top { module_ = m; name } when m = module_ ->
      List.find_opt (fun builtin -> builtin_name builtin = name) builtins
  | _ -> None

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
  | Storage_reserve
  | Storage_push
  | Storage_pop
  | Storage_insert
  | Storage_remove
  | Storage_swap
  | Storage_at
  | Storage_at_mut
  | Storage_view
  | View_length
  | View_at
  | View_slice
  | Storage_model
  | View_model
  | Crash
  | Write_bytes
  | Read_bytes
  | Write_float
  | Open_file
  | Handle_read
  | Handle_write
  | Environment_variable
  | Run_process
  | Clock_now
  | Random_fill

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
    Storage_reserve;
    Storage_push;
    Storage_pop;
    Storage_insert;
    Storage_remove;
    Storage_swap;
    Storage_at;
    Storage_at_mut;
    Storage_view;
    View_length;
    View_at;
    View_slice;
    Storage_model;
    View_model;
    Crash;
    Write_bytes;
    Read_bytes;
    Write_float;
    Open_file;
    Handle_read;
    Handle_write;
    Environment_variable;
    Run_process;
    Clock_now;
    Random_fill;
  ]

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
  | Storage_reserve -> "storage_reserve"
  | Storage_push -> "storage_push"
  | Storage_pop -> "storage_pop"
  | Storage_insert -> "storage_insert"
  | Storage_remove -> "storage_remove"
  | Storage_swap -> "storage_swap"
  | Storage_at -> "storage_at"
  | Storage_at_mut -> "storage_at_mut"
  | Storage_view -> "storage_view"
  | View_length -> "view_length"
  | View_at -> "view_at"
  | View_slice -> "view_slice"
  | Storage_model -> "storage_model"
  | View_model -> "view_model"
  | Crash -> "crash"
  | Write_bytes -> "write_bytes"
  | Read_bytes -> "read_bytes"
  | Write_float -> "write_float"
  | Open_file -> "open_file"
  | Handle_read -> "handle_read"
  | Handle_write -> "handle_write"
  | Environment_variable -> "environment_variable"
  | Run_process -> "run_process"
  | Clock_now -> "clock_now"
  | Random_fill -> "random_fill"

let operation_path operation = Path.Top { module_; name = operation_name operation }

let operation_of_path = function
  | Path.Top { module_ = m; name } when m = module_ ->
      List.find_opt (fun operation -> operation_name operation = name) operations
  | _ -> None
