(** The module [standard::intrinsic], which exists in no source file. The compiler declares what is
    in it: the built-in types, whose rules no definition could state, and the operations the
    standard library is written on top of. Only the [standard] package can import it. *)

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
  | USize
  | ISize
  | Float32
  | Float64
  | Bool
  | Character
  | Unit
  | Never
  | Integer  (** The mathematical integers, in specifications only. *)
  | Array  (** [Array[Element, count: USize]] *)
  | Storage
      (** [Storage[Element]]: owned storage on the heap, a buffer, a length, and a capacity, with
          the elements below the length live. The compiler generates its drop and copy, so [List]
          and [String] need no destructor. It is [Copyable] when its elements are, and never
          [Plain]. *)
  | View  (** [View[Element]]: a read-only view of elements, a pointer and a length. A view type. *)
  | Handle
      (** An operating system's descriptor for an open file, owned: dropping it closes it, so it is
          neither [Copyable] nor [Plain]. *)

val builtins : builtin list
val builtin_name : builtin -> string
val builtin_path : builtin -> Path.t
val builtin_of_path : Path.t -> builtin option

val libc_builtin : Libc.scalar -> builtin
(** The built-in type of a number the C library takes or gives. *)

(** The operations of [standard::intrinsic], which the standard library is written on. The type
    checker gives each its signature, and code generation lowers each directly; both match on this
    type exhaustively, so a new operation cannot compile until both handle it. Arithmetic and
    comparison are generic over the built-in number type, which code generation sees after
    monomorphization. *)
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
      (** [(storage, capacity)]: gives the storage a buffer of its own with room for exactly that
          many elements, at least as many as it has. Nothing else makes room: [storage_push] and
          [storage_insert] write into room the storage has, and how much to grow by is the standard
          library's to say. *)
  | Storage_lengthen
      (** [(storage, by)]: the [by] elements after the last, which a function of the C library wrote
          into room the storage had, are the storage's *)
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
  | View_address
      (** [(view) -> USize]: the address of a view's elements as a number, for the lists of
          addresses that some functions of the C library take *)
  | Crash
  | Write_float  (** [(buffer, value)]: appends the shortest decimal that reads back as the float *)
  | Handle_from
      (** [(descriptor) -> Handle]: owns a descriptor that is open, which dropping it closes *)
  | Handle_descriptor  (** [(handle) -> Int32]: the descriptor a handle owns *)
  | Libc of Libc.function_
      (** A function of the system's C library, named [libc_] and its name: [libc_write] *)
  | Libc_number of Libc.number
      (** A number the C library's headers define, which differs between systems, as an operation
          that takes nothing: [libc_o_creat()] *)

val operations : operation list
val operation_name : operation -> string
val operation_path : operation -> Path.t
val operation_of_path : Path.t -> operation option
