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
  | Storage_shorten
      (** [storage_shorten(mut storage, length)]: the storage keeps its first [length] elements and
          its capacity, and the rest are forgotten, which elements with nothing to drop can be. Its
          length is at least [length]. *)
  | Storage_push
  | Storage_pop
  | Storage_insert
  | Storage_remove
  | Storage_swap
  | Storage_from_array
      (** [storage_from_array(array)]: new storage that holds the elements of an [own] array, in
          order, with the array's length as its length and its capacity. The array is moved. *)
  | Array_from_storage
      (** [array_from_storage(storage)]: an array of the elements of an [own] storage, in order,
          whose length is the array's. The storage is moved, and its buffer freed. A checked build
          stops if the lengths differ. *)
  | Array_view
      (** [array_view(array)]: a view of an array's elements, in order, which is valid for as long
          as the array is *)
  | Array_at_mut
      (** [array_at_mut(mut array, index)]: lends the element at an index, to change. The index is
          less than the array's length. *)
  | Storage_at
  | Storage_at_mut
  | Storage_view
  | Storage_view_mut
      (** [storage_view_mut(mut storage)]: a view of the storage's elements to change them through,
          with [view_at_mut] and [view_swap]. Storage whose elements are static gets a buffer of its
          own first, as it does before any other change. *)
  | View_length
  | View_at
  | View_at_mut
      (** [view_at_mut(mut view, index)]: lends the element at an index, to change. The index is
          less than the view's length, and the view is of elements that may be changed: it came from
          [storage_view_mut] or from an array held [mut]. *)
  | View_swap
      (** [view_swap(mut view, first, second)]: exchanges two elements of a view of elements that
          may be changed. Each index is less than the view's length. *)
  | Storage_take_view
      (** [storage_take_view(mut storage, view, start)]: says that the storage's elements from
          [start] are the view's, where the view was made from this storage to change them through.
          In memory they already are, so it does nothing; the prover gives the storage's model the
          view's elements. A checked build stops if the view is not of those elements. *)
  | View_take_view  (** [view_take_view(mut view, part, start)]: the same for a view of a view *)
  | Array_take_view
      (** [array_take_view(mut array, view, start)]: the same for a view of an array *)
  | View_slice
  | Storage_model  (** [(storage) -> Sequence]: its elements, in specifications only *)
  | View_model  (** [(view) -> Sequence]: its elements, in specifications only *)
  | Array_model  (** [(array) -> Sequence]: its elements, in specifications only *)
  | View_address
      (** [(view) -> USize]: the address of a view's elements as a number, for the lists of
          addresses that some functions of the C library take *)
  | Crash
  | Handle_from
      (** [(descriptor) -> Handle]: owns a descriptor that is open, which dropping it closes *)
  | Handle_descriptor  (** [(handle) -> Int32]: the descriptor a handle owns *)
  | Handle_release
      (** [(own handle) -> Int32]: the descriptor of a handle that is given up without closing it,
          so that the caller can close it and see whether closing failed *)
  | Run_test
      (** [(index)]: runs a test of the test program, by its place in the program's table of them *)
  | Report_tests_to
      (** [(descriptor)]: from here on a panic, a failed [assert], a [todo], and an [echo] are
          written as records to the descriptor, for a test's worker *)
  | Live_blocks  (** [() -> USize]: how many blocks a test program has allocated and not freed *)
  | Environment_entry
      (** [environment_entry(index, found: mut found)]: the text of the entry at an index of the
          environment the process was started with, [NAME=value], as a view, with [found] false
          where the environment has no entry there. It counts from the first entry each time, so it
          never reads past the last. *)
  | Coroutine_start
      (** [coroutine_start(work: own fn(UInt64), item: UInt64) -> USize]: creates a suspended
          coroutine that will call [work(item)] on its own stack, and returns its handle. A
          scheduler that runs one task at a time, such as a test's, runs each task as a coroutine.
      *)
  | Coroutine_resume
      (** [coroutine_resume(coroutine) -> Bool]: runs the coroutine until it suspends or its
          function returns. Returns true if it suspended. Returns false if its function returned,
          which also frees the coroutine. *)
  | Coroutine_suspend
      (** [coroutine_suspend()]: called in a coroutine. Switches to the code that resumed the
          coroutine, and returns when the coroutine is resumed again. *)
  | Tasks_spawn
      (** [tasks_spawn(group, work: own fn(UInt64), item: UInt64) -> Bool]: spawns a runtime task
          that calls [work(item)], and returns true. If the group is already cancelled, spawns
          nothing and returns false. The runtime's other task functions take only integers, so they
          are rows of the C library's table. *)
  | System_is_os of Libc.os
      (** [system_is_linux()], [system_is_macos()]: whether the program is built for that operating
          system, which lowering knows *)
  | System_is_architecture of Libc.architecture  (** [system_is_x86_64()], [system_is_arm64()] *)
  | Libc of Libc.function_
      (** A function of the system's C library, named [libc_] and its name: [libc_write] *)
  | Libc_number of Libc.number
      (** A number the C library's headers define, which differs between systems, as an operation
          that takes nothing: [libc_o_creat()] *)

val operations : operation list
val operation_name : operation -> string
val operation_path : operation -> Path.t
val operation_of_path : Path.t -> operation option

val uses : operation -> Path.t list
(** The capabilities that a call of the operation requires. An intrinsic takes no evidence, so only
    the capability check reads this. The check allows the call where each capability is available,
    and in the body of a method of a capability's [impl]. Every operation returns the empty list for
    now. *)
