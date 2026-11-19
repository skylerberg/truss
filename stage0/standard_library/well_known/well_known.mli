type t =
  | Equal
  | Ordered
  | Ordering
  | Hash
  | Copyable
  | Plain
  | Storable
  | Display
  | Default
  | Index
  | Index_mut
  | Index_assign
  | Cursor
  | Model
  | From
  | Add
  | Subtract
  | Multiply
  | Divide
  | Remainder
  | Negate
  | Fixed_width_integer
  | Signed_integer
  | Unsigned_integer
  | Floating_point
  | Range
  | Exit_code
  | Option
  | Result
  | List
  | Slice
  | String
  | String_slice
  | Literal
  | Template
  | From_template
  | From_elements
  | Map
  | Set
  | Sorted_set
  | Sorted_map
  | List_cursor
  | Entry
  | From_entries
  | Sequence
  | Finite_set
  | Finite_map
  | Panic
  | Run_forever
  | Tasks
  | Serialize
  | Deserialize
  | Serializer
  | Deserializer
  | Deserialize_required
  | Deserialize_optional
  | Unknown_variant
  | Write_fully
  | Writing_append
  | Writing_signed
  | Writing_unsigned
  | Writing_float32
  | Writing_float64
  | Writing_boolean
  | Writing_quoted_character
  | Writing_quoted_text
  | Text_copied_from
  | Run_tests

val make_path : t -> Path.t
val of_path : Path.t -> t option
val is : t -> Path.t -> bool
val specification : Path.module_
val is_system_module : Path.module_ -> bool

module For_testing : sig
  val all : t list
end
