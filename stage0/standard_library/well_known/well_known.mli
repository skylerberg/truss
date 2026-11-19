type t =
  | Equal
  | Ordered
  | Ordering
  | Hash
  | Hasher
  | Copyable
  | Plain
  | Storable
  | Display
  | Default
  | From
  | Try_from
  | Index
  | Index_mut
  | Index_assign
  | Iterable
  | Cursor
  | Model
  | Add
  | Subtract
  | Multiply
  | Divide
  | Remainder
  | Negate
  | Fixed_width_integer
  | Signed_integer
  | Unsigned_integer
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
  | Multiset
  | Instant
  | Duration
  | File_path
  | Panic
  | Run_forever
  | System
  | Tasks
  | System_error
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

type method_ =
  | Add_add
  | Subtract_subtract
  | Multiply_multiply
  | Divide_divide
  | Remainder_remainder
  | Negate_negate
  | Equal_equal
  | Ordered_compare
  | Hash_hash
  | Hasher_write
  | Default_default
  | Display_display
  | Copyable_copy
  | From_from
  | Model_model
  | Index_at
  | Index_mut_at
  | Index_assign_assign
  | Cursor_next
  | Fixed_width_integer_minimum_value
  | Fixed_width_integer_maximum_value
  | Fixed_width_integer_bit_width
  | List_from_storage
  | String_push
  | From_template_from_template
  | From_elements_from_elements
  | From_entries_from_entries
  | Sequence_length
  | Sequence_sum
  | Finite_set_contains
  | Finite_set_size
  | Finite_map_contains_key
  | Finite_map_get
  | Finite_map_size
  | Serialize_serialize
  | Deserialize_deserialize
  | Serializer_field
  | Serializer_begin_record
  | Serializer_end_record
  | Serializer_begin_variant
  | Serializer_end_variant
  | Deserializer_begin_record
  | Deserializer_end_record
  | Deserializer_variant
  | Deserializer_end_variant
  | Deserializer_error
  | Tasks_open
  | Tasks_spawn
  | Tasks_join
  | Tasks_cancel
  | Tasks_lock
  | Tasks_unlock

type associated =
  | Add_output
  | Subtract_output
  | Multiply_output
  | Divide_output
  | Remainder_output
  | Negate_output
  | Index_key
  | Index_output
  | Cursor_element
  | Model_value
  | From_template_part
  | From_elements_element
  | From_entries_key
  | From_entries_value

type variant =
  | Option_some
  | Option_none
  | Result_ok
  | Result_err
  | Ordering_less
  | Ordering_equal
  | Ordering_greater

type field =
  | Range_start
  | Range_stop
  | Range_inclusive
  | Template_literals
  | Template_parts
  | Literal_text
  | Entry_key
  | Entry_value
  | Option_some_value
  | Result_ok_value
  | Result_err_error

type method_location = { owner : t; name : string; receiver : Path.receiver }

val make_path : t -> Path.t
val of_path : Path.t -> t option
val is : t -> Path.t -> bool
val is_buffer_sequence : Path.t -> bool
val locate_method : method_ -> method_location
val make_method_path : method_ -> Path.t
val make_impl_method_path : method_ -> impl:Path.t -> Path.t
val find_method : Path.t -> method_ option
val is_method : method_ -> Path.t -> bool
val show_associated : associated -> string
val show_variant : variant -> string
val make_variant_type_path : variant -> Path.t
val show_field : field -> string
val specification : Path.module_
val intrinsic_module : Path.module_
val make_builtin_type_path : Language.Builtin_type.t -> Path.t
val find_builtin_type : Path.t -> Language.Builtin_type.t option
val is_system_module : Path.module_ -> bool

module For_testing : sig
  type field_owner = Record of t | Variant of variant

  val all : t list
  val all_methods : method_ list
  val all_associated_types : (associated * t) list
  val all_variants : variant list
  val all_fields : (field * field_owner) list
end
