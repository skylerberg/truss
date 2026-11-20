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
  | Finite_cursor
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
  | Instant
  | Duration
  | File_path
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
  | Float_text_write_shortest_float32
  | Float_text_write_shortest_float64
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
  | Finite_cursor_remaining
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

type field_owner = Record of t | Variant of variant
type method_location = { owner : t; name : string; receiver : Path.receiver }

let items =
  [
    (Equal, [ "core" ], "Equal");
    (Ordered, [ "core" ], "Ordered");
    (Ordering, [ "core" ], "Ordering");
    (Hash, [ "core" ], "Hash");
    (Hasher, [ "core" ], "Hasher");
    (Copyable, [ "core" ], "Copyable");
    (Plain, [ "core" ], "Plain");
    (Storable, [ "core" ], "Storable");
    (Display, [ "core" ], "Display");
    (Default, [ "core" ], "Default");
    (From, [ "core" ], "From");
    (Try_from, [ "core" ], "TryFrom");
    (Index, [ "core" ], "Index");
    (Index_mut, [ "core" ], "IndexMut");
    (Index_assign, [ "core" ], "IndexAssign");
    (Iterable, [ "core" ], "Iterable");
    (Cursor, [ "core" ], "Cursor");
    (Finite_cursor, [ "core" ], "FiniteCursor");
    (Model, [ "core" ], "Model");
    (Add, [ "core" ], "Add");
    (Subtract, [ "core" ], "Subtract");
    (Multiply, [ "core" ], "Multiply");
    (Divide, [ "core" ], "Divide");
    (Remainder, [ "core" ], "Remainder");
    (Negate, [ "core" ], "Negate");
    (Fixed_width_integer, [ "numbers"; "integers" ], "FixedWidthInteger");
    (Signed_integer, [ "numbers"; "integers" ], "SignedInteger");
    (Unsigned_integer, [ "numbers"; "integers" ], "UnsignedInteger");
    (Floating_point, [ "numbers"; "float_math" ], "FloatingPoint");
    (Range, [ "core" ], "Range");
    (Exit_code, [ "core" ], "ExitCode");
    (Option, [ "option" ], "Option");
    (Result, [ "result" ], "Result");
    (List, [ "list" ], "List");
    (Slice, [ "list" ], "Slice");
    (String, [ "text" ], "String");
    (String_slice, [ "text" ], "StringSlice");
    (Literal, [ "text" ], "Literal");
    (Template, [ "text" ], "Template");
    (From_template, [ "text" ], "FromTemplate");
    (From_elements, [ "list" ], "FromElements");
    (Map, [ "map" ], "Map");
    (Set, [ "set" ], "Set");
    (Sorted_set, [ "collections" ], "SortedSet");
    (Sorted_map, [ "collections" ], "SortedMap");
    (List_cursor, [ "list" ], "ListCursor");
    (Entry, [ "map" ], "Entry");
    (From_entries, [ "map" ], "FromEntries");
    (Sequence, [ "specification" ], "Sequence");
    (Finite_set, [ "specification" ], "FiniteSet");
    (Finite_map, [ "specification" ], "FiniteMap");
    (Instant, [ "time" ], "Instant");
    (Duration, [ "time" ], "Duration");
    (File_path, [ "files" ], "Path");
    (Tasks, [ "capabilities" ], "Tasks");
    (System_error, [ "capabilities" ], "SystemError");
    (Serialize, [ "serialization" ], "Serialize");
    (Deserialize, [ "serialization" ], "Deserialize");
    (Serializer, [ "serialization" ], "Serializer");
    (Deserializer, [ "serialization" ], "Deserializer");
    (Deserialize_required, [ "serialization" ], "required");
    (Deserialize_optional, [ "serialization" ], "optional");
    (Unknown_variant, [ "serialization" ], "unknown_variant");
    (Write_fully, [ "system"; "calls" ], "write_fully");
    (Writing_append, [ "writing" ], "append");
    (Writing_signed, [ "writing" ], "signed");
    (Writing_unsigned, [ "writing" ], "unsigned");
    (Float_text_write_shortest_float32, [ "numbers"; "float_text" ], "write_shortest_float32");
    (Float_text_write_shortest_float64, [ "numbers"; "float_text" ], "write_shortest_float64");
    (Writing_boolean, [ "writing" ], "boolean");
    (Writing_quoted_character, [ "writing" ], "quoted_character");
    (Writing_quoted_text, [ "writing" ], "quoted_text");
    (Text_copied_from, [ "system"; "calls" ], "text_copied_from");
    (Run_tests, [ "system"; "test_runner" ], "run");
  ]

let methods =
  [
    (Add_add, Add, "add", Path.Instance Read);
    (Subtract_subtract, Subtract, "subtract", Instance Read);
    (Multiply_multiply, Multiply, "multiply", Instance Read);
    (Divide_divide, Divide, "divide", Instance Read);
    (Remainder_remainder, Remainder, "remainder", Instance Read);
    (Negate_negate, Negate, "negate", Instance Read);
    (Equal_equal, Equal, "equal", Instance Read);
    (Ordered_compare, Ordered, "compare", Instance Read);
    (Hash_hash, Hash, "hash", Instance Read);
    (Hasher_write, Hasher, "write", Instance Read);
    (Default_default, Default, "default", Static);
    (Display_display, Display, "display", Instance Read);
    (Copyable_copy, Copyable, "copy", Instance Read);
    (From_from, From, "from", Static);
    (Model_model, Model, "model", Instance Read);
    (Index_at, Index, "at", Instance Read);
    (Index_mut_at, Index_mut, "at", Instance Mut);
    (Index_assign_assign, Index_assign, "assign", Instance Mut);
    (Cursor_next, Cursor, "next", Instance Mut);
    (Finite_cursor_remaining, Finite_cursor, "remaining", Instance Read);
    (Fixed_width_integer_minimum_value, Fixed_width_integer, "minimum_value", Static);
    (Fixed_width_integer_maximum_value, Fixed_width_integer, "maximum_value", Static);
    (Fixed_width_integer_bit_width, Fixed_width_integer, "bit_width", Static);
    (List_from_storage, List, "from_storage", Static);
    (String_push, String, "push", Instance Mut);
    (From_template_from_template, From_template, "from_template", Static);
    (From_elements_from_elements, From_elements, "from_elements", Static);
    (From_entries_from_entries, From_entries, "from_entries", Static);
    (Sequence_length, Sequence, "length", Instance Read);
    (Sequence_sum, Sequence, "sum", Instance Read);
    (Finite_set_contains, Finite_set, "contains", Instance Read);
    (Finite_set_size, Finite_set, "size", Instance Read);
    (Finite_map_contains_key, Finite_map, "contains_key", Instance Read);
    (Finite_map_get, Finite_map, "get", Instance Read);
    (Finite_map_size, Finite_map, "size", Instance Read);
    (Serialize_serialize, Serialize, "serialize", Instance Read);
    (Deserialize_deserialize, Deserialize, "deserialize", Static);
    (Serializer_field, Serializer, "field", Instance Mut);
    (Serializer_begin_record, Serializer, "begin_record", Instance Mut);
    (Serializer_end_record, Serializer, "end_record", Instance Mut);
    (Serializer_begin_variant, Serializer, "begin_variant", Instance Mut);
    (Serializer_end_variant, Serializer, "end_variant", Instance Mut);
    (Deserializer_begin_record, Deserializer, "begin_record", Instance Mut);
    (Deserializer_end_record, Deserializer, "end_record", Instance Mut);
    (Deserializer_variant, Deserializer, "variant", Instance Mut);
    (Deserializer_end_variant, Deserializer, "end_variant", Instance Mut);
    (Deserializer_error, Deserializer, "error", Instance Read);
    (Tasks_open, Tasks, "open", Static);
    (Tasks_spawn, Tasks, "spawn", Static);
    (Tasks_join, Tasks, "join", Static);
    (Tasks_cancel, Tasks, "cancel", Static);
    (Tasks_lock, Tasks, "lock", Static);
    (Tasks_unlock, Tasks, "unlock", Static);
  ]

let associated_types =
  [
    (Add_output, Add, "Output");
    (Subtract_output, Subtract, "Output");
    (Multiply_output, Multiply, "Output");
    (Divide_output, Divide, "Output");
    (Remainder_output, Remainder, "Output");
    (Negate_output, Negate, "Output");
    (Index_key, Index, "Key");
    (Index_output, Index, "Output");
    (Cursor_element, Cursor, "Element");
    (Model_value, Model, "Value");
    (From_template_part, From_template, "Part");
    (From_elements_element, From_elements, "Element");
    (From_entries_key, From_entries, "Key");
    (From_entries_value, From_entries, "Value");
  ]

let variants =
  [
    (Option_some, Option, "Some");
    (Option_none, Option, "None");
    (Result_ok, Result, "Ok");
    (Result_err, Result, "Err");
    (Ordering_less, Ordering, "Less");
    (Ordering_equal, Ordering, "Equal");
    (Ordering_greater, Ordering, "Greater");
  ]

let fields =
  [
    (Range_start, Record Range, "start");
    (Range_stop, Record Range, "stop");
    (Range_inclusive, Record Range, "inclusive");
    (Template_literals, Record Template, "literals");
    (Template_parts, Record Template, "parts");
    (Literal_text, Record Literal, "text");
    (Entry_key, Record Entry, "key");
    (Entry_value, Record Entry, "value");
    (Option_some_value, Variant Option_some, "value");
    (Result_ok_value, Variant Result_ok, "value");
    (Result_err_error, Variant Result_err, "error");
  ]

let index_rows kind rows =
  let table = Hashtbl.create (List.length rows) in
  List.iter (fun (member, location) -> Hashtbl.replace table member location) rows;
  fun member ->
    match Hashtbl.find_opt table member with
    | Some location -> location
    | None -> invalid_arg ("a well-known " ^ kind ^ " has no row in its table")

let make_path =
  index_rows "item"
    (List.map (fun (known, modules, name) -> (known, Path.make_standard_path modules name)) items)

let by_path =
  Path.Map.of_seq (List.to_seq (List.map (fun (known, _, _) -> (make_path known, known)) items))

let of_path path = Path.Map.find_opt path by_path
let is known path = of_path path = Some known
let is_buffer_sequence path = is List path || is Slice path

let locate_method =
  index_rows "method"
    (List.map
       (fun (method_, owner, name, receiver) -> (method_, { owner; name; receiver }))
       methods)

let make_method_path method_ =
  let { owner; name; receiver } = locate_method method_ in
  Path.Method { owner = make_path owner; name; receiver }

let make_impl_method_path method_ ~impl =
  let { name; receiver; _ } = locate_method method_ in
  Path.Method { owner = impl; name; receiver }

let methods_by_path =
  Path.Map.of_seq
    (List.to_seq (List.map (fun (method_, _, _, _) -> (make_method_path method_, method_)) methods))

let find_method path = Path.Map.find_opt path methods_by_path
let is_method method_ path = find_method path = Some method_

let show_associated =
  index_rows "associated type"
    (List.map (fun (associated, _, name) -> (associated, name)) associated_types)

let show_variant =
  index_rows "variant" (List.map (fun (variant, _, name) -> (variant, name)) variants)

let make_variant_type_path =
  index_rows "variant" (List.map (fun (variant, owner, _) -> (variant, make_path owner)) variants)

let show_field = index_rows "field" (List.map (fun (field, _, name) -> (field, name)) fields)
let specification = Path.make_standard_module [ "specification" ]
let intrinsic_module = Path.make_standard_module [ "intrinsic" ]

let make_builtin_type_path builtin_type =
  Path.Top { module_ = intrinsic_module; name = Language.Builtin_type.show builtin_type }

let builtin_types_by_path =
  Path.Map.of_seq
    (List.to_seq
       (List.map
          (fun builtin_type -> (make_builtin_type_path builtin_type, builtin_type))
          Language.Builtin_type.all))

let find_builtin_type path = Path.Map.find_opt path builtin_types_by_path

let find_view path =
  if is List path || find_builtin_type path = Some Array then Some (make_path Slice)
  else if is String path then Some (make_path String_slice)
  else None

let make_builtin_capability_path builtin_capability =
  Path.make_standard_path [ "capabilities" ] (Language.Builtin_capability.show builtin_capability)

let builtin_capabilities_by_path =
  Path.Map.of_seq
    (List.to_seq
       (List.map
          (fun builtin_capability ->
            (make_builtin_capability_path builtin_capability, builtin_capability))
          Language.Builtin_capability.all))

let find_builtin_capability path = Path.Map.find_opt path builtin_capabilities_by_path

let is_system_module (module_ : Path.module_) =
  module_.package = Path.standard_package
  && match module_.modules with [ "system"; _ ] -> true | _ -> false

module For_testing = struct
  type nonrec field_owner = field_owner = Record of t | Variant of variant

  let all = List.map (fun (known, _, _) -> known) items
  let all_methods = List.map (fun (method_, _, _, _) -> method_) methods

  let all_associated_types =
    List.map (fun (associated, owner, _) -> (associated, owner)) associated_types

  let all_variants = List.map (fun (variant, _, _) -> variant) variants
  let all_fields = List.map (fun (field, owner, _) -> (field, owner)) fields
end
