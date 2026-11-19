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

let all =
  [
    Equal;
    Ordered;
    Ordering;
    Hash;
    Copyable;
    Plain;
    Storable;
    Display;
    Default;
    Index;
    Index_mut;
    Index_assign;
    Cursor;
    Model;
    From;
    Add;
    Subtract;
    Multiply;
    Divide;
    Remainder;
    Negate;
    Fixed_width_integer;
    Signed_integer;
    Unsigned_integer;
    Range;
    Exit_code;
    Option;
    Result;
    List;
    Slice;
    String;
    String_slice;
    Literal;
    Template;
    From_template;
    From_elements;
    Map;
    Set;
    Sorted_set;
    Sorted_map;
    List_cursor;
    Entry;
    From_entries;
    Sequence;
    Finite_set;
    Finite_map;
    Panic;
    Run_forever;
    Tasks;
    Serialize;
    Deserialize;
    Serializer;
    Deserializer;
    Deserialize_required;
    Deserialize_optional;
    Unknown_variant;
    Write_fully;
    Writing_append;
    Writing_signed;
    Writing_unsigned;
    Writing_float32;
    Writing_float64;
    Writing_boolean;
    Writing_quoted_character;
    Writing_quoted_text;
    Text_copied_from;
    Run_tests;
  ]

let locate_known = function
  | Equal -> ([ "core" ], "Equal")
  | Ordered -> ([ "core" ], "Ordered")
  | Ordering -> ([ "core" ], "Ordering")
  | Hash -> ([ "core" ], "Hash")
  | Copyable -> ([ "core" ], "Copyable")
  | Plain -> ([ "core" ], "Plain")
  | Storable -> ([ "core" ], "Storable")
  | Display -> ([ "core" ], "Display")
  | Default -> ([ "core" ], "Default")
  | Index -> ([ "core" ], "Index")
  | Index_mut -> ([ "core" ], "IndexMut")
  | Index_assign -> ([ "core" ], "IndexAssign")
  | Cursor -> ([ "core" ], "Cursor")
  | Model -> ([ "core" ], "Model")
  | From -> ([ "core" ], "From")
  | Add -> ([ "core" ], "Add")
  | Subtract -> ([ "core" ], "Subtract")
  | Multiply -> ([ "core" ], "Multiply")
  | Divide -> ([ "core" ], "Divide")
  | Remainder -> ([ "core" ], "Remainder")
  | Negate -> ([ "core" ], "Negate")
  | Fixed_width_integer -> ([ "numbers"; "integers" ], "FixedWidthInteger")
  | Signed_integer -> ([ "numbers"; "integers" ], "SignedInteger")
  | Unsigned_integer -> ([ "numbers"; "integers" ], "UnsignedInteger")
  | Range -> ([ "core" ], "Range")
  | Exit_code -> ([ "core" ], "ExitCode")
  | Option -> ([ "option" ], "Option")
  | Result -> ([ "result" ], "Result")
  | List -> ([ "list" ], "List")
  | Slice -> ([ "list" ], "Slice")
  | String -> ([ "text" ], "String")
  | String_slice -> ([ "text" ], "StringSlice")
  | Literal -> ([ "text" ], "Literal")
  | Template -> ([ "text" ], "Template")
  | From_template -> ([ "text" ], "FromTemplate")
  | From_elements -> ([ "list" ], "FromElements")
  | Map -> ([ "map" ], "Map")
  | Set -> ([ "set" ], "Set")
  | Sorted_set -> ([ "collections" ], "SortedSet")
  | Sorted_map -> ([ "collections" ], "SortedMap")
  | List_cursor -> ([ "list" ], "ListCursor")
  | Entry -> ([ "map" ], "Entry")
  | From_entries -> ([ "map" ], "FromEntries")
  | Sequence -> ([ "specification" ], "Sequence")
  | Finite_set -> ([ "specification" ], "FiniteSet")
  | Finite_map -> ([ "specification" ], "FiniteMap")
  | Panic -> ([ "capabilities" ], "Panic")
  | Run_forever -> ([ "capabilities" ], "RunForever")
  | Tasks -> ([ "capabilities" ], "Tasks")
  | Serialize -> ([ "serialization" ], "Serialize")
  | Deserialize -> ([ "serialization" ], "Deserialize")
  | Serializer -> ([ "serialization" ], "Serializer")
  | Deserializer -> ([ "serialization" ], "Deserializer")
  | Deserialize_required -> ([ "serialization" ], "required")
  | Deserialize_optional -> ([ "serialization" ], "optional")
  | Unknown_variant -> ([ "serialization" ], "unknown_variant")
  | Write_fully -> ([ "system"; "calls" ], "write_fully")
  | Writing_append -> ([ "writing" ], "append")
  | Writing_signed -> ([ "writing" ], "signed")
  | Writing_unsigned -> ([ "writing" ], "unsigned")
  | Writing_float32 -> ([ "writing" ], "float32")
  | Writing_float64 -> ([ "writing" ], "float64")
  | Writing_boolean -> ([ "writing" ], "boolean")
  | Writing_quoted_character -> ([ "writing" ], "quoted_character")
  | Writing_quoted_text -> ([ "writing" ], "quoted_text")
  | Text_copied_from -> ([ "system"; "calls" ], "text_copied_from")
  | Run_tests -> ([ "system"; "test_runner" ], "run")

let make_path known =
  let modules, name = locate_known known in
  Path.make_standard_path modules name

let by_path = Path.Map.of_seq (List.to_seq (List.map (fun known -> (make_path known, known)) all))
let of_path path = Path.Map.find_opt path by_path
let is known path = of_path path = Some known
let specification = Path.make_standard_module [ "specification" ]

let is_system_module (module_ : Path.module_) =
  module_.package = Path.standard_package
  && match module_.modules with [ "system"; _ ] -> true | _ -> false

module For_testing = struct
  let all = all
end
