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
  | Range
  | Exit_code
  | Option
  | Result
  | List
  | Slice
  | String
  | String_slice
  | Text_builder
  | Literal
  | Template
  | From_template
  | Set
  | Map
  | Sequence
  | Finite_set
  | Finite_map
  | Panic
  | Tasks
  | Write_fully
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
    Range;
    Exit_code;
    Option;
    Result;
    List;
    Slice;
    String;
    String_slice;
    Text_builder;
    Literal;
    Template;
    From_template;
    Set;
    Map;
    Sequence;
    Finite_set;
    Finite_map;
    Panic;
    Tasks;
    Write_fully;
    Text_copied_from;
    Run_tests;
  ]

let modules_and_name = function
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
  | Range -> ([ "core" ], "Range")
  | Exit_code -> ([ "core" ], "ExitCode")
  | Option -> ([ "option" ], "Option")
  | Result -> ([ "result" ], "Result")
  | List -> ([ "list" ], "List")
  | Slice -> ([ "list" ], "Slice")
  | String -> ([ "text" ], "String")
  | String_slice -> ([ "text" ], "StringSlice")
  | Text_builder -> ([ "text" ], "TextBuilder")
  | Literal -> ([ "text" ], "Literal")
  | Template -> ([ "text" ], "Template")
  | From_template -> ([ "text" ], "FromTemplate")
  | Set -> ([ "set" ], "Set")
  | Map -> ([ "map" ], "Map")
  | Sequence -> ([ "specification" ], "Sequence")
  | Finite_set -> ([ "specification" ], "FiniteSet")
  | Finite_map -> ([ "specification" ], "FiniteMap")
  | Panic -> ([ "capabilities" ], "Panic")
  | Tasks -> ([ "capabilities" ], "Tasks")
  | Write_fully -> ([ "system"; "calls" ], "write_fully")
  | Text_copied_from -> ([ "system"; "calls" ], "text_copied_from")
  | Run_tests -> ([ "system"; "test_runner" ], "run")

let path known =
  let modules, name = modules_and_name known in
  Path.standard modules name

let by_path = Path.Map.of_seq (List.to_seq (List.map (fun known -> (path known, known)) all))
let of_path path = Path.Map.find_opt path by_path
let is known path = of_path path = Some known
let specification = Path.standard_module [ "specification" ]
let system_module name = Path.standard_module [ "system"; name ]

let in_system (module_ : Path.module_) =
  module_.package = Path.standard_package
  && match module_.modules with "system" :: _ -> true | _ -> false
