type t =
  | Code of { path : Path.t; instantiation : Ground.instantiation; assumes_condition : bool }
  | Constant of Path.t
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty
  | Any_drop of Ground.ty
  | Any_copy of Ground.ty
  | Encode of Ground.ty
  | Evaluator of t
  | Assertion of { definition : Path.t; condition : int }
  | Generated of generated
  | Table of table

and generated =
  | Entry of impl_method
  | Any_entry of impl_method
  | Locked_entry of { capability : Path.t; name : string }
  | Adapter of {
      function_ : Path.t;
      instantiation : Ground.instantiation;
      ty : Ground.function_type;
    }
  | Program_main of Path.t
  | Test_main of Path.t

and table =
  | Impl_table of { impl : Path.t; type_arguments : Ground.argument list }
  | Any_table of { impl : Path.t; type_arguments : Ground.argument list }
  | Locked_table of Path.t

and impl_method = {
  impl : Path.t;
  name : string;
  receiver : Path.receiver;
  type_arguments : Ground.argument list;
}

let make_method_path { impl; name; receiver; _ } = Path.Method { owner = impl; name; receiver }
let make_code path instantiation = Code { path; instantiation; assumes_condition = false }

let make_method_code (impl_method : impl_method) =
  make_code (make_method_path impl_method)
    { Ground.no_instantiation with type_arguments = impl_method.type_arguments }

module Key = Structural_key.Make (struct
  type nonrec t = t
end)

let compare = Key.compare
let equal = Key.equal
let hash = Key.hash

let rec to_string = function
  | Code { path; instantiation; assumes_condition } ->
      Path.show path
      ^ show_arguments instantiation.type_arguments
      ^ show_capability_arguments instantiation.capability_arguments
      ^ if assumes_condition then " assuming its condition on values" else ""
  | Constant path -> Path.show path
  | Drop ty -> "drop " ^ Ground.to_string ty
  | Copy ty -> "copy " ^ Ground.to_string ty
  | Debug ty -> "debug " ^ Ground.to_string ty
  | Encode ty -> "encode " ^ Ground.to_string ty
  | Any_drop ty -> "any drop " ^ Ground.to_string ty
  | Any_copy ty -> "any copy " ^ Ground.to_string ty
  | Evaluator evaluated -> "evaluator " ^ to_string evaluated
  | Assertion { definition; condition } ->
      Printf.sprintf "assertion %d of %s" condition (Path.show definition)
  | Generated (Adapter { function_; instantiation; _ }) ->
      "adapter " ^ to_string (make_code function_ instantiation)
  | Generated (Any_entry impl_method) -> "any entry " ^ to_string (make_method_code impl_method)
  | Generated (Locked_entry { capability; name }) ->
      "locked entry " ^ Path.show capability ^ "." ^ name
  | Generated (Entry impl_method) -> "entry " ^ to_string (make_method_code impl_method)
  | Generated (Program_main main) -> "program " ^ Path.show main
  | Generated (Test_main test) -> "test main " ^ Path.show test
  | Table (Any_table { impl; type_arguments }) ->
      "any table " ^ Path.show impl ^ show_arguments type_arguments
  | Table (Locked_table capability) -> "locked table " ^ Path.show capability
  | Table (Impl_table { impl; type_arguments }) ->
      "table " ^ Path.show impl ^ show_arguments type_arguments

and show_arguments = function
  | [] -> ""
  | arguments -> "[" ^ String.concat ", " (List.map Ground.show_argument arguments) ^ "]"

and show_capability_arguments arguments =
  String.concat ""
    (List.map
       (fun (name, set) ->
         Printf.sprintf " generic %s = {%s}" name (String.concat ", " (List.map Path.show_name set)))
       arguments)

let find_type_definition : Ground.ty -> Path.t option = function
  | Named { path; _ } -> Some path
  | Any { trait; _ } -> Some trait
  | Function _ | Never -> None

let rec find_definition : t -> Path.t option = function
  | Code { path; _ }
  | Constant path
  | Assertion { definition = path; _ }
  | Generated
      ( Locked_entry { capability = path; _ }
      | Adapter { function_ = path; _ }
      | Program_main path
      | Test_main path )
  | Table (Impl_table { impl = path; _ } | Any_table { impl = path; _ } | Locked_table path) ->
      Some path
  | Evaluator evaluated -> find_definition evaluated
  | Drop ty | Copy ty | Debug ty | Any_drop ty | Any_copy ty | Encode ty -> find_type_definition ty
  | Generated (Entry impl_method | Any_entry impl_method) -> Some (make_method_path impl_method)
