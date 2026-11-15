type key =
  | Code of { path : Path.t; type_arguments : Ground.argument list }
  | Constant of Path.t
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty
  | Any_drop of Ground.ty
  | Encode of Ground.ty
  | Evaluator of Path.t
  | Template_check of { from_template : Path.t; texts : string list }
  | Call_evaluation of { function_ : Path.t; arguments : Z.t list }
  | Adapter of { function_ : key; ty : Ground.function_type }
  | Entry of key
  | Table of { impl : Path.t; type_arguments : Ground.argument list }
  | Program_main of Path.t
  | Any_entry of key
  | Any_table of { impl : Path.t; type_arguments : Ground.argument list }
  | Locked_entry of { capability : Path.t; name : string }
  | Locked_table of Path.t

let compare = Stdlib.compare
let equal = ( = )
let marker word = "_" ^ word ^ "_"

let module_path (module_ : Path.module_) =
  let package =
    match module_.package.owner with
    | Some owner -> owner ^ marker "Owns" ^ module_.package.name
    | None -> module_.package.name
  in
  String.concat "__" (package :: module_.modules)

let text value =
  String.concat ""
    (List.map
       (fun order ->
         match order with
         | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> String.make 1 order
         | order -> Printf.sprintf "_C%02X_" (Char.code order))
       (List.of_seq (String.to_seq value)))

let receiver : Path.receiver -> string = function
  | Static -> marker "Static"
  | Read -> ""
  | Mut -> marker "Mut"
  | Own -> marker "Own"

let rec path : Path.t -> string = function
  | Top { module_; name } -> module_path module_ ^ "__" ^ name
  | Method { owner; name; receiver = method_receiver } ->
      path owner ^ "_" ^ name ^ receiver method_receiver
  | Member_constant { owner; name } -> path owner ^ marker "Member" ^ name
  | Impl { module_; trait; for_type } ->
      module_path module_ ^ marker "Impl" ^ text trait ^ marker "For"
      ^ text (Path.show_type_head for_type)
      ^ marker "End"
  | Derived { type_; trait } ->
      marker "Derived" ^ path trait ^ marker "For" ^ path type_ ^ marker "End"
  | Test { module_; name } -> module_path module_ ^ marker "Test" ^ text name ^ marker "End"
  | Law_proof { module_; trait; law; for_type } ->
      module_path module_ ^ marker "Proof" ^ text trait ^ marker "Law" ^ text law ^ marker "For"
      ^ text (Path.show_type_head for_type)
      ^ marker "End"

let mode : Ground.mode -> string = function Read -> "" | Mut -> marker "Mut" | Own -> marker "Own"

let rec mangle_ty (ty : Ground.ty) =
  match ty with
  | Named { path = instance_path; arguments } -> path instance_path ^ mangle_arguments arguments
  | Function { parameters; result; uses } ->
      marker "Fn"
      ^ String.concat ""
          (List.map (fun (module_, ty) -> mode module_ ^ mangle_ty ty ^ marker "And") parameters)
      ^ (match result with
        | Returns ty -> marker "Returns" ^ mangle_ty ty
        | Lends (module_, ty) -> marker "Lends" ^ mode module_ ^ mangle_ty ty)
      ^ (match uses with
        | [] -> ""
        | uses -> marker "Uses" ^ String.concat (marker "And") (List.map path uses))
      ^ marker "End"
  | Any { trait; arguments; associated } ->
      marker "Any" ^ path trait ^ mangle_arguments arguments
      ^ String.concat ""
          (List.map
             (fun (name, ty) -> marker "Assoc" ^ name ^ marker "Is" ^ mangle_ty ty)
             associated)
      ^ marker "End"
  | Never -> marker "Never"

and mangle_argument = function
  | Ground.Type ty -> mangle_ty ty
  | Value value -> marker "Value" ^ Z.to_string value
  | Capabilities set ->
      marker "Granted" ^ String.concat (marker "And") (List.map path set) ^ marker "End"

and mangle_arguments = function
  | [] -> ""
  | arguments ->
      marker "Of" ^ String.concat (marker "And") (List.map mangle_argument arguments) ^ marker "End"

let rec mangle = function
  | Code { path = instance_path; type_arguments } ->
      path instance_path ^ mangle_arguments type_arguments
  | Constant instance_path -> marker "Constant" ^ path instance_path
  | Drop ty -> marker "Drop" ^ mangle_ty ty
  | Copy ty -> marker "Copy" ^ mangle_ty ty
  | Debug ty -> marker "Debug" ^ mangle_ty ty
  | Encode ty -> marker "Encode" ^ mangle_ty ty
  | Any_drop ty -> marker "AnyDrop" ^ mangle_ty ty
  | Evaluator instance_path -> marker "Evaluator" ^ path instance_path
  | Template_check { from_template; texts } ->
      marker "Check" ^ path from_template
      ^ String.concat ""
          (List.map
             (fun component_type -> marker "Text" ^ text component_type ^ marker "End")
             texts)
  | Call_evaluation { function_; arguments } ->
      marker "Evaluate" ^ path function_
      ^ String.concat ""
          (List.map (fun number -> marker "Value" ^ text (Z.to_string number)) arguments)
      ^ marker "End"
  | Adapter { function_; ty } ->
      marker "Adapter" ^ mangle function_ ^ marker "As" ^ mangle_ty (Function ty)
  | Any_entry key -> marker "Dynamic" ^ mangle key
  | Any_table { impl; type_arguments } ->
      marker "Vtable" ^ path impl ^ mangle_arguments type_arguments
  | Locked_entry { capability; name } ->
      marker "LockedEntry" ^ path capability ^ marker "Method" ^ text name
  | Locked_table capability -> marker "LockedTable" ^ path capability
  | Entry key -> marker "Entry" ^ mangle key
  | Table { impl; type_arguments } -> marker "Table" ^ path impl ^ mangle_arguments type_arguments
  | Program_main main -> marker "Program" ^ path main

let limit = 200
let prefix_length = 180

let shorten name =
  if String.length name <= limit then name
  else String.sub name 0 prefix_length ^ "_Hash_" ^ Blake3.hex_digest ~digits:32 name

let path_symbol = path
let symbol key = shorten ("t_" ^ mangle key)
let type_symbol ty = shorten ("t_" ^ mangle_ty ty)

let rec to_string = function
  | Code { path; type_arguments; _ } -> Path.show path ^ arguments_to_string type_arguments
  | Constant path -> Path.show path
  | Drop ty -> "drop " ^ Ground.to_string ty
  | Copy ty -> "copy " ^ Ground.to_string ty
  | Debug ty -> "debug " ^ Ground.to_string ty
  | Encode ty -> "encode " ^ Ground.to_string ty
  | Any_drop ty -> "any drop " ^ Ground.to_string ty
  | Evaluator path -> "evaluator " ^ Path.show path
  | Template_check { from_template; texts } ->
      "template check " ^ Path.show from_template ^ " of "
      ^ String.concat ", " (List.map (Printf.sprintf "%S") texts)
  | Call_evaluation { function_; arguments } ->
      "evaluation " ^ Path.show function_ ^ "("
      ^ String.concat ", " (List.map Z.to_string arguments)
      ^ ")"
  | Adapter { function_; _ } -> "adapter " ^ to_string function_
  | Any_entry key -> "any entry " ^ to_string key
  | Any_table { impl; type_arguments } ->
      "any table " ^ Path.show impl ^ arguments_to_string type_arguments
  | Locked_entry { capability; name } -> "locked entry " ^ Path.show capability ^ "." ^ name
  | Locked_table capability -> "locked table " ^ Path.show capability
  | Entry key -> "entry " ^ to_string key
  | Table { impl; type_arguments } -> "table " ^ Path.show impl ^ arguments_to_string type_arguments
  | Program_main main -> "program " ^ Path.show main

and arguments_to_string = function
  | [] -> ""
  | arguments -> "[" ^ String.concat ", " (List.map Ground.argument_to_string arguments) ^ "]"
