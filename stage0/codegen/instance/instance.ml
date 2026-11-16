type key =
  | Code of { path : Path.t; type_arguments : Ground.argument list }
  | Constant of Path.t
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty
  | Any_drop of Ground.ty
  | Any_copy of Ground.ty
  | Encode of Ground.ty
  | Evaluator of Path.t
  | Template_check of { from_template : Path.t; literals : string list; clauses : int list }
  | Call_evaluation of { function_ : Path.t; arguments : Z.t list }
  | Generated of generated
  | Table of table

and generated =
  | Entry of impl_method
  | Any_entry of impl_method
  | Locked_entry of { capability : Path.t; name : string }
  | Adapter of {
      function_ : Path.t;
      type_arguments : Ground.argument list;
      ty : Ground.function_type;
    }
  | Program_main of Path.t

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

let make_method_code (impl_method : impl_method) =
  Code { path = make_method_path impl_method; type_arguments = impl_method.type_arguments }

type t = key

let compare = Stdlib.compare
let equal = ( = )
let hash key = Hashtbl.hash_param 64 256 key
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
      module_path module_ ^ marker "Impl" ^ reference trait ^ marker "For" ^ path for_type
      ^ marker "End"
  | Derived { type_; trait } ->
      marker "Derived" ^ path trait ^ marker "For" ^ path type_ ^ marker "End"
  | Test { module_; name } -> module_path module_ ^ marker "Test" ^ text name ^ marker "End"
  | Law_proof { module_; trait; law; for_type } ->
      module_path module_ ^ marker "Proof" ^ reference trait ^ marker "Law" ^ text law
      ^ marker "For" ^ path for_type ^ marker "End"
  | Unresolved { names; _ } ->
      marker "Unresolved" ^ String.concat (marker "In") (List.map text names) ^ marker "End"

and reference ({ path = trait; arguments; associated } : Path.reference) =
  match (arguments, associated) with
  | [], [] -> path trait
  | _ ->
      path trait
      ^ String.concat "" (List.map (fun argument -> marker "Of" ^ path_argument argument) arguments)
      ^ String.concat ""
          (List.map
             (fun (name, argument) ->
               marker "Where" ^ text name ^ marker "Is" ^ path_argument argument)
             associated)
      ^ marker "Done"

and path_argument : Path.argument -> string = function
  | Named named -> reference named
  | Parameter name -> marker "Parameter" ^ text name
  | Any trait -> marker "Any" ^ reference trait
  | Count value -> marker "Count" ^ text (Z.to_string value)
  | Constant constant -> marker "Constant" ^ path constant

let mode : Ground.mode -> string = function Read -> "" | Mut -> marker "Mut" | Own -> marker "Own"

let rec mangle_ty (ty : Ground.ty) =
  match ty with
  | Named { path = instance_path; arguments } -> path instance_path ^ mangle_arguments arguments
  | Function { parameters; result; uses } ->
      marker "Fn"
      ^ String.concat ""
          (List.map (fun (module_, ty) -> mode module_ ^ mangle_ty ty ^ marker "And") parameters)
      ^ marker "Returns" ^ mangle_ty result
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
  | Any_copy ty -> marker "AnyCopy" ^ mangle_ty ty
  | Evaluator instance_path -> marker "Evaluator" ^ path instance_path
  | Template_check { from_template; literals; clauses } ->
      marker "Check" ^ path from_template
      ^ String.concat ""
          (List.map (fun literal -> marker "Text" ^ text literal ^ marker "End") literals)
      ^ String.concat "" (List.map (fun clause -> marker "Clause" ^ string_of_int clause) clauses)
      ^ marker "End"
  | Call_evaluation { function_; arguments } ->
      marker "Evaluate" ^ path function_
      ^ String.concat ""
          (List.map (fun number -> marker "Value" ^ text (Z.to_string number)) arguments)
      ^ marker "End"
  | Generated (Adapter { function_; type_arguments; ty }) ->
      marker "Adapter"
      ^ mangle (Code { path = function_; type_arguments })
      ^ marker "As" ^ mangle_ty (Function ty)
  | Generated (Any_entry impl_method) -> marker "Dynamic" ^ mangle (make_method_code impl_method)
  | Generated (Locked_entry { capability; name }) ->
      marker "LockedEntry" ^ path capability ^ marker "Method" ^ text name
  | Generated (Entry impl_method) -> marker "Entry" ^ mangle (make_method_code impl_method)
  | Generated (Program_main main) -> marker "Program" ^ path main
  | Table (Any_table { impl; type_arguments }) ->
      marker "Vtable" ^ path impl ^ mangle_arguments type_arguments
  | Table (Locked_table capability) -> marker "LockedTable" ^ path capability
  | Table (Impl_table { impl; type_arguments }) ->
      marker "Table" ^ path impl ^ mangle_arguments type_arguments

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
  | Any_copy ty -> "any copy " ^ Ground.to_string ty
  | Evaluator path -> "evaluator " ^ Path.show path
  | Template_check { from_template; literals; clauses } ->
      "template check " ^ Path.show from_template ^ " of "
      ^ String.concat ", " (List.map (Printf.sprintf "%S") literals)
      ^ " for clauses "
      ^ String.concat ", " (List.map string_of_int clauses)
  | Call_evaluation { function_; arguments } ->
      "evaluation " ^ Path.show function_ ^ "("
      ^ String.concat ", " (List.map Z.to_string arguments)
      ^ ")"
  | Generated (Adapter { function_; type_arguments; _ }) ->
      "adapter " ^ to_string (Code { path = function_; type_arguments })
  | Generated (Any_entry impl_method) -> "any entry " ^ to_string (make_method_code impl_method)
  | Generated (Locked_entry { capability; name }) ->
      "locked entry " ^ Path.show capability ^ "." ^ name
  | Generated (Entry impl_method) -> "entry " ^ to_string (make_method_code impl_method)
  | Generated (Program_main main) -> "program " ^ Path.show main
  | Table (Any_table { impl; type_arguments }) ->
      "any table " ^ Path.show impl ^ arguments_to_string type_arguments
  | Table (Locked_table capability) -> "locked table " ^ Path.show capability
  | Table (Impl_table { impl; type_arguments }) ->
      "table " ^ Path.show impl ^ arguments_to_string type_arguments

and arguments_to_string = function
  | [] -> ""
  | arguments -> "[" ^ String.concat ", " (List.map Ground.argument_to_string arguments) ^ "]"
