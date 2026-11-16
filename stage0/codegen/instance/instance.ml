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

module Key = Structural_key.Make (struct
  type nonrec t = t
end)

let compare = Key.compare
let equal = Key.equal
let hash = Key.hash
let render_marker word = "_" ^ word ^ "_"

let mangle_module_path (module_ : Path.module_) =
  let package =
    match module_.package.owner with
    | Some owner -> owner ^ render_marker "Owns" ^ module_.package.name
    | None -> module_.package.name
  in
  String.concat "__" (package :: module_.modules)

let mangle_text value =
  String.concat ""
    (List.map
       (fun order ->
         match order with
         | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> String.make 1 order
         | order -> Printf.sprintf "_C%02X_" (Char.code order))
       (List.of_seq (String.to_seq value)))

let mangle_receiver : Path.receiver -> string = function
  | Static -> render_marker "Static"
  | Read -> ""
  | Mut -> render_marker "Mut"
  | Own -> render_marker "Own"

let rec mangle_path : Path.t -> string = function
  | Top { module_; name } -> mangle_module_path module_ ^ "__" ^ name
  | Method { owner; name; receiver = method_receiver } ->
      mangle_path owner ^ "_" ^ name ^ mangle_receiver method_receiver
  | Member_constant { owner; name } -> mangle_path owner ^ render_marker "Member" ^ name
  | Impl { module_; trait; for_type } ->
      mangle_module_path module_ ^ render_marker "Impl" ^ mangle_reference trait
      ^ render_marker "For" ^ mangle_path for_type ^ render_marker "End"
  | Derived { type_; trait } ->
      render_marker "Derived" ^ mangle_path trait ^ render_marker "For" ^ mangle_path type_
      ^ render_marker "End"
  | Test { module_; name } ->
      mangle_module_path module_ ^ render_marker "Test" ^ mangle_text name ^ render_marker "End"
  | Law_proof { module_; trait; law; for_type } ->
      mangle_module_path module_ ^ render_marker "Proof" ^ mangle_reference trait
      ^ render_marker "Law" ^ mangle_text law ^ render_marker "For" ^ mangle_path for_type
      ^ render_marker "End"
  | Unresolved { names; _ } ->
      render_marker "Unresolved"
      ^ String.concat (render_marker "In") (List.map mangle_text names)
      ^ render_marker "End"

and mangle_reference ({ path = trait; arguments; associated } : Path.reference) =
  match (arguments, associated) with
  | [], [] -> mangle_path trait
  | _ ->
      mangle_path trait
      ^ String.concat ""
          (List.map (fun argument -> render_marker "Of" ^ mangle_path_argument argument) arguments)
      ^ String.concat ""
          (List.map
             (fun (name, argument) ->
               render_marker "Where" ^ mangle_text name ^ render_marker "Is"
               ^ mangle_path_argument argument)
             associated)
      ^ render_marker "Done"

and mangle_path_argument : Path.argument -> string = function
  | Named named -> mangle_reference named
  | Parameter name -> render_marker "Parameter" ^ mangle_text name
  | Any trait -> render_marker "Any" ^ mangle_reference trait
  | Count value -> render_marker "Count" ^ mangle_text (Z.to_string value)
  | Constant constant -> render_marker "Constant" ^ mangle_path constant

let mangle_mode : Ground.mode -> string = function
  | Read -> ""
  | Mut -> render_marker "Mut"
  | Own -> render_marker "Own"

let rec mangle_ty (ty : Ground.ty) =
  match ty with
  | Named { path = instance_path; arguments } ->
      mangle_path instance_path ^ mangle_arguments arguments
  | Function { parameters; result; uses } ->
      render_marker "Fn"
      ^ String.concat ""
          (List.map
             (fun (module_, ty) -> mangle_mode module_ ^ mangle_ty ty ^ render_marker "And")
             parameters)
      ^ render_marker "Returns" ^ mangle_ty result
      ^ (match uses with
        | [] -> ""
        | uses ->
            render_marker "Uses" ^ String.concat (render_marker "And") (List.map mangle_path uses))
      ^ render_marker "End"
  | Any { trait; arguments; associated } ->
      render_marker "Any" ^ mangle_path trait ^ mangle_arguments arguments
      ^ String.concat ""
          (List.map
             (fun (name, ty) -> render_marker "Assoc" ^ name ^ render_marker "Is" ^ mangle_ty ty)
             associated)
      ^ render_marker "End"
  | Never -> render_marker "Never"

and mangle_argument = function
  | Ground.Type ty -> mangle_ty ty
  | Value value -> render_marker "Value" ^ Z.to_string value
  | Capabilities set ->
      render_marker "Granted"
      ^ String.concat (render_marker "And") (List.map mangle_path set)
      ^ render_marker "End"

and mangle_arguments = function
  | [] -> ""
  | arguments ->
      render_marker "Of"
      ^ String.concat (render_marker "And") (List.map mangle_argument arguments)
      ^ render_marker "End"

let rec mangle = function
  | Code { path = instance_path; type_arguments } ->
      mangle_path instance_path ^ mangle_arguments type_arguments
  | Constant instance_path -> render_marker "Constant" ^ mangle_path instance_path
  | Drop ty -> render_marker "Drop" ^ mangle_ty ty
  | Copy ty -> render_marker "Copy" ^ mangle_ty ty
  | Debug ty -> render_marker "Debug" ^ mangle_ty ty
  | Encode ty -> render_marker "Encode" ^ mangle_ty ty
  | Any_drop ty -> render_marker "AnyDrop" ^ mangle_ty ty
  | Any_copy ty -> render_marker "AnyCopy" ^ mangle_ty ty
  | Evaluator instance_path -> render_marker "Evaluator" ^ mangle_path instance_path
  | Template_check { from_template; literals; clauses } ->
      render_marker "Check" ^ mangle_path from_template
      ^ String.concat ""
          (List.map
             (fun literal -> render_marker "Text" ^ mangle_text literal ^ render_marker "End")
             literals)
      ^ String.concat ""
          (List.map (fun clause -> render_marker "Clause" ^ string_of_int clause) clauses)
      ^ render_marker "End"
  | Call_evaluation { function_; arguments } ->
      render_marker "Evaluate" ^ mangle_path function_
      ^ String.concat ""
          (List.map
             (fun number -> render_marker "Value" ^ mangle_text (Z.to_string number))
             arguments)
      ^ render_marker "End"
  | Generated (Adapter { function_; type_arguments; ty }) ->
      render_marker "Adapter"
      ^ mangle (Code { path = function_; type_arguments })
      ^ render_marker "As" ^ mangle_ty (Function ty)
  | Generated (Any_entry impl_method) ->
      render_marker "Dynamic" ^ mangle (make_method_code impl_method)
  | Generated (Locked_entry { capability; name }) ->
      render_marker "LockedEntry" ^ mangle_path capability ^ render_marker "Method"
      ^ mangle_text name
  | Generated (Entry impl_method) -> render_marker "Entry" ^ mangle (make_method_code impl_method)
  | Generated (Program_main main) -> render_marker "Program" ^ mangle_path main
  | Table (Any_table { impl; type_arguments }) ->
      render_marker "Vtable" ^ mangle_path impl ^ mangle_arguments type_arguments
  | Table (Locked_table capability) -> render_marker "LockedTable" ^ mangle_path capability
  | Table (Impl_table { impl; type_arguments }) ->
      render_marker "Table" ^ mangle_path impl ^ mangle_arguments type_arguments

let limit = 200
let prefix_length = 180

let shorten name =
  if String.length name <= limit then name
  else String.sub name 0 prefix_length ^ "_Hash_" ^ Blake3.hash_to_hex ~digits:32 name

let make_symbol key = shorten ("t_" ^ mangle key)
let make_type_symbol ty = shorten ("t_" ^ mangle_ty ty)

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
