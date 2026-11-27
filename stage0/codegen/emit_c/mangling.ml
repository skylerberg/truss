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
       (fun character ->
         match character with
         | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> String.of_char character
         | character -> Printf.sprintf "_C%02X_" (Char.code character))
       (List.of_seq (String.to_seq value)))

let mangle_receiver : Path.receiver -> string = function
  | Static -> render_marker "Static"
  | Instance Read -> ""
  | Instance Mut -> render_marker "Mut"
  | Instance Own -> render_marker "Own"

let rec mangle_path : Path.t -> string = function
  | Top { module_; name } -> mangle_module_path module_ ^ "__" ^ name
  | Method { owner; name; receiver = method_receiver } ->
      mangle_path owner ^ "_" ^ name ^ mangle_receiver method_receiver
  | Member_constant { owner; name } -> mangle_path owner ^ render_marker "Member" ^ name
  | Default { owner; variant; name } ->
      mangle_path owner
      ^ (match variant with Some variant -> render_marker "Variant" ^ variant | None -> "")
      ^ render_marker "Default" ^ name
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
  | Count value -> render_marker "Count" ^ mangle_text (Z.to_string value)
  | Constant constant -> render_marker "Constant" ^ mangle_path constant

let mangle_mode : Language.Mode.t -> string = function
  | Read -> ""
  | Mut -> render_marker "Mut"
  | Own -> render_marker "Own"

let rec mangle_ty (ty : Ground.ty) =
  match ty with
  | Named { path; arguments } -> mangle_path path ^ mangle_arguments arguments
  | Function { parameters; result; uses } ->
      render_marker "Fn"
      ^ String.concat ""
          (List.map
             (fun (mode, ty) -> mangle_mode mode ^ mangle_ty ty ^ render_marker "And")
             parameters)
      ^ render_marker "Returns" ^ mangle_ty result
      ^ (match uses with
        | [] -> ""
        | uses ->
            render_marker "Uses" ^ String.concat (render_marker "And") (List.map mangle_path uses))
      ^ render_marker "End" ^ render_marker "End"
  | Never -> render_marker "Never"

and mangle_argument = function
  | Ground.Type ty -> mangle_ty ty
  | Value value -> render_marker "Value" ^ Z.to_string value

and mangle_arguments = function
  | [] -> ""
  | arguments ->
      render_marker "Of"
      ^ String.concat (render_marker "And") (List.map mangle_argument arguments)
      ^ render_marker "End"

let mangle_capability_arguments arguments =
  String.concat ""
    (List.map
       (fun (name, set) ->
         render_marker "Granted" ^ mangle_text name ^ render_marker "Is"
         ^ String.concat (render_marker "And") (List.map mangle_path set)
         ^ render_marker "End")
       arguments)

let rec mangle : Lowered.Item.t -> string = function
  | Code { path; instantiation; assumes_condition } ->
      mangle_path path
      ^ mangle_arguments instantiation.type_arguments
      ^ mangle_capability_arguments instantiation.capability_arguments
      ^ if assumes_condition then render_marker "Assuming" else ""
  | Constant { path; arguments } ->
      render_marker "Constant" ^ mangle_path path
      ^ mangle_arguments (List.map (fun (_, argument) -> argument) arguments)
  | Drop ty -> render_marker "Drop" ^ mangle_ty ty
  | Copy ty -> render_marker "Copy" ^ mangle_ty ty
  | Debug ty -> render_marker "Debug" ^ mangle_ty ty
  | Encode ty -> render_marker "Encode" ^ mangle_ty ty
  | Untyped_drop ty -> render_marker "UntypedDrop" ^ mangle_ty ty
  | Evaluator evaluated -> render_marker "Evaluator" ^ mangle evaluated
  | Assertion { definition; condition } ->
      render_marker "Assertion" ^ mangle_path definition ^ render_marker "Value"
      ^ mangle_text (string_of_int condition)
  | Generated (Adapter { function_; instantiation; ty }) ->
      render_marker "Adapter"
      ^ mangle (Lowered.Item.make_code function_ instantiation)
      ^ render_marker "As" ^ mangle_ty (Function ty)
  | Generated (Locked_entry { capability; name }) ->
      render_marker "LockedEntry" ^ mangle_path capability ^ render_marker "Method"
      ^ mangle_text name
  | Generated (Entry impl_method) ->
      render_marker "Entry" ^ mangle (Lowered.Item.make_method_code impl_method)
  | Generated (Program_main main) -> render_marker "Program" ^ mangle_path main
  | Generated (Test_main test) -> render_marker "TestMain" ^ mangle_path test
  | Table (Locked_table capability) -> render_marker "LockedTable" ^ mangle_path capability
  | Table (Impl_table { impl; type_arguments }) ->
      render_marker "Table" ^ mangle_path impl ^ mangle_arguments type_arguments

let limit = 200
let prefix_length = 180

let shorten name =
  if String.length name <= limit then name
  else String.sub name 0 prefix_length ^ "_Hash_" ^ Blake3.hash_to_hex ~digits:32 name

let make_symbol item = shorten ("truss_" ^ mangle item)
let make_type_name ty = shorten ("truss_" ^ mangle_ty ty)
