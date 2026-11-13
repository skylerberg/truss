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
  | Cursor_next of Ground.yielding
  | Looped of { yielding : Ground.yielding; chunked : bool }
  | Adapter of { function_ : key; ty : Ground.function_type }
  | Entry of key
  | Table of { impl : Path.t; type_arguments : Ground.argument list }
  | Program_main of Path.t
  | Any_entry of key
  | Any_table of { impl : Path.t; type_arguments : Ground.argument list }
  | Locked_entry of { capability : Path.t; name : string }
  | Locked_table of Path.t

let rank = function
  | Code _ -> 0
  | Constant _ -> 1
  | Drop _ -> 2
  | Copy _ -> 3
  | Debug _ -> 4
  | Cursor_next _ -> 5
  | Adapter _ -> 6
  | Entry _ -> 7
  | Table _ -> 8
  | Program_main _ -> 10
  | Any_entry _ -> 11
  | Any_table _ -> 12
  | Encode _ -> 13
  | Evaluator _ -> 14
  | Any_drop _ -> 15
  | Template_check _ -> 16
  | Call_evaluation _ -> 17
  | Locked_entry _ -> 18
  | Looped _ -> 20
  | Locked_table _ -> 19

let ( >>= ) order next = if order <> 0 then order else next ()

let rec compare left right =
  match (left, right) with
  | Code left, Code right ->
      Path.compare left.path right.path >>= fun () ->
      Ground.compare_arguments left.type_arguments right.type_arguments
  | Constant left, Constant right -> Path.compare left right
  | Drop left, Drop right
  | Copy left, Copy right
  | Debug left, Debug right
  | Encode left, Encode right
  | Any_drop left, Any_drop right ->
      Ground.compare left right
  | Cursor_next left, Cursor_next right -> Ground.compare (Cursor left) (Cursor right)
  | Looped left, Looped right ->
      Ground.compare (Cursor left.yielding) (Cursor right.yielding) >>= fun () ->
      Bool.compare left.chunked right.chunked
  | Adapter left, Adapter right ->
      compare left.function_ right.function_ >>= fun () ->
      Ground.compare (Function left.ty) (Function right.ty)
  | Entry left, Entry right | Any_entry left, Any_entry right -> compare left right
  | Any_table left, Any_table right ->
      Path.compare left.impl right.impl >>= fun () ->
      Ground.compare_arguments left.type_arguments right.type_arguments
  | Locked_entry left, Locked_entry right ->
      Path.compare left.capability right.capability >>= fun () ->
      String.compare left.name right.name
  | Locked_table left, Locked_table right -> Path.compare left right
  | Table left, Table right ->
      Path.compare left.impl right.impl >>= fun () ->
      Ground.compare_arguments left.type_arguments right.type_arguments
  | Program_main left, Program_main right | Evaluator left, Evaluator right ->
      Path.compare left right
  | Template_check left, Template_check right ->
      Path.compare left.from_template right.from_template >>= fun () ->
      List.compare String.compare left.texts right.texts
  | Call_evaluation left, Call_evaluation right ->
      Path.compare left.function_ right.function_ >>= fun () ->
      List.compare Z.compare left.arguments right.arguments
  | _ -> Int.compare (rank left) (rank right)

let equal left right = compare left right = 0
let tagged tag items = Cbor.Array (Cbor.int tag :: items)

let rec encode ?(path = Ground.encode_path) key =
  let ty = Ground.encode ~path in
  let arguments arguments = Cbor.Array (List.map (Ground.encode_argument ~path) arguments) in
  match key with
  | Code { path = instance_path; type_arguments } ->
      tagged 0 [ path instance_path; arguments type_arguments ]
  | Constant instance_path -> tagged 1 [ path instance_path ]
  | Drop component_type -> tagged 2 [ ty component_type ]
  | Copy component_type -> tagged 3 [ ty component_type ]
  | Debug component_type -> tagged 4 [ ty component_type ]
  | Encode component_type -> tagged 13 [ ty component_type ]
  | Any_drop component_type -> tagged 15 [ ty component_type ]
  | Evaluator instance_path -> tagged 14 [ path instance_path ]
  | Template_check { from_template; texts } ->
      tagged 16 [ path from_template; Cbor.Array (List.map (fun text -> Cbor.Text text) texts) ]
  | Call_evaluation { function_; arguments } ->
      tagged 17
        [
          path function_;
          Cbor.Array (List.map (fun number -> Cbor.Text (Z.to_string number)) arguments);
        ]
  | Cursor_next yielding -> tagged 5 [ ty (Cursor yielding) ]
  | Looped { yielding; chunked } -> tagged 20 [ ty (Cursor yielding); Cbor.Bool chunked ]
  | Adapter { function_; ty } ->
      tagged 6 [ encode ~path function_; Ground.encode ~path (Function ty) ]
  | Any_entry key -> tagged 11 [ encode ~path key ]
  | Any_table { impl; type_arguments } -> tagged 12 [ path impl; arguments type_arguments ]
  | Locked_entry { capability; name } -> tagged 18 [ path capability; Cbor.Text name ]
  | Locked_table capability -> tagged 19 [ path capability ]
  | Entry key -> tagged 7 [ encode ~path key ]
  | Table { impl; type_arguments } -> tagged 8 [ path impl; arguments type_arguments ]
  | Program_main main -> tagged 10 [ path main ]

(* Mangling. A Truss name is either [UpperCamelCase], with no [_], or
   [lower_snake_case], with no uppercase letter, no [__], and no [_] at
   either end. So in a symbol, [__] can only separate the parts of a module
   path, [_] followed by a lowercase letter can only separate a type from
   its method's name, and [_] followed by an uppercase word and another [_]
   is a marker, such as [_Of_] before type arguments. Text that is not a
   name, such as an [impl]'s name ["From[Int32] for Int64"] or a test's
   name, is written between markers with every character other than a
   letter or digit, [_] included, as a marker [_C] and its hexadecimal code
   [_]. Every name ends where one of these begins, so a symbol reads back in
   exactly one way: mangling never gives two keys one symbol. *)

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
        | Yields (module_, ty) -> marker "Yields" ^ mode module_ ^ mangle_ty ty
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
  | Cursor yielding -> marker "Cursor" ^ mangle_yielding yielding ^ marker "End"
  | Lent lent -> mangle_lent lent
  | Never -> marker "Never"

and mangle_lent ({ base; writable; fields } : Ground.lent) =
  marker "Lent"
  ^ (if writable then marker "Mut" else "")
  ^ mangle_ty base
  ^ String.concat ""
      (List.map
         (fun ({ variant; field; holds } : Ground.lent_field) ->
           marker "Field"
           ^ Option.fold ~none:"" ~some:(fun variant -> text variant ^ marker "Variant") variant
           ^ text field
           ^ match holds with Address -> marker "Address" | Nested lent -> mangle_lent lent)
         fields)
  ^ marker "End"

and mangle_argument = function
  | Ground.Type ty -> mangle_ty ty
  | Value value -> marker "Value" ^ Z.to_string value
  | Capabilities set ->
      marker "Granted" ^ String.concat (marker "And") (List.map path set) ^ marker "End"

and mangle_arguments = function
  | [] -> ""
  | arguments ->
      marker "Of" ^ String.concat (marker "And") (List.map mangle_argument arguments) ^ marker "End"

and mangle_yielding (yielding : Ground.yielding) =
  path yielding.method_ ^ mangle_arguments yielding.type_arguments

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
  | Cursor_next yielding -> marker "Next" ^ mangle_yielding yielding
  | Looped { yielding; chunked } ->
      marker (if chunked then "Chunked" else "Looped") ^ mangle_yielding yielding
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

(* A long name keeps its start, which a profiler shows, and ends
   with a hash of the whole name, which keeps it unique. *)
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
  | Cursor_next yielding -> "next " ^ Ground.to_string (Cursor yielding)
  | Looped { yielding; chunked } ->
      (if chunked then "chunked " else "looped ") ^ Ground.to_string (Cursor yielding)
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
