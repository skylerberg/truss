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
  | Adapter of { function_ : key; ty : Ground.function_type }
  | Entry of key
      (** The entry for an [impl]'s method of a capability: takes the evidence, then calls the
          method on its implementation with the evidence that implementation captured *)
  | Table of { impl : Path.t; type_arguments : Ground.argument list }
      (** A capability [impl]'s table of entries, one for each of the capability's methods *)
  | Real_evidence of Path.t
      (** The evidence for the real implementation of a standard capability, which a program's
          [main] is given *)
  | Program_main of Path.t  (** The C [main]'s Truss side: it calls the program's [main] *)
  | Any_entry of key
      (** The entry for an [impl]'s method in an [any] table: takes a pointer to the value *)
  | Any_table of { impl : Path.t; type_arguments : Ground.argument list }
      (** The table of an [any] value of a type and trait: the type's drop, then an entry for each
          of the trait's methods *)

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
  | Real_evidence _ -> 9
  | Program_main _ -> 10
  | Any_entry _ -> 11
  | Any_table _ -> 12
  | Encode _ -> 13
  | Evaluator _ -> 14
  | Any_drop _ -> 15
  | Template_check _ -> 16
  | Call_evaluation _ -> 17

let ( >>= ) c next = if c <> 0 then c else next ()

let rec compare a b =
  match (a, b) with
  | Code a, Code b ->
      Path.compare a.path b.path >>= fun () ->
      Ground.compare_arguments a.type_arguments b.type_arguments
  | Constant a, Constant b -> Path.compare a b
  | Drop a, Drop b | Copy a, Copy b | Debug a, Debug b | Encode a, Encode b | Any_drop a, Any_drop b
    ->
      Ground.compare a b
  | Cursor_next a, Cursor_next b -> Ground.compare (Cursor a) (Cursor b)
  | Adapter a, Adapter b ->
      compare a.function_ b.function_ >>= fun () -> Ground.compare (Function a.ty) (Function b.ty)
  | Entry a, Entry b | Any_entry a, Any_entry b -> compare a b
  | Any_table a, Any_table b ->
      Path.compare a.impl b.impl >>= fun () ->
      Ground.compare_arguments a.type_arguments b.type_arguments
  | Table a, Table b ->
      Path.compare a.impl b.impl >>= fun () ->
      Ground.compare_arguments a.type_arguments b.type_arguments
  | Real_evidence a, Real_evidence b | Program_main a, Program_main b | Evaluator a, Evaluator b ->
      Path.compare a b
  | Template_check a, Template_check b ->
      Path.compare a.from_template b.from_template >>= fun () ->
      List.compare String.compare a.texts b.texts
  | Call_evaluation a, Call_evaluation b ->
      Path.compare a.function_ b.function_ >>= fun () ->
      List.compare Z.compare a.arguments b.arguments
  | _ -> Int.compare (rank a) (rank b)

let equal a b = compare a b = 0
let tagged n items = Cbor.Array (Cbor.int n :: items)

let rec encode ?(path = Ground.encode_path) key =
  let ty = Ground.encode ~path in
  let arguments arguments = Cbor.Array (List.map (Ground.encode_argument ~path) arguments) in
  match key with
  | Code { path = p; type_arguments } -> tagged 0 [ path p; arguments type_arguments ]
  | Constant p -> tagged 1 [ path p ]
  | Drop t -> tagged 2 [ ty t ]
  | Copy t -> tagged 3 [ ty t ]
  | Debug t -> tagged 4 [ ty t ]
  | Encode t -> tagged 13 [ ty t ]
  | Any_drop t -> tagged 15 [ ty t ]
  | Evaluator p -> tagged 14 [ path p ]
  | Template_check { from_template; texts } ->
      tagged 16 [ path from_template; Cbor.Array (List.map (fun text -> Cbor.Text text) texts) ]
  | Call_evaluation { function_; arguments } ->
      tagged 17
        [ path function_; Cbor.Array (List.map (fun z -> Cbor.Text (Z.to_string z)) arguments) ]
  | Cursor_next yielding -> tagged 5 [ ty (Cursor yielding) ]
  | Adapter { function_; ty } ->
      tagged 6 [ encode ~path function_; Ground.encode ~path (Function ty) ]
  | Any_entry key -> tagged 11 [ encode ~path key ]
  | Any_table { impl; type_arguments } -> tagged 12 [ path impl; arguments type_arguments ]
  | Entry key -> tagged 7 [ encode ~path key ]
  | Table { impl; type_arguments } -> tagged 8 [ path impl; arguments type_arguments ]
  | Real_evidence capability -> tagged 9 [ path capability ]
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
let module_path (m : Path.module_) = String.concat "__" (m.package :: m.modules)

let text value =
  String.concat ""
    (List.map
       (fun c ->
         match c with
         | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> String.make 1 c
         | c -> Printf.sprintf "_C%02X_" (Char.code c))
       (List.of_seq (String.to_seq value)))

let receiver : Path.receiver -> string = function
  | Static -> marker "Static"
  | Read -> ""
  | Mut -> marker "Mut"
  | Own -> marker "Own"

let rec path : Path.t -> string = function
  | Top { module_; name } -> module_path module_ ^ "__" ^ name
  | Method { owner; name; receiver = r } -> path owner ^ "_" ^ name ^ receiver r
  | Member_constant { owner; name } -> path owner ^ marker "Member" ^ name
  | Impl { module_; name } -> module_path module_ ^ marker "Impl" ^ text name ^ marker "End"
  | Derived { type_; trait } ->
      marker "Derived" ^ path trait ^ marker "For" ^ path type_ ^ marker "End"
  | Test { module_; name } -> module_path module_ ^ marker "Test" ^ text name ^ marker "End"
  | Law_proof { module_; name } -> module_path module_ ^ marker "Proof" ^ text name ^ marker "End"

let mode : Ground.mode -> string = function Read -> "" | Mut -> marker "Mut" | Own -> marker "Own"

let rec mangle_ty (ty : Ground.ty) =
  match ty with
  | Named { path = p; arguments } -> path p ^ mangle_arguments arguments
  | Function { parameters; result; uses } ->
      marker "Fn"
      ^ String.concat "" (List.map (fun (m, ty) -> mode m ^ mangle_ty ty ^ marker "And") parameters)
      ^ (match result with
        | Returns ty -> marker "Returns" ^ mangle_ty ty
        | Yields (m, ty) -> marker "Yields" ^ mode m ^ mangle_ty ty
        | Lends (m, ty) -> marker "Lends" ^ mode m ^ mangle_ty ty)
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

and mangle_yielding (yielding : Ground.yielding) =
  path yielding.method_ ^ mangle_arguments yielding.type_arguments

let rec mangle = function
  | Code { path = p; type_arguments } -> path p ^ mangle_arguments type_arguments
  | Constant p -> marker "Constant" ^ path p
  | Drop ty -> marker "Drop" ^ mangle_ty ty
  | Copy ty -> marker "Copy" ^ mangle_ty ty
  | Debug ty -> marker "Debug" ^ mangle_ty ty
  | Encode ty -> marker "Encode" ^ mangle_ty ty
  | Any_drop ty -> marker "Any_drop" ^ mangle_ty ty
  | Evaluator p -> marker "Evaluator" ^ path p
  | Template_check { from_template; texts } ->
      marker "Check" ^ path from_template
      ^ String.concat "" (List.map (fun t -> marker "Text" ^ text t ^ marker "End") texts)
  | Call_evaluation { function_; arguments } ->
      marker "Evaluate" ^ path function_
      ^ String.concat "" (List.map (fun z -> marker "Value" ^ text (Z.to_string z)) arguments)
      ^ marker "End"
  | Cursor_next yielding -> marker "Next" ^ mangle_yielding yielding
  | Adapter { function_; ty } ->
      marker "Adapter" ^ mangle function_ ^ marker "As" ^ mangle_ty (Function ty)
  | Any_entry key -> marker "Dynamic" ^ mangle key
  | Any_table { impl; type_arguments } ->
      marker "Vtable" ^ path impl ^ mangle_arguments type_arguments
  | Entry key -> marker "Entry" ^ mangle key
  | Table { impl; type_arguments } -> marker "Table" ^ path impl ^ mangle_arguments type_arguments
  | Real_evidence capability -> marker "Evidence" ^ path capability
  | Program_main main -> marker "Program" ^ path main

let limit = 200
let kept = 180

(* A long name keeps its start, which is what a profiler shows, and ends
   with a hash of the whole name, which keeps it unique. *)
let shorten name =
  if String.length name <= limit then name
  else String.sub name 0 kept ^ "_Hash_" ^ String.sub (Blake3.to_hex (Blake3.hash name)) 0 32

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
  | Adapter { function_; _ } -> "adapter " ^ to_string function_
  | Any_entry key -> "any entry " ^ to_string key
  | Any_table { impl; type_arguments } ->
      "any table " ^ Path.show impl ^ arguments_to_string type_arguments
  | Entry key -> "entry " ^ to_string key
  | Table { impl; type_arguments } -> "table " ^ Path.show impl ^ arguments_to_string type_arguments
  | Real_evidence capability -> "real evidence " ^ Path.show capability
  | Program_main main -> "program " ^ Path.show main

and arguments_to_string = function
  | [] -> ""
  | arguments -> "[" ^ String.concat ", " (List.map Ground.argument_to_string arguments) ^ "]"
