type capabilities = Path.t list list

type key =
  | Code of { path : Path.t; type_arguments : Ground.argument list; capabilities : capabilities }
  | Constant of Path.t
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty
  | Cursor_next of Ground.yielding
  | Cursor_drop of Ground.yielding
  | Adapter of key

let rank = function
  | Code _ -> 0
  | Constant _ -> 1
  | Drop _ -> 2
  | Copy _ -> 3
  | Debug _ -> 4
  | Cursor_next _ -> 5
  | Cursor_drop _ -> 6
  | Adapter _ -> 7

let ( >>= ) c next = if c <> 0 then c else next ()
let compare_capabilities = List.compare (List.compare Path.compare)

let rec compare a b =
  match (a, b) with
  | Code a, Code b ->
      Path.compare a.path b.path >>= fun () ->
      Ground.compare_arguments a.type_arguments b.type_arguments >>= fun () ->
      compare_capabilities a.capabilities b.capabilities
  | Constant a, Constant b -> Path.compare a b
  | Drop a, Drop b | Copy a, Copy b | Debug a, Debug b -> Ground.compare a b
  | Cursor_next a, Cursor_next b | Cursor_drop a, Cursor_drop b ->
      Ground.compare (Cursor a) (Cursor b)
  | Adapter a, Adapter b -> compare a b
  | _ -> Int.compare (rank a) (rank b)

let equal a b = compare a b = 0
let tagged n items = Cbor.Array (Cbor.int n :: items)
let encode_arguments arguments = Cbor.Array (List.map Ground.encode_argument arguments)

let encode_capabilities sets =
  Cbor.Array (List.map (fun set -> Cbor.Array (List.map Ground.encode_path set)) sets)

let rec encode = function
  | Code { path; type_arguments; capabilities } ->
      tagged 0
        [
          Ground.encode_path path; encode_arguments type_arguments; encode_capabilities capabilities;
        ]
  | Constant path -> tagged 1 [ Ground.encode_path path ]
  | Drop ty -> tagged 2 [ Ground.encode ty ]
  | Copy ty -> tagged 3 [ Ground.encode ty ]
  | Debug ty -> tagged 4 [ Ground.encode ty ]
  | Cursor_next yielding -> tagged 5 [ Ground.encode (Cursor yielding) ]
  | Cursor_drop yielding -> tagged 6 [ Ground.encode (Cursor yielding) ]
  | Adapter key -> tagged 7 [ encode key ]

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

and mangle_arguments = function
  | [] -> ""
  | arguments ->
      marker "Of" ^ String.concat (marker "And") (List.map mangle_argument arguments) ^ marker "End"

and mangle_capabilities = function
  | [] -> ""
  | sets ->
      String.concat ""
        (List.map
           (fun set ->
             marker "Granted" ^ String.concat (marker "And") (List.map path set) ^ marker "End")
           sets)

and mangle_yielding (yielding : Ground.yielding) =
  path yielding.method_
  ^ mangle_arguments yielding.type_arguments
  ^ mangle_capabilities yielding.capabilities

let rec mangle = function
  | Code { path = p; type_arguments; capabilities } ->
      path p ^ mangle_arguments type_arguments ^ mangle_capabilities capabilities
  | Constant p -> marker "Constant" ^ path p
  | Drop ty -> marker "Drop" ^ mangle_ty ty
  | Copy ty -> marker "Copy" ^ mangle_ty ty
  | Debug ty -> marker "Debug" ^ mangle_ty ty
  | Cursor_next yielding -> marker "Next" ^ mangle_yielding yielding
  | Cursor_drop yielding -> marker "Release" ^ mangle_yielding yielding
  | Adapter key -> marker "Adapter" ^ mangle key

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
  | Cursor_next yielding -> "next " ^ Ground.to_string (Cursor yielding)
  | Cursor_drop yielding -> "release " ^ Ground.to_string (Cursor yielding)
  | Adapter key -> "adapter " ^ to_string key

and arguments_to_string = function
  | [] -> ""
  | arguments ->
      "["
      ^ String.concat ", "
          (List.map
             (function Ground.Type ty -> Ground.to_string ty | Value v -> Z.to_string v)
             arguments)
      ^ "]"
