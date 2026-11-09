type capabilities = Ground.definition list list

type key =
  | Function of {
      definition : Ground.definition;
      type_arguments : Ground.argument list;
      capabilities : capabilities;
    }
  | Method of {
      owner : Ground.definition;
      name : string;
      receiver : Ground.mode option;
      type_arguments : Ground.argument list;
      capabilities : capabilities;
    }
  | Impl_method of {
      trait : Ground.definition;
      trait_arguments : Ground.argument list;
      self : Ground.ty;
      name : string;
      receiver : Ground.mode option;
      type_arguments : Ground.argument list;
      capabilities : capabilities;
    }
  | Constant of Ground.definition
  | Drop of Ground.ty
  | Copy of Ground.ty
  | Debug of Ground.ty
  | Cursor_next of Ground.yielding
  | Cursor_drop of Ground.yielding
  | Adapter of key

let rank = function
  | Function _ -> 0
  | Method _ -> 1
  | Impl_method _ -> 2
  | Constant _ -> 3
  | Drop _ -> 4
  | Copy _ -> 5
  | Debug _ -> 6
  | Cursor_next _ -> 7
  | Cursor_drop _ -> 8
  | Adapter _ -> 9

let ( >>= ) c next = if c <> 0 then c else next ()
let compare_arguments = Ground.compare_arguments
let compare_capabilities = List.compare (List.compare Ground.compare_definition)

let rec compare a b =
  match (a, b) with
  | Function a, Function b ->
      Ground.compare_definition a.definition b.definition >>= fun () ->
      compare_arguments a.type_arguments b.type_arguments >>= fun () ->
      compare_capabilities a.capabilities b.capabilities
  | Method a, Method b ->
      Ground.compare_definition a.owner b.owner >>= fun () ->
      String.compare a.name b.name >>= fun () ->
      Stdlib.compare a.receiver b.receiver >>= fun () ->
      compare_arguments a.type_arguments b.type_arguments >>= fun () ->
      compare_capabilities a.capabilities b.capabilities
  | Impl_method a, Impl_method b ->
      Ground.compare_definition a.trait b.trait >>= fun () ->
      compare_arguments a.trait_arguments b.trait_arguments >>= fun () ->
      Ground.compare a.self b.self >>= fun () ->
      String.compare a.name b.name >>= fun () ->
      Stdlib.compare a.receiver b.receiver >>= fun () ->
      compare_arguments a.type_arguments b.type_arguments >>= fun () ->
      compare_capabilities a.capabilities b.capabilities
  | Constant a, Constant b -> Ground.compare_definition a b
  | Drop a, Drop b | Copy a, Copy b | Debug a, Debug b -> Ground.compare a b
  | Cursor_next a, Cursor_next b | Cursor_drop a, Cursor_drop b ->
      Ground.compare (Cursor a) (Cursor b)
  | Adapter a, Adapter b -> compare a b
  | _ -> Int.compare (rank a) (rank b)

let equal a b = compare a b = 0
let tagged n items = Cbor.Array (Cbor.int n :: items)
let encode_arguments arguments = Cbor.Array (List.map Ground.encode_argument arguments)

let encode_capabilities sets =
  Cbor.Array (List.map (fun set -> Cbor.Array (List.map Ground.encode_definition set)) sets)

let encode_receiver = function None -> Cbor.Null | Some mode -> Ground.encode_mode mode

let rec encode = function
  | Function { definition; type_arguments; capabilities } ->
      tagged 0
        [
          Ground.encode_definition definition;
          encode_arguments type_arguments;
          encode_capabilities capabilities;
        ]
  | Method { owner; name; receiver; type_arguments; capabilities } ->
      tagged 1
        [
          Ground.encode_definition owner;
          Text name;
          encode_receiver receiver;
          encode_arguments type_arguments;
          encode_capabilities capabilities;
        ]
  | Impl_method { trait; trait_arguments; self; name; receiver; type_arguments; capabilities } ->
      tagged 2
        [
          Ground.encode_definition trait;
          encode_arguments trait_arguments;
          Ground.encode self;
          Text name;
          encode_receiver receiver;
          encode_arguments type_arguments;
          encode_capabilities capabilities;
        ]
  | Constant definition -> tagged 3 [ Ground.encode_definition definition ]
  | Drop ty -> tagged 4 [ Ground.encode ty ]
  | Copy ty -> tagged 5 [ Ground.encode ty ]
  | Debug ty -> tagged 6 [ Ground.encode ty ]
  | Cursor_next yielding -> tagged 7 [ Ground.encode (Cursor yielding) ]
  | Cursor_drop yielding -> tagged 8 [ Ground.encode (Cursor yielding) ]
  | Adapter key -> tagged 9 [ encode key ]

let definition = function
  | Function { definition; _ } | Constant definition -> Some definition
  | Method { owner; name; _ } -> Some { owner with name = owner.name ^ "." ^ name }
  | Impl_method { trait; name; _ } -> Some { trait with name = trait.name ^ "." ^ name }
  | Drop _ | Copy _ | Debug _ | Adapter _ -> None
  | Cursor_next yielding | Cursor_drop yielding -> Some yielding.method_

(* Mangling. A Truss name is either [UpperCamelCase], with no [_], or
   [lower_snake_case], with no uppercase letter, no [__], and no [_] at
   either end. So in a symbol, [__] can only separate the parts of a path,
   [_] followed by a lowercase letter can only separate a type from its
   method's name, and [_] followed by an uppercase word and another [_] is a
   marker, such as [_Of_] before type arguments. Every name ends where one
   of these begins, so a symbol is read back in exactly one way: mangling
   never gives two keys one symbol. *)

let path (definition : Ground.definition) =
  String.concat "__" ((definition.package :: definition.modules) @ [ definition.name ])

let marker word = "_" ^ word ^ "_"

let rec mangle_ty (ty : Ground.ty) =
  match ty with
  | Named { definition; arguments } -> path definition ^ mangle_arguments arguments
  | Function { parameters; result; uses } ->
      marker "Fn"
      ^ String.concat ""
          (List.map
             (fun (mode, ty) -> mangle_mode (Some mode) ^ mangle_ty ty ^ marker "And")
             parameters)
      ^ (match result with
        | Returns ty -> marker "Returns" ^ mangle_ty ty
        | Yields (mode, ty) -> marker "Yields" ^ mangle_mode (Some mode) ^ mangle_ty ty
        | Lends (mode, ty) -> marker "Lends" ^ mangle_mode (Some mode) ^ mangle_ty ty)
      ^ mangle_uses uses ^ marker "End"
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

and mangle_mode = function
  | None -> marker "Static"
  | Some Ground.Read -> ""
  | Some Mut -> marker "Mut"
  | Some Own -> marker "Own"

and mangle_uses = function
  | [] -> ""
  | uses -> marker "Uses" ^ String.concat (marker "And") (List.map path uses)

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
  ^ mangle_mode (Some yielding.receiver)
  ^ mangle_arguments yielding.type_arguments
  ^ mangle_capabilities yielding.capabilities

let rec mangle = function
  | Function { definition; type_arguments; capabilities } ->
      path definition ^ mangle_arguments type_arguments ^ mangle_capabilities capabilities
  | Method { owner; name; receiver; type_arguments; capabilities } ->
      path owner ^ "_" ^ name ^ mangle_mode receiver ^ mangle_arguments type_arguments
      ^ mangle_capabilities capabilities
  | Impl_method { trait; trait_arguments; self; name; receiver; type_arguments; capabilities } ->
      marker "Impl" ^ path trait ^ mangle_arguments trait_arguments ^ marker "For" ^ mangle_ty self
      ^ marker "Method" ^ name ^ mangle_mode receiver ^ mangle_arguments type_arguments
      ^ mangle_capabilities capabilities
  | Constant definition -> marker "Constant" ^ path definition
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

let mode_to_string = function
  | None -> "static "
  | Some Ground.Read -> ""
  | Some Mut -> "mut "
  | Some Own -> "own "

let rec to_string = function
  | Function { definition; type_arguments; _ } ->
      Ground.definition_to_string definition ^ arguments_to_string type_arguments
  | Method { owner; name; receiver; type_arguments; _ } ->
      mode_to_string receiver ^ Ground.definition_to_string owner ^ "." ^ name
      ^ arguments_to_string type_arguments
  | Impl_method { trait; trait_arguments; self; name; receiver; _ } ->
      mode_to_string receiver ^ "impl " ^ trait.name
      ^ arguments_to_string trait_arguments
      ^ " for " ^ Ground.to_string self ^ "." ^ name
  | Constant definition -> Ground.definition_to_string definition
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
