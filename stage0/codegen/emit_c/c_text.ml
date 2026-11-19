type key =
  | Type of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Environment of Lowered.Item.t * int
  | Evidence of int
  | Capabilities of int

type reference =
  | Item of Lowered.Item.t
  | Type_name of key
  | Site of Lowered.site
  | Local of Lowered.local
  | Byte_constant of int
  | Nested_function of int
  | Static of int
  | Helper of C_runtime.helper
  | Capability of Path.t

type t = Text of string | Name of reference | Concat of t list

let empty = Concat []
let ( ++ ) first second = Concat [ first; second ]

let join separator parts =
  match parts with
  | [] -> empty
  | first :: rest -> Concat (first :: List.concat_map (fun part -> [ Text separator; part ]) rest)

let render_key_name = function
  | Type ty -> Mangling.make_type_name ty
  | Block (ty, variant) -> Mangling.make_type_name ty ^ "_Block_" ^ variant
  | Code function_type -> Mangling.make_type_name (Function function_type) ^ "_Code"
  | Environment (item, nested_index) ->
      Printf.sprintf "%s_Environment_%d" (Mangling.make_symbol item) nested_index
  | Evidence nested_index -> Printf.sprintf "t_Evidence_%d" nested_index
  | Capabilities count -> Printf.sprintf "t_Capabilities_%d" count

let render text ~resolve =
  let buffer = Buffer.create 256 in
  let rec add = function
    | Text text -> Buffer.add_string buffer text
    | Name reference -> Buffer.add_string buffer (resolve reference)
    | Concat parts -> List.iter add parts
  in
  add text;
  Buffer.contents buffer
