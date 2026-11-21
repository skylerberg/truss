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
  | Nested_body of int
  | Static of int
  | Helper of C_runtime.helper
  | Capability of Path.t

type t =
  | Text of string
  | Name of reference
  | Concat of t list
  | Line_control of Lowered.site option

type segment = { site : Lowered.site option; text : string }

let empty = Concat []
let ( ++ ) first second = Concat [ first; second ]

let join separator parts =
  match parts with
  | [] -> empty
  | first :: rest -> Concat (first :: List.concat_map (fun part -> [ Text separator; part ]) rest)

let render_braces = function
  | [] -> Text "{ 0 }"
  | parts -> Text "{ " ++ join ", " parts ++ Text " }"

let render_key_name = function
  | Type ty -> Mangling.make_type_name ty
  | Block (ty, variant) -> Mangling.make_type_name ty ^ "_Block_" ^ variant
  | Code function_type -> Mangling.make_type_name (Function function_type) ^ "_Code"
  | Environment (item, nested_index) ->
      Printf.sprintf "%s_Environment_%d" (Mangling.make_symbol item) nested_index
  | Evidence nested_index -> Printf.sprintf "truss_Evidence_%d" nested_index
  | Capabilities count -> Printf.sprintf "truss_Capabilities_%d" count

let render text ~resolve =
  let buffer = Buffer.create 256 in
  let rec add = function
    | Text text -> Buffer.add_string buffer text
    | Name reference -> Buffer.add_string buffer (resolve reference)
    | Concat parts -> List.iter add parts
    | Line_control _ -> ()
  in
  add text;
  Buffer.contents buffer

let render_segments text ~site ~resolve =
  let buffer = Buffer.create 256 in
  let segments = ref [] and current = ref site in
  let close_segment () =
    if Buffer.length buffer > 0 then begin
      segments := { site = !current; text = Buffer.contents buffer } :: !segments;
      Buffer.clear buffer
    end
  in
  let rec add = function
    | Text text -> Buffer.add_string buffer text
    | Name reference -> Buffer.add_string buffer (resolve reference)
    | Concat parts -> List.iter add parts
    | Line_control site ->
        if site <> !current then begin
          close_segment ();
          current := site
        end
  in
  add text;
  close_segment ();
  List.rev !segments
