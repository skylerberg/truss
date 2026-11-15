let bug format = Compiler_bug.bug ~stage:"Memory_layout" format

type integer = Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64

type pointee =
  | Data of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Opaque

type scalar =
  | Integer of integer
  | Float32
  | Float64
  | Bool
  | Character
  | Pointer of pointee
  | Nullable_pointer of pointee

type member = Typed of Ground.ty | Raw of scalar

type shape =
  | Scalar of scalar
  | Record of (string * member) list
  | Sum of variant_shape list
  | Array of Ground.ty * int

and variant_shape = { name : string; indirect : bool; fields : (string * member) list }

type representation = Shape of shape | Storage of Ground.ty | Handle | Shared of Ground.ty

type t = { size : int; alignment : int; form : form; niche : niche option }

and form =
  | Zero_size
  | Scalar of scalar
  | Struct of field list
  | Array of { element : Ground.ty; element_layout : t; count : int }
  | Tag_only of { tag : integer; variants : string list }
  | Tagged of { tag : integer; payload_offset : int; variants : variant list }
  | Niche_encoded of { dataful : variant; others : (string * Z.t) list; encoding : niche option }

and field = { name : string; member : member; layout : t; offset : int }
and variant = { name : string; index : int; payload : t }
and niche = { path : step list; scalar : scalar; start : Z.t; count : Z.t }
and step = Field of string | Tag

type env = { system : Libc.system; shape_of : Ground.ty -> shape; layout_of : Ground.ty -> t }

let create system ~shape_of ~layout_of = { system; shape_of; layout_of }
let system env = env.system
let shape env ty = env.shape_of ty
let of_type env ty = env.layout_of ty

let integer_size = function
  | Int8 | UInt8 -> 1
  | Int16 | UInt16 -> 2
  | Int32 | UInt32 -> 4
  | Int64 | UInt64 -> 8

let integer_range integer =
  let bits = 8 * integer_size integer in
  match integer with
  | Int8 | Int16 | Int32 | Int64 ->
      (Z.neg (Z.shift_left Z.one (bits - 1)), Z.pred (Z.shift_left Z.one (bits - 1)))
  | UInt8 | UInt16 | UInt32 | UInt64 -> (Z.zero, Z.pred (Z.shift_left Z.one bits))

let scalar_size = function
  | Integer integer -> integer_size integer
  | Float32 -> 4
  | Float64 -> 8
  | Bool -> 1
  | Character -> 4
  | Pointer _ | Nullable_pointer _ -> 8

let zero_size = { size = 0; alignment = 1; form = Zero_size; niche = None }
let round_up value alignment = (value + alignment - 1) / alignment * alignment
let bits bytes = Z.shift_left Z.one (8 * bytes)

let scalar_niche = function
  | Bool -> Some { path = []; scalar = Bool; start = Z.of_int 2; count = Z.of_int 254 }
  | Character ->
      let start = Z.of_int 0x110000 in
      Some { path = []; scalar = Character; start; count = Z.sub (bits 4) start }
  | Pointer _ as scalar -> Some { path = []; scalar; start = Z.zero; count = Z.one }
  | Integer _ | Float32 | Float64 | Nullable_pointer _ -> None

let of_scalar scalar =
  let size = scalar_size scalar in
  { size; alignment = size; form = Scalar scalar; niche = scalar_niche scalar }

let tag_for count = if count <= 0x100 then UInt8 else if count <= 0x10000 then UInt16 else UInt32

let tag_niche tag count path =
  let start = Z.of_int count in
  { path; scalar = Integer tag; start; count = Z.sub (bits (integer_size tag)) start }

let under name niche = { niche with path = Field name :: niche.path }

let best_niche (fields : field list) =
  List.fold_left
    (fun best (field : field) ->
      match (field.layout.niche, best) with
      | None, _ -> best
      | Some niche, None -> Some (under field.name niche)
      | Some niche, Some current ->
          if Z.gt niche.count current.count then Some (under field.name niche) else best)
    None fields

let place (fields : (string * member * t) list) =
  let sized = List.filter (fun (_, _, (layout : t)) -> layout.size > 0) fields in
  let ordered =
    List.stable_sort
      (fun (name, _, (left : t)) (other, _, (right : t)) ->
        let order = Int.compare right.alignment left.alignment in
        if order <> 0 then order else String.compare name other)
      sized
  in
  let offset, alignment, placed =
    List.fold_left
      (fun (offset, alignment, placed) (name, member, (layout : t)) ->
        let offset = round_up offset layout.alignment in
        ( offset + layout.size,
          max alignment layout.alignment,
          { name; member; layout; offset } :: placed ))
      (0, 1, []) ordered
  in
  let placed = List.rev placed in
  if placed = [] then zero_size
  else
    { size = round_up offset alignment; alignment; form = Struct placed; niche = best_niche placed }

let of_member layout_of = function Typed ty -> layout_of ty | Raw scalar -> of_scalar scalar

let fields layout_of fields =
  place (List.map (fun (name, member) -> (name, member, of_member layout_of member)) fields)

let rec layout ~layout_of ty (shape : shape) =
  match shape with
  | Scalar scalar -> of_scalar scalar
  | Record fields' -> fields layout_of fields'
  | Array (_, 0) -> zero_size
  | Array (element, count) ->
      let element_layout = layout_of element in
      if element_layout.size = 0 then zero_size
      else
        {
          size = element_layout.size * count;
          alignment = element_layout.alignment;
          form = Array { element; element_layout; count };
          niche = None;
        }
  | Sum variants -> of_sum layout_of ty variants

and payload layout_of ty (variant : variant_shape) =
  if variant.indirect then of_scalar (Pointer (Block (ty, variant.name)))
  else fields layout_of variant.fields

and of_sum layout_of ty shapes =
  let variants =
    List.mapi
      (fun index (shape : variant_shape) ->
        { name = shape.name; index; payload = payload layout_of ty shape })
      shapes
  in
  let count = List.length variants in
  let dataful, dataless = List.partition (fun variant -> variant.payload.size > 0) variants in
  match dataful with
  | [] when count <= 1 -> zero_size
  | [] ->
      let tag = tag_for count in
      let size = integer_size tag in
      {
        size;
        alignment = size;
        form =
          Tag_only { tag; variants = List.map (fun (variant : variant) -> variant.name) variants };
        niche = Some (tag_niche tag count []);
      }
  | [ only ]
    when match only.payload.niche with
         | Some niche -> Z.geq niche.count (Z.of_int (List.length dataless))
         | None -> dataless = [] ->
      let encoding, others, niche =
        match only.payload.niche with
        | None -> (None, [], None)
        | Some niche ->
            let used = List.length dataless in
            let others =
              List.mapi
                (fun position (variant : variant) ->
                  (variant.name, Z.add niche.start (Z.of_int position)))
                dataless
            in
            let remaining = Z.sub niche.count (Z.of_int used) in
            let rest =
              if Z.equal remaining Z.zero then None
              else Some { niche with start = Z.add niche.start (Z.of_int used); count = remaining }
            in
            (Some niche, others, rest)
      in
      {
        size = only.payload.size;
        alignment = only.payload.alignment;
        form = Niche_encoded { dataful = only; others; encoding };
        niche;
      }
  | _ ->
      let tag = tag_for count in
      let tag_size = integer_size tag in
      let union_size, union_alignment =
        List.fold_left
          (fun (size, alignment) variant ->
            (max size variant.payload.size, max alignment variant.payload.alignment))
          (0, 1) variants
      in
      let payload_offset = round_up tag_size union_alignment in
      let alignment = max tag_size union_alignment in
      {
        size = round_up (payload_offset + union_size) alignment;
        alignment;
        form = Tagged { tag; payload_offset; variants };
        niche = Some (tag_niche tag count [ Tag ]);
      }

let block env ty name =
  match env.shape_of ty with
  | Sum variants -> (
      match List.find_opt (fun (variant : variant_shape) -> variant.name = name) variants with
      | Some { indirect = true; fields = fields'; _ } -> fields env.layout_of fields'
      | Some _ -> bug "variant %s is not indirect" name
      | None -> bug "no variant %s" name)
  | _ -> bug "a block of a type that is not a sum type"

type discriminant = Only | Tag_value of Z.t | Niche_value of Z.t | Not_niche

let discriminant layout name =
  let missing () = bug "no variant %s" name in
  match layout.form with
  | Zero_size -> Only
  | Tag_only { variants; _ } -> (
      match List.find_index (String.equal name) variants with
      | Some index -> Tag_value (Z.of_int index)
      | None -> missing ())
  | Tagged { variants; _ } -> (
      match List.find_opt (fun (variant : variant) -> variant.name = name) variants with
      | Some variant -> Tag_value (Z.of_int variant.index)
      | None -> missing ())
  | Niche_encoded { dataful; others; _ } -> (
      if dataful.name = name then if others = [] then Only else Not_niche
      else
        match List.assoc_opt name others with Some value -> Niche_value value | None -> missing ())
  | Scalar _ | Struct _ | Array _ -> bug "a discriminant of a type that is not a sum type"

let integer_to_string = function
  | Int8 -> "Int8"
  | Int16 -> "Int16"
  | Int32 -> "Int32"
  | Int64 -> "Int64"
  | UInt8 -> "UInt8"
  | UInt16 -> "UInt16"
  | UInt32 -> "UInt32"
  | UInt64 -> "UInt64"

let scalar_to_string = function
  | Integer integer -> integer_to_string integer
  | Float32 -> "Float32"
  | Float64 -> "Float64"
  | Bool -> "Bool"
  | Character -> "Character"
  | Pointer _ -> "pointer"
  | Nullable_pointer _ -> "nullable pointer"

let path_to_string = function
  | [] -> "."
  | path -> String.concat "." (List.map (function Field name -> name | Tag -> "tag") path)

let niche_to_string niche =
  Printf.sprintf "niche %s %s+%s" (path_to_string niche.path) (Z.to_string niche.start)
    (Z.to_string niche.count)

let rec to_string layout =
  let form =
    match layout.form with
    | Zero_size -> "zero"
    | Scalar scalar -> scalar_to_string scalar
    | Struct fields ->
        "struct("
        ^ String.concat " "
            (List.map
               (fun (field : field) -> Printf.sprintf "%s@%d" field.name field.offset)
               fields)
        ^ ")"
    | Array { element_layout; count; _ } ->
        Printf.sprintf "array(%d x %s)" count (to_string element_layout)
    | Tag_only { tag; variants } ->
        Printf.sprintf "tag(%s: %s)" (integer_to_string tag) (String.concat " " variants)
    | Tagged { tag; payload_offset; variants } ->
        Printf.sprintf "tagged(%s, payload@%d: %s)" (integer_to_string tag) payload_offset
          (String.concat " " (List.map (fun (variant : variant) -> variant.name) variants))
    | Niche_encoded { dataful; others; encoding } ->
        Printf.sprintf "niche-encoded(%s; %s at %s)" dataful.name
          (String.concat " "
             (List.map (fun (name, value) -> name ^ "=" ^ Z.to_string value) others))
          (match encoding with None -> "nothing" | Some { path; _ } -> path_to_string path)
  in
  Printf.sprintf "%d/%d %s%s" layout.size layout.alignment form
    (match layout.niche with None -> "" | Some niche -> " " ^ niche_to_string niche)

let has_zero_size env ty = (of_type env ty).size = 0
let typed members = List.filter_map (function _, Typed ty -> Some ty | _, Raw _ -> None) members

let stored_in_place (shape : shape) =
  match shape with
  | Scalar _ | Array (_, 0) -> []
  | Record members -> typed members
  | Array (element, _) -> [ element ]
  | Sum variants ->
      List.concat_map
        (fun (variant : variant_shape) -> if variant.indirect then [] else typed variant.fields)
        variants

let pointee_types = function
  | Data ty | Block (ty, _) -> [ ty ]
  | Code { parameters; result = Returns result | Lends (_, result); _ } ->
      result :: List.map snd parameters
  | Opaque -> []

let member_reaches = function
  | _, Typed ty -> [ ty ]
  | _, Raw (Pointer pointee | Nullable_pointer pointee) -> pointee_types pointee
  | _, Raw (Integer _ | Float32 | Float64 | Bool | Character) -> []

let reaches (shape : shape) =
  match shape with
  | Scalar (Pointer pointee | Nullable_pointer pointee) -> pointee_types pointee
  | Scalar (Integer _ | Float32 | Float64 | Bool | Character) -> []
  | Record members -> List.concat_map member_reaches members
  | Array (element, _) -> [ element ]
  | Sum variants ->
      List.concat_map
        (fun (variant : variant_shape) -> List.concat_map member_reaches variant.fields)
        variants

module For_testing = struct
  let to_string = to_string
end
