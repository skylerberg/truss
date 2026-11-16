let raise_bug format = Compiler_bug.raise_bug ~stage:"Memory_layout" format

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

type t = { size : int; alignment : int; form : form; niche : niche option }

and form =
  | Zero_size
  | Scalar of scalar
  | Struct of field list
  | Array of { element : Ground.ty; element_layout : t; count : int }
  | Tag_only of { tag : integer; variants : string list }
  | Tagged of { tag : integer; payload_offset : int; variants : variant list }
  | Niche_encoded of { dataful : variant; dataless : dataless option }

and field = { name : string; member : member; layout : t; offset : int }
and variant = { name : string; index : int; payload : t }
and dataless = { niche : niche; niche_values : (string * Z.t) list }
and niche = { path : step list; scalar : scalar; start : Z.t; count : Z.t }
and step = Field of string | Tag

module Type_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Ground.ty
end))

exception Infinite_size of Ground.ty

type env = {
  system : Libc.system;
  compute_shape : Ground.ty -> shape;
  layouts : t Type_table.t;
  in_progress : unit Type_table.t;
}

let create system ~compute_shape =
  { system; compute_shape; layouts = Type_table.create 64; in_progress = Type_table.create 8 }

let system env = env.system
let shape env ty = env.compute_shape ty

let compute_integer_size = function
  | Int8 | UInt8 -> 1
  | Int16 | UInt16 -> 2
  | Int32 | UInt32 -> 4
  | Int64 | UInt64 -> 8

let compute_integer_range integer =
  let bits = 8 * compute_integer_size integer in
  match integer with
  | Int8 | Int16 | Int32 | Int64 ->
      (Z.neg (Z.shift_left Z.one (bits - 1)), Z.pred (Z.shift_left Z.one (bits - 1)))
  | UInt8 | UInt16 | UInt32 | UInt64 -> (Z.zero, Z.pred (Z.shift_left Z.one bits))

let compute_scalar_size = function
  | Integer integer -> compute_integer_size integer
  | Float32 -> 4
  | Float64 -> 8
  | Bool -> 1
  | Character -> 4
  | Pointer _ | Nullable_pointer _ -> 8

let zero_size = { size = 0; alignment = 1; form = Zero_size; niche = None }
let round_up value alignment = (value + alignment - 1) / alignment * alignment
let count_values bytes = Z.shift_left Z.one (8 * bytes)

let find_scalar_niche = function
  | Bool -> Some { path = []; scalar = Bool; start = Z.of_int 2; count = Z.of_int 254 }
  | Character ->
      let start = Z.of_int 0x110000 in
      Some { path = []; scalar = Character; start; count = Z.sub (count_values 4) start }
  | Pointer _ as scalar -> Some { path = []; scalar; start = Z.zero; count = Z.one }
  | Integer _ | Float32 | Float64 | Nullable_pointer _ -> None

let of_scalar scalar =
  let size = compute_scalar_size scalar in
  { size; alignment = size; form = Scalar scalar; niche = find_scalar_niche scalar }

let choose_tag count = if count <= 0x100 then UInt8 else if count <= 0x10000 then UInt16 else UInt32

let make_tag_niche tag count path =
  let start = Z.of_int count in
  {
    path;
    scalar = Integer tag;
    start;
    count = Z.sub (count_values (compute_integer_size tag)) start;
  }

let nest_niche name niche = { niche with path = Field name :: niche.path }

let choose_best_niche (fields : field list) =
  List.fold_left
    (fun best (field : field) ->
      match (field.layout.niche, best) with
      | None, _ -> best
      | Some niche, None -> Some (nest_niche field.name niche)
      | Some niche, Some current ->
          if Z.gt niche.count current.count then Some (nest_niche field.name niche) else best)
    None fields

let place_fields (fields : (string * member * t) list) =
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
    {
      size = round_up offset alignment;
      alignment;
      form = Struct placed;
      niche = choose_best_niche placed;
    }

let rec of_type env ty =
  match Type_table.find_opt env.layouts ty with
  | Some layout -> layout
  | None ->
      if Type_table.mem env.in_progress ty then raise (Infinite_size ty);
      Type_table.replace env.in_progress ty ();
      let layout =
        Fun.protect
          ~finally:(fun () -> Type_table.remove env.in_progress ty)
          (fun () -> lay_out env ty (env.compute_shape ty))
      in
      Type_table.replace env.layouts ty layout;
      layout

and of_member env = function Typed ty -> of_type env ty | Raw scalar -> of_scalar scalar

and lay_out_fields env fields =
  place_fields (List.map (fun (name, member) -> (name, member, of_member env member)) fields)

and lay_out env ty (shape : shape) =
  match shape with
  | Scalar scalar -> of_scalar scalar
  | Record fields' -> lay_out_fields env fields'
  | Array (_, 0) -> zero_size
  | Array (element, count) ->
      let element_layout = of_type env element in
      if element_layout.size = 0 then zero_size
      else
        {
          size = element_layout.size * count;
          alignment = element_layout.alignment;
          form = Array { element; element_layout; count };
          niche = None;
        }
  | Sum variants -> of_sum env ty variants

and lay_out_payload env ty (variant : variant_shape) =
  if variant.indirect then of_scalar (Pointer (Block (ty, variant.name)))
  else lay_out_fields env variant.fields

and of_sum env ty shapes =
  let variants =
    List.mapi
      (fun index (shape : variant_shape) ->
        { name = shape.name; index; payload = lay_out_payload env ty shape })
      shapes
  in
  let count = List.length variants in
  let dataful, dataless = List.partition (fun variant -> variant.payload.size > 0) variants in
  match dataful with
  | [] when count <= 1 -> zero_size
  | [] ->
      let tag = choose_tag count in
      let size = compute_integer_size tag in
      {
        size;
        alignment = size;
        form =
          Tag_only { tag; variants = List.map (fun (variant : variant) -> variant.name) variants };
        niche = Some (make_tag_niche tag count []);
      }
  | [ only ]
    when match only.payload.niche with
         | Some niche -> Z.geq niche.count (Z.of_int (List.length dataless))
         | None -> dataless = [] ->
      let encoded, niche =
        match only.payload.niche with
        | None -> (None, None)
        | Some niche ->
            let used = List.length dataless in
            let remaining = Z.sub niche.count (Z.of_int used) in
            let rest =
              if Z.equal remaining Z.zero then None
              else Some { niche with start = Z.add niche.start (Z.of_int used); count = remaining }
            in
            let niche_values =
              List.mapi
                (fun position (variant : variant) ->
                  (variant.name, Z.add niche.start (Z.of_int position)))
                dataless
            in
            ((if niche_values = [] then None else Some { niche; niche_values }), rest)
      in
      {
        size = only.payload.size;
        alignment = only.payload.alignment;
        form = Niche_encoded { dataful = only; dataless = encoded };
        niche;
      }
  | _ ->
      let tag = choose_tag count in
      let tag_size = compute_integer_size tag in
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
        niche = Some (make_tag_niche tag count [ Tag ]);
      }

let lay_out_block env ty name =
  match env.compute_shape ty with
  | Sum variants -> (
      match List.find_opt (fun (variant : variant_shape) -> variant.name = name) variants with
      | Some { indirect = true; fields = fields'; _ } -> lay_out_fields env fields'
      | Some _ -> raise_bug "variant %s is not indirect" name
      | None -> raise_bug "no variant %s" name)
  | _ -> raise_bug "a block of a type that is not a sum type"

type tag = { at : step list; integer : integer }

type discriminant =
  | Only
  | Tag_value of { tag : tag; value : Z.t }
  | Niche_value of { niche : niche; value : Z.t }
  | Not_niche of { niche : niche; stop : Z.t }

type 'case dispatch =
  | Switch of { tag : tag; cases : (Z.t * 'case) list }
  | Tests of (discriminant * 'case) list

let list_tag_only_values tag variants =
  ({ at = []; integer = tag }, List.mapi (fun index name -> (name, Z.of_int index)) variants)

let list_tagged_values tag variants =
  ( { at = [ Tag ]; integer = tag },
    List.map (fun (variant : variant) -> (variant.name, Z.of_int variant.index)) variants )

let find_tag_value values name =
  match List.assoc_opt name values with
  | Some value -> value
  | None -> raise_bug "no variant %s" name

let compute_discriminant layout name =
  let tag_value (tag, values) = Tag_value { tag; value = find_tag_value values name } in
  match layout.form with
  | Zero_size -> Only
  | Tag_only { tag; variants } -> tag_value (list_tag_only_values tag variants)
  | Tagged { tag; variants; _ } -> tag_value (list_tagged_values tag variants)
  | Niche_encoded { dataful; dataless = None } ->
      if dataful.name = name then Only else raise_bug "no variant %s" name
  | Niche_encoded { dataful; dataless = Some { niche; niche_values } } -> (
      if dataful.name = name then
        Not_niche { niche; stop = Z.add niche.start (Z.of_int (List.length niche_values)) }
      else
        match List.assoc_opt name niche_values with
        | Some value -> Niche_value { niche; value }
        | None -> raise_bug "no variant %s" name)
  | Scalar _ | Struct _ | Array _ -> raise_bug "a discriminant of a type that is not a sum type"

let dispatch layout cases =
  let switch (tag, values) =
    Switch { tag; cases = List.map (fun (name, case) -> (find_tag_value values name, case)) cases }
  in
  match layout.form with
  | Tag_only { tag; variants } -> switch (list_tag_only_values tag variants)
  | Tagged { tag; variants; _ } -> switch (list_tagged_values tag variants)
  | Zero_size | Niche_encoded _ | Scalar _ | Struct _ | Array _ ->
      Tests (List.map (fun (name, case) -> (compute_discriminant layout name, case)) cases)

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
    | Niche_encoded { dataful; dataless = None } ->
        Printf.sprintf "niche-encoded(%s;  at nothing)" dataful.name
    | Niche_encoded { dataful; dataless = Some { niche; niche_values } } ->
        Printf.sprintf "niche-encoded(%s; %s at %s)" dataful.name
          (String.concat " "
             (List.map (fun (name, value) -> name ^ "=" ^ Z.to_string value) niche_values))
          (path_to_string niche.path)
  in
  Printf.sprintf "%d/%d %s%s" layout.size layout.alignment form
    (match layout.niche with None -> "" | Some niche -> " " ^ niche_to_string niche)

let has_zero_size env ty = (of_type env ty).size = 0

module For_testing = struct
  let to_string = to_string
end
