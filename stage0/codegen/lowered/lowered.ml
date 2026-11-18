module Item = Item
include Lowered_types

let make_local_place local = { root = Local local; projections = [] }
let project place projection = { place with projections = place.projections @ [ projection ] }
let make_uint64_constant number = Constant (Integer (UInt64, Z.of_int number))
let raise_bug format = Compiler_bug.raise_bug ~stage:"Lowered" format

let is_erased env = function
  | Value ty -> Memory_layout.has_zero_size env ty
  | Pointer _ | Raw _ | Environment _ | Evidence _ | Capabilities _ | Trace | Lend | Lend_mark ->
      false

let convert_member : Memory_layout.member -> ty = function
  | Typed ty -> Value ty
  | Raw scalar -> Raw scalar

let find_field (fields : Memory_layout.field list) name =
  List.find_map
    (fun (field : Memory_layout.field) ->
      if field.name = name then Some (convert_member field.member) else None)
    fields

let find_struct_field (layout : Memory_layout.t) name =
  match layout.form with Struct fields -> find_field fields name | _ -> None

let find_variant_field_type env sum variant field =
  let layout = Memory_layout.of_type env sum in
  let find_in_payload (payload : Memory_layout.t) =
    match payload.form with
    | Struct fields -> find_field fields field
    | Scalar (Pointer (Block _)) ->
        find_struct_field (Memory_layout.lay_out_block env sum variant) field
    | _ -> None
  in
  match layout.form with
  | Tagged { variants; _ } -> (
      match
        List.find_opt
          (fun (variant_layout : Memory_layout.variant) -> variant_layout.name = variant)
          variants
      with
      | Some variant_layout -> find_in_payload variant_layout.payload
      | None -> raise_bug "%s has no variant %s" (Ground.to_string sum) variant)
  | Niche_encoded { dataful; _ } when dataful.name = variant -> find_in_payload dataful.payload
  | Niche_encoded _ | Tag_only _ | Zero_size -> None
  | _ -> raise_bug "a variant of %s, which is not a sum type" (Ground.to_string sum)

let find_projection_type env ~list_environment ty projection =
  let result =
    match (projection, ty) with
    | Deref, Pointer { target; _ } -> Some target
    | Deref, Raw (Pointer (Data target) | Nullable_pointer (Data target)) -> Some (Value target)
    | Field name, Value record -> (
        let layout = Memory_layout.of_type env record in
        match layout.form with
        | Struct _ -> find_struct_field layout name
        | Zero_size -> None
        | _ -> raise_bug "field %s of %s, which is not a record" name (Ground.to_string record))
    | Field name, Environment nested_index -> (
        match List.assoc_opt name (list_environment nested_index) with
        | Some ty -> Some ty
        | None -> raise_bug "environment %d has no field %s" nested_index name)
    | Variant_field { variant; field }, Value sum -> find_variant_field_type env sum variant field
    | Index _, Value array -> (
        match (Memory_layout.of_type env array).form with
        | Array { element; _ } -> Some (Value element)
        | Zero_size -> None
        | _ -> raise_bug "an index into %s" (Ground.to_string array))
    | Index _, Raw (Pointer (Data element) | Nullable_pointer (Data element)) ->
        Some (Value element)
    | _ -> raise_bug "a projection that does not fit its place"
  in
  match result with Some ty when is_erased env ty -> None | other -> other

let list_successors = function
  | Goto block -> [ block ]
  | Switch { cases; default; _ } -> List.map snd cases @ [ default ]
  | Switch_variant { cases; default; _ } -> List.map snd cases @ Option.to_list default
  | Return _ | Unreachable | Fail _ -> []
