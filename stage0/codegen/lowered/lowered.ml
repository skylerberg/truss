(* The statements' types, and the queries over them. *)

include Lowered_types

let local_place local = { root = Local local; projections = [] }
let bug format = Compiler_bug.bug ~stage:"Lowered" format

(* A cursor always holds its state, which lets code over a cursor that holds
   another be lowered before the cursor's fields are known. *)
let erased env = function
  | Value (Cursor _) -> false
  | Value ty -> Memory_layout.has_zero_size env ty
  | Pointer _ | Raw _ | Environment _ | Evidence _ -> false

let member_ty : Memory_layout.member -> ty = function
  | Typed ty -> Value ty
  | Raw scalar -> Raw scalar

let find_field (fields : Memory_layout.field list) name =
  List.find_map
    (fun (field : Memory_layout.field) ->
      if field.name = name then Some (member_ty field.member) else None)
    fields

let struct_field (layout : Memory_layout.t) name =
  match layout.form with Struct fields -> find_field fields name | _ -> None

let variant_field_type env sum variant field =
  let layout = Memory_layout.of_type env sum in
  let in_payload (payload : Memory_layout.t) =
    match payload.form with
    | Struct fields -> find_field fields field
    | Scalar (Pointer (Block _)) -> struct_field (Memory_layout.block env sum variant) field
    | _ -> None
  in
  match layout.form with
  | Tagged { variants; _ } -> (
      match
        List.find_opt
          (fun (variant_layout : Memory_layout.variant) -> variant_layout.name = variant)
          variants
      with
      | Some variant_layout -> in_payload variant_layout.payload
      | None -> bug "%s has no variant %s" (Ground.to_string sum) variant)
  | Niche_encoded { dataful; _ } when dataful.name = variant -> in_payload dataful.payload
  | Niche_encoded _ | Tag_only _ | Zero_size -> None
  | _ -> bug "a variant of %s, which is not a sum type" (Ground.to_string sum)

let projection_type env ~environment ty projection =
  let result =
    match (projection, ty) with
    | Deref, Pointer { target; _ } -> Some target
    | Deref, Raw (Pointer (Data target) | Nullable_pointer (Data target)) -> Some (Value target)
    | Field name, Value record -> (
        let layout = Memory_layout.of_type env record in
        match layout.form with
        | Struct _ -> struct_field layout name
        | Zero_size -> None
        | _ -> bug "field %s of %s, which is not a record" name (Ground.to_string record))
    | Field name, Environment nested_index -> (
        match List.assoc_opt name (environment nested_index) with
        | Some ty -> Some ty
        | None -> bug "environment %d has no field %s" nested_index name)
    | Variant_field { variant; field }, Value sum -> variant_field_type env sum variant field
    | Index _, Value array -> (
        match (Memory_layout.of_type env array).form with
        | Array { element; _ } -> Some (Value element)
        | Zero_size -> None
        | _ -> bug "an index into %s" (Ground.to_string array))
    | Index _, Raw (Pointer (Data element) | Nullable_pointer (Data element)) ->
        Some (Value element)
    | _ -> bug "a projection that does not fit its place"
  in
  match result with Some ty when erased env ty -> None | other -> other

let successors = function
  | Goto block -> [ block ]
  | Switch { cases; default; _ } -> List.map snd cases @ Option.to_list default
  | Switch_variant { cases; default; _ } -> List.map snd cases @ Option.to_list default
  | Return _ | Unreachable | Fail _ -> []
