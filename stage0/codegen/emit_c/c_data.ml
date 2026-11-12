(* Static data as C: constants' values, storage and blocks as static
   objects of their own, capability tables, and evidence. *)

open C_runtime
open C_types
open C_values

let static_name context =
  let name = Printf.sprintf "t_static_%d" (List.length context.statics) in
  name

(* A static value as a C initializer, or [None] for a value of zero size.
   Storage elements and the blocks of [indirect] variants become static
   objects of their own, defined before the data that points at them. *)
let rec initializer_c context ty (value : Lir.static_value) : string option =
  let layout = layout context ty in
  let fields_c (fields : Memory_layout.field list) (values : (string * Lir.static_value) list)
      prefix =
    String.concat ", "
      (List.filter_map
         (fun (field : Memory_layout.field) ->
           match (List.assoc_opt field.name values, field.member) with
           | Some value, Typed field_ty ->
               Option.map
                 (Printf.sprintf "%s.f_%s = %s" prefix field.name)
                 (initializer_c context field_ty value)
           | _ -> None)
         fields)
  in
  let block_c variant fields =
    let key = Block (ty, variant) in
    register context key;
    let block_fields =
      match (Memory_layout.block context.env ty variant).form with Struct f -> f | _ -> []
    in
    (* The parts first, which are static objects of their own, then this
       one's name, so no two share one. *)
    let block_value = fields_c block_fields fields "" in
    let name = static_name context in
    context.statics <-
      Printf.sprintf "static const %s %s = { %s };\n" (key_name key) name block_value
      :: context.statics;
    Printf.sprintf "((%s *)&%s)" (key_name key) name
  in
  match (layout.form, value) with
  | Zero_size, _ -> None
  | _, Static_storage { element; elements; owned } ->
      let element_c = value_c context element in
      let count = List.length elements in
      let buffer =
        if count = 0 || Memory_layout.has_zero_size context.env element then
          "((void *)" ^ bytes_name context "" ^ ")"
        else begin
          let values = List.filter_map (initializer_c context element) elements in
          let name = static_name context in
          context.statics <-
            Printf.sprintf "static const %s %s[%d] = { %s };\n" element_c name count
              (String.concat ", " values)
            :: context.statics;
          Printf.sprintf "((%s *)%s)" element_c name
        end
      in
      Some
        (Printf.sprintf "{ .f_%s = %s, .f_%s = %d, .f_%s = %d }" Storage.buffer_field buffer
           Storage.length_field count Storage.capacity_field
           (if owned then count else 0))
  | Scalar _, Static_scalar constant -> Some (fst (constant_c context constant))
  | Struct fields, Static_record values -> Some ("{ " ^ fields_c fields values "" ^ " }")
  | Array { element; _ }, Static_array values ->
      Some
        ("{ .items = { "
        ^ String.concat ", " (List.filter_map (initializer_c context element) values)
        ^ " } }")
  | Tag_only { variants; _ }, Static_variant (name, _) -> (
      match List.find_index (String.equal name) variants with
      | Some index -> Some (string_of_int index)
      | None -> bug "no variant %s" name)
  | Tagged { variants; _ }, Static_variant (name, values) -> (
      match List.find_opt (fun (v : Memory_layout.variant) -> v.name = name) variants with
      | None -> bug "no variant %s" name
      | Some v -> (
          match v.payload.form with
          | Zero_size -> Some (Printf.sprintf "{ .tag = %d }" v.index)
          | Struct fields ->
              Some
                (Printf.sprintf "{ .tag = %d, %s }" v.index
                   (fields_c fields values (".payload.v_" ^ name)))
          | Scalar (Pointer (Block _)) ->
              Some
                (Printf.sprintf "{ .tag = %d, .payload.v_%s = %s }" v.index name
                   (block_c name values))
          | _ -> bug "a payload"))
  | Niche_encoded { dataful; others; encoding }, Static_variant (name, values) ->
      if dataful.name = name then
        match dataful.payload.form with
        | Struct fields -> Some ("{ " ^ fields_c fields values "" ^ " }")
        | Scalar (Pointer (Block _)) -> Some (block_c name values)
        | _ -> bug "a payload"
      else
        begin match (List.assoc_opt name others, encoding) with
        | Some stored, Some niche -> (
            let stored = niche_value context niche stored in
            match niche.path with
            | [] -> Some stored
            | path ->
                Some
                  (Printf.sprintf "{ %s = %s }"
                     (String.concat ""
                        (List.map
                           (function Memory_layout.Field name -> ".f_" ^ name | Tag -> ".tag")
                           path))
                     stored))
        | _ -> bug "no variant %s" name
        end
  | _ -> bug "static data that does not fit %s" (Ground.to_string ty)

let table_c context (table : Lir.table) =
  let entries =
    List.map
      (fun (key, signature) ->
        let symbol = Instance.symbol key in
        declare_prototype context symbol
          (prototype context "" symbol ~linkage:External signature ^ ";\n");
        Printf.sprintf "(const void *)&%s" symbol)
      table.entries
  in
  Printf.sprintf "const void *const %s[%d] = { %s };\n" (Instance.symbol table.table_key)
    (max 1 (List.length entries))
    (if entries = [] then "0" else String.concat ", " entries)

let data_c context (data : Lir.data) =
  let symbol = Instance.symbol data.data_key in
  match initializer_c context data.ty data.value with
  | None -> ""
  | Some value -> Printf.sprintf "const %s %s = %s;\n" (value_c context data.ty) symbol value
