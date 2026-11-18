let allocate_static_name (context : C_types.context) =
  let name = Printf.sprintf "%s_static_%d" context.prefix (List.length context.statics) in
  name

let rec render_initializer context ty (value : Lowered.static_value) : string option =
  let layout = C_types.compute_layout context ty in
  let render_fields (fields : Memory_layout.field list)
      (values : (string * Lowered.static_value) list) prefix =
    String.concat ", "
      (List.filter_map
         (fun (field : Memory_layout.field) ->
           match (List.assoc_opt field.name values, field.member) with
           | Some value, Typed field_ty ->
               Option.map
                 (Printf.sprintf "%s.f_%s = %s" prefix field.name)
                 (render_initializer context field_ty value)
           | _ -> None)
         fields)
  in
  let render_block variant fields =
    let key = C_types.Block (ty, variant) in
    C_types.register context key;
    let block_fields =
      match (Memory_layout.lay_out_block context.env ty variant).form with
      | Struct fields -> fields
      | _ -> []
    in
    let block_value = render_fields block_fields fields "" in
    let name = allocate_static_name context in
    context.statics <-
      Printf.sprintf "static const %s %s = { %s };\n" (C_types.render_key_name key) name block_value
      :: context.statics;
    Printf.sprintf "((%s *)&%s)" (C_types.render_key_name key) name
  in
  match (layout.form, value) with
  | Zero_size, _ -> None
  | _, Static_storage { element; elements } ->
      let element_c = C_types.render_value_type context element in
      let count = List.length elements in
      let buffer =
        if count = 0 || Memory_layout.has_zero_size context.env element then
          fst (C_values.render_constant context Storage.empty_buffer)
        else begin
          let values = List.filter_map (render_initializer context element) elements in
          let name = allocate_static_name context in
          context.statics <-
            Printf.sprintf "static const %s %s[%d] = { %s };\n" element_c name count
              (String.concat ", " values)
            :: context.statics;
          Printf.sprintf "((%s *)%s)" element_c name
        end
      in
      Some
        (Printf.sprintf "{ .f_%s = %s, .f_%s = %d, .f_%s = %d }" Storage.buffer_field buffer
           Storage.length_field count Storage.capacity_field count)
  | Scalar _, Static_scalar constant -> Some (fst (C_values.render_constant context constant))
  | Struct fields, Static_record values -> Some ("{ " ^ render_fields fields values "" ^ " }")
  | Array { element; _ }, Static_array values ->
      Some
        ("{ .items = { "
        ^ String.concat ", " (List.filter_map (render_initializer context element) values)
        ^ " } }")
  | Tag_only { variants; _ }, Static_variant (name, _) -> (
      match List.find_index (String.equal name) variants with
      | Some index -> Some (string_of_int index)
      | None -> C_runtime.raise_bug "no variant %s" name)
  | Tagged { variants; _ }, Static_variant (name, values) -> (
      match
        List.find_opt (fun (variant : Memory_layout.variant) -> variant.name = name) variants
      with
      | None -> C_runtime.raise_bug "no variant %s" name
      | Some variant -> (
          match variant.payload.form with
          | Zero_size -> Some (Printf.sprintf "{ .tag = %d }" variant.index)
          | Struct fields ->
              Some
                (Printf.sprintf "{ .tag = %d, %s }" variant.index
                   (render_fields fields values (".payload.v_" ^ name)))
          | Scalar (Pointer (Block _)) ->
              Some
                (Printf.sprintf "{ .tag = %d, .payload.v_%s = %s }" variant.index name
                   (render_block name values))
          | _ -> C_runtime.raise_bug "a payload"))
  | Niche_encoded { dataful; dataless }, Static_variant (name, values) ->
      if dataful.name = name then
        match dataful.payload.form with
        | Struct fields -> Some ("{ " ^ render_fields fields values "" ^ " }")
        | Scalar (Pointer (Block _)) -> Some (render_block name values)
        | _ -> C_runtime.raise_bug "a payload"
      else
        begin match dataless with
        | Some { niche; niche_values } -> (
            match List.assoc_opt name niche_values with
            | None -> C_runtime.raise_bug "no variant %s" name
            | Some value -> (
                let stored = C_values.render_niche_value context niche value in
                match niche.path with
                | [] -> Some stored
                | path -> Some (Printf.sprintf "{ %s = %s }" (C_values.render_path "" path) stored))
            )
        | None -> C_runtime.raise_bug "no variant %s" name
        end
  | _ -> C_runtime.raise_bug "static data that does not fit %s" (Ground.to_string ty)

let render_table context (table : Lowered.table) =
  let entries =
    List.map
      (fun (item, signature) ->
        let symbol = Mangling.make_symbol item in
        C_values.declare_prototype context symbol
          (C_values.render_prototype context "" symbol ~linkage:External signature ^ ";\n");
        Printf.sprintf "(const void *)&%s" symbol)
      table.entries
  in
  Printf.sprintf "const void *const %s[%d] = { %s };\n"
    (Mangling.make_symbol table.table_item)
    (max 1 (List.length entries))
    (if entries = [] then "0" else String.concat ", " entries)

let render_data context (data : Lowered.data) =
  let symbol = Mangling.make_symbol data.data_item in
  match render_initializer context data.ty data.value with
  | None -> ""
  | Some value ->
      Printf.sprintf "const %s %s = %s;\n" (C_types.render_value_type context data.ty) symbol value
