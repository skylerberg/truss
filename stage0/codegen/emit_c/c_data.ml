let ( ++ ) = C_text.( ++ )

let render_static ~c_type ~name ~dimension value =
  Text "static const " ++ c_type ++ Text " " ++ name
  ++ Text (dimension ^ " = ")
  ++ value ++ Text ";\n"

let rec render_initializer (emission : Emission.t) ty (value : Lowered.static_value) :
    C_text.t option =
  let layout = C_types.compute_layout emission.types ty in
  let render_fields (fields : Memory_layout.field list)
      (values : (string * Lowered.static_value) list) prefix =
    List.filter_map
      (fun (field : Memory_layout.field) ->
        match (List.assoc_opt field.name values, field.member) with
        | Some value, Typed field_ty ->
            Option.map
              (fun initializer_ ->
                Text (Printf.sprintf "%s.f_%s = " prefix field.name) ++ initializer_)
              (render_initializer emission field_ty value)
        | _ -> None)
      fields
  in
  let render_block variant fields =
    let key = C_types.render_key emission.types (Block (ty, variant)) in
    let block_fields =
      match (Memory_layout.lay_out_block emission.types.env ty variant).form with
      | Struct fields -> fields
      | _ -> []
    in
    let block_value = render_fields block_fields fields "" in
    let name =
      Emission.add_static emission (fun name ->
          render_static ~c_type:key ~name ~dimension:"" (C_text.render_braces block_value))
    in
    Text "((" ++ key ++ Text " *)&" ++ name ++ Text ")"
  in
  let render_buffer element elements =
    let element_c = C_types.render_value_type emission.types element in
    let count = List.length elements in
    if count = 0 || Memory_layout.has_zero_size emission.types.env element then
      fst (C_values.render_constant emission Storage.empty_buffer)
    else begin
      let values = List.filter_map (render_initializer emission element) elements in
      let name =
        Emission.add_static emission (fun name ->
            render_static ~c_type:element_c ~name ~dimension:(Printf.sprintf "[%d]" count)
              (C_text.render_braces values))
      in
      C_values.render_cast (element_c ++ Text " *") name
    end
  in
  let render_sequence list_fields element elements =
    Some
      (C_text.render_braces
         (List.map
            (fun (field, value) -> Text (".f_" ^ field ^ " = ") ++ value)
            (list_fields ~buffer:(render_buffer element elements)
               ~length:(C_text.Text (string_of_int (List.length elements))))))
  in
  match (layout.form, value) with
  | Zero_size, _ -> None
  | _, Static_storage { element; elements } ->
      render_sequence Storage.list_borrowed_fields element elements
  | _, Static_view { element; elements } ->
      render_sequence Storage.list_view_fields element elements
  | Scalar _, Static_scalar constant -> Some (fst (C_values.render_constant emission constant))
  | Struct fields, Static_record values ->
      Some (C_text.render_braces (render_fields fields values ""))
  | Array { element; _ }, Static_array values ->
      Some
        (Text "{ .items = "
        ++ C_text.render_braces (List.filter_map (render_initializer emission element) values)
        ++ Text " }")
  | Tag_only { variants; _ }, Static_variant (name, _) -> (
      match List.find_index (String.equal name) variants with
      | Some index -> Some (Text (string_of_int index))
      | None -> C_runtime.raise_bug "no variant %s" name)
  | Tagged { variants; _ }, Static_variant (name, values) -> (
      match
        List.find_opt (fun (variant : Memory_layout.variant) -> variant.name = name) variants
      with
      | None -> C_runtime.raise_bug "no variant %s" name
      | Some variant -> (
          let tag = C_text.Text (Printf.sprintf ".tag = %d" variant.index) in
          match variant.payload.form with
          | Zero_size -> Some (C_text.render_braces [ tag ])
          | Struct fields ->
              Some
                (C_text.render_braces (tag :: render_fields fields values (".payload.v_" ^ name)))
          | Scalar (Pointer (Block _)) ->
              Some
                (C_text.render_braces
                   [ tag; Text (".payload.v_" ^ name ^ " = ") ++ render_block name values ])
          | _ -> C_runtime.raise_bug "a payload"))
  | Niche_encoded { dataful; dataless }, Static_variant (name, values) ->
      if dataful.name = name then
        match dataful.payload.form with
        | Struct fields -> Some (C_text.render_braces (render_fields fields values ""))
        | Scalar (Pointer (Block _)) -> Some (render_block name values)
        | _ -> C_runtime.raise_bug "a payload"
      else
        begin match dataless with
        | Some { niche; niche_values } -> (
            match List.assoc_opt name niche_values with
            | None -> C_runtime.raise_bug "no variant %s" name
            | Some value -> (
                let stored = C_values.render_niche_value emission niche value in
                match niche.path with
                | [] -> Some stored
                | path ->
                    Some
                      (C_text.render_braces [ Text (C_values.render_path path ^ " = ") ++ stored ]))
            )
        | None -> C_runtime.raise_bug "no variant %s" name
        end
  | _ -> C_runtime.raise_bug "static data that does not fit %s" (Ground.to_string ty)

let render_table (emission : Emission.t) (table : Lowered.table) =
  let entries =
    List.map
      (fun (item, signature) ->
        let symbol = Emission.render_item emission item in
        Emission.declare_prototype emission symbol
          (C_values.render_prototype emission symbol ~linkage:External signature ++ Text ";\n");
        Text "(const void *)&" ++ symbol)
      table.entries
  in
  Text "const void *const "
  ++ Emission.render_item emission table.table_item
  ++ Text (Printf.sprintf "[%d] = " (max 1 (List.length entries)))
  ++ (match entries with [] -> Text "{ 0 }" | _ -> C_text.render_braces entries)
  ++ Text ";\n"

let render_data (emission : Emission.t) (data : Lowered.data) =
  match render_initializer emission data.ty data.value with
  | None -> C_text.empty
  | Some value ->
      Text "const "
      ++ C_types.render_value_type emission.types data.ty
      ++ Text " "
      ++ Emission.render_item emission data.data_item
      ++ Text " = " ++ value ++ Text ";\n"
