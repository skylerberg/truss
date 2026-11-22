let ( ++ ) = C_text.( ++ )

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
  match C_values.render_initializer emission data.ty data.value with
  | None -> C_text.empty
  | Some value ->
      Text "const "
      ++ C_types.render_value_type emission.types data.ty
      ++ Text " "
      ++ Emission.render_item emission data.data_item
      ++ Text " = " ++ value ++ Text ";\n"
