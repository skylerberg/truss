let find_written_entries (definition : Syntax.definition) =
  match definition.kind with
  | Function { signature; _ } | Method_declaration signature ->
      List.find_map
        (fun (clause : Syntax.clause) ->
          match clause.kind with Modifies entries -> Some entries | _ -> None)
        signature.clauses
  | _ -> None

let has_todo (tree : Mir.t) =
  let has_todo = ref false in
  Mir.iter_code
    (fun (statement : Mir.statement) ->
      match statement.kind with Jump Todo -> has_todo := true | _ -> ())
    tree;
  !has_todo

let is_trait_method (interface : Interface.Lookups.t) key =
  match interface.names.find_container key with
  | Some container -> (
      match (interface.names.read_definition container).kind with Trait _ -> true | _ -> false)
  | None -> false

let check (context : Context.context) (key : Resolve.Names.key) (tree : Mir.t) =
  let interface = context.lookups.interface in
  match Interface.Impls.read_signature interface key.path with
  | None -> ()
  | Some signature -> (
      let package = Path.locate_package key.path in
      let has_valid_parts position =
        List.for_all
          (fun (part : Types.modified) ->
            part.position <> position
            ||
            match
              Interface.Definition.find_field_path_type interface ~package
                (Types.read_parameter_at signature position).type_ part.field_path
            with
            | Ok _ | Error (Hidden_fields _) -> true
            | Error (Broken_type | No_fields _ | Variant_fields _ | Unknown_field _) -> false)
          signature.modifies
      in
      let framed =
        List.filter has_valid_parts
          (List.sort_uniq compare
             (List.map (fun (part : Types.modified) -> part.position) signature.modifies))
      in
      match framed with
      | [] -> ()
      | _ :: _ -> (
          let name_parameter position = (Types.read_parameter_at signature position).name in
          let written_entries = find_written_entries (interface.names.read_definition key) in
          let changes =
            List.filter_map
              (fun ((origin : Core.origin), (place : Mir.place)) ->
                match place.root with
                | Local local ->
                    Option.map
                      (fun position ->
                        (origin, position, Mir.list_leading_fields place.projections))
                      (List.find_index (Int.equal local) tree.body.parameters)
                | Constant _ | Literal _ -> None)
              (Mir.list_changed_places
                 ~list_modified:
                   (Mir.list_callee_modified_fields
                      ~read_signature:(Interface.Impls.read_signature interface)
                      interface Types.no_substitution)
                 [ tree.body.code ])
          in
          let reported = ref [] in
          List.iter
            (fun (origin, position, fields) ->
              let allowed =
                Option.value ~default:[] (Types.list_modified_fields signature position)
              in
              if
                List.mem position framed
                && not
                     (List.exists (fun prefix -> Types.is_field_path_prefix prefix fields) allowed
                     || List.mem (position, fields) !reported)
              then begin
                reported := (position, fields) :: !reported;
                Context.report context
                  (Undeclared_change
                     {
                       at = origin;
                       function_ = key.path;
                       parameter = name_parameter position;
                       fields;
                       last_entry =
                         Option.bind written_entries (fun entries ->
                             Option.map
                               (fun (last : Syntax.expression) -> Core.Written last.id)
                               (List.nth_opt entries (List.length entries - 1)));
                     })
              end)
            changes;
          match written_entries with
          | Some entries when not (is_trait_method interface key || has_todo tree) ->
              let is_changed position fields =
                List.exists
                  (fun (_, changed_position, changed_fields) ->
                    changed_position = position
                    && (Types.is_field_path_prefix fields changed_fields
                       || Types.is_field_path_prefix changed_fields fields))
                  changes
              in
              let written_parts =
                List.map
                  (fun (entry : Syntax.expression) ->
                    Option.bind (Interface.Elaborator.split_field_path entry) (fun (root, names) ->
                        Option.map
                          (fun position ->
                            (position, List.map (fun (name : Syntax.name) -> name.text) names, root))
                          (Types.find_parameter_position signature root)))
                  entries
              in
              List.iteri
                (fun index written_part ->
                  match written_part with
                  | Some (position, fields, root)
                    when List.mem position framed
                         && List.mem { Types.position; field_path = fields } signature.modifies
                         && not (is_changed position fields) ->
                      let has_changed_part =
                        List.exists
                          (function
                            | Some (other, other_fields, _) ->
                                other = position && is_changed other other_fields
                            | None -> false)
                          written_parts
                      in
                      let change : Catalog.Usage.part_change =
                        if has_changed_part then
                          Named_part_changed
                            (Catalog.read_entry_siblings
                               (List.map
                                  (fun (entry : Syntax.expression) ->
                                    { Catalog.covering = [ Core.Written entry.id ] })
                                  entries)
                               index)
                        else if
                          List.exists
                            (fun (_, changed_position, _) -> changed_position = position)
                            changes
                        then Unnamed_part_changed
                        else Parameter_unchanged
                      in
                      context.diagnostics <-
                        Catalog.Usage
                          (Unmodified_part
                             {
                               entry = Written (List.nth entries index).id;
                               function_ = key.path;
                               parameter = root;
                               fields;
                               change;
                             })
                        :: context.diagnostics
                  | Some _ | None -> ())
                written_parts
          | Some _ | None -> ()))
