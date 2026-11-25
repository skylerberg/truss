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
          let shown_function =
            match key.path with
            | Top { name; _ } | Method { name; _ } -> name
            | path -> Path.show path
          in
          let find_storage_field (container : Types.modified) =
            match
              Interface.Definition.find_field_path_type interface ~package
                (Types.read_parameter_at signature container.position).type_ container.field_path
            with
            | Ok (Named { path; arguments }) -> (
                match
                  Option.bind (Interface.Definition.find_type_interface interface path)
                    (fun type_interface -> Types.instantiate_fields type_interface arguments)
                with
                | Some [ field ] when Types.is_builtin Storage field.field_type ->
                    Some field.field_name
                | _ -> None)
            | Ok _ | Error _ -> None
          in
          let is_named_by (container : Types.modified) (part : Types.modified) =
            Types.is_part_within ~container part
            || container.is_elements && part.is_elements
               &&
               match find_storage_field container with
               | Some storage -> part.field_path = container.field_path @ [ storage ]
               | None -> false
          in
          let changes =
            List.filter_map
              (fun (changed : Mir.changed) ->
                match changed.place.root with
                | Local local ->
                    Option.map
                      (fun position ->
                        let field_path, is_elements = Mir.classify_changed_part changed in
                        (changed.origin, { Types.position; field_path; is_elements }))
                      (List.find_index (Int.equal local) tree.body.parameters)
                | Constant _ | Literal _ -> None)
              (Mir.list_changed_places
                 ~list_modified:
                   (Mir.list_callee_modified_parts
                      ~read_signature:(Interface.Impls.read_signature interface)
                      interface Types.no_substitution)
                 [ tree.body.code ])
          in
          let reported = ref [] in
          List.iter
            (fun (origin, (part : Types.modified)) ->
              let allowed =
                Option.value ~default:[] (Types.list_modified_parts signature part.position)
              in
              if
                List.mem part.position framed
                && not
                     (List.exists (fun container -> is_named_by container part) allowed
                     || List.mem part !reported)
              then begin
                reported := part :: !reported;
                let shown = Types.show_modified_part ~root:(name_parameter part.position) part in
                let is_whole = part.field_path = [] && not part.is_elements in
                let fixes =
                  match (is_whole, written_entries) with
                  | false, Some entries -> (
                      match List.rev entries with
                      | last :: _ ->
                          let stop = (Lazy.force context.spans).(last.id).stop in
                          [
                            Diagnostic.fix
                              (Printf.sprintf "Add `%s` to the `modifies` clause." shown)
                              [
                                Diagnostic.insert
                                  (Source.Definition_span.make stop stop)
                                  (", " ^ shown);
                              ];
                          ]
                      | [] -> [])
                  | _ -> []
                in
                Context.report context Undeclared_change
                  (Context.locate_origin context origin)
                  ~fixes
                  (Printf.sprintf
                     "%s changes here, and the `modifies` clause of `%s` does not name it. The \
                      proofs of its callers take every part of `%s` that the clause does not name \
                      to keep its value."
                     (if is_whole then Printf.sprintf "All of `%s`" shown
                      else Printf.sprintf "`%s`" shown)
                     shown_function (name_parameter part.position))
              end)
            changes;
          match written_entries with
          | Some entries when not (is_trait_method interface key || has_todo tree) ->
              let spans = Lazy.force context.spans in
              let is_changed (written : Types.modified) =
                List.exists
                  (fun (_, (changed : Types.modified)) ->
                    changed.position = written.position
                    && (Types.is_field_path_prefix written.field_path changed.field_path
                       || Types.is_field_path_prefix changed.field_path written.field_path))
                  changes
              in
              let written_parts =
                List.map
                  (fun (entry : Syntax.expression) ->
                    Option.bind (Interface.Elaborator.split_part entry)
                      (fun (root, names, is_elements) ->
                        Option.map
                          (fun position ->
                            ( {
                                Types.position;
                                field_path = List.map (fun (name : Syntax.name) -> name.text) names;
                                is_elements;
                              },
                              root ))
                          (Types.find_parameter_position signature root)))
                  entries
              in
              List.iteri
                (fun index written_part ->
                  match written_part with
                  | Some ((written : Types.modified), root)
                    when List.mem written.position framed
                         && List.mem written signature.modifies
                         && not (is_changed written) ->
                      let shown = Types.show_modified_part ~root written in
                      let has_changed_part =
                        List.exists
                          (function
                            | Some ((other : Types.modified), _) ->
                                other.position = written.position && is_changed other
                            | None -> false)
                          written_parts
                      in
                      let entry_spans =
                        List.map (fun (entry : Syntax.expression) -> spans.(entry.id)) entries
                      in
                      context.diagnostics <-
                        Diagnostic.make ~severity:Warning ~code:(Usage Unmodified_part)
                          ~fixes:
                            (if has_changed_part then
                               [
                                 Diagnostic.fix
                                   (Printf.sprintf "Remove `%s` from the `modifies` clause." shown)
                                   [ Diagnostic.delete_list_entry entry_spans index ];
                               ]
                             else [])
                          (List.nth entry_spans index)
                          (if
                             has_changed_part
                             || List.exists
                                  (fun (_, (changed : Types.modified)) ->
                                    changed.position = written.position)
                                  changes
                           then
                             Printf.sprintf
                               "`%s` never changes `%s`, so the proofs of its callers do not learn \
                                that `%s` keeps its value. Remove it from `modifies`."
                               shown_function shown shown
                           else
                             Printf.sprintf
                               "`%s` changes no part of `%s` that its `modifies` clause names, nor \
                                any other: `%s` need not be `mut`."
                               shown_function root root)
                        :: context.diagnostics
                  | Some _ | None -> ())
                written_parts
          | Some _ | None -> ()))

let check_ranges (context : Context.context) (tree : Mir.t) =
  let interface = context.lookups.interface in
  let list_modified =
    Mir.list_callee_modified_parts
      ~read_signature:(Interface.Impls.read_signature interface)
      interface Types.no_substitution
  in
  let keeps_length callee position =
    match list_modified callee position with
    | Some parts ->
        List.for_all (fun (part : Types.modified) -> part.field_path = [] && part.is_elements) parts
    | None -> false
  in
  let check_call (call : Mir.call) =
    List.iteri
      (fun position (argument : Mir.argument) ->
        match argument with
        | { mode = Mut; value = Borrow { place; origin; _ } | Use { place; origin; _ }; _ } -> (
            match List.rev place.projections with
            | Range _ :: _ when not (keeps_length call.callee position) ->
                Context.report context Resized_range
                  (Context.locate_origin context origin)
                  (Printf.sprintf
                     "This range is passed `mut` to %s, which may change the length of its \
                      argument, and a range has a fixed length. Pass the whole list, or declare \
                      that the function changes only elements, with `modifies` and `[..]`."
                     (Context.describe_call context call.origin))
            | _ -> ())
        | _ -> ())
      call.arguments
  in
  Mir.iter_code
    (fun (statement : Mir.statement) ->
      match statement.kind with
      | Basic (Call { call; _ } | Lend { call; _ }) -> check_call call
      | _ -> ())
    tree
