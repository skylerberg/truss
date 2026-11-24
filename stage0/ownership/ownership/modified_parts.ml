let find_written_parts (definition : Syntax.definition) =
  let find_in (signature : Syntax.signature) =
    List.find_map
      (fun (clause : Syntax.clause) ->
        match clause.kind with Modifies entries -> Some entries | _ -> None)
      signature.clauses
  in
  match definition.kind with
  | Function { signature; _ } | Method_declaration signature -> find_in signature
  | _ -> None

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
      | _ :: _ ->
          let name_parameter position = (Types.read_parameter_at signature position).name in
          let written_parts = find_written_parts (interface.names.read_definition key) in
          let shown_function =
            match key.path with
            | Top { name; _ } | Method { name; _ } -> name
            | path -> Path.show path
          in
          let reported = ref [] in
          List.iter
            (fun ((origin : Core.origin), (place : Mir.place)) ->
              match place.root with
              | Local local -> (
                  match List.find_index (Int.equal local) tree.body.parameters with
                  | Some position when List.mem position framed ->
                      let fields = Mir.list_leading_fields place.projections in
                      let allowed =
                        Option.value ~default:[] (Types.list_modified_fields signature position)
                      in
                      if
                        not
                          (List.exists
                             (fun prefix -> Types.is_field_path_prefix prefix fields)
                             allowed
                          || List.mem (position, fields) !reported)
                      then begin
                        reported := (position, fields) :: !reported;
                        let shown = String.concat "." (name_parameter position :: fields) in
                        let fixes =
                          match (fields, written_parts) with
                          | _ :: _, Some entries -> (
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
                             "%s changes here, and the `modifies` clause of `%s` does not name it. \
                              The proofs of its callers take every part of `%s` that the clause \
                              does not name to keep its value."
                             (if fields = [] then Printf.sprintf "All of `%s`" shown
                              else Printf.sprintf "`%s`" shown)
                             shown_function (name_parameter position))
                      end
                  | Some _ | None -> ())
              | Constant _ | Literal _ -> ())
            (Mir.list_changed_places
               ~list_modified:
                 (Mir.list_callee_modified_fields
                    ~read_signature:(Interface.Impls.read_signature interface)
                    interface Types.no_substitution)
               [ tree.body.code ]))
