let parse_position text =
  match List.rev (String.split_on_char ':' text) with
  | column :: line :: (_ :: _ as file) -> (
      match (int_of_string_opt line, int_of_string_opt column) with
      | Some line, Some column when line > 0 && column > 0 ->
          (String.concat ":" (List.rev file), line, column)
      | _ -> Outcome.raise_cannot_run "`%s` is not FILE:LINE:COLUMN." text)
  | _ -> Outcome.raise_cannot_run "`%s` is not FILE:LINE:COLUMN." text

let run ~position =
  let json = Output.json () in
  let file, line, column = parse_position position in
  let snapshot, packages = Command_packages.load_worktree () in
  let path = Shown_path.resolve_real_path file in
  match
    List.find_opt
      (fun written -> Command_packages.locate_file snapshot written = path)
      (Command_packages.list_files snapshot packages)
  with
  | None -> Outcome.raise_cannot_run "%s is not a file of a package in this worktree." file
  | Some written -> (
      let database = Workspace.open_database snapshot in
      let offset =
        Source.compute_offset Source.Scalar_values
          (Workspace.read_source snapshot written)
          ~line:(line - 1) ~column:(column - 1)
      in
      let names = Database.make_name_lookups database packages in
      let symbol_at =
        List.find_map
          (fun (declaration : Resolve.Names.declaration) ->
            let key = Resolve.Names.make_key declaration in
            let ({ base; _ } : Resolve.Names.place) = names.place key in
            let text = names.text key in
            if base <= offset && offset <= base + String.length text then
              match Database.read_resolved database key with
              | Some resolved ->
                  let tables =
                    Option.map
                      (fun (checked : Infer.checked) -> checked.tables)
                      (Database.read_checked_body database key)
                  in
                  Inspect.explain_at ~path:key.path (names.spans key) (names.definition key)
                    resolved tables ~text (offset - base)
              | None -> None
            else None)
          (names.declarations_in written)
      in
      match symbol_at with
      | None ->
          if json then Json.print (Json.make_document ~diagnostics:[] [ ("found", Json.Null) ])
          else Output.print_line "Nothing there.";
          0
      | Some explanation ->
          let signature = Option.bind explanation.refers_to (Signatures.find_signature names) in
          if json then
            Json.print
              (Json.make_document ~diagnostics:[]
                 [
                   ( "found",
                     Json.Object
                       [
                         ("text", Json.String explanation.text);
                         ( "meaning",
                           Json.encode_option
                             (fun meaning -> Json.String meaning)
                             explanation.meaning );
                         ( "refers_to",
                           Json.encode_option
                             (fun target -> Json.String (Path.show target))
                             explanation.refers_to );
                         ( "type",
                           Json.encode_option
                             (fun type_text -> Json.String type_text)
                             explanation.type_ );
                         ("signature", Json.encode_option (fun text -> Json.String text) signature);
                       ] );
                 ])
          else begin
            Output.printf "`%s`\n" explanation.text;
            Option.iter (Output.printf "means %s\n") explanation.meaning;
            Option.iter (Output.printf "has type %s\n") explanation.type_;
            Option.iter
              (fun text ->
                Output.printf "signature:\n  %s\n"
                  (String.concat "\n  " (String.split_on_char '\n' text)))
              signature
          end;
          0)
