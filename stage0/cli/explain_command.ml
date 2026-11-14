(* [truss explain FILE:LINE:COLUMN]: the name or expression at a position,
   its meaning, its type, and the signature of the definition it refers
   to. *)

module Names = Resolve.Names

(* Parses [FILE:LINE:COLUMN] from the right, so a file name may contain a
   colon. *)
let parse_position text =
  match List.rev (String.split_on_char ':' text) with
  | column :: line :: (_ :: _ as file) -> (
      match (int_of_string_opt line, int_of_string_opt column) with
      | Some line, Some column when line > 0 && column > 0 ->
          (String.concat ":" (List.rev file), line, column)
      | _ -> Outcome.cannot_run "`%s` is not FILE:LINE:COLUMN." text)
  | _ -> Outcome.cannot_run "`%s` is not FILE:LINE:COLUMN." text

let run ~position =
  let json = Output.json () in
  let file, line, column = parse_position position in
  let session, packages = Command_packages.worktree () in
  let path = Shown_path.real file in
  match
    List.find_opt
      (fun written -> Command_packages.path session written = path)
      (Command_packages.files session packages)
  with
  | None -> Outcome.cannot_run "%s is not a file of a package in this worktree." file
  | Some written -> (
      let context = Database.context session in
      let offset =
        Source.offset Source.Scalar_values (Query.demand context Workspace.file written).source
          ~line:(line - 1) ~column:(column - 1)
      in
      let symbol_at =
        List.find_map
          (fun (declaration : Names.declaration) ->
            let key = Names.key_of declaration in
            match (Query.demand context Names.base key, Query.demand context Names.text key) with
            | Some (_, base), Some text when base <= offset && offset <= base + String.length text
              -> (
                match
                  ( Query.demand context Names.definition key,
                    Query.demand context Resolve.resolved key )
                with
                | Some definition, Some resolved ->
                    let tables =
                      Option.map
                        (fun (result : Infer.type_check_result) -> result.tables)
                        (Query.demand context Infer.type_check_result key)
                    in
                    Inspect.explain_at ~path:key.path definition resolved tables ~text
                      (offset - base)
                | _ -> None)
            | _ -> None)
          (Query.demand context Names.declarations_in written)
      in
      match symbol_at with
      | None ->
          if json then Json.print (Json.document ~diagnostics:[] [ ("found", Json.Null) ])
          else Output.print_line "Nothing there.";
          0
      | Some explanation ->
          let signature =
            Option.bind explanation.refers_to (fun path ->
                match Query.demand context Interface.Summary.key path with
                | Some key -> Signatures.text context ~body:false ~opaque:false key
                | None -> None)
          in
          if json then
            Json.print
              (Json.document ~diagnostics:[]
                 [
                   ( "found",
                     Json.Object
                       [
                         ("text", Json.String explanation.text);
                         ( "meaning",
                           Json.option (fun meaning -> Json.String meaning) explanation.meaning );
                         ( "refers_to",
                           Json.option
                             (fun target -> Json.String (Path.show target))
                             explanation.refers_to );
                         ( "type",
                           Json.option (fun type_text -> Json.String type_text) explanation.type_ );
                         ("signature", Json.option (fun text -> Json.String text) signature);
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
