(* [truss explain FILE:LINE:COLUMN]: what is at a position: the name or
   expression there, what it means, its type, and the signature of the
   definition it refers to. *)

module Names = Resolve.Names

(* The byte offset of a line and column, both counting from 1, where a
   column counts Unicode scalar values, as diagnostics do. *)
let offset_of text ~line ~column =
  let length = String.length text in
  let rec start_of current offset =
    if current >= line || offset >= length then offset
    else
      match String.index_from_opt text offset '\n' with
      | Some newline -> start_of (current + 1) (newline + 1)
      | None -> length
  in
  let rec advance offset remaining =
    if remaining <= 0 || offset >= length || text.[offset] = '\n' then offset
    else
      let width = Uchar.utf_decode_length (String.get_utf_8_uchar text offset) in
      advance (offset + max 1 width) (remaining - 1)
  in
  advance (start_of 1 0) (column - 1)

(* [FILE:LINE:COLUMN], from the right, so a file name may hold a colon. *)
let parse_position text =
  match List.rev (String.split_on_char ':' text) with
  | column :: line :: (_ :: _ as file) -> (
      match (int_of_string_opt line, int_of_string_opt column) with
      | Some line, Some column when line > 0 && column > 0 ->
          (String.concat ":" (List.rev file), line, column)
      | _ -> Project.cannot_run "`%s` is not FILE:LINE:COLUMN." text)
  | _ -> Project.cannot_run "`%s` is not FILE:LINE:COLUMN." text

let run ~directory ~position ~json =
  let file, line, column = parse_position position in
  let here = Project.load directory in
  let project = Project.load (Database.root here.session) in
  let path = Project.real file in
  match List.find_opt (fun (_, f) -> f = path) project.files with
  | None -> Project.cannot_run "%s is not a module of a package in this worktree." file
  | Some (module_, _) -> (
      let context = project.context in
      let text = Source.text (Project.parsed project module_).source in
      let offset = offset_of text ~line ~column in
      let found =
        List.find_map
          (fun (d : Names.declaration) ->
            let key = Names.key_of d in
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
                    Inspect.explain_at definition resolved tables ~text (offset - base)
                | _ -> None)
            | _ -> None)
          (Query.demand context Names.declarations module_)
      in
      match found with
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
                         ("meaning", Json.option (fun m -> Json.String m) explanation.meaning);
                         ( "refers_to",
                           Json.option (fun p -> Json.String (Path.show p)) explanation.refers_to );
                         ("type", Json.option (fun t -> Json.String t) explanation.type_);
                         ("signature", Json.option (fun s -> Json.String s) signature);
                       ] );
                 ])
          else begin
            Output.printf "`%s`\n" explanation.text;
            Option.iter (Output.printf "means %s\n") explanation.meaning;
            Option.iter (Output.printf "has type %s\n") explanation.type_;
            Option.iter
              (fun s ->
                Output.printf "signature:\n  %s\n"
                  (String.concat "\n  " (String.split_on_char '\n' s)))
              signature
          end;
          0)
