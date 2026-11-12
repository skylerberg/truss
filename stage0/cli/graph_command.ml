(* [truss references] and [truss dependencies]: a definition's readers,
   and its dependencies, part by part, from the graph of results the
   session keeps. *)

type direction = References | Dependencies

let run ~directory ~direction ~name ~json =
  let project = Project.load directory in
  match Database.find_definitions project.session name with
  | [] -> Project.cannot_run "No definition named %s in this worktree." name
  | targets ->
      let dependencies = Database.dependencies project.session in
      (* Each row: the reader, its part, the part it reads, and the definition it reads. *)
      let rows =
        List.concat_map
          (fun target ->
            match direction with
            | References ->
                List.map
                  (fun (reader, part, read) -> (reader, part, read, target))
                  (Database.readers dependencies target)
            | Dependencies ->
                List.map
                  (fun (read_path, part, read) -> (target, part, read, read_path))
                  (Database.reads dependencies target))
          targets
        |> List.sort_uniq compare
      in
      if json then
        Json.print
          (Json.document ~diagnostics:[]
             [
               ( "reads",
                 Json.List
                   (List.map
                      (fun (reader, part, read, path) ->
                        Json.Object
                          [
                            ("reader", Json.String (Path.show reader));
                            ("part", Json.String part);
                            ("reads", Json.String read);
                            ("of", Json.String (Path.show path));
                          ])
                      rows) );
             ])
      else if rows = [] then
        Output.print_line
          (match direction with
          | References -> "Nothing reads it."
          | Dependencies -> "It reads nothing.")
      else
        List.iter
          (fun (reader, part, read, path) ->
            Output.printf "%s: its %s reads the %s of %s\n" (Path.show reader) part read
              (Path.show path))
          rows;
      0
