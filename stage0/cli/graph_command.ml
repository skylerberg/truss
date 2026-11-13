(* [truss references] and [truss dependencies]: a definition's dependents
   and dependencies, by part, from the session's dependency graph. *)

type direction = References | Dependencies

let run ~direction ~name =
  let project = Project.current () in
  match Database.find_definitions project.session name with
  | [] -> Project.cannot_run "No definition named %s in this worktree." name
  | targets ->
      let edges =
        match direction with
        | References -> Database.dependents project.session targets
        | Dependencies -> Database.dependencies project.session targets
      in
      if Output.json () then
        Json.print
          (Json.document ~diagnostics:[]
             [
               ( "reads",
                 Json.List
                   (List.map
                      (fun (edge : Graph_types.edge) ->
                        Json.Object
                          [
                            ("reader", Json.String (Path.show edge.dependent));
                            ("part", Json.String edge.dependent_part);
                            ("reads", Json.String edge.dependency_part);
                            ("of", Json.String (Path.show edge.dependency));
                          ])
                      edges) );
             ])
      else if edges = [] then
        Output.print_line
          (match direction with
          | References -> "Nothing reads it."
          | Dependencies -> "It reads nothing.")
      else
        List.iter
          (fun (edge : Graph_types.edge) ->
            Output.printf "%s: its %s reads the %s of %s\n" (Path.show edge.dependent)
              edge.dependent_part edge.dependency_part (Path.show edge.dependency))
          edges;
      0
