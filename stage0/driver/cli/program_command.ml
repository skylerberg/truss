let mains pipeline packages =
  List.filter_map (Pipeline.entry_point (Pipeline.names pipeline packages)) packages

let main pipeline packages =
  let package = Command_packages.one packages in
  match Pipeline.entry_point (Pipeline.names pipeline packages) package with
  | Some main -> main
  | None ->
      Outcome.cannot_run
        "The package %s has no `main` in its root module, a file in its top directory, so it has \
         no program."
        (Path.show_package package)

let refuse_unshippable snapshot packages compile main proofs =
  let reached =
    match Compile.reach_program compile ~main with
    | Error message -> Outcome.cannot_run "%s" message
    | Ok reached -> reached
  in
  let in_code =
    List.map
      (fun ({ failure; file; line; column; way } : Compile.unshippable) ->
        ( Command_packages.shown_workspace_path snapshot packages file,
          line,
          column,
          (failure :> [ `Todo | `Echo | `Proof_hole ]),
          way ))
      reached.unshippable
  in
  let in_proofs =
    List.concat_map
      (fun definition ->
        List.map
          (fun (file, line, column) -> (file, line, column, `Proof_hole, [ definition ]))
          (Proofs.holes snapshot packages proofs definition))
      reached.definitions
  in
  match List.sort_uniq compare (in_code @ in_proofs) with
  | [] -> ()
  | refusals ->
      let kind = function `Todo -> "todo" | `Echo -> "echo" | `Proof_hole -> "proof hole" in
      let shown = function
        | `Todo -> "`todo`"
        | `Echo -> "`echo`"
        | `Proof_hole -> "`todo` in a proof"
      in
      if Output.json () then
        Json.print
          (Json.document ~diagnostics:[]
             [
               ( "unshippable",
                 Json.List
                   (List.map
                      (fun (file, line, column, failure, way) ->
                        Json.Object
                          [
                            ("kind", Json.String (kind failure));
                            ("file", Json.String file);
                            ("line", Json.Int line);
                            ("column", Json.Int column);
                            ( "way",
                              Json.List (List.map (fun path -> Json.String (Path.show path)) way) );
                          ])
                      refusals) );
             ])
      else
        List.iter
          (fun (file, line, column, failure, way) ->
            Output.eprintf
              "%s:%d:%d: %s can be reached from `main`, so the program cannot be built.\n    %s\n"
              file line column (shown failure)
              (String.concat " -> " (List.map Path.show way)))
          refusals;
      raise (Outcome.Stop 1)

let build_program ?output snapshot packages (build : Compiler.build) =
  let is_release = build = Release in
  let pipeline = Database.pipeline ~checks:(not is_release) snapshot in
  let report = Report.gather ~proofs:is_release pipeline snapshot packages in
  if not (Report.clean report) then raise (Report.Errors report);
  let main = main pipeline packages in
  let compile = Compiler.create pipeline snapshot packages build in
  Option.iter (refuse_unshippable snapshot packages compile main) (Report.proofs report);
  let output = Option.value output ~default:(Compile.fresh_program compile) in
  match Compile.build_program compile ~main ~output with
  | Error message -> Outcome.cannot_run "%s" message
  | Ok () -> output

let run ~release ~arguments =
  let snapshot, packages = Command_packages.current () in
  let program = build_program snapshot packages (if release then Release else Development) in
  Outcome.Run_program { program; arguments }

let build ~output =
  let snapshot, packages = Command_packages.current () in
  let package = Command_packages.one packages in
  let output = Shown_path.normalize (Option.value output ~default:(Path.show_package package)) in
  ignore (build_program snapshot packages Release ~output);
  if Output.json () then
    Json.print (Json.document ~diagnostics:[] [ ("output", Json.String (Shown_path.shown output)) ])
  else Output.printf "Built %s.\n" (Shown_path.shown output);
  Outcome.Exit 0
