let find_main snapshot database packages (package : Path.package) =
  if List.mem { Path.package; modules = [] } (Command_packages.list_modules snapshot packages) then
    Database.find_main database package
  else None

let list_mains snapshot packages =
  List.filter_map (find_main snapshot (Workspace.open_database snapshot) packages) packages

let require_main snapshot database packages =
  let package = Command_packages.require_one packages in
  match find_main snapshot database packages package with
  | Some main -> main
  | None ->
      Outcome.raise_cannot_run
        "The package %s has no `main` in its root module, a file in its top directory, so it has \
         no program."
        (Path.show_package package)

let refuse_unshippable snapshot packages lookups main proofs =
  let in_code =
    List.map
      (fun ({ failure; file; line; column; way } : Backend.unshippable) ->
        ( Command_packages.show_file snapshot packages file,
          line,
          column,
          (failure :> [ `Todo | `Echo | `Proof_hole ]),
          way ))
      (Backend.list_unshippable lookups ~main)
  in
  let in_proofs =
    List.concat_map
      (fun definition ->
        List.map
          (fun (file, line, column) -> (file, line, column, `Proof_hole, [ definition ]))
          (Proofs.list_holes snapshot packages proofs definition))
      (Backend.list_reached_definitions lookups main)
  in
  match List.sort_uniq compare (in_code @ in_proofs) with
  | [] -> ()
  | refusals ->
      let show_kind = function `Todo -> "todo" | `Echo -> "echo" | `Proof_hole -> "proof hole" in
      let show_hole_kind = function
        | `Todo -> "`todo`"
        | `Echo -> "`echo`"
        | `Proof_hole -> "`todo` in a proof"
      in
      if Output.json () then
        Json.print
          (Json.make_document ~diagnostics:[]
             [
               ( "unshippable",
                 Json.List
                   (List.map
                      (fun (file, line, column, failure, way) ->
                        Json.Object
                          [
                            ("kind", Json.String (show_kind failure));
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
              file line column (show_hole_kind failure)
              (String.concat " -> " (List.map Path.show way)))
          refusals;
      raise (Outcome.Stop 1)

let build_program ?output snapshot packages (profile : Backend.profile) =
  let database = Workspace.open_database snapshot in
  let report = Report.gather ~proofs:(profile = Release) database snapshot packages in
  if not (Report.clean report) then raise (Report.Errors report);
  let main = require_main snapshot database packages in
  let lookups = Workspace_backend.require_lowered_lookups database packages in
  Option.iter (refuse_unshippable snapshot packages lookups main) (Report.force_proofs report);
  let backend = Workspace_backend.create snapshot packages lookups profile in
  let output = Option.value output ~default:(Backend.make_program_path backend) in
  match Backend.build_program backend ~main ~output with
  | Error message -> Outcome.raise_cannot_run "%s" message
  | Ok () -> output

let run ~release ~arguments =
  let snapshot, packages = Command_packages.load_current () in
  let program = build_program snapshot packages (if release then Release else Development) in
  Outcome.Run_program { program; arguments }

let build ~output =
  let snapshot, packages = Command_packages.load_current () in
  let package = Command_packages.require_one packages in
  let output = Shown_path.normalize (Option.value output ~default:(Path.show_package package)) in
  ignore (build_program snapshot packages Release ~output);
  if Output.json () then
    Json.print
      (Json.make_document ~diagnostics:[] [ ("output", Json.String (Shown_path.show_path output)) ])
  else Output.printf "Built %s.\n" (Shown_path.show_path output);
  Outcome.Exit 0
