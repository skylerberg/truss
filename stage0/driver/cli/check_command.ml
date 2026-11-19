let rounds = 32

let remove_unused_dependencies snapshot database packages =
  let root = Workspace.locate_root snapshot in
  List.filter_map
    (fun (file, package, (problem : Database.manifest_problem)) ->
      match problem with
      | Unused_dependency dependency ->
          let path = Filename.concat root file in
          let text = In_channel.with_open_bin path In_channel.input_all in
          Command_packages.write_file path (Manifest.remove_dependency text dependency);
          Some
            (Json.to_string
               (Json.Object
                  [
                    ("file", Json.String file);
                    ( "message",
                      Json.String (Package_checks.describe_unused_dependency ~package dependency) );
                  ]))
      | Not_a_capability _ -> None)
    (Command_packages.list_manifest_problems snapshot database packages)

let lock_file snapshot =
  match Workspace.lock_fix snapshot with
  | None -> []
  | Some text ->
      let path = Filename.concat (Workspace.locate_root snapshot) "truss.lock" in
      Command_packages.write_file path text;
      [
        Json.to_string
          (Json.Object
             [
               ("file", Json.String (Command_packages.show_project_path snapshot path));
               ("message", Json.String "This is not the lock file the manifests give.");
             ]);
      ]

let fix snapshot packages =
  let rec run_round snapshot number fixed =
    let database = Workspace.open_database snapshot in
    let applied =
      List.concat_map
        (fun file ->
          let diagnostics = Database.list_file_diagnostics database file in
          match Diagnostic.list_machine_applicable diagnostics with
          | [] -> []
          | chosen ->
              let source = Command_packages.read_source snapshot database file in
              let edits =
                List.concat_map
                  (fun (diagnostic : Diagnostic.t) ->
                    match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
                  chosen
              in
              Command_packages.write_file
                (Command_packages.locate_file snapshot file)
                (Diagnostic.apply_edits (Source.text source) edits);
              List.map (fun diagnostic -> Diagnostic.to_json_object source diagnostic) chosen)
        (Command_packages.list_files snapshot packages)
      @ remove_unused_dependencies snapshot database packages
      @ lock_file snapshot
    in
    if applied = [] || number = rounds then (snapshot, List.rev fixed)
    else run_round (Command_packages.retake snapshot) (number + 1) (List.rev_append applied fixed)
  in
  run_round snapshot 1 []

let run ~fix:fixing ~proofs =
  let snapshot, packages = Command_packages.load_current () in
  let snapshot, fixed = if fixing then fix snapshot packages else (snapshot, []) in
  let database = Workspace.open_database snapshot in
  let report = Report.gather ~proofs database snapshot packages in
  if Output.json () then
    Json.print
      (Report.make_document report
         (if fixing then
            [ ("fixed", Json.List (List.map (fun fixed_text -> Json.Raw fixed_text) fixed)) ]
          else []))
  else begin
    if fixed <> [] then
      Output.eprintf "Fixed %s.\n" (Diagnostic.show_count (List.length fixed) "error" "errors");
    Report.print report
  end;
  if Report.has_errors report then 1 else 0
