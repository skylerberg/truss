let rounds = 32

let unused_dependencies snapshot pipeline packages =
  let root = Database.root snapshot in
  List.filter_map
    (fun (file, package, (problem : Package_checks.manifest_problem)) ->
      match problem with
      | Unused dependency ->
          let path = Filename.concat root file in
          let text = In_channel.with_open_bin path In_channel.input_all in
          Command_packages.write_file path (Manifest.without_dependency text dependency);
          Some
            (Json.to_string
               (Json.Object
                  [
                    ("file", Json.String (Shown_path.shown path));
                    ("message", Json.String (Package_checks.manifest_sentence ~package problem));
                  ]))
      | Not_a_capability _ -> None)
    (Command_packages.manifest_problems snapshot pipeline packages)

let lock_file snapshot =
  match Database.lock_fix snapshot with
  | None -> []
  | Some text ->
      let path = Filename.concat (Database.root snapshot) "truss.lock" in
      Command_packages.write_file path text;
      [
        Json.to_string
          (Json.Object
             [
               ("file", Json.String (Shown_path.shown path));
               ("message", Json.String "This is not the lock file the manifests give.");
             ]);
      ]

let fix snapshot packages =
  let rec round snapshot number fixed =
    let pipeline = Database.pipeline snapshot in
    Pipeline.check pipeline packages;
    let applied =
      List.concat_map
        (fun file ->
          let diagnostics = Pipeline.file_diagnostics pipeline file in
          match Diagnostic.machine_applicable diagnostics with
          | [] -> []
          | chosen ->
              let source = Command_packages.source snapshot packages file in
              let edits =
                List.concat_map
                  (fun (diagnostic : Diagnostic.t) ->
                    match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
                  chosen
              in
              Command_packages.write_file
                (Command_packages.path snapshot file)
                (Diagnostic.apply_edits (Source.text source) edits);
              List.map (fun diagnostic -> Diagnostic.to_json_object source diagnostic) chosen)
        (Command_packages.files snapshot packages)
      @ unused_dependencies snapshot pipeline packages
      @ lock_file snapshot
    in
    if applied = [] || number = rounds then (snapshot, List.rev fixed)
    else round (Database.retake snapshot) (number + 1) (List.rev_append applied fixed)
  in
  round snapshot 1 []

let run ~fix:fixing ~proofs =
  let snapshot, packages = Command_packages.current () in
  let snapshot, fixed = if fixing then fix snapshot packages else (snapshot, []) in
  let report = Report.gather ~proofs (Database.pipeline snapshot) snapshot packages in
  if Output.json () then
    Json.print
      (Report.document report
         (if fixing then
            [ ("fixed", Json.List (List.map (fun fixed_text -> Json.Raw fixed_text) fixed)) ]
          else []))
  else begin
    if fixed <> [] then
      Output.eprintf "Fixed %s.\n" (Report.plural (List.length fixed) "error" "errors");
    Report.print report
  end;
  if Report.clean report then 0 else 1
