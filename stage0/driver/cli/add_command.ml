let run ~names =
  let snapshot, packages = Command_packages.load_current () in
  let package = Command_packages.require_one packages in
  let wanted = List.map Upgrade_command.parse_wanted names in
  let manifest =
    Filename.concat
      (Command_packages.locate_directory snapshot package)
      Command_packages.manifest_name
  in
  let written = In_channel.with_open_bin manifest In_channel.input_all in
  let with_entries =
    try List.fold_left (fun text (name, _) -> Manifest.add_dependency text name) written wanted
    with Manifest.Malformed { line; problem } ->
      Outcome.raise_cannot_run "%s:%d: %s"
        (Command_packages.show_project_path snapshot manifest)
        line
        (Project_catalog.describe_manifest_problem problem)
  in
  if with_entries <> written then Command_packages.write_file manifest with_entries;
  match Workspace.plan_lock (Command_packages.retake snapshot) ~set:wanted ~all:false with
  | Error problems ->
      if with_entries <> written then Command_packages.write_file manifest written;
      Outcome.raise_problems problems
  | Ok plan ->
      Command_packages.write_file (Upgrade_command.lock_file snapshot) plan.text;
      Upgrade_command.report
        ~lock:(Upgrade_command.lock_changes ~before:plan.before ~after:plan.after)
        ~signatures:[] ~broken:[];
      0
