let run ~names =
  let snapshot, packages = Command_packages.load_current () in
  let package = Command_packages.require_one packages in
  let wanted = List.map Upgrade_command.parse_wanted names in
  let registry =
    match Registry.Index.find_current_registry () with
    | Some registry -> registry
    | None ->
        Outcome.raise_cannot_run "No registry is set. Set `%s` to the registry's directory."
          Registry.Index.variable
  in
  List.iter
    (fun (name, version) ->
      match version with
      | None ->
          if Registry.Index.find_newest registry name = None then
            Outcome.raise_cannot_run "The registry has no package `%s`." (Path.show_package name)
      | Some version ->
          if Registry.Index.hash_of registry name version = None then
            Outcome.raise_cannot_run "The registry has no `%s` %s." (Path.show_package name)
              (Registry.Version.show version))
    wanted;
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
  | Error message ->
      if with_entries <> written then Command_packages.write_file manifest written;
      Outcome.raise_cannot_run "%s" message
  | Ok plan ->
      Command_packages.write_file (Upgrade_command.lock_file snapshot) plan.text;
      Upgrade_command.report
        ~lock:(Upgrade_command.lock_changes ~before:plan.before ~after:plan.after)
        ~signatures:[] ~broken:[];
      0
