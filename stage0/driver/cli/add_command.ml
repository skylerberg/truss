let run ~names =
  let snapshot, packages = Command_packages.current () in
  let package = Command_packages.one packages in
  let wanted = List.map Upgrade_command.wanted names in
  let registry =
    match Registry.Index.current () with
    | Some registry -> registry
    | None ->
        Outcome.cannot_run "No registry is set. Set `%s` to the registry's directory."
          Registry.Index.variable
  in
  List.iter
    (fun (name, version) ->
      match version with
      | None ->
          if Registry.Index.newest registry name = None then
            Outcome.cannot_run "The registry has no package `%s`." (Path.show_package name)
      | Some version ->
          if Registry.Index.hash_of registry name version = None then
            Outcome.cannot_run "The registry has no `%s` %s." (Path.show_package name)
              (Registry.Version.show version))
    wanted;
  let manifest =
    Filename.concat (Command_packages.directory snapshot package) Command_packages.manifest_name
  in
  let written = In_channel.with_open_bin manifest In_channel.input_all in
  let with_entries =
    try List.fold_left (fun text (name, _) -> Manifest.with_dependency text name) written wanted
    with Manifest.Malformed { line; message } ->
      Outcome.cannot_run "%s:%d: %s" (Shown_path.shown manifest) line message
  in
  if with_entries <> written then Command_packages.write_file manifest with_entries;
  match Database.plan_lock (Command_packages.retake snapshot) ~set:wanted ~all:false with
  | Error message ->
      if with_entries <> written then Command_packages.write_file manifest written;
      Outcome.cannot_run "%s" message
  | Ok plan ->
      Command_packages.write_file (Upgrade_command.lock_file snapshot) plan.text;
      Upgrade_command.report
        ~lock:(Upgrade_command.lock_changes ~before:plan.before ~after:plan.after)
        ~broken:[];
      0
