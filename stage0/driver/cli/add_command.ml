(* [truss add]: adds registry packages as dependencies of the package the
   command runs in. Each gets a manifest entry that grants it nothing, and
   a lock file line at the requested version or the newest, with lines for
   its own dependencies. *)

let run ~names =
  let session, packages = Command_packages.current () in
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
    Filename.concat (Command_packages.directory session package) Command_packages.manifest_name
  in
  let written = In_channel.with_open_bin manifest In_channel.input_all in
  let with_entries =
    try List.fold_left (fun text (name, _) -> Manifest.with_dependency text name) written wanted
    with Manifest.Malformed (line, message) ->
      Outcome.cannot_run "%s:%d: %s" (Shown_path.shown manifest) line message
  in
  let write text =
    if text <> In_channel.with_open_bin manifest In_channel.input_all then begin
      Command_packages.write_file manifest text;
      Database.refresh session
    end
  in
  write with_entries;
  match Database.plan_lock session ~set:wanted ~all:false with
  | Error message ->
      (* The manifest is restored, so a package that cannot be fetched
         is not left as a dependency. *)
      write written;
      Outcome.cannot_run "%s" message
  | Ok plan ->
      Command_packages.write_file (Upgrade_command.lock_file session) plan.text;
      Database.refresh session;
      Upgrade_command.report
        ~lock:(Upgrade_command.lock_changes ~before:plan.before ~after:plan.after)
        ~signatures:[] ~broken:[];
      0
