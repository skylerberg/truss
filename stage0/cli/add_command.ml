(* [truss add]: adds registry packages as dependencies of the package the
   command runs in. Each gets a manifest entry that grants it nothing, and
   a lock file line at the requested version or the newest, with lines for
   its own dependencies. *)

let run ~directory ~names ~json =
  let project = Project.load directory in
  let package = Project.package project in
  let wanted = List.map Upgrade_command.wanted names in
  let registry =
    match Registry.Index.current () with
    | Some registry -> registry
    | None ->
        Project.cannot_run "No registry is set. Set `%s` to the registry's directory."
          Registry.Index.variable
  in
  List.iter
    (fun (name, version) ->
      match version with
      | None ->
          if Registry.Index.newest registry name = None then
            Project.cannot_run "The registry has no package `%s`." (Path.show_package name)
      | Some version ->
          if Registry.Index.hash_of registry name version = None then
            Project.cannot_run "The registry has no `%s` %s." (Path.show_package name)
              (Registry.Version.show version))
    wanted;
  let manifest = Filename.concat package.directory Project.manifest_name in
  let written = In_channel.with_open_bin manifest In_channel.input_all in
  let with_entries =
    try List.fold_left (fun text (name, _) -> Manifest.with_dependency text name) written wanted
    with Manifest.Malformed (line, message) ->
      Project.cannot_run "%s:%d: %s" (Project.shown manifest) line message
  in
  let write text =
    if text <> In_channel.with_open_bin manifest In_channel.input_all then begin
      Project.write_file manifest text;
      Project.reload project
    end
  in
  write with_entries;
  match Database.plan_lock project.session ~set:wanted ~all:false with
  | Error message ->
      (* The manifest is restored, so a package that cannot be fetched
         is not left as a dependency. *)
      write written;
      Project.cannot_run "%s" message
  | Ok plan ->
      Project.write_file (Upgrade_command.lock_file project) plan.text;
      Project.reload project;
      Upgrade_command.report ~json
        ~lock:(Upgrade_command.lock_changes ~before:plan.before ~after:plan.after)
        ~signatures:[] ~broken:[];
      0
