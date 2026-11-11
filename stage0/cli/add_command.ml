(* [truss add]: makes registry packages dependencies of the package it is
   run in. Each gets an entry in the manifest that grants it nothing, and a
   line in the project's lock file at the version asked for, or its newest,
   with the packages it brings with it. *)

let run ~directory ~names ~json =
  let project = Project.load directory in
  let package = Project.package project in
  let wanted = List.map Upgrade_command.wanted names in
  let registry =
    match Registry.Index.current () with
    | Some registry -> registry
    | None ->
        Project.cannot_run "No registry is set: `%s` names its directory." Registry.Index.variable
  in
  List.iter
    (fun (name, version) ->
      match version with
      | None ->
          if Registry.Index.newest registry name = None then
            Project.cannot_run "The registry has no package `%s`." name
      | Some version ->
          if Registry.Index.hash_of registry name version = None then
            Project.cannot_run "The registry has no `%s` %s." name (Registry.Version.show version))
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
      (* The manifest is left as it was, so that a package that cannot be
         had is not left as a dependency. *)
      write written;
      Project.cannot_run "%s" message
  | Ok plan ->
      Project.write_file (Upgrade_command.lock_file project) plan.text;
      Project.reload project;
      Upgrade_command.report ~json
        ~lock:(Upgrade_command.lock_changes ~before:plan.before ~after:plan.after)
        ~signatures:[] ~broken:[];
      0
