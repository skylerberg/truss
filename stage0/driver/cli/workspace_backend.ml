let require_lowered_lookups database packages =
  match Database.find_lowered_lookups database packages with
  | Ok lookups -> lookups
  | Error message -> Outcome.raise_cannot_run "%s" message

let make_debug_prefix_map (directory, package) =
  (Path.show_package_directory package ^ "/", Filename.concat directory "")

let create snapshot lookups (profile : Backend.profile) =
  let cache = Workspace.open_cache () in
  let c_compiler =
    match
      C_compiler.find
        ~debug_prefix_maps:(List.map make_debug_prefix_map (Workspace.list_packages snapshot))
        ~x86_64_level:(Workspace.x86_64_level snapshot)
        ~objects:(Cache.make_objects_directory cache)
        ()
    with
    | Ok c_compiler -> c_compiler
    | Error message -> Outcome.raise_cannot_run "%s" message
  in
  Backend.create ~show_file:(Workspace.locate_file snapshot)
    ~programs:(Cache.make_programs_directory cache)
    lookups c_compiler profile
