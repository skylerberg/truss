let require_lowered_lookups database packages =
  match Database.find_lowered_lookups database packages with
  | Ok lookups -> lookups
  | Error message -> Outcome.raise_cannot_run "%s" message

let make_results cache : Backend.results =
  {
    find = (fun key -> Cache.find_result cache ~kind:Test_result ~key);
    add = (fun key value -> Cache.add_result cache ~kind:Test_result ~key value);
  }

let create snapshot packages lookups (profile : Backend.profile) =
  let cache = Workspace.open_cache () in
  let c_compiler =
    match C_compiler.find ~objects:(Cache.make_objects_directory cache) with
    | Ok c_compiler -> c_compiler
    | Error message -> Outcome.raise_cannot_run "%s" message
  in
  let show_file =
    match profile with
    | Development -> Command_packages.show_file snapshot packages
    | Release -> Path.show_file
  in
  let own = List.map snd (Workspace.list_packages snapshot) in
  Backend.create ~show_file ~results:(make_results cache)
    ~programs:(Cache.make_programs_directory cache)
    ~is_worked_on:(fun package -> List.mem package own)
    lookups c_compiler profile
