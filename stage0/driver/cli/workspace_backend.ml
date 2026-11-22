let require_lowered_lookups database packages =
  match Database.find_lowered_lookups database packages with
  | Ok lookups -> lookups
  | Error message -> Outcome.raise_cannot_run "%s" message

let make_results cache : Backend.results =
  {
    find = (fun key -> Cache.find_result cache ~kind:Test_result ~key);
    add = (fun key value -> Cache.add_result cache ~kind:Test_result ~key value);
  }

let make_debug_prefix_map snapshot package =
  let probe : Path.file = { module_ = { package; modules = [] }; name = "" } in
  let remove_file_name path = String.sub path 0 (String.length path - String.length ".truss") in
  (remove_file_name (Path.show_file probe), remove_file_name (Workspace.locate_file snapshot probe))

let create snapshot lookups (profile : Backend.profile) =
  let cache = Workspace.open_cache () in
  let c_compiler =
    match
      C_compiler.find
        ~debug_prefix_maps:
          (List.map
             (fun (_, package) -> make_debug_prefix_map snapshot package)
             (Workspace.list_packages snapshot))
        ~objects:(Cache.make_objects_directory cache)
        ()
    with
    | Ok c_compiler -> c_compiler
    | Error message -> Outcome.raise_cannot_run "%s" message
  in
  Backend.create ~show_file:(Workspace.locate_file snapshot) ~results:(make_results cache)
    ~programs:(Cache.make_programs_directory cache)
    lookups c_compiler profile
