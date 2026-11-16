type build = Development | Release

let c_flags () =
  Toolchain.split_flags (Option.value (Sys.getenv_opt Toolchain.added_flags_variable) ~default:"")

let toolchain () =
  match Toolchain.find () with
  | Ok toolchain -> toolchain
  | Error message -> Outcome.cannot_run "%s" message

let requests pipeline packages =
  match Libc.host with
  | Some _ -> Pipeline.lowering_requests pipeline packages
  | None -> Outcome.cannot_run "Stage0 builds programs only for Linux and macOS."

let results () : Compile.results =
  let cache = Workspace.open_cache () in
  {
    find = (fun key -> Cache.find_result cache ~kind:Test_result ~key);
    add = (fun key value -> Cache.add_result cache ~kind:Test_result ~key value);
  }

let development_settings () : Build.settings =
  { build = Development; optimization = O1; extra = c_flags () }

let lowering_only pipeline packages =
  Compile.create ~results:(results ()) (requests pipeline packages)
    { compiler = "cc"; identity = "lowering only" }
    (Build.cache (Cache.make_objects_directory (Workspace.open_cache ())))
    (development_settings ())

let create pipeline snapshot packages build =
  let toolchain = toolchain () in
  let settings : Build.settings =
    match build with
    | Development -> development_settings ()
    | Release ->
        {
          build = Release;
          optimization = O2;
          extra = Toolchain.link_time_optimization toolchain @ c_flags ();
        }
  in
  let file_name file =
    match build with
    | Development when List.mem file.Path.module_.package packages ->
        Shown_path.shown (Command_packages.path snapshot file)
    | _ -> Path.show_file file
  in
  let own = List.map snd (Workspace.packages snapshot) in
  Compile.create ~file_name ~results:(results ())
    ~programs:(Cache.make_programs_directory (Workspace.open_cache ()))
    ~worked_on:(fun package -> List.mem package own)
    (requests pipeline packages) toolchain
    (Build.cache (Cache.make_objects_directory (Workspace.open_cache ())))
    settings
