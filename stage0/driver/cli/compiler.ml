type build = Development | Release

let read_c_flags () =
  Toolchain.split_flags (Option.value (Sys.getenv_opt Toolchain.added_flags_variable) ~default:"")

let require_toolchain () =
  match Toolchain.find () with
  | Ok toolchain -> toolchain
  | Error message -> Outcome.raise_cannot_run "%s" message

let make_requests database packages =
  match Libc.host with
  | Some _ -> Database.make_lowering_requests database packages
  | None -> Outcome.raise_cannot_run "Stage0 builds programs only for Linux and macOS."

let make_results () : Compile.results =
  let cache = Workspace.open_cache () in
  {
    find = (fun key -> Cache.find_result cache ~kind:Test_result ~key);
    add = (fun key value -> Cache.add_result cache ~kind:Test_result ~key value);
  }

let make_development_settings () : Build.settings =
  { build = Development; optimization = O1; extra = read_c_flags () }

let make_lowering_compiler database packages =
  Compile.create ~results:(make_results ()) (make_requests database packages)
    { compiler = "cc"; identity = "lowering only" }
    (Build.make_cache (Cache.make_objects_directory (Workspace.open_cache ())))
    (make_development_settings ())

let create database snapshot packages build =
  let toolchain = require_toolchain () in
  let settings : Build.settings =
    match build with
    | Development -> make_development_settings ()
    | Release ->
        {
          build = Release;
          optimization = O2;
          extra = Toolchain.link_time_optimization toolchain @ read_c_flags ();
        }
  in
  let show_file (file : Path.file) =
    match build with
    | Development when List.mem file.module_.package packages ->
        Shown_path.show_path (Command_packages.locate_file snapshot file)
    | _ -> Path.show_file file
  in
  let own = List.map snd (Workspace.list_packages snapshot) in
  Compile.create ~show_file ~results:(make_results ())
    ~programs:(Cache.make_programs_directory (Workspace.open_cache ()))
    ~is_worked_on:(fun package -> List.mem package own)
    (make_requests database packages) toolchain
    (Build.make_cache (Cache.make_objects_directory (Workspace.open_cache ())))
    settings
