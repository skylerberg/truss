type build = Development | Release

let c_flags () =
  Toolchain.split_flags (Option.value (Sys.getenv_opt Toolchain.added_flags_variable) ~default:"")

let toolchain () =
  match Toolchain.find () with
  | Ok toolchain -> toolchain
  | Error message -> Outcome.cannot_run "%s" message

let system () =
  match Libc.host with
  | Some system -> system
  | None -> Outcome.cannot_run "Stage0 builds programs only for Linux and macOS."

let want session context lowering wanted =
  Database.set session Compile.roots lowering (Compile.add_roots context lowering wanted)

let results () : Compile.results =
  let find, add = Database.results ~kind:Store.Test_result in
  { find; add }

let development_settings () : Build.settings =
  { build = Development; optimization = O1; extra = c_flags () }

let lowering_only session context =
  Compile.create ~want:(want session context) context (system ())
    { compiler = "cc"; identity = "lowering only" }
    (Build.cache (Database.objects_directory ()))
    (development_settings ())

let create ?(checks = true) session packages build =
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
        Shown_path.shown (Command_packages.path session file)
    | _ -> Path.show_file file
  in
  let own = List.map snd (Database.packages session) in
  Compile.create ~checks ~file_name ~results:(results ()) ~programs:(Database.programs_directory ())
    ~want:(want session (Database.context session))
    ~worked_on:(fun package -> List.mem package own)
    (Database.context session) (system ()) toolchain
    (Build.cache (Database.objects_directory ()))
    settings
