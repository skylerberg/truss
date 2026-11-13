(* Code generation, configured for the commands that build programs. *)

type build = Development | Release

(* A process that answers for others, as the background process does, is
   told each one's [TRUSS_CFLAGS], which is not its own environment's. *)
let configured_c_flags : string option option ref = ref None
let configure_c_flags flags = configured_c_flags := Some flags

let c_flags () =
  let value =
    match !configured_c_flags with
    | Some told -> told
    | None -> Sys.getenv_opt Toolchain.added_flags_variable
  in
  Toolchain.split_flags (Option.value value ~default:"")

let toolchain () =
  match Toolchain.find () with
  | Ok toolchain -> toolchain
  | Error message -> Project.cannot_run "%s" message

(* Stage0 builds programs for the system it runs on. *)
let target () =
  match Libc.host with
  | Some system -> Memory_layout.target_64 system
  | None -> Project.cannot_run "Stage0 builds programs only for Linux and macOS."

(* Adds the instances a compiler asks keys for to the session's roots. *)
let want session context lowering wanted =
  Database.set session Compile.roots lowering (Compile.add_roots context lowering wanted)

(* Where the results of runs are kept: the database's store. *)
let results () : Compile.results =
  let find, add = Database.results ~kind:"tests" in
  { find; add }

(* A compiler that lowers code and compiles nothing, so it needs no C
   compiler. *)
let lowering_only session context =
  Compile.create ~want:(want session context) context (target ())
    { compiler = "cc"; identity = "lowering only" }
    (Build.cache (Database.objects_directory ()))
    { build = Development; optimization = O1; extra = c_flags () }

(* A development build compiles at -O1, one C file per instance. A release
   build compiles at -O2 with link-time optimization. A build checks every
   fallible primitive operation at run time unless [checks] is false, which
   is sound only when every obligation the program reaches is proven. *)
let create ?(checks = true) (project : Project.t) build =
  let toolchain = toolchain () in
  let extra = c_flags () in
  let settings : Build.settings =
    match build with
    | Development -> { build = Development; optimization = O1; extra }
    | Release ->
        {
          build = Release;
          optimization = O2;
          extra = Toolchain.link_time_optimization toolchain @ extra;
        }
  in
  (* A development build names files relative to the current directory,
     as diagnostics do. A release build names them relative to the
     package root, so the program is identical wherever it is built. *)
  let file_name file =
    match (build, List.assoc_opt file project.files) with
    | Development, Some path -> Project.shown path
    | _ -> Path.show_file file
  in
  let own = List.map snd (Database.packages project.session) in
  Compile.create ~checks ~file_name ~results:(results ())
    ~want:(want project.session project.context)
    ~worked_on:(fun package -> List.mem package own)
    project.context (target ()) toolchain
    (Build.cache (Database.objects_directory ()))
    settings
