(* Code generation, configured for the commands that build programs. *)

type build = Development | Release

(* [--sanitize] builds with AddressSanitizer and UndefinedBehaviorSanitizer,
   for testing the compiler: every report is a compiler bug. *)
let sanitizers =
  [ "-fsanitize=address,undefined"; "-fno-sanitize-recover=undefined"; "-fno-omit-frame-pointer" ]

let toolchain () =
  match Toolchain.find () with
  | Ok toolchain -> toolchain
  | Error message -> Project.cannot_run "%s" message

(* Stage0 builds programs for the system it runs on. *)
let target () =
  match Libc.host with
  | Some system -> Memory_layout.target_64 system
  | None -> Project.cannot_run "Stage0 builds programs only for Linux and macOS."

(* A development build compiles at -O1, one C file per instance. A release
   build compiles at -O2 with link-time optimization. A build checks every
   fallible primitive operation at run time unless [checks] is false, which
   is sound only when every obligation the program reaches is proven. *)
let create ?(sanitize = false) ?(checks = true) (project : Project.t) build =
  let toolchain = toolchain () in
  let extra = if sanitize then sanitizers else [] in
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
  let file_name module_ =
    match (build, List.assoc_opt module_ project.files) with
    | Development, Some file -> Project.shown file
    | _ -> Workspace.file_path module_
  in
  let own = List.map snd (Database.packages project.session) in
  Compile.create ~checks ~file_name
    ~want:(fun lowering wanted ->
      Database.set project.session Compile.roots lowering
        (Compile.add_roots project.context lowering wanted))
    ~worked_on:(fun package -> List.mem package own)
    project.context (target ()) toolchain
    (Build.cache (Database.objects_directory ()))
    settings

let test_results () : Compile.results =
  let find, add = Database.results ~kind:"tests" in
  { find; add }
