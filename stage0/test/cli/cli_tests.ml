let test = Harness.test
let fail = Harness.fail
let expect_string = Harness.expect_string
let expect_strings = Harness.expect_strings

let make_directory files =
  let root = Harness.make_scratch_directory "package" in
  Harness.write_files root files;
  Cli.Shown_path.normalize root

let make_manifest name = Printf.sprintf "[package]\nname = \"%s\"\ntruss = \"0.1\"\n" name
let manifest = ("truss.toml", make_manifest "demo")
let make_package files = make_directory (manifest :: files)
let read root path = In_channel.with_open_bin (Filename.concat root path) In_channel.input_all

let capture work =
  let out = Buffer.create 256 and err = Buffer.create 256 in
  let result =
    Cli.Output.with_
      {
        print_out = Buffer.add_string out;
        print_err = Buffer.add_string err;
        terminal = false;
        columns = None;
        json = false;
      }
      work
  in
  Workspace.flush ();
  (result, Buffer.contents out ^ Buffer.contents err)

let run_truss arguments =
  match capture (fun () -> Cli.Main.For_testing.run_command_line arguments) with
  | Cli.Outcome.Exit status, output -> (status, output)
  | Cli.Outcome.Run_program { program; _ }, output ->
      Sys.remove program;
      (0, output)

let run_quietly arguments = fst (run_truss arguments)
let run_json arguments = Cli.Json.parse (snd (run_truss (arguments @ [ "--json" ])))
let list_objects = function Cli.Json.List items -> items | _ -> []

let read_string_field name value =
  match Cli.Json.lookup_field name value with Cli.Json.String text -> text | _ -> ""

let list_shown root path =
  list_objects (Cli.Json.lookup_field "definitions" (run_json [ "show"; "-C"; root; path ]))

let run_show root path = List.map (read_string_field "text") (list_shown root path)
let read_header text = List.hd (String.split_on_char '\n' text)

let () =
  let store = Harness.make_scratch_directory "store" in
  Workspace.For_testing.copy_standard_package_database ~into:store;
  Workspace.reset ();
  Unix.putenv "TRUSS_CACHE" store

let () =
  test "-C before the command is read as an option of the command" (fun () ->
      expect_strings
        ~expected:[ "truss"; "test"; "-C"; "dir"; "--rerun" ]
        (Cli.Arguments.move_leading_options [ "truss"; "-C"; "dir"; "test"; "--rerun" ]));
  test "--no-server before the command is read as an option of the command" (fun () ->
      expect_strings
        ~expected:[ "truss"; "check"; "--no-server"; "-C"; "dir"; "--fix" ]
        (Cli.Arguments.move_leading_options
           [ "truss"; "--no-server"; "-C"; "dir"; "check"; "--fix" ]));
  test "an option before -- is an option of run, not the program's" (fun () ->
      let status, output = run_truss [ "run"; "input.txt"; "-v" ] in
      if status <> 2 || not (String.includes ~affix:"-v" output) then
        fail "exited with %d: %s" status output)

let () =
  test
    "a synchronization reports a file written in a watched directory and no skipped directory, or \
     asks for a rescan where events can arrive late" (fun () ->
      let root = Harness.make_scratch_directory "watched" in
      Unix.mkdir (Filename.concat root "src") 0o755;
      let watcher =
        Watcher.start
          ~is_skipped_name:(fun name -> name = "skipped")
          ~cookie_directory:".truss" root
      in
      Fun.protect
        ~finally:(fun () -> Watcher.stop watcher)
        (fun () ->
          Unix.mkdir (Filename.concat root "skipped") 0o755;
          Out_channel.with_open_bin (Filename.concat root "src/main.truss") (fun out ->
              output_string out "fn main() {}\n");
          match Watcher.read_changes watcher with
          | Changed paths when List.mem "src/main.truss" paths && not (List.mem "skipped" paths) ->
              ()
          | Changed paths -> fail "reported %s" (String.concat ", " paths)
          | Rescan when not (Watcher.For_testing.is_delivered_before_synchronizing ()) -> ()
          | Rescan ->
              fail "asked for a rescan, though each event arrives before the synchronization"
          | Removed -> fail "reported a removal"));
  test "a watcher reports that its cookie directory was removed" (fun () ->
      let root = Harness.make_scratch_directory "unwatched" in
      let watcher =
        Watcher.start ~is_skipped_name:(fun _ -> false) ~cookie_directory:".truss" root
      in
      Fun.protect
        ~finally:(fun () -> Watcher.stop watcher)
        (fun () ->
          Unix.rmdir (Filename.concat root ".truss");
          match Watcher.read_changes watcher with
          | Removed -> ()
          | Changed _ | Rescan -> fail "did not report the removal"))

let () =
  test "a second process reports that the project's database is open elsewhere" (fun () ->
      let root = make_package [ ("main.truss", "fn main() {}\n") ] in
      ignore (run_quietly [ "check"; "-C"; root ]);
      let ready, signal = Unix.pipe ~cloexec:true () in
      match Unix.fork () with
      | 0 ->
          ignore (Lock_file.acquire (Filename.concat root ".truss/lock"));
          ignore (Unix.write_substring signal "x" 0 1);
          Unix.sleep 60;
          Unix._exit 0
      | owner ->
          Fun.protect
            ~finally:(fun () ->
              Unix.kill owner Sys.sigkill;
              ignore (Unix.waitpid [] owner))
            (fun () ->
              ignore (Unix.read ready (Bytes.create 1) 0 1);
              let status, output = run_truss [ "check"; "-C"; root ] in
              if status <> 2 || not (String.includes ~affix:"is open in another process" output)
              then fail "exited with %d: %s" status output))

let other_build =
  lazy
    (Unix.realpath
       (Filename.concat (Filename.dirname Sys.executable_name) "../../driver/truss/truss.exe"))

let is_database_open_elsewhere root = Lock_file.is_held (Filename.concat root ".truss/lock")

let make_package_served_by_other_build () =
  let root = make_package [ ("one.truss", "public fn one() -> Int64 { 1 }\n") ] in
  Unix.putenv "TRUSS_NO_SERVER" "";
  (match Process.run (Lazy.force other_build) [ "check"; "-C"; root ] with
  | 0, _, _ -> ()
  | status, out, err -> fail "the other build exited with %d: %s%s" status out err);
  if not (is_database_open_elsewhere root) then
    fail "the other build's background process is not running";
  root

let () =
  test "a command takes the project's database from a background process of another build"
    (fun () ->
      let root = make_package_served_by_other_build () in
      let status, output = run_truss [ "check"; "-C"; root ] in
      if status <> 0 then fail "exited with %d: %s" status output);
  test "stop ends the background process of another build" (fun () ->
      let root = make_package_served_by_other_build () in
      let status, output =
        capture (fun () -> Cli.Main.run_client [ "truss"; "stop"; "-C"; root ])
      in
      if status <> 0 then fail "exited with %d: %s" status output;
      if is_database_open_elsewhere root then fail "the background process still runs");
  test "stop leaves the background processes of other projects running, and --all ends them"
    (fun () ->
      let stopped = make_package_served_by_other_build () in
      let other = make_package_served_by_other_build () in
      ignore (capture (fun () -> Cli.Main.run_client [ "truss"; "stop"; "-C"; stopped ]));
      if is_database_open_elsewhere stopped then fail "the project's background process still runs";
      if not (is_database_open_elsewhere other) then fail "stopped another project's process";
      ignore (capture (fun () -> Cli.Main.run_client [ "truss"; "stop"; "--all" ]));
      if is_database_open_elsewhere other then fail "--all left a background process running");
  test "status lists the package databases that the background processes hold" (fun () ->
      let root = make_package_served_by_other_build () in
      let status, out, err = Process.run (Lazy.force other_build) [ "status" ] in
      ignore (capture (fun () -> Cli.Main.run_client [ "truss"; "stop"; "-C"; root ]));
      if status <> 0 || not (String.includes ~affix:"standard " out) then
        fail "exited with %d: %s%s" status out err);
  test "stop outside any project asks for --all, and exits with 2" (fun () ->
      let directory = Harness.make_scratch_directory "no-project" in
      let status, output =
        capture (fun () -> Cli.Main.run_client [ "truss"; "stop"; "-C"; directory ])
      in
      if status <> 2 || not (String.includes ~affix:"use --all" output) then
        fail "exited with %d: %s" status output)

let with_fresh_cache work =
  let cache = Harness.make_scratch_directory "cleaned-cache" in
  Workspace.For_testing.copy_standard_package_database ~into:cache;
  Workspace.reset ();
  Unix.putenv "TRUSS_CACHE" cache;
  Fun.protect ~finally:Workspace.reset (fun () -> work cache)

let () =
  test "the help lists clean and lsp" (fun () ->
      let status, output = capture (fun () -> Cli.Main.run_client [ "truss"; "--help=plain" ]) in
      if
        status <> 0
        || not (List.for_all (fun affix -> String.includes ~affix output) [ "clean"; "lsp" ])
      then fail "exited with %d: %s" status output);
  test "lsp --help shows the command's help" (fun () ->
      let status, output =
        capture (fun () -> Cli.Main.run_client [ "truss"; "lsp"; "--help=plain" ])
      in
      if status <> 0 || not (String.includes ~affix:"Language Server Protocol" output) then
        fail "exited with %d: %s" status output);
  test "clean --help shows the cache directory and deletes nothing" (fun () ->
      with_fresh_cache (fun cache ->
          let status, output =
            capture (fun () -> Cli.Main.run_client [ "truss"; "clean"; "--help=plain" ])
          in
          if status <> 0 || not (String.includes ~affix:"TRUSS_CACHE" output) then
            fail "exited with %d: %s" status output;
          if not (Sys.file_exists cache) then fail "deleted the cache directory"));
  test "clean ends the background processes and deletes the cache directory" (fun () ->
      with_fresh_cache (fun cache ->
          let root = make_package_served_by_other_build () in
          let status, output = capture (fun () -> Cli.Main.run_client [ "truss"; "clean" ]) in
          if status <> 0 then fail "exited with %d: %s" status output;
          if is_database_open_elsewhere root then fail "the background process still runs";
          if Sys.file_exists cache then fail "the cache directory is still there"))

let list_server_files () =
  let directory = Filename.concat (Sys.getenv "TRUSS_CACHE") "servers" in
  List.filter (( <> ) "server.log")
    (Array.to_list (try Sys.readdir directory with Sys_error _ -> [||]))

let list_server_files_added ~before =
  List.sort compare (List.filter (fun name -> not (List.mem name before)) (list_server_files ()))

let wait_until_deadline ~is_done =
  let deadline = Unix.gettimeofday () +. 10. in
  let rec wait () =
    if (not (is_done ())) && Unix.gettimeofday () < deadline then begin
      Unix.sleepf 0.1;
      wait ()
    end
  in
  wait ()

let () =
  test "a background process that stops leaves none of its files in the cache" (fun () ->
      let before = list_server_files () in
      let root = make_package_served_by_other_build () in
      ignore (capture (fun () -> Cli.Main.run_client [ "truss"; "stop"; "-C"; root ]));
      match list_server_files_added ~before with
      | [] -> ()
      | added -> fail "left %s" (String.concat ", " added));
  test "a command outside any project runs without a background process" (fun () ->
      let directory = Harness.make_scratch_directory "outside-a-project" in
      let before = list_server_files () in
      Unix.putenv "TRUSS_NO_SERVER" "";
      let status, out, err = Process.run (Lazy.force other_build) [ "check"; "-C"; directory ] in
      if status <> 2 || not (String.includes ~affix:"so it is in no project" (out ^ err)) then
        fail "exited with %d: %s%s" status out err;
      match list_server_files_added ~before with
      | [] -> ()
      | added -> fail "started a background process: %s" (String.concat ", " added));
  test "help and usage errors inside a project start no background process" (fun () ->
      let root = make_package [ ("main.truss", "fn main() {}\n") ] in
      let before = list_server_files () in
      Unix.putenv "TRUSS_NO_SERVER" "";
      List.iter
        (fun (arguments, expected_status) ->
          let status, out, err = Process.run (Lazy.force other_build) arguments in
          if status <> expected_status then
            fail "`truss %s` exited with %d: %s%s" (String.concat " " arguments) status out err)
        [ ([ "check"; "-C"; root; "--help=plain" ], 0); ([ "chekc"; "-C"; root ], 2) ];
      match list_server_files_added ~before with
      | [] -> ()
      | added -> fail "started a background process: %s" (String.concat ", " added));
  test "--no-server after -- is an argument of the program" (fun () ->
      let root =
        make_package
          [
            ( "main.truss",
              "fn main(arguments: List[String]) -> ExitCode {\n\
              \  if arguments.length() == 2 { ExitCode.success } else { ExitCode.failure }\n\
               }\n" );
          ]
      in
      Unix.putenv "TRUSS_NO_SERVER" "1";
      match Process.run (Lazy.force other_build) [ "run"; "-C"; root; "--"; "--no-server" ] with
      | 0, _, _ -> ()
      | status, out, err -> fail "exited with %d: %s%s" status out err);
  test "a background process whose project is deleted ends, and does not make the project again"
    (fun () ->
      let before = list_server_files () in
      let root = make_package_served_by_other_build () in
      wait_until_deadline ~is_done:(fun () ->
          match File_system.remove root with
          | () -> true
          | exception (Unix.Unix_error _ | Sys_error _) -> false);
      wait_until_deadline ~is_done:(fun () -> list_server_files_added ~before = []);
      (match list_server_files_added ~before with
      | [] -> ()
      | added -> fail "left %s" (String.concat ", " added));
      if Sys.file_exists root then fail "made the project's directory again");
  test "a background process that has answered a command removes the files of an ended one"
    (fun () ->
      let servers = Filename.concat (Sys.getenv "TRUSS_CACHE") "servers" in
      (try Unix.mkdir servers 0o700 with Unix.Unix_error (EEXIST, _, _) -> ());
      let ended = Filename.concat servers "0123456789abcdef-0123456789abcdef" in
      let paths = List.map (fun suffix -> ended ^ suffix) [ ".key"; ".lock"; ".start" ] in
      List.iter (fun path -> Out_channel.with_open_bin path ignore) paths;
      ignore (make_package_served_by_other_build ());
      let is_removed () = not (List.exists Sys.file_exists paths) in
      wait_until_deadline ~is_done:is_removed;
      if not (is_removed ()) then fail "the ended process's files are still there");
  test "a background process does its periodic work while its project keeps changing" (fun () ->
      let servers = Filename.concat (Sys.getenv "TRUSS_CACHE") "servers" in
      (try Unix.mkdir servers 0o700 with Unix.Unix_error (EEXIST, _, _) -> ());
      let ended = Filename.concat servers "fedcba9876543210-fedcba9876543210" in
      let paths = List.map (fun suffix -> ended ^ suffix) [ ".key"; ".lock"; ".start" ] in
      List.iter (fun path -> Out_channel.with_open_bin path ignore) paths;
      let root = make_package_served_by_other_build () in
      let notes = Filename.concat root "notes.txt" in
      let deadline = Unix.gettimeofday () +. 10. in
      let is_removed () = not (List.exists Sys.file_exists paths) in
      let rec change_until_removed count =
        if (not (is_removed ())) && Unix.gettimeofday () < deadline then begin
          Out_channel.with_open_bin notes (fun out -> output_string out (string_of_int count));
          Unix.sleepf 0.1;
          change_until_removed (count + 1)
        end
      in
      change_until_removed 0;
      if not (is_removed ()) then fail "the ended process's files are still there")

let () =
  test "a command refuses a cache that other users can write, and exits with 2" (fun () ->
      let root = make_package [ ("main.truss", "fn main() {}\n") ] in
      let cache = Harness.make_scratch_directory "writable-cache" in
      Unix.chmod cache 0o777;
      Workspace.reset ();
      Unix.putenv "TRUSS_CACHE" cache;
      Fun.protect ~finally:Workspace.reset (fun () ->
          let status, output = run_truss [ "build"; "-C"; root ] in
          if
            status <> 2
            || not
                 (String.includes
                    ~affix:("Users other than its owner can write the cache " ^ cache)
                    output)
          then fail "exited with %d: %s" status output))

let list_names (_, packages) = List.sort compare (List.map Path.show_package packages)
let list_modules (snapshot, packages) = Cli.Command_packages.list_modules snapshot packages
let list_files (snapshot, packages) = Cli.Command_packages.list_files snapshot packages

let gather ?proofs (snapshot, packages) =
  Cli.Report.gather ?proofs (Workspace.open_database snapshot) snapshot packages

let select (snapshot, packages) =
  Cli.Test_command.select snapshot (Workspace.open_database snapshot) packages

let list_mains (snapshot, packages) = Cli.Program_command.list_mains snapshot packages

let () =
  test "the package is found from a directory below its manifest" (fun () ->
      let root = make_package [ ("forecast/hourly.truss", "") ] in
      expect_strings ~expected:[ "demo" ]
        (list_names (Cli.Command_packages.load (Filename.concat root "forecast"))));
  test "a directory with no manifest at or above it cannot run a command" (fun () ->
      let root = make_directory [ ("main.truss", "") ] in
      match Cli.Command_packages.load root with
      | exception Cli.Outcome.Cannot_run _ -> ()
      | _ -> fail "found a package");
  test "a project's root is about every package under it" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("one/truss.toml", make_manifest "one");
            ("libraries/two/truss.toml", make_manifest "two");
          ]
      in
      expect_strings ~expected:[ "one"; "two" ] (list_names (Cli.Command_packages.load root));
      expect_strings ~expected:[ "two" ]
        (list_names (Cli.Command_packages.load (Filename.concat root "libraries"))));
  test "a package under a project's root is in the project, whichever directory a command is in"
    (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("one/truss.toml", make_manifest "one" ^ "[dependencies]\ntwo = []\n");
            ("one/main.truss", Fixtures.Cli.four_through_two_numbers);
            ("two/truss.toml", make_manifest "two");
            ("two/numbers/numbers.truss", Fixtures.Cli.public_two);
          ]
      in
      let project = Cli.Command_packages.load (Filename.concat root "one") in
      expect_strings ~expected:[ "one" ] (list_names project);
      if Cli.Report.has_errors (gather project) then fail "has errors");
  test "a dependency's failed proof is the program's" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("app/truss.toml", make_manifest "app" ^ "[dependencies]\nlib = []\n");
            ("app/main.truss", Fixtures.Cli.two_through_arith);
            ("lib/truss.toml", make_manifest "lib");
            ("lib/arith/arith.truss", Fixtures.Cli.public_bump);
          ]
      in
      let status, output = run_truss [ "check"; "-C"; Filename.concat root "app" ] in
      if status <> 1 || not (String.includes ~affix:"lib/arith/arith.truss" output) then
        fail "the dependency's overflow is not reported: %s" output);
  test "a dependency's type error is reported without proofs" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("app/truss.toml", make_manifest "app" ^ "[dependencies]\nlib = []\n");
            ("app/main.truss", Fixtures.Cli.main_through_arith);
            ("lib/truss.toml", make_manifest "lib");
            ("lib/arith/arith.truss", Fixtures.Cli.public_two_of_a_boolean);
          ]
      in
      let status, output = run_truss [ "run"; "-C"; Filename.concat root "app" ] in
      if status <> 1 || not (String.includes ~affix:"lib/arith/arith.truss" output) then
        fail "%s" output);
  test "a package with no [project] above it is a project by itself" (fun () ->
      let root =
        make_directory
          [
            ("one/truss.toml", make_manifest "one" ^ "[dependencies]\ntwo = []\n");
            ("one/main.truss", "");
            ("two/truss.toml", make_manifest "two");
          ]
      in
      let project = Cli.Command_packages.load (Filename.concat root "one") in
      let problems = Workspace.problems (fst project) in
      if
        not
          (List.exists
             (fun (problem : Project.problem) ->
               String.includes ~affix:"`two` is not a package of this project" problem.message)
             problems)
      then fail "problems: %s" (String.concat "; " (List.map Project.show_problem problems));
      match Cli.Command_packages.load root with
      | exception Cli.Outcome.Cannot_run _ -> ()
      | _ -> fail "found a project above the two");
  test "a directory with its own manifest is another package's, not modules of this one" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n" ^ make_manifest "demo");
            ("main.truss", "");
            ("vendor/truss.toml", make_manifest "other");
            ("vendor/x.truss", "");
          ]
      in
      let project = Cli.Command_packages.load root in
      expect_strings ~expected:[ "demo"; "other" ]
        (List.sort compare (List.map Path.show_module (list_modules project))));
  test "a directory with its own [project] is another project's, and so is all under it" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n" ^ make_manifest "demo");
            ("main.truss", "");
            ("examples/truss.toml", "[project]\n");
            ("examples/hello/truss.toml", make_manifest "hello");
            ("examples/hello/main.truss", "");
          ]
      in
      expect_strings ~expected:[ "demo" ]
        (List.map Path.show_module (list_modules (Cli.Command_packages.load root)));
      expect_strings ~expected:[ "hello" ]
        (list_names (Cli.Command_packages.load (Filename.concat root "examples"))));
  test "a project manifest with a mistake is still the root of the packages under it" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n\n[test]\ntime_limit = \"ten\"\n");
            ("app/truss.toml", make_manifest "app");
            ("app/main.truss", "");
          ]
      in
      let project = Cli.Command_packages.load (Filename.concat root "app") in
      expect_strings ~expected:[ "app" ] (list_names project);
      let problems = Workspace.problems (fst project) in
      if
        not
          (List.exists
             (fun (problem : Project.problem) ->
               problem.file = "truss.toml" && problem.line = Some 4)
             problems)
      then fail "problems: %s" (String.concat "; " (List.map Project.show_problem problems)));
  test "under a package that is a project by itself, a directory with a manifest is no part of it"
    (fun () ->
      let root =
        make_package
          [
            ("main.truss", ""); ("vendor/truss.toml", make_manifest "other"); ("vendor/x.truss", "");
          ]
      in
      expect_strings ~expected:[ "demo" ]
        (List.map Path.show_module (list_modules (Cli.Command_packages.load root)));
      expect_strings ~expected:[ "other" ]
        (list_names (Cli.Command_packages.load (Filename.concat root "vendor"))));
  test "a directory whose name starts with a dot is not read" (fun () ->
      let root = make_package [ ("main.truss", ""); (".hidden/x.truss", "") ] in
      expect_strings ~expected:[ "demo" ]
        (List.map Path.show_module (list_modules (Cli.Command_packages.load root))));
  test "a path is shown relative to the directory it is read from" (fun () ->
      expect_string ~expected:"../weather/forecast.truss"
        (Cli.Shown_path.make_relative ~from:"/code/app" "/code/weather/forecast.truss"))

let list_problems files =
  let project = Cli.Command_packages.load (make_directory files) in
  Workspace.problems (fst project)

let report_problems report =
  match Cli.Json.lookup_field "problems" (Cli.Report.make_document report []) with
  | Cli.Json.List problems ->
      List.filter_map (function Cli.Json.String problem -> Some problem | _ -> None) problems
  | _ -> []

let expect_problem ?file files message =
  let problems_reported = list_problems files in
  let is_expected (problem : Project.problem) =
    String.includes ~affix:message problem.message
    && match file with Some file -> problem.file = file | None -> true
  in
  if not (List.exists is_expected problems_reported) then
    fail "problems: [%s]" (String.concat "; " (List.map Project.show_problem problems_reported))

let expect_problem_in root part =
  let problems_reported = report_problems (gather (Cli.Command_packages.load root)) in
  if not (List.exists (fun problem -> String.includes ~affix:part problem) problems_reported) then
    fail "problems: [%s]" (String.concat "; " problems_reported)

let () =
  test "a package that does not say which Truss it is written for has a problem" (fun () ->
      expect_problem ~file:"truss.toml"
        [ ("truss.toml", "[package]\nname = \"demo\"\n") ]
        "`[package]` needs `truss = \"0.1\"`");
  test "a package written for a newer Truss than the toolchain's has a problem" (fun () ->
      expect_problem
        [ ("truss.toml", "[package]\nname = \"demo\"\ntruss = \"99.0\"\n") ]
        "`demo` is written for Truss 99.0, and this toolchain is Truss 0.1");
  test "a package cannot depend on itself" (fun () ->
      expect_problem
        [ ("truss.toml", make_manifest "demo" ^ "[dependencies]\ndemo = []\n") ]
        "`demo` cannot depend on itself");
  test "packages cannot depend on each other in a cycle" (fun () ->
      expect_problem_in
        (make_directory
           [
             ("truss.toml", "[project]\n");
             ("one/truss.toml", make_manifest "one" ^ "[dependencies]\ntwo = []\n");
             ("two/truss.toml", make_manifest "two" ^ "[dependencies]\nthree = []\n");
             ("three/truss.toml", make_manifest "three" ^ "[dependencies]\none = []\n");
           ])
        "one/truss.toml: Packages cannot depend on each other in a cycle: `one` -> `two` -> \
         `three` -> `one`");
  test "a package's name cannot be the owner in another's" (fun () ->
      expect_problem
        [
          ("truss.toml", "[project]\n");
          ("acme/truss.toml", make_manifest "acme");
          ("geometry/truss.toml", make_manifest "acme::geometry");
        ]
        "The package name `acme` is the owner in `acme::geometry`");
  test "two packages of a project cannot have one name" (fun () ->
      expect_problem ~file:"two/truss.toml"
        [
          ("truss.toml", "[project]\n");
          ("one/truss.toml", make_manifest "same");
          ("two/truss.toml", make_manifest "same");
        ]
        "The package name `same` is already used by one/truss.toml")

let () =
  test "a dependency nothing uses is a problem, which check --fix fixes by deleting its entry"
    (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ( "app/truss.toml",
              make_manifest "app" ^ "[dependencies]\nlibrary = []\nother = [\n  \"Clock\",\n]\n" );
            ("app/main.truss", Fixtures.Cli.one_through_numbers);
            ("library/truss.toml", make_manifest "library");
            ("library/numbers/numbers.truss", Fixtures.Cli.public_one);
            ("other/truss.toml", make_manifest "other");
            ("other/nothing/nothing.truss", Fixtures.Cli.public_nothing);
          ]
      in
      let app = Filename.concat root "app" in
      let problems = report_problems (gather (Cli.Command_packages.load app)) in
      if
        not
          (List.exists
             (fun problem ->
               String.includes ~affix:"app/truss.toml: Nothing in `app` uses `other`" problem)
             problems)
      then fail "problems: [%s]" (String.concat "; " problems);
      if run_quietly [ "check"; "-C"; app; "--fix" ] <> 0 then fail "still has errors";
      let manifest = read root "app/truss.toml" in
      if
        String.includes ~affix:"other" manifest
        || String.includes ~affix:"Clock" manifest
        || not (String.includes ~affix:"library = []" manifest)
      then fail "wrote %s" manifest)

let owned =
  [
    ("truss.toml", "[project]\n");
    ("geometry/truss.toml", make_manifest "acme::geometry");
    ("geometry/vector/vector.truss", Fixtures.Cli.vector_with_length_and_double);
    ("app/truss.toml", make_manifest "app" ^ "[dependencies]\n\"acme::geometry\" = []\n");
    ("app/main.truss", Fixtures.Cli.four_through_vector_double);
  ]

let () =
  test "a project's package with an owner in its name is named by both in a path" (fun () ->
      let root = make_directory owned in
      let project = Cli.Command_packages.load root in
      expect_strings ~expected:[ "acme::geometry"; "app" ] (list_names project);
      if Cli.Report.has_errors (gather ~proofs:true project) then fail "has errors");
  test "show finds a definition of a package with an owner by its full path" (fun () ->
      match run_show (make_directory owned) "acme::geometry::vector::double" with
      | [ text ] ->
          if not (String.includes ~affix:"public fn double(value: Int64) -> Int64" text) then
            fail "showed %s" text
      | texts -> fail "found %d" (List.length texts));
  test "show lists the public definitions of a package with an owner" (fun () ->
      if List.length (run_show (make_directory owned) "acme::geometry") < 3 then
        fail "found too few")

let () =
  test "the project's [test] time_limit gives each test's limit in seconds" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n[test]\ntime_limit = 3\n");
            ("one/truss.toml", make_manifest "one");
          ]
      in
      let project = Cli.Command_packages.load (Filename.concat root "one") in
      let limit = Workspace.time_limit_ms (fst project) in
      if limit <> 3000 then fail "got %d ms" limit);
  test "a project without a time limit gives tests 10 seconds" (fun () ->
      let limit = Workspace.time_limit_ms (fst (Cli.Command_packages.load (make_package []))) in
      if limit <> 10_000 then fail "got %d ms" limit);
  test "a time limit in a package's manifest that is not its project's is a problem" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("one/truss.toml", make_manifest "one" ^ "[test]\ntime_limit = 3\n");
          ]
      in
      let project = Cli.Command_packages.load root in
      let problems = Workspace.problems (fst project) in
      if
        not
          (List.exists
             (fun (problem : Project.problem) ->
               problem.file = "one/truss.toml"
               && String.includes ~affix:"A test's time limit is its project's" problem.message)
             problems)
      then fail "problems: %s" (String.concat "; " (List.map Project.show_problem problems)));
  test "a time limit of 0 is malformed, at its line" (fun () ->
      match Manifest.parse "[package]\nname = \"a\"\n[test]\ntime_limit = 0\n" with
      | exception Manifest.Malformed { line = 4; _ } -> ()
      | _ -> fail "accepted")

let edit start stop replacement = Diagnostic.replace (Source.make_span start stop) replacement

let make_diagnostic ~fixes start stop =
  Diagnostic.make ~fixes ~code:(Usage Unused_variable) (Source.make_span start stop) "x."

let () =
  test "edits apply at the offsets of the text they were made for" (fun () ->
      expect_string ~expected:"A bb C"
        (Diagnostic.apply_edits "a bb c" [ edit 0 1 "A"; edit 5 6 "C" ]));
  test "a fix that overlaps an earlier one waits for the next round" (fun () ->
      let first = make_diagnostic ~fixes:[ Diagnostic.fix "one" [ edit 0 3 "x" ] ] 0 3 in
      let second = make_diagnostic ~fixes:[ Diagnostic.fix "two" [ edit 2 4 "y" ] ] 2 4 in
      if Diagnostic.list_machine_applicable [ first; second ] <> [ first ] then fail "chose both");
  test "a diagnostic with several fixes is left for the person or agent to choose" (fun () ->
      let choice =
        make_diagnostic
          ~fixes:[ Diagnostic.fix "one" [ edit 0 1 "x" ]; Diagnostic.fix "two" [ edit 0 1 "y" ] ]
          0 1
      in
      if Diagnostic.list_machine_applicable [ choice ] <> [] then fail "chose one");
  test "check --fix writes the only fix and leaves no diagnostic" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.twice_with_one_fix) ] in
      let status = run_quietly [ "check"; "-C"; root; "--fix" ] in
      if status <> 0 then fail "status %d" status;
      if not (String.includes ~affix:"let _ = value" (read root "main.truss")) then
        fail "wrote %s" (read root "main.truss"))

let () =
  test "check proves, and reports each unproven obligation" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.next_count) ] in
      let status, output = run_truss [ "check"; "-C"; root ] in
      if status <> 1 then fail "status %d" status;
      if not (String.includes ~affix:"prover.overflow" output) then fail "%s" output);
  test "check --no-proofs reports no obligation" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.next_count) ] in
      let status, output = run_truss [ "check"; "-C"; root; "--no-proofs" ] in
      if status <> 0 then fail "status %d: %s" status output);
  test "check prints type errors before it proves" (fun () ->
      let root =
        make_package
          [ ("a.truss", Fixtures.Cli.next_count); ("b.truss", Fixtures.Cli.wrong_boolean_return) ]
      in
      let status, output = run_truss [ "check"; "-C"; root ] in
      if status <> 1 then fail "status %d" status;
      match
        (String.find_first ~sub:"b.truss" output, String.find_first ~sub:"prover.overflow" output)
      with
      | Some type_error, Some overflow when type_error < overflow -> ()
      | _ -> fail "%s" output);
  test "build refuses a program that can reach a hole in a proof" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.main_with_a_todo_proof) ] in
      let status, output = run_truss [ "build"; "-C"; root ] in
      if status <> 1 then fail "did not refuse";
      if not (String.includes ~affix:"main.truss:3:5: `todo` in a proof can be reached" output) then
        fail "%s" output)

let () =
  test "a report's records come back in the order of the tests, however they ended" (fun () ->
      let records =
        Backend.Test_report.For_testing.parse ~tests:2
          "start 0\nstart 1\nmessage 4\nboom\ntest 1 panicked 30\ntest 0 passed 12\n"
      in
      match records with
      | Ok
          [
            { outcome = Passed; microseconds = 12; _ };
            { outcome = Panicked; message = Some "boom"; _ };
          ] ->
          ()
      | Ok records -> fail "read %d records differently" (List.length records)
      | Error message -> fail "%s" message);
  test "a duration is shown in the largest unit under its size" (fun () ->
      expect_strings ~expected:[ "2.31s"; "42ms"; "87µs" ]
        (List.map Cli.Test_command.For_testing.show_duration [ 2_310_000; 42_000; 87 ]));
  test "the status line is cut by characters, never inside one" (fun () ->
      expect_string ~expected:"café" (Cli.Status_line.For_testing.cut "café au lait" 4))

let suite = Fixtures.Cli.suite

let () =
  test "--match keeps the tests whose names contain the text" (fun () ->
      let project = Cli.Command_packages.load (make_package [ ("main.truss", suite) ]) in
      expect_strings
        ~expected:[ "doubles two"; "doubles three" ]
        (List.map
           (fun (test : Cli.Test_command.test) -> test.name)
           (select project ~paths:[] ~match_:(Some "doubles"))));
  test "a file narrows the tests to those defined in it" (fun () ->
      let root =
        make_package [ ("main.truss", suite); ("other.truss", "test \"elsewhere\" {\n}\n") ]
      in
      let project = Cli.Command_packages.load root in
      expect_strings ~expected:[ "elsewhere" ]
        (List.map
           (fun (test : Cli.Test_command.test) -> test.name)
           (select project ~paths:[ Filename.concat root "other.truss" ] ~match_:None)))

let () =
  test "a function's signature is its text without its body" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.public_double_with_a_requires) ] in
      match run_show root "demo::double" with
      | [ text ] ->
          expect_string ~expected:"public fn double(value: Int64) -> Int64\n  requires value < 100"
            text
      | texts -> fail "found %d" (List.length texts));
  test "a type is shown with its methods" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.point_with_a_sum_method) ] in
      expect_strings
        ~expected:[ "public type Point(x: Int64, y: Int64)"; "public fn Point.sum(self) -> Int64" ]
        (run_show root "demo::Point"));
  test "a standard library type is shown with its file" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.point_with_a_sum_method) ] in
      match list_shown root "standard::option::Option" with
      | option :: _ ->
          expect_string ~expected:"standard/option/option.truss" (read_string_field "file" option);
          expect_string ~expected:"public type Option[Value] ="
            (read_header (read_string_field "text" option))
      | [] -> fail "found nothing")

let make_two_points () =
  make_package
    [
      ("main.truss", Fixtures.Cli.impl_for_geometry_point);
      ("geometry/geometry.truss", Fixtures.Cli.geometry_point);
      ("drawing/drawing.truss", Fixtures.Cli.drawing_point);
    ]

let list_headers texts = List.map read_header texts

let () =
  test "a type is shown with an impl that names it by its module's path" (fun () ->
      expect_strings
        ~expected:
          [ "public type Point(x: Int64, y: Int64)"; "impl Display for demo::geometry::Point {" ]
        (list_headers (run_show (make_two_points ()) "demo::geometry::Point")));
  test "a type is shown without the impls of another module's type of the same name" (fun () ->
      let root = make_two_points () in
      let geometry = list_headers (run_show root "demo::geometry::Point")
      and drawing = list_headers (run_show root "demo::drawing::Point") in
      if not (List.mem "impl Display for Point {" drawing) then
        fail "the drawing's Point showed %s" (String.concat "; " drawing);
      if List.mem "impl Display for Point {" geometry then
        fail "the geometry's Point showed %s" (String.concat "; " geometry))

let expect_headers ~expected texts =
  let headers = list_headers texts in
  List.iter
    (fun header ->
      if not (List.mem header headers) then
        fail "%s is missing from %s" header (String.concat "; " headers))
    expected

let () =
  test "a built-in type is shown by its name with its methods and its impls" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.point_with_a_sum_method) ] in
      expect_headers
        ~expected:
          [
            "public fn Float64.to_float32(self) -> Float32";
            "impl FloatingPoint for Float64 {";
            "impl Serialize for Float64 {";
          ]
        (run_show root "Float64"));
  test "a dependency's type is shown with its impls of public traits only" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("geometry/truss.toml", make_manifest "acme::geometry");
            ("geometry/vector/vector.truss", Fixtures.Cli.vector_with_a_public_and_a_private_impl);
            ("app/truss.toml", make_manifest "app" ^ "[dependencies]\n\"acme::geometry\" = []\n");
            ("app/main.truss", "fn main() {}\n");
          ]
      in
      expect_strings
        ~expected:[ "public type Vector(x: Int64, y: Int64)"; "impl Display for Vector {" ]
        (list_headers (run_show (Filename.concat root "app") "acme::geometry::vector::Vector")));
  test "a dependency's module is shown with its law proofs and without its tests" (fun () ->
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("geometry/truss.toml", make_manifest "acme::geometry");
            ("geometry/pairs/pairs.truss", Fixtures.Cli.pair_with_a_law_proof_and_a_test);
            ("app/truss.toml", make_manifest "app" ^ "[dependencies]\n\"acme::geometry\" = []\n");
            ("app/main.truss", "fn main() {}\n");
          ]
      in
      let headers = list_headers (run_show (Filename.concat root "app") "acme::geometry::pairs") in
      if not (List.mem "proof Ordered.agrees_with_equal for Pair" headers) then
        fail "the law proof is missing from %s" (String.concat "; " headers);
      if List.exists (String.starts_with ~prefix:"test ") headers then
        fail "a test is shown in %s" (String.concat "; " headers));
  test "a built-in type is shown with an impl that the project writes for it" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.doubled_for_int64) ] in
      expect_headers ~expected:[ "impl Doubled for Int64 {" ] (run_show root "Int64"));
  test "a prelude type and a prelude trait are shown by their names" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.point_with_a_sum_method) ] in
      expect_headers ~expected:[ "public type Option[Value] =" ] (run_show root "Option");
      expect_headers
        ~expected:[ "public trait FixedWidthInteger:" ]
        (run_show root "FixedWidthInteger"));
  test "a method written in an impl is shown through the implementing type" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.square_area) ] in
      expect_strings ~expected:[ "fn area(self) -> Int64" ] (run_show root "demo::Square.area"));
  test "a module is shown without repeating the methods written in its traits and impls" (fun () ->
      let root =
        make_package
          [
            ("main.truss", Fixtures.Cli.point_with_a_sum_method);
            ("shapes/shapes.truss", Fixtures.Cli.square_area);
          ]
      in
      expect_strings
        ~expected:[ "trait Shape {"; "type Square(side: Int64)"; "impl Shape for Square {" ]
        (list_headers (run_show root "demo::shapes")));
  test "a built-in type that no definition names is shown as having nothing to show" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.point_with_a_sum_method) ] in
      let status, output = run_truss [ "show"; "-C"; root; "Never" ] in
      if
        status <> 0
        || not
             (String.includes ~affix:"`Never` is visible here but has no definition to show." output)
      then fail "status %d: %s" status output)

let make_lowered_lookups (snapshot, packages) =
  Cli.Workspace_backend.require_lowered_lookups (Workspace.open_database snapshot) packages

let make_speaker_calling called =
  make_package
    [
      ( "main.truss",
        Printf.sprintf
          "capability Speaker {\n\
          \  fn say(text: StringSlice)\n\
          \  fn shout(text: StringSlice)\n\
           }\n\n\
           type Quiet()\n\n\
           impl Speaker for Quiet {\n\
          \  fn say(self, text: StringSlice) {}\n\n\
          \  fn shout(self, text: StringSlice) {\n\
          \    todo\n\
          \  }\n\
           }\n\n\
           fn speak()\n\
          \  uses Speaker\n\
           {\n\
          \  Speaker.%s(\"hello\")\n\
           }\n\n\
           fn main(arguments: List[String]) -> ExitCode {\n\
          \  provide Quiet() {\n\
          \    speak()\n\
          \  }\n\
          \  ExitCode.success\n\
           }\n\n\
           test \"speaks\" {\n\
          \  provide Quiet() {\n\
          \    speak()\n\
          \  }\n\
           }\n"
          called );
    ]

let () =
  test "a todo main can reach is refused, with the way from main to it" (fun () ->
      let project =
        Cli.Command_packages.load
          (make_package [ ("main.truss", Fixtures.Cli.main_reaching_a_todo_through_a_helper) ])
      in
      match
        Backend.list_unshippable (make_lowered_lookups project) ~main:(List.hd (list_mains project))
      with
      | [ { failure = `Todo; location = { line = 6; _ }; way } ] ->
          expect_strings ~expected:[ "demo::main"; "demo::helper" ] (List.map Path.show way)
      | reached -> fail "found %d" (List.length reached));
  test "a todo in a capability's method counts only where the method is called" (fun () ->
      let list_reached_from called =
        let project = Cli.Command_packages.load (make_speaker_calling called) in
        Backend.list_unshippable (make_lowered_lookups project) ~main:(List.hd (list_mains project))
      in
      (match list_reached_from "say" with
      | [] -> ()
      | _ -> fail "a method nothing calls stops the program");
      match list_reached_from "shout" with
      | [ { failure = `Todo; location = { line = 12; _ }; way } ] -> (
          match List.map Path.show way with
          | "demo::main" :: "demo::speak" :: _ -> ()
          | way -> fail "reached by %s" (String.concat ", " way))
      | unshippable -> fail "found %d" (List.length unshippable));
  test "a package's program is the main of its root module, and of no other" (fun () ->
      let main_text = Fixtures.Cli.main_returning_success in
      let with_main = Cli.Command_packages.load (make_package [ ("main.truss", main_text) ]) in
      expect_strings ~expected:[ "demo::main" ] (List.map Path.show (list_mains with_main));
      let elsewhere =
        Cli.Command_packages.load (make_package [ ("start/start.truss", main_text) ])
      in
      if list_mains elsewhere <> [] then fail "took a main from another module");
  test "a function named main outside the root module is an ordinary function" (fun () ->
      let project =
        Cli.Command_packages.load
          (make_package [ ("menu/menu.truss", Fixtures.Cli.menu_main_of_a_course) ])
      in
      if Cli.Report.has_errors (gather project) then fail "has errors");
  test "an echo main can reach is refused" (fun () ->
      let project =
        Cli.Command_packages.load (make_package [ ("main.truss", Fixtures.Cli.main_with_an_echo) ])
      in
      match
        Backend.list_unshippable (make_lowered_lookups project) ~main:(List.hd (list_mains project))
      with
      | [ { failure = `Echo; location = { line = 2; _ }; _ } ] -> ()
      | reached -> fail "found %d" (List.length reached))

let two_files =
  [
    ("weather/weather.truss", Fixtures.Cli.two_files_weather); ("main.truss", Fixtures.Cli.two_files);
  ]

let rename root from_ to_ = run_quietly [ "rename"; "-C"; root; from_; to_ ]

let () =
  test "renaming a function rewrites every reference in the package" (fun () ->
      let root = make_package two_files in
      if rename root "demo::weather::total" "sum" <> 0 then fail "refused";
      if
        not
          (String.includes ~affix:"weather::sum([1]) + demo::weather::sum([2])"
             (read root "main.truss")
          && String.includes ~affix:"public fn sum(" (read root "weather/weather.truss"))
      then fail "wrote %s" (read root "main.truss"));
  test "a rename that would cause a diagnostic changes nothing" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.first_and_second) ] in
      let before = read root "main.truss" in
      if rename root "demo::first" "second" <> 1 then fail "not refused";
      expect_string ~expected:before (read root "main.truss"));
  test "renaming a module moves its files and rewrites its uses and full paths" (fun () ->
      let root = make_package two_files in
      if rename root "demo::weather" "demo::outlook" <> 0 then fail "refused";
      if Sys.file_exists (Filename.concat root "weather/weather.truss") then
        fail "kept the old file";
      let main = read root "main.truss" in
      if
        not
          (String.includes ~affix:"use demo::outlook" main
          && String.includes ~affix:"outlook::total([1]) + demo::outlook::total([2])" main)
      then fail "wrote %s" main);
  test "renaming in a package with an owner rewrites a full path into it" (fun () ->
      let root = make_directory owned in
      if rename root "acme::geometry::vector::double" "twice" <> 0 then fail "refused";
      let main = read root "app/main.truss" in
      if
        not
          (String.includes ~affix:"let _ = vector::twice(1)" main
          && String.includes ~affix:"  acme::geometry::vector::twice(2)" main)
      then fail "wrote %s" main);
  test "renaming a module of a package with an owner rewrites its uses and full paths" (fun () ->
      let root = make_directory owned in
      if rename root "acme::geometry::vector" "acme::geometry::arrow" <> 0 then fail "refused";
      if not (Sys.file_exists (Filename.concat root "geometry/arrow/vector.truss")) then
        fail "did not move the file";
      let main = read root "app/main.truss" in
      if
        not
          (String.includes ~affix:"use acme::geometry::arrow" main
          && String.includes ~affix:"let _ = arrow::double(1)" main
          && String.includes ~affix:"  acme::geometry::arrow::double(2)" main)
      then fail "wrote %s" main);
  test "renaming a method rewrites its calls" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.point_get_and_its_calls) ] in
      if rename root "demo::Point.get" "value" <> 0 then fail "refused";
      let text = read root "main.truss" in
      if
        not
          (String.includes ~affix:"fn Point.value(self)" text
          && String.includes ~affix:"Point(x: 1).value()" text)
      then fail "wrote %s" text);
  test "renaming a member constant rewrites its uses" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.point_origin_and_its_use) ] in
      if rename root "demo::Point.origin" "center" <> 0 then fail "refused";
      let text = read root "main.truss" in
      if
        not
          (String.includes ~affix:"let Point.center: Point" text
          && String.includes ~affix:"Point.center.x" text)
      then fail "wrote %s" text);
  test "a method is renamed by a suffix of its path" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.point_get_and_its_calls) ] in
      if rename root "Point.get" "value" <> 0 then fail "refused";
      let text = read root "main.truss" in
      if not (String.includes ~affix:"Point(x: 1).value()" text) then fail "wrote %s" text);
  test "a new name with a full path is checked against the renamed definition's module" (fun () ->
      let root = make_package two_files in
      if rename root "total" "demo::weather::sum" <> 0 then fail "refused";
      if not (String.includes ~affix:"public fn sum(" (read root "weather/weather.truss")) then
        fail "wrote %s" (read root "weather/weather.truss"));
  test "a suffix that names two definitions renames neither" (fun () ->
      let root = make_two_points () in
      let status, output = run_truss [ "rename"; "-C"; root; "Point"; "Spot" ] in
      if status <> 2 || not (String.includes ~affix:"`Point` names 2 definitions" output) then
        fail "status %d: %s" status output)

let rewrite root path text =
  Out_channel.with_open_bin (Filename.concat root path) (fun out -> output_string out text);
  let now = Unix.gettimeofday () in
  Unix.utimes (Filename.concat root path) now (now +. 10.)

let () =
  test "a position's line and column count characters, as diagnostics do" (fun () ->
      let source = Source.create ~path:"" "ab\ncé x" in
      if Source.compute_offset Source.Scalar_values source ~line:1 ~column:3 <> 7 then
        fail "wrong offset");
  test "explaining a name gives its meaning and the signature it refers to" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.doubling) ] in
      let status, output =
        run_truss [ "explain"; "-C"; root; Filename.concat root "main.truss" ^ ":8:3" ]
      in
      if status <> 0 then fail "status %d" status;
      if
        not
          (String.includes ~affix:"means the definition demo::double" output
          && String.includes ~affix:"internal fn double(value: Int64) -> Int64" output)
      then fail "wrote %s" output);
  let explain root position =
    let status, output =
      run_truss [ "explain"; "-C"; root; Filename.concat root "main.truss" ^ ":" ^ position ]
    in
    if status <> 0 then fail "status %d" status;
    output
  in
  test "explaining a definition's declared name gives the definition" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.counter) ] in
      let output = explain root "3:13" in
      if
        not
          (String.includes ~affix:"means the definition demo::Counter.bump(mut self)" output
          && String.includes ~affix:"fn Counter.bump(mut self)" output)
      then fail "wrote %s" output);
  test "explaining a method call's callee gives the method" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.counter) ] in
      let output = explain root "9:16" in
      if not (String.includes ~affix:"means the definition demo::Counter.bump(mut self)" output)
      then fail "wrote %s" output);
  test "explaining a variable where it is bound gives its type" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.counter) ] in
      let output = explain root "8:8" in
      if
        not
          (String.includes ~affix:"means a name bound here" output
          && String.includes ~affix:"has type Counter" output)
      then fail "wrote %s" output)

let list_strings = function
  | Cli.Json.List items ->
      List.filter_map (function Cli.Json.String text -> Some text | _ -> None) items
  | _ -> []

let list_reads command root name =
  list_objects (Cli.Json.lookup_field "reads" (run_json [ command; "-C"; root; name ]))

let expect_read lines ~reader ~parts ~reads ~of_ =
  if
    not
      (List.exists
         (fun line ->
           read_string_field "reader" line = reader
           && read_string_field "of" line = of_
           && List.mem reads (list_strings (Cli.Json.lookup_field "reads" line))
           && List.for_all
                (fun part -> List.mem part (list_strings (Cli.Json.lookup_field "parts" line)))
                parts)
         lines)
  then
    fail "no line says that the %s of %s reads the %s of %s: [%s]" (String.concat ", " parts) reader
      reads of_
      (String.concat "; " (List.map Cli.Json.to_string lines))

let () =
  test "dependents say which definitions read a definition's interface, and which its contract"
    (fun () ->
      let lines =
        list_reads "dependents" (make_package [ ("main.truss", Fixtures.Cli.doubling) ]) "double"
      in
      expect_read lines ~reader:"demo::four" ~parts:[ "checked body" ] ~reads:"interface"
        ~of_:"demo::double";
      expect_read lines ~reader:"demo::four" ~parts:[ "proof" ] ~reads:"MIR of the contract"
        ~of_:"demo::double");
  test "dependencies list the parts of other definitions that a definition reads" (fun () ->
      let lines =
        list_reads "dependencies" (make_package [ ("main.truss", Fixtures.Cli.doubling) ]) "four"
      in
      expect_read lines ~reader:"demo::four" ~parts:[ "checked body" ] ~reads:"interface"
        ~of_:"demo::double";
      if List.exists (fun line -> read_string_field "of" line = "demo::four") lines then
        fail "four is listed as its own dependency");
  test "a mut self method's dependents are found by its name without the receiver" (fun () ->
      expect_read
        (list_reads "dependents"
           (make_package [ ("main.truss", Fixtures.Cli.counter) ])
           "Counter.bump")
        ~reader:"demo::bumped" ~parts:[ "checked body" ] ~reads:"interface"
        ~of_:"demo::Counter.bump(mut self)");
  test "a definition is found by its full path and by every suffix of its path" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.doubling) ] in
      List.iter
        (fun name ->
          expect_read
            (list_reads "dependents" root name)
            ~reader:"demo::four" ~parts:[ "checked body" ] ~reads:"interface" ~of_:"demo::double")
        [ "demo::double"; "double" ]);
  test "a suffix that ends inside a name finds nothing" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.doubling) ] in
      let status, output = run_truss [ "dependents"; "-C"; root; "ouble" ] in
      if status <> 2 || not (String.includes ~affix:"No definition named ouble" output) then
        fail "status %d: %s" status output);
  test "a built-in type has no definition whose dependents could be listed" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.doubling) ] in
      let status, output = run_truss [ "dependents"; "-C"; root; "Int64" ] in
      if status <> 2 || not (String.includes ~affix:"No definition named Int64" output) then
        fail "status %d: %s" status output);
  test "a name that is not a path is refused" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.doubling) ] in
      let status, output = run_truss [ "dependents"; "-C"; root; "demo:double" ] in
      if status <> 2 || not (String.includes ~affix:"`demo:double` is not a path" output) then
        fail "status %d: %s" status output);
  test "a method of an impl is found through the implementing type" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.square_area) ] in
      List.iter
        (fun name ->
          let status, output = run_truss [ "dependencies"; "-C"; root; name ] in
          if status <> 0 then fail "%s: status %d: %s" name status output)
        [ "Square.area"; "demo::Square.area"; "Shape.area" ])

let find_counts output kind =
  let prefix = kind ^ "  " in
  List.find_map
    (fun line ->
      if String.starts_with ~prefix line then
        Some
          (List.filter (( <> ) "")
             (String.split_on_char ' '
                (String.sub line (String.length prefix) (String.length line - String.length prefix))))
      else None)
    (String.split_on_char '\n' output)

let () =
  test "TRUSS_DATABASE_COUNTS=1 writes the database's work during the command, by kind of part"
    (fun () ->
      ignore (Workspace.For_testing.load_standard_package_database ());
      let root = make_package [ ("main.truss", Fixtures.Cli.doubling) ] in
      Unix.putenv "TRUSS_DATABASE_COUNTS" "1";
      let _, output = run_truss [ "check"; "--no-proofs"; "-C"; root ] in
      if find_counts output "parsed file" <> Some [ "1"; "0"; "1"; "1"; "1" ] then
        fail "no row counts one parsed file, computed, written, and read once: %s" output);
  test "a second release build of an unchanged package computes no body, proof, or code" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.main_with_a_todo_proof) ] in
      Unix.putenv "TRUSS_DATABASE_COUNTS" "";
      ignore (run_truss [ "build"; "-C"; root ]);
      Unix.putenv "TRUSS_DATABASE_COUNTS" "1";
      let _, output = run_truss [ "build"; "-C"; root ] in
      Unix.putenv "TRUSS_DATABASE_COUNTS" "";
      List.iter
        (fun kind ->
          match find_counts output kind with
          | None | Some ("0" :: _) -> ()
          | Some _ -> fail "the second build computed parts of kind %s: %s" kind output)
        [ "parsed file"; "checked body"; "proof"; "lowered code"; "test key" ])

let list_holes root =
  list_objects (Cli.Json.lookup_field "holes" (run_json [ "holes"; "-C"; root ]))

let () =
  test "a hole has the type it must have and the names in scope with theirs" (fun () ->
      match list_holes (make_package [ ("main.truss", Fixtures.Cli.unfinished) ]) with
      | [ hole ] ->
          if read_string_field "type" hole <> "String" then fail "the type is not String";
          expect_strings
            ~expected:[ "count: Int64"; "header: String"; "title: String" ]
            (List.map
               (fun binding ->
                 read_string_field "name" binding ^ ": " ^ read_string_field "type" binding)
               (list_objects (Cli.Json.lookup_field "in_scope" hole)))
      | found -> fail "found %d holes" (List.length found));
  test "a hole blocks the tests that can reach it, and only those" (fun () ->
      match list_holes (make_package [ ("main.truss", Fixtures.Cli.unfinished) ]) with
      | [ hole ] ->
          expect_strings ~expected:[ "test demo \"renders\"" ]
            (list_strings (Cli.Json.lookup_field "blocks" hole))
      | found -> fail "found %d holes" (List.length found));
  test "a hole in a capability's method blocks the tests and main that call the method" (fun () ->
      let list_blocks called =
        match list_holes (make_speaker_calling called) with
        | [ hole ] -> list_strings (Cli.Json.lookup_field "blocks" hole)
        | found -> failwith (Printf.sprintf "found %d holes" (List.length found))
      in
      expect_strings ~expected:[] (list_blocks "say");
      expect_strings ~expected:[ "main"; "test demo \"speaks\"" ] (list_blocks "shout"));
  test "a hole blocks a test that also reaches a type defined as todo" (fun () ->
      match
        list_holes
          (make_package [ ("main.truss", Fixtures.Cli.hole_beside_a_type_defined_as_todo) ])
      with
      | [ session; greet ] ->
          expect_strings
            ~expected:[ "main"; "test demo \"greets\"" ]
            (list_strings (Cli.Json.lookup_field "blocks" session));
          expect_strings
            ~expected:[ "main"; "test demo \"greets\"" ]
            (list_strings (Cli.Json.lookup_field "blocks" greet))
      | found -> fail "found %d holes" (List.length found));
  test "a hole blocks the tests that can reach it while other code has errors" (fun () ->
      match list_holes (make_package [ ("main.truss", Fixtures.Cli.hole_beside_an_error) ]) with
      | [ hole ] ->
          expect_strings ~expected:[ "test demo \"greets\"" ]
            (list_strings (Cli.Json.lookup_field "blocks" hole))
      | found -> fail "found %d holes" (List.length found));
  test "a hole whose type nothing fixes, such as one interpolated, is not decided yet" (fun () ->
      match
        list_holes (make_package [ ("main.truss", Fixtures.Cli.show_of_an_interpolated_todo) ])
      with
      | [ hole ] ->
          if read_string_field "type" hole <> "not decided yet" then
            fail "type %s" (read_string_field "type" hole)
      | found -> fail "found %d holes" (List.length found));
  test "a type defined as todo is a hole" (fun () ->
      match list_holes (make_package [ ("main.truss", "type Session = todo\n") ]) with
      | [ hole ] ->
          if read_string_field "kind" hole <> "type" then
            fail "kind %s" (read_string_field "kind" hole)
      | found -> fail "found %d holes" (List.length found));
  test "a type defined as todo blocks main and the tests that reach it, and only those" (fun () ->
      match list_holes (make_package [ ("main.truss", Fixtures.Cli.unfinished_type) ]) with
      | [ hole ] ->
          expect_strings
            ~expected:[ "main"; "test demo \"reaches\"" ]
            (list_strings (Cli.Json.lookup_field "blocks" hole))
      | found -> fail "found %d holes" (List.length found));
  test "a test that reaches a type defined as todo is incomplete, and the others run" (fun () ->
      let outcomes =
        List.map
          (fun test ->
            ( read_string_field "name" test,
              read_string_field "outcome" test,
              match Cli.Json.lookup_field "message" test with
              | Cli.Json.String message -> message
              | _ -> "" ))
          (list_objects
             (Cli.Json.lookup_field "tests"
                (run_json
                   [ "test"; "-C"; make_package [ ("main.truss", Fixtures.Cli.unfinished_type) ] ])))
      in
      match outcomes with
      | [ ("reaches", "incomplete", message); ("counts", "passed", _) ]
        when message = "the type demo::Session is defined as todo\n  at main.truss:1:6" ->
          ()
      | _ ->
          fail "%s"
            (String.concat "; "
               (List.map
                  (fun (name, outcome, message) -> String.concat " " [ name; outcome; message ])
                  outcomes)));
  test "truss test shows the echo output of a passing test" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.passing_test_reaching_an_echo) ] in
      let status, output = run_truss [ "test"; "-C"; root ] in
      if status <> 0 then fail "status %d: %s" status output;
      if not (String.includes ~affix:"\"triples\": passed\n    main.truss:2:3: 6\n\n" output) then
        fail "%s" output);
  test "truss test shows a failed test's output, and --json gives each test's output" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.tests_printing_to_the_console) ] in
      let status, output = run_truss [ "test"; "-C"; root ] in
      if status <> 1 then fail "status %d: %s" status output;
      if
        (not (String.includes ~affix:"    output:\n      printed by a failing test\n" output))
        || String.includes ~affix:"printed by a passing test" output
      then fail "%s" output;
      let outputs =
        List.map
          (fun test -> (read_string_field "name" test, read_string_field "output" test))
          (list_objects (Cli.Json.lookup_field "tests" (run_json [ "test"; "-C"; root ])))
      in
      match outputs with
      | [
       ("prints and passes", "printed by a passing test\n");
       ("prints and fails", "printed by a failing test\n");
      ] ->
          ()
      | _ ->
          fail "%s"
            (String.concat "; " (List.map (fun (name, output) -> name ^ " " ^ output) outputs)));
  test "build refuses a program whose main can reach a type defined as todo" (fun () ->
      let status, output =
        run_truss [ "build"; "-C"; make_package [ ("main.truss", Fixtures.Cli.unfinished_type) ] ]
      in
      if status <> 1 then fail "status %d: %s" status output;
      if
        not
          (String.includes
             ~affix:
               "main.truss:1:6: `todo` can be reached from `main`, so the program cannot be built.\n\
               \    demo::main -> demo::Session"
             output)
      then fail "%s" output);
  test "build refuses a todo that main reaches beside a type defined as todo" (fun () ->
      let status, output =
        run_truss
          [
            "build";
            "-C";
            make_package [ ("main.truss", Fixtures.Cli.hole_beside_a_type_defined_as_todo) ];
          ]
      in
      if status <> 1 then fail "status %d: %s" status output;
      if
        not
          (String.includes
             ~affix:
               "main.truss:12:3: `todo` can be reached from `main`, so the program cannot be built.\n\
               \    demo::main -> demo::greet"
             output)
      then fail "%s" output)

let registry_root = ref ""

let make_registry () =
  registry_root := make_directory [];
  Unix.putenv Registry.Index.variable !registry_root;
  Option.get (Registry.Index.find_current_registry ())

let make_version_directory (package : Path.package) version =
  List.fold_left Filename.concat !registry_root
    (Path.list_package_parts package @ [ Registry.Version.show version ])

let publish registry name version ?(dependencies = []) ?(record = []) modules =
  let manifest =
    make_manifest name
    ^
    if dependencies = [] then ""
    else
      "[dependencies]\n"
      ^ String.concat ""
          (List.map
             (fun (dependency, capabilities) ->
               Printf.sprintf "%S = [%s]\n" dependency
                 (String.concat ", " (List.map (Printf.sprintf "%S") capabilities)))
             dependencies)
  in
  let lock =
    Registry.Lock.print
      (List.map
         (fun (dependency, version) ->
           match Registry.Index.hash_of registry dependency version with
           | Some hash -> { Registry.Lock.name = dependency; version; hash; holds = [] }
           | None -> failwith (Path.show_package dependency ^ " is not in the registry"))
         record)
  in
  Registry.Index.add registry
    (Option.get (Path.parse_package name))
    version
    ((("truss.toml", manifest) :: (if record = [] then [] else [ ("truss.lock", lock) ])) @ modules)

let list_units text =
  [ ("lengths/lengths.truss", Printf.sprintf "public fn meter() -> Int64 {\n  %s\n}\n" text) ]

let geometry = [ ("vector/vector.truss", Fixtures.Cli.geometry_vector) ]

let make_stocked_registry () =
  let registry = make_registry () in
  publish registry "acme::units" (1, 0, 0) (list_units "1");
  publish registry "acme::units" (1, 1, 0) (list_units "100");
  publish registry "acme::geometry" (1, 0, 0)
    ~dependencies:[ ("acme::units", []) ]
    ~record:[ ({ Path.owner = Some "acme"; name = "units" }, (1, 0, 0)) ]
    geometry;
  registry

let uses_geometry = ("main.truss", Fixtures.Cli.length_through_vector)
let add root names = run_quietly ([ "add"; "-C"; root ] @ names)
let lock_lines root = String.split_on_char '\n' (String.trim (read root "truss.lock"))

let list_versions root =
  List.map
    (fun (entry : Registry.Lock.entry) ->
      (Path.show_package entry.name, Registry.Version.show entry.version))
    (Registry.Lock.parse (read root "truss.lock"))

let expect_versions root expected =
  let listed = list_versions root in
  if listed <> expected then
    fail "the lock file has [%s]"
      (String.concat "; " (List.map (fun (name, version) -> name ^ " " ^ version) listed))

let clean root = not (Cli.Report.has_errors (gather (Cli.Command_packages.load root)))

let () =
  test "adding a package writes its entry, and a line for it and for each package it brings"
    (fun () ->
      let _ = make_stocked_registry () in
      let root = make_package [ uses_geometry ] in
      if add root [ "acme::geometry" ] <> 0 then fail "not added";
      if not (String.includes ~affix:"\"acme::geometry\" = []" (read root "truss.toml")) then
        fail "the manifest is %s" (read root "truss.toml");
      expect_versions root [ ("acme::geometry", "1.0.0"); ("acme::units", "1.0.0") ];
      if not (clean root) then fail "has errors");
  test "a package is added at the version it was published with, and nothing newer" (fun () ->
      let registry = make_stocked_registry () in
      let root = make_package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      publish registry "acme::shapes" (1, 0, 0)
        ~dependencies:[ ("acme::units", []) ]
        ~record:[ ({ Path.owner = Some "acme"; name = "units" }, (1, 1, 0)) ]
        [ ("square/square.truss", Fixtures.Cli.public_sides) ];
      rewrite root "main.truss" (snd uses_geometry ^ Fixtures.Cli.sides_through_square);
      if add root [ "acme::shapes" ] <> 0 then fail "not added";
      expect_versions root
        [ ("acme::geometry", "1.0.0"); ("acme::shapes", "1.0.0"); ("acme::units", "1.1.0") ];
      if not (clean root) then fail "has errors");
  test "a package is added at the version written after @" (fun () ->
      let _ = make_stocked_registry () in
      let root = make_package [ ("main.truss", Fixtures.Cli.meter_through_lengths) ] in
      if add root [ "acme::units@1.0.0" ] <> 0 then fail "not added";
      expect_versions root [ ("acme::units", "1.0.0") ]);
  test "a package the registry does not hold is not added, and the manifest is left as it was"
    (fun () ->
      let _ = make_stocked_registry () in
      let root = make_package [ ("main.truss", "") ] in
      let before = read root "truss.toml" in
      if add root [ "acme::nothing" ] <> 2 then fail "added";
      expect_string ~expected:before (read root "truss.toml");
      if Sys.file_exists (Filename.concat root "truss.lock") then fail "wrote a lock file");
  test "a dependency with no line in the lock file is reported once, by the lock file" (fun () ->
      let _ = make_stocked_registry () in
      let root =
        make_directory
          [ ("truss.toml", make_manifest "demo" ^ "[dependencies]\n\"acme::units\" = []\n") ]
      in
      let problems = Workspace.problems (fst (Cli.Command_packages.load root)) in
      match
        List.filter
          (fun (problem : Project.problem) ->
            String.includes ~affix:"not a package of this project" problem.message)
          problems
      with
      | [ { file = "truss.lock"; message; _ } ]
        when String.includes ~affix:"Run `truss add acme::units`" message ->
          ()
      | _ -> fail "problems: [%s]" (String.concat "; " (List.map Project.show_problem problems)));
  test "registry packages that depend on each other in a cycle are a problem, and none is built"
    (fun () ->
      let registry = make_registry () in
      let make_acme_package name : Path.package = { owner = Some "acme"; name } in
      publish registry "acme::rings" (1, 0, 0) [ ("ring/ring.truss", "") ];
      publish registry "acme::chains" (1, 0, 0)
        ~dependencies:[ ("acme::rings", []) ]
        ~record:[ (make_acme_package "rings", (1, 0, 0)) ]
        [];
      publish registry "acme::rings" (1, 1, 0)
        ~dependencies:[ ("acme::chains", []) ]
        ~record:[ (make_acme_package "chains", (1, 0, 0)) ]
        [];
      let root = make_package [ ("main.truss", "") ] in
      if add root [ "acme::rings" ] <> 0 then fail "not added";
      expect_versions root [ ("acme::chains", "1.0.0"); ("acme::rings", "1.1.0") ];
      expect_problem_in root
        "truss.lock: Packages cannot depend on each other in a cycle: `acme::chains` -> \
         `acme::rings` -> `acme::chains`";
      if
        List.exists
          (fun state ->
            String.includes ~affix:"acme::rings" state
            || String.includes ~affix:"acme::chains" state)
          (Workspace.list_package_databases ())
      then fail "a package of the cycle has a state");
  test "a project's package and a registry package that depend on each other form a cycle"
    (fun () ->
      let _ = make_stocked_registry () in
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("app/truss.toml", make_manifest "app" ^ "[dependencies]\n\"acme::geometry\" = []\n");
            ( "units/truss.toml",
              make_manifest "acme::units" ^ "[dependencies]\n\"acme::geometry\" = []\n" );
          ]
      in
      if add (Filename.concat root "app") [ "acme::geometry" ] <> 0 then fail "not added";
      expect_problem_in root
        "units/truss.toml: Packages cannot depend on each other in a cycle: `acme::units` -> \
         `acme::geometry` -> `acme::units`");
  test "a lock file that is not the one the manifests give is a problem, which check --fix fixes"
    (fun () ->
      let _ = make_stocked_registry () in
      let root = make_package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      rewrite root "truss.toml"
        (make_manifest "demo" ^ "[dependencies]\n\"acme::geometry\" = [\"Clock\"]\n");
      expect_problem_in root
        "`acme::geometry` is said to hold nothing, and the manifests grant it Clock";
      if run_quietly [ "check"; "-C"; root; "--fix" ] <> 0 then fail "still has errors";
      if
        not
          (List.exists
             (fun line ->
               String.includes ~affix:"acme::geometry 1.0.0" line
               && String.includes ~affix:" holds Clock" line)
             (lock_lines root))
      then fail "the lock file is %s" (read root "truss.lock"));
  test "a line that no package uses is a problem, which check --fix fixes by deleting it" (fun () ->
      let _ = make_stocked_registry () in
      let root = make_package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      rewrite root "main.truss" "";
      rewrite root "truss.toml" (make_manifest "demo");
      expect_problem_in root "Nothing in the build uses `acme::geometry`";
      if run_quietly [ "check"; "-C"; root; "--fix" ] <> 0 then fail "still has errors";
      expect_versions root []);
  test "files in the registry that do not have the lock file's hash are not used" (fun () ->
      let registry = make_stocked_registry () in
      publish registry "acme::angles" (1, 0, 0) [ ("degrees/degrees.truss", "") ];
      let root = make_package [ ("main.truss", "") ] in
      let hash =
        Option.get
          (Registry.Index.hash_of registry { Path.owner = Some "acme"; name = "angles" } (1, 0, 0))
      in
      rewrite root "truss.toml" (make_manifest "demo" ^ "[dependencies]\n\"acme::angles\" = []\n");
      rewrite root "truss.lock" (Printf.sprintf "format 1\nacme::angles 1.0.0 %s\n" hash);
      Out_channel.with_open_bin
        (Filename.concat
           (make_version_directory { Path.owner = Some "acme"; name = "angles" } (1, 0, 0))
           "degrees/degrees.truss")
        (fun channel -> output_string channel "fn stolen() {}\n");
      expect_problem_in root "do not have the hash the lock file names");
  test "a package that is not in the store cannot be had without a registry" (fun () ->
      let registry = make_stocked_registry () in
      publish registry "acme::tides" (1, 0, 0) [ ("moon/moon.truss", "") ];
      let root = make_package [ ("main.truss", "") ] in
      let hash =
        Option.get
          (Registry.Index.hash_of registry { Path.owner = Some "acme"; name = "tides" } (1, 0, 0))
      in
      rewrite root "truss.toml" (make_manifest "demo" ^ "[dependencies]\n\"acme::tides\" = []\n");
      rewrite root "truss.lock" (Printf.sprintf "format 1\nacme::tides 1.0.0 %s\n" hash);
      Unix.putenv Registry.Index.variable "";
      expect_problem_in root "no registry is set");
  test "a project's package takes the place of the registry's package of its name" (fun () ->
      let _ = make_stocked_registry () in
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("app/truss.toml", make_manifest "app" ^ "[dependencies]\n\"acme::geometry\" = []\n");
            ("app/main.truss", snd uses_geometry);
            ("units/truss.toml", make_manifest "acme::units");
            ("units/lengths/lengths.truss", Fixtures.Cli.public_meter_of_seven);
          ]
      in
      let app = Filename.concat root "app" in
      if add app [ "acme::geometry" ] <> 0 then fail "not added";
      expect_versions root [ ("acme::geometry", "1.0.0") ];
      if not (clean root) then fail "has errors";
      let project = Cli.Command_packages.load root in
      if
        not
          (List.mem "units/lengths/lengths.truss"
             (List.map (Workspace.locate_file (fst project)) (list_files project)))
      then fail "the project's package is not the one in the build")

let () =
  test "a registry package that does not check with this toolchain is a problem that names it"
    (fun () ->
      let registry = make_registry () in
      publish registry "acme::broken" (1, 0, 0)
        [ ("lengths/lengths.truss", "public fn meter() -> Int64 {\n  \"one\"\n}\n") ];
      let root =
        make_package
          [
            ( "main.truss",
              "use acme::broken::lengths\n\nfn length() -> Int64 {\n  lengths::meter()\n}\n" );
          ]
      in
      ignore (add root [ "acme::broken" ]);
      expect_problem_in root
        "`acme::broken` 1.0.0 does not check with this toolchain. It has 1 error; the first is at")

let upgrade root names = run_truss ([ "upgrade"; "-C"; root ] @ names)

let () =
  test "upgrading moves a package to its newest version and says so" (fun () ->
      let _ = make_stocked_registry () in
      let root = make_package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      let status, output = upgrade root [] in
      if status <> 0 then fail "status %d: %s" status output;
      if not (String.includes ~affix:"`acme::units` goes from 1.0.0 to 1.1.0" output) then
        fail "said %s" output;
      expect_versions root [ ("acme::geometry", "1.0.0"); ("acme::units", "1.1.0") ]);
  test "upgrading a package that is at its newest version changes nothing" (fun () ->
      let _ = make_stocked_registry () in
      let root = make_package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      let before = read root "truss.lock" in
      let status, output = upgrade root [ "acme::geometry" ] in
      if
        status <> 0
        || not (String.includes ~affix:"Every package is at the version asked for" output)
      then fail "status %d: %s" status output;
      expect_string ~expected:before (read root "truss.lock"));
  test "an upgrade says which signatures the project reads change, and which code breaks" (fun () ->
      let registry = make_stocked_registry () in
      let root = make_package [ ("main.truss", Fixtures.Cli.meter_through_lengths) ] in
      ignore (add root [ "acme::units" ]);
      publish registry "acme::units" (1, 2, 0)
        [ ("lengths/lengths.truss", Fixtures.Cli.public_meter_with_a_scale) ];
      let status, output = upgrade root [ "acme::units" ] in
      if status <> 1 then fail "status %d: %s" status output;
      List.iter
        (fun part ->
          if not (String.includes ~affix:part output) then fail "%s is not in: %s" part output)
        [
          "`acme::units` goes from 1.1.0 to 1.2.0";
          "acme::units::lengths::meter";
          "was: public fn meter() -> Int64";
          "now: public fn meter(scale: Int64) -> Int64";
          "read by: demo::meter";
          "errors it does not have now";
        ]);
  test "an upgrade says which packages would hold a capability they did not" (fun () ->
      let registry = make_stocked_registry () in
      let root = make_package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      rewrite root "truss.toml"
        (make_manifest "demo" ^ "[dependencies]\n\"acme::geometry\" = [\"Clock\"]\n");
      ignore (run_quietly [ "check"; "-C"; root; "--fix" ]);
      publish registry "acme::geometry" (1, 1, 0)
        ~dependencies:[ ("acme::units", [ "Clock" ]) ]
        ~record:[ ({ Path.owner = Some "acme"; name = "units" }, (1, 0, 0)) ]
        geometry;
      let _, output = upgrade root [ "acme::geometry" ] in
      if not (String.includes ~affix:"`acme::units` would hold Clock, which it did not" output) then
        fail "said %s" output)

let publish_from root ~version = run_truss [ "publish"; version; "-C"; root ]

let make_angles_package text =
  make_directory [ ("truss.toml", make_manifest "acme::angles"); ("degrees/degrees.truss", text) ]

let turn = Fixtures.Cli.turn
let angles = { Path.owner = Some "acme"; name = "angles" }

let list_published registry name =
  List.map
    (fun (version, _) -> Registry.Version.show version)
    (Registry.Index.list_versions registry name)

let expect_published registry name expected =
  expect_strings ~expected (list_published registry name)

let expect_refused root part =
  let status, output = publish_from root ~version:"1.0.0" in
  if status <> 1 then fail "status %d: %s" status output;
  if not (String.includes ~affix:part output) then fail "said %s" output

let expect_cannot_publish root ~version part =
  let status, output = publish_from root ~version in
  if status <> 2 then fail "status %d: %s" status output;
  if not (String.includes ~affix:part output) then fail "said %s" output

let () =
  test "a package is published at the version it is given, and holds its files" (fun () ->
      let registry = make_registry () in
      let root = make_angles_package turn in
      let status, output = publish_from root ~version:"1.0.0" in
      if status <> 0 then fail "status %d: %s" status output;
      if not (String.includes ~affix:"Published `acme::angles` 1.0.0" output) then
        fail "said %s" output;
      expect_published registry angles [ "1.0.0" ];
      let files = Registry.Content.list_all_files (make_version_directory angles (1, 0, 0)) in
      expect_strings ~expected:[ "degrees/degrees.truss"; "truss.toml" ] (List.map fst files));
  test "a version that is not three numbers is not published" (fun () ->
      let registry = make_registry () in
      expect_cannot_publish (make_angles_package turn) ~version:"1.0"
        "`1.0` is not a version, which is three numbers";
      expect_published registry angles []);
  test "a version whose first number is not the one at the end of the name is not published"
    (fun () ->
      let registry = make_registry () in
      expect_cannot_publish (make_angles_package turn) ~version:"2.0.0"
        "A version of `acme::angles` starts with 1";
      expect_cannot_publish (make_angles_package turn) ~version:"2.0.0"
        "published under another name, such as `acme::angles_v2`";
      let root =
        make_directory
          [ ("truss.toml", make_manifest "acme::angles_v2"); ("degrees/degrees.truss", turn) ]
      in
      expect_cannot_publish root ~version:"1.0.0" "A version of `acme::angles_v2` starts with 2";
      let status, output = publish_from root ~version:"2.0.0" in
      if status <> 0 then fail "status %d: %s" status output;
      expect_published registry angles [];
      expect_published registry { Path.owner = Some "acme"; name = "angles_v2" } [ "2.0.0" ]);
  test "a release needs a version higher than the newest release's" (fun () ->
      let registry = make_registry () in
      let root = make_angles_package turn in
      ignore (publish_from root ~version:"1.1.0");
      rewrite root "degrees/degrees.truss" Fixtures.Cli.turn_of_a_sum;
      List.iter
        (fun version ->
          expect_cannot_publish root ~version
            "The newest release of `acme::angles` is 1.1.0, so this release needs a higher version")
        [ "1.1.0"; "1.0.5" ];
      let status, output = publish_from root ~version:"1.1.1" in
      if status <> 0 then fail "status %d: %s" status output;
      expect_published registry angles [ "1.1.0"; "1.1.1" ]);
  test "a package with no owner in its name is not published" (fun () ->
      let _ = make_registry () in
      let status, output =
        publish_from (make_package [ ("degrees/degrees.truss", turn) ]) ~version:"1.0.0"
      in
      if status <> 2 || not (String.includes ~affix:"has no owner in its name" output) then
        fail "status %d: %s" status output);
  test "a package with an error is not published" (fun () ->
      let _ = make_registry () in
      expect_refused (make_angles_package Fixtures.Cli.turn_of_a_boolean) "1 error");
  test "a package with a todo or an echo is not published, and each is listed" (fun () ->
      let registry = make_registry () in
      let root = make_angles_package Fixtures.Cli.turn_with_a_todo_and_an_echo in
      expect_refused root "degrees.truss:2:3: `todo` is not finished code";
      expect_refused root "degrees.truss:6:3: `echo` is not finished code";
      expect_refused root "degrees.truss:10:13: `echo` is not finished code";
      expect_refused root "degrees.truss:13:13: `todo` is not finished code";
      expect_published registry angles []);
  test "a package whose test fails is not published" (fun () ->
      let registry = make_registry () in
      let root = make_angles_package (turn ^ Fixtures.Cli.turn_test_of_a_right_angle) in
      expect_refused root "Cannot publish a package whose tests fail";
      expect_published registry angles []);
  test "a package whose tests pass is published" (fun () ->
      let registry = make_registry () in
      let root = make_angles_package (turn ^ Fixtures.Cli.turn_test_of_a_whole_turn) in
      let status, output = publish_from root ~version:"1.0.0" in
      if status <> 0 then fail "status %d: %s" status output;
      expect_published registry angles [ "1.0.0" ])

let () =
  test "a package is published with the versions of the packages its code uses" (fun () ->
      let _ = make_stocked_registry () in
      let root =
        make_directory
          [
            ("truss.toml", make_manifest "acme::walls");
            ("height/height.truss", Fixtures.Cli.height_through_vector);
          ]
      in
      ignore (add root [ "acme::geometry" ]);
      let status, output = publish_from root ~version:"1.0.0" in
      if status <> 0 then fail "status %d: %s" status output;
      let record =
        Registry.Lock.parse
          (In_channel.with_open_bin
             (Filename.concat
                (make_version_directory { Path.owner = Some "acme"; name = "walls" } (1, 0, 0))
                "truss.lock")
             In_channel.input_all)
      in
      match record with
      | [
       { name = { Path.owner = Some "acme"; name = "geometry" }; version = 1, 0, 0; holds = []; _ };
       { name = { Path.owner = Some "acme"; name = "units" }; version = 1, 0, 0; holds = []; _ };
      ] ->
          ()
      | _ -> fail "published with other versions");
  test "a published package is used by another project, with its dependencies at publication"
    (fun () ->
      let _ = make_stocked_registry () in
      let walls =
        make_directory
          [
            ("truss.toml", make_manifest "acme::walls");
            ("height/height.truss", Fixtures.Cli.height_through_vector);
          ]
      in
      ignore (add walls [ "acme::geometry" ]);
      ignore (publish_from walls ~version:"1.0.0");
      let root = make_package [ ("main.truss", Fixtures.Cli.tall_through_walls) ] in
      if add root [ "acme::walls" ] <> 0 then fail "not added";
      expect_versions root
        [ ("acme::geometry", "1.0.0"); ("acme::units", "1.0.0"); ("acme::walls", "1.0.0") ];
      if not (clean root) then fail "has errors");
  test "a dependency that only a package's tests use is left out of its published lock file"
    (fun () ->
      let _ = make_stocked_registry () in
      let root =
        make_directory
          [
            ("truss.toml", make_manifest "acme::walls");
            ("height/height.truss", Fixtures.Cli.height_tested_against_a_meter);
          ]
      in
      ignore (add root [ "acme::units@1.0.0" ]);
      let status, output = publish_from root ~version:"1.0.0" in
      if status <> 0 then fail "status %d: %s" status output;
      if
        Sys.file_exists
          (Filename.concat
             (make_version_directory { Path.owner = Some "acme"; name = "walls" } (1, 0, 0))
             "truss.lock")
      then fail "published with a package only its test uses";
      let user = make_package [ ("main.truss", Fixtures.Cli.tall_through_walls) ] in
      ignore (add user [ "acme::walls" ]);
      expect_versions user [ ("acme::walls", "1.0.0") ];
      if Cli.Report.has_errors (gather ~proofs:true (Cli.Command_packages.load user)) then
        fail "has diagnostics");
  test "a package that depends on one of its project's that is not published is refused" (fun () ->
      let _ = make_registry () in
      let root =
        make_directory
          [
            ("truss.toml", "[project]\n");
            ("angles/truss.toml", make_manifest "acme::angles");
            ("angles/degrees/degrees.truss", turn);
            ( "walls/truss.toml",
              make_manifest "acme::walls" ^ "[dependencies]\n\"acme::angles\" = []\n" );
            ("walls/corner.truss", Fixtures.Cli.corner_through_degrees);
          ]
      in
      let walls = Filename.concat root "walls" in
      expect_refused walls "publish `acme::angles` first";
      ignore (publish_from (Filename.concat root "angles") ~version:"1.0.0");
      let status, output = publish_from walls ~version:"1.0.0" in
      if status <> 0 then fail "status %d: %s" status output)

let () =
  test "a command line is parsed and run as the client would run it" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.doubling) ] in
      let status, _ =
        capture (fun () -> Cli.Main.run_client [ "truss"; "--no-server"; "check"; "-C"; root ])
      in
      if status <> 0 then fail "did not succeed");
  test "an unknown command is a bad argument" (fun () ->
      let status, _ = capture (fun () -> Cli.Main.run_client [ "truss"; "--no-server"; "bogus" ]) in
      if status <> 2 then fail "did not exit with 2")

let () =
  test "check accepts an HTML template that interpolates into text and quoted attributes" (fun () ->
      let root =
        make_package
          [
            ( "main.truss",
              "use standard::html\n\n\
               public fn page(name: own String, link: own String) -> html::Html {\n\
              \  html::Html\"<p title='${name.copy()}'><a href=\\\"${own link}\\\">${own \
               name}</a></p>\"\n\
               }\n" );
          ]
      in
      let status, output =
        capture (fun () -> Cli.Main.run_client [ "truss"; "--no-server"; "check"; "-C"; root ])
      in
      if status <> 0 then fail "did not succeed: %s" output);
  test "check rejects an HTML template that interpolates into an event handler or a script"
    (fun () ->
      List.iter
        (fun template ->
          let root =
            make_package
              [
                ( "main.truss",
                  Printf.sprintf
                    "use standard::html\n\n\
                     public fn page(code: own String) -> html::Html {\n\
                    \  html::Html\"%s\"\n\
                     }\n"
                    template );
              ]
          in
          let status, output =
            capture (fun () -> Cli.Main.run_client [ "truss"; "--no-server"; "check"; "-C"; root ])
          in
          if status = 0 || not (String.includes ~affix:"is_valid_template" output) then
            fail "accepted %s: %s" template output)
        [
          "<a onclick=\\\"${own code}\\\">x</a>";
          "<${own code}>x</p>";
          "<script>${own code}</script>";
          "<a href=${own code}>x</a>";
        ])

let () =
  test "a name that is not a package's makes nothing" (fun () ->
      let root = make_directory [] in
      List.iter
        (fun name -> if run_quietly [ "new"; "-C"; root; name ] <> 2 then fail "made %s" name)
        [ "Weather"; "weather__x"; "1st"; ""; "a::b::c" ]);
  test "a new package with an owner is made in a directory named without it" (fun () ->
      let root = make_directory [] in
      if run_quietly [ "new"; "-C"; root; "acme::weather" ] <> 0 then fail "not made";
      let project = Cli.Command_packages.load (Filename.concat root "weather") in
      expect_strings ~expected:[ "acme::weather" ] (list_names project);
      if Cli.Report.has_errors (gather ~proofs:true project) then fail "has errors");
  test "a new package checks cleanly" (fun () ->
      let root = make_directory [] in
      if run_quietly [ "new"; "-C"; root; "weather" ] <> 0 then fail "not made";
      let project = Cli.Command_packages.load (Filename.concat root "weather") in
      if Cli.Report.has_errors (gather ~proofs:true project) then fail "has errors")

let () =
  test "JSON with escapes and a surrogate pair is read" (fun () ->
      match Cli.Json.parse {|{"a": [1, -2, true, null], "b": "x\né😀"}|} with
      | Cli.Json.Object
          [ ("a", Cli.Json.List [ Int 1; Int -2; Bool true; Null ]); ("b", String text) ] ->
          expect_string ~expected:"x\n\xc3\xa9\xf0\x9f\x98\x80" text
      | _ -> fail "not read");
  test "a position counts UTF-16 code units, and an offset is its inverse" (fun () ->
      let text = "a\n\xf0\x9f\x98\x80b" in
      let source = Source.create ~path:"" text in
      let offset = String.length text - 1 in
      (match Cli.Lsp_command.For_testing.locate_position Utf_16 source offset with
      | 1, 2 -> ()
      | line, column -> fail "line %d, column %d" line column);
      if Cli.Lsp_command.For_testing.locate_offset Utf_16 source ~line:1 ~column:2 <> offset then
        fail "not the inverse");
  test "an open file's text is checked in place of the file on disk" (fun () ->
      let root = make_package [ ("main.truss", Fixtures.Cli.main_returning_success) ] in
      let uri = "file://" ^ Filename.concat root "main.truss" in
      let answer =
        fst
          (capture (fun () -> Cli.Lsp_command.check ~root Utf_16 [ (uri, Fixtures.Cli.next_count) ]))
      in
      match Cli.Json.lookup_field "files" answer with
      | Cli.Json.List [ file ] -> (
          match (Cli.Json.lookup_field "diagnostics" file, Cli.Json.lookup_field "states" file) with
          | Cli.Json.List [ diagnostic ], Cli.Json.List [ state ] ->
              if Cli.Json.lookup_field "code" diagnostic <> Cli.Json.String "prover.overflow" then
                fail "diagnostic %s" (Cli.Json.to_string diagnostic);
              if Cli.Json.lookup_field "proven" state <> Cli.Json.Bool false then
                fail "state %s" (Cli.Json.to_string state);
              if
                Cli.Json.lookup_field "range" diagnostic
                <> Cli.Json.Object
                     [
                       ( "start",
                         Cli.Json.Object [ ("line", Cli.Json.Int 1); ("character", Cli.Json.Int 2) ]
                       );
                       ( "end",
                         Cli.Json.Object
                           [ ("line", Cli.Json.Int 1); ("character", Cli.Json.Int 11) ] );
                     ]
              then fail "range %s" (Cli.Json.to_string (Cli.Json.lookup_field "range" diagnostic))
          | _ -> fail "%s" (Cli.Json.to_string file))
      | _ -> fail "%s" (Cli.Json.to_string answer));
  test "the server answers initialize, an unsupported request, and shutdown" (fun () ->
      let frame_message body =
        Printf.sprintf "Content-Length: %d\r\n\r\n%s" (String.length body) body
      in
      let input_file = Filename.temp_file "lsp-input" ""
      and output_file = Filename.temp_file "lsp-output" "" in
      Out_channel.with_open_bin input_file (fun channel ->
          List.iter
            (fun body -> output_string channel (frame_message body))
            [
              {|{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"rootUri":"file:///project","capabilities":{"general":{"positionEncodings":["utf-8"]}}}}|};
              {|{"jsonrpc":"2.0","id":2,"method":"textDocument/hover","params":{}}|};
              {|{"jsonrpc":"2.0","id":3,"method":"shutdown"}|};
              {|{"jsonrpc":"2.0","method":"exit"}|};
            ]);
      let status =
        In_channel.with_open_bin input_file (fun input ->
            Out_channel.with_open_bin output_file (fun output ->
                Cli.Lsp_command.serve ~input ~output ~check:(fun ~root:_ _ _ -> None)))
      in
      let written = In_channel.with_open_bin output_file In_channel.input_all in
      if status <> 0 then fail "status %d" status;
      List.iter
        (fun part ->
          if not (String.includes ~affix:part written) then fail "no %s in %s" part written)
        [
          {|"positionEncoding":"utf-8"|};
          {|"id":2,"error":{"code":-32601|};
          {|"id":3,"result":null|};
        ]);
  test "an open file's check is published, and cleared once it is closed" (fun () ->
      let written = ref [] and asked = ref [] in
      let check ~root encoding buffers =
        asked := (root, encoding, buffers) :: !asked;
        Some {|{"files":[{"uri":"file:///project/a%20b.truss","diagnostics":[],"states":[]}]}|}
      in
      let server =
        Cli.Lsp_command.For_testing.create
          ~write:(fun value -> written := Cli.Json.to_string value :: !written)
          ~check
      in
      let handle text = ignore (Cli.Lsp_command.For_testing.handle server (Cli.Json.parse text)) in
      handle
        {|{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"rootUri":"file:///project"}}|};
      handle
        {|{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///project/a%20b.truss","text":"x"}}}|};
      Cli.Lsp_command.For_testing.refresh server;
      (match !asked with
      | [ ("/project", Utf_16, [ ("file:///project/a%20b.truss", "x") ]) ] -> ()
      | _ -> fail "asked %d times, or with other buffers" (List.length !asked));
      handle
        {|{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///project/a%20b.truss"}}}|};
      Cli.Lsp_command.For_testing.refresh server;
      let all = String.concat "\n" (List.rev !written) in
      List.iter
        (fun part -> if not (String.includes ~affix:part all) then fail "no %s in %s" part all)
        [
          {|"method":"textDocument/publishDiagnostics"|};
          {|"method":"truss/proofStates"|};
          {|"params":{"uri":"file:///project/a%20b.truss","diagnostics":[]}|};
        ];
      if List.length !asked <> 1 then fail "a check with no open file")

let () =
  test "check reports an unused private function as a warning, and passes" (fun () ->
      let root =
        make_package
          [
            ( "main.truss",
              "fn main(arguments: List[String]) -> ExitCode {\n\
              \  ExitCode.success\n\
               }\n\n\
               fn helper() -> Int64 {\n\
              \  1\n\
               }\n" );
          ]
      in
      let status, output = run_truss [ "check"; "-C"; root ] in
      if status <> 0 then fail "check exited %d:\n%s" status output;
      if not (String.includes ~affix:"warning[usage.unused_function]" output) then
        fail "output %S" output;
      if not (String.includes ~affix:"1 warning" output) then fail "output %S" output;
      match
        list_objects (Cli.Json.lookup_field "diagnostics" (run_json [ "check"; "-C"; root ]))
      with
      | [ diagnostic ] ->
          expect_string ~expected:"warning" (read_string_field "severity" diagnostic)
      | found -> fail "found %d diagnostics" (List.length found))
