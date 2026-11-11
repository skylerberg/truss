(* The command line's tests. Each gives a small package or input and states
   one fact about what a command makes of it. *)

open Cli

let test = Harness.test
let fail = Harness.fail

let expect_string ~expected actual =
  if not (String.equal expected actual) then fail "expected %S, got %S" expected actual

let expect_strings ~expected actual =
  if expected <> actual then
    fail "expected [%s], got [%s]" (String.concat "; " expected) (String.concat "; " actual)

let contains text part =
  let n = String.length part in
  let rec at i = i + n <= String.length text && (String.sub text i n = part || at (i + 1)) in
  at 0

(* Packages on disk *)

let counter = ref 0

(* A new directory holding the files, each a path under it and its text,
   with directories made as needed. *)
let directory files =
  incr counter;
  let root =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "truss-cli-tests-%d-%d" (Unix.getpid ()) !counter)
  in
  let rec make path =
    if not (Sys.file_exists path) then begin
      make (Filename.dirname path);
      Sys.mkdir path 0o755
    end
  in
  make root;
  List.iter
    (fun (path, text) ->
      let path = Filename.concat root path in
      make (Filename.dirname path);
      Out_channel.with_open_bin path (fun channel -> output_string channel text))
    files;
  Project.normalize root

let manifest_of name = Printf.sprintf "[package]\nname = \"%s\"\ntruss = \"0.1\"\n" name
let manifest = ("truss.toml", manifest_of "demo")
let package files = directory (manifest :: files)
let read root path = In_channel.with_open_bin (Filename.concat root path) In_channel.input_all

(* Runs [f] as a command would, with what it writes kept, and returns its
   result and its output, then saves the sessions it opened, as the command
   line does after each command. *)
let captured f =
  let out = Buffer.create 256 and err = Buffer.create 256 in
  let result =
    Output.with_
      { out = Buffer.add_string out; err = Buffer.add_string err; terminal = false; columns = None }
      f
  in
  List.iter Database.save_session !Project.opened;
  Project.opened := [];
  (result, Buffer.contents out ^ Buffer.contents err)

let quietly f = fst (captured f)

(* The tests' sessions are in a store of their own, apart from the user's. *)
let () =
  Unix.putenv "TRUSS_CACHE"
    (Filename.concat (Filename.get_temp_dir_name ())
       (Printf.sprintf "truss-cli-tests-store-%d" (Unix.getpid ())))

(* Arguments *)

let () =
  test "-C before the command is read as an option of the command" (fun () ->
      expect_strings
        ~expected:[ "truss"; "test"; "-C"; "dir"; "--rerun" ]
        (Arguments.prepare [ "truss"; "-C"; "dir"; "test"; "--rerun" ]));
  test "the first argument of run that is not one of its options starts the program's" (fun () ->
      expect_strings
        ~expected:[ "truss"; "run"; "--release"; "--"; "input.txt"; "-v" ]
        (Arguments.prepare [ "truss"; "run"; "--release"; "input.txt"; "-v" ]));
  test "a -- after run is kept as written" (fun () ->
      expect_strings ~expected:[ "truss"; "run"; "--"; "-x" ]
        (Arguments.prepare [ "truss"; "run"; "--"; "-x" ]))

(* Finding the package *)

let names (project : Project.t) =
  List.sort compare (List.map (fun (p : Project.package) -> p.name) project.packages)

let () =
  test "the package is found from a directory below its manifest" (fun () ->
      let root = package [ ("forecast/hourly.truss", "") ] in
      expect_strings ~expected:[ "demo" ] (names (Project.load (Filename.concat root "forecast"))));
  test "a directory with no manifest at or above it cannot run a command" (fun () ->
      let root = directory [ ("main.truss", "") ] in
      (* The temporary directory is not inside a package. *)
      match Project.load root with
      | exception Project.Cannot_run _ -> ()
      | _ -> fail "found a package");
  test "a project's root is about every package under it" (fun () ->
      let root =
        directory
          [
            ("truss.toml", "[project]\n");
            ("one/truss.toml", manifest_of "one");
            ("libraries/two/truss.toml", manifest_of "two");
          ]
      in
      expect_strings ~expected:[ "one"; "two" ] (names (Project.load root));
      expect_strings ~expected:[ "two" ] (names (Project.load (Filename.concat root "libraries"))));
  test "a package under a project's root is in the project, whichever directory a command is in"
    (fun () ->
      let root =
        directory
          [
            ("truss.toml", "[project]\n");
            ("one/truss.toml", manifest_of "one" ^ "[dependencies]\ntwo = []\n");
            ("one/main.truss", "use two::numbers\n\nfn four() -> Int64 {\n  numbers::two() * 2\n}\n");
            ("two/truss.toml", manifest_of "two");
            ("two/numbers.truss", "public fn two() -> Int64 {\n  2\n}\n");
          ]
      in
      let project = Project.load (Filename.concat root "one") in
      expect_strings ~expected:[ "one" ] (names project);
      if not (Report.clean (Report.gather project)) then fail "has diagnostics");
  test "a dependency's failed proof is the program's" (fun () ->
      let root =
        directory
          [
            ("truss.toml", "[project]\n");
            ("app/truss.toml", manifest_of "app" ^ "[dependencies]\nlib = []\n");
            ("app/main.truss", "use lib::arith\n\nfn two() -> UInt8 {\n  arith::bump(1)\n}\n");
            ("lib/truss.toml", manifest_of "lib");
            ("lib/arith.truss", "public fn bump(count: UInt8) -> UInt8 {\n  count + 1\n}\n");
          ]
      in
      let project = Project.load (Filename.concat root "app") in
      let report = Report.gather ~proofs:true project in
      if not (List.exists (fun (file : Report.file) -> file.module_.package = "lib") report.files)
      then fail "the dependency's overflow is not reported");
  test "a package with no [project] above it is a project by itself" (fun () ->
      let root =
        directory
          [
            ("one/truss.toml", manifest_of "one" ^ "[dependencies]\ntwo = []\n");
            ("one/main.truss", "");
            ("two/truss.toml", manifest_of "two");
          ]
      in
      let project = Project.load (Filename.concat root "one") in
      if
        not
          (List.exists
             (fun problem -> contains problem "`two` is not a package of this project")
             (Database.problems project.session))
      then fail "problems: %s" (String.concat "; " (Database.problems project.session));
      match Project.load root with
      | exception Project.Cannot_run _ -> ()
      | _ -> fail "found a project above the two");
  test "a directory with its own manifest is another package's, not modules of this one" (fun () ->
      let root =
        directory
          [
            ("truss.toml", "[project]\n" ^ manifest_of "demo");
            ("main.truss", "");
            ("vendor/truss.toml", manifest_of "other");
            ("vendor/x.truss", "");
          ]
      in
      let project = Project.load root in
      expect_strings ~expected:[ "demo::main"; "other::x" ]
        (List.sort compare (List.map Path.show_module (Project.modules project))));
  test "a directory with its own [project] is another project's, and so is all under it" (fun () ->
      let root =
        directory
          [
            ("truss.toml", "[project]\n" ^ manifest_of "demo");
            ("main.truss", "");
            ("examples/truss.toml", "[project]\n");
            ("examples/hello/truss.toml", manifest_of "hello");
            ("examples/hello/main.truss", "");
          ]
      in
      expect_strings ~expected:[ "demo::main" ]
        (List.map Path.show_module (Project.modules (Project.load root)));
      expect_strings ~expected:[ "hello" ] (names (Project.load (Filename.concat root "examples"))));
  test "under a package that is a project by itself, a directory with a manifest is no part of it"
    (fun () ->
      let root =
        package
          [ ("main.truss", ""); ("vendor/truss.toml", manifest_of "other"); ("vendor/x.truss", "") ]
      in
      expect_strings ~expected:[ "demo::main" ]
        (List.map Path.show_module (Project.modules (Project.load root)));
      expect_strings ~expected:[ "other" ] (names (Project.load (Filename.concat root "vendor"))));
  test "a directory whose name starts with a dot is not read" (fun () ->
      let root = package [ ("main.truss", ""); (".hidden/x.truss", "") ] in
      expect_strings ~expected:[ "demo::main" ]
        (List.map Path.show_module (Project.modules (Project.load root))));
  test "a path is shown relative to the directory it is read from" (fun () ->
      expect_string ~expected:"../weather/forecast.truss"
        (Project.relative ~from:"/code/app" "/code/weather/forecast.truss"))

(* What is wrong between manifests *)

let problems files =
  let project = Project.load (directory files) in
  Database.problems project.session

let expect_problem files part =
  let found = problems files in
  if not (List.exists (fun problem -> contains problem part) found) then
    fail "problems: [%s]" (String.concat "; " found)

(* The same, of a directory that is there already. *)
let expect_problem_in root part =
  let found = (Report.gather (Project.load root)).problems in
  if not (List.exists (fun problem -> contains problem part) found) then
    fail "problems: [%s]" (String.concat "; " found)

let () =
  test "a package that does not say which Truss it is written for has a problem" (fun () ->
      expect_problem
        [ ("truss.toml", "[package]\nname = \"demo\"\n") ]
        "truss.toml: `[package]` needs `truss = \"0.1\"`");
  test "a package written for a newer Truss than the toolchain's has a problem" (fun () ->
      expect_problem
        [ ("truss.toml", "[package]\nname = \"demo\"\ntruss = \"99.0\"\n") ]
        "`demo` is written for Truss 99.0, and this toolchain is Truss 0.1");
  test "a package cannot depend on itself" (fun () ->
      expect_problem
        [ ("truss.toml", manifest_of "demo" ^ "[dependencies]\ndemo = []\n") ]
        "`demo` cannot depend on itself");
  test "packages cannot depend on each other in a cycle" (fun () ->
      expect_problem
        [
          ("truss.toml", "[project]\n");
          ("one/truss.toml", manifest_of "one" ^ "[dependencies]\ntwo = []\n");
          ("two/truss.toml", manifest_of "two" ^ "[dependencies]\nthree = []\n");
          ("three/truss.toml", manifest_of "three" ^ "[dependencies]\none = []\n");
        ]
        "Packages cannot depend on each other in a cycle: `one` -> `two` -> `three` -> `one`");
  test "a package's name cannot be the owner in another's" (fun () ->
      expect_problem
        [
          ("truss.toml", "[project]\n");
          ("acme/truss.toml", manifest_of "acme");
          ("geometry/truss.toml", manifest_of "acme::geometry");
        ]
        "The package name `acme` is the owner in `acme::geometry`");
  test "two packages of a project cannot have one name" (fun () ->
      expect_problem
        [
          ("truss.toml", "[project]\n");
          ("one/truss.toml", manifest_of "same");
          ("two/truss.toml", manifest_of "same");
        ]
        "two/truss.toml: The package name `same` is already used by one/truss.toml")

(* A dependency that nothing uses *)

let () =
  test "a dependency nothing uses is a problem, which check --fix fixes by deleting its entry"
    (fun () ->
      let root =
        directory
          [
            ("truss.toml", "[project]\n");
            ( "app/truss.toml",
              manifest_of "app" ^ "[dependencies]\nlibrary = []\nother = [\n  \"Clock\",\n]\n" );
            ("app/main.truss", "use library::numbers\n\nfn one() -> Int64 {\n  numbers::one()\n}\n");
            ("library/truss.toml", manifest_of "library");
            ("library/numbers.truss", "public fn one() -> Int64 {\n  1\n}\n");
            ("other/truss.toml", manifest_of "other");
            ("other/nothing.truss", "public fn nothing() -> Int64 {\n  0\n}\n");
          ]
      in
      let app = Filename.concat root "app" in
      let report = Report.gather (Project.load app) in
      if
        not
          (List.exists
             (fun problem -> contains problem "app/truss.toml: Nothing in `app` uses `other`")
             report.problems)
      then fail "problems: [%s]" (String.concat "; " report.problems);
      if quietly (fun () -> Check_command.run ~directory:app ~fix:true ~json:false) <> 0 then
        fail "still has errors";
      let manifest = read root "app/truss.toml" in
      if
        contains manifest "other" || contains manifest "Clock"
        || not (contains manifest "library = []")
      then fail "wrote %s" manifest)

(* A package with an owner in its name *)

let owned =
  [
    ("truss.toml", "[project]\n");
    ("geometry/truss.toml", manifest_of "acme::geometry");
    ( "geometry/vector.truss",
      "public type Vector(x: Int64)\n\n\
       public fn Vector.length(self) -> Int64 {\n\
      \  self.x\n\
       }\n\n\
       public fn double(value: Int64) -> Int64\n\
      \  requires value < 1000 && value > -1000\n\
       {\n\
      \  value * 2\n\
       }\n" );
    ("app/truss.toml", manifest_of "app" ^ "[dependencies]\n\"acme::geometry\" = []\n");
    ( "app/main.truss",
      "use acme::geometry::vector\n\n\
       fn four() -> Int64 {\n\
      \  let _ = vector::double(1)\n\
      \  acme::geometry::vector::double(2)\n\
       }\n" );
  ]

let () =
  test "a project's package with an owner in its name is named by both in a path" (fun () ->
      let root = directory owned in
      let project = Project.load root in
      expect_strings ~expected:[ "acme::geometry"; "app" ] (names project);
      if not (Report.clean (Report.gather ~proofs:true project)) then fail "has diagnostics");
  test "show finds a definition of a package with an owner by its full path" (fun () ->
      let project = Project.load (directory owned) in
      match Show_command.find project ~body:false "acme::geometry::vector::double" with
      | [ found ] ->
          if not (contains found.text "public fn double(value: Int64) -> Int64") then
            fail "showed %s" found.text
      | found -> fail "found %d" (List.length found));
  test "show lists what a package with an owner makes public" (fun () ->
      let project = Project.load (directory owned) in
      if List.length (Show_command.find project ~body:false "acme::geometry") < 3 then
        fail "found too few")

let () =
  test "the project's [test] time_limit gives each test's limit in seconds" (fun () ->
      let root =
        directory
          [
            ("truss.toml", "[project]\n[test]\ntime_limit = 3\n");
            ("one/truss.toml", manifest_of "one");
          ]
      in
      let project = Project.load (Filename.concat root "one") in
      let limit = Database.time_limit project.session in
      if limit <> 3 then fail "got %d" limit);
  test "a project without a time limit gives tests 10 seconds" (fun () ->
      let limit = Database.time_limit (Project.load (package [])).session in
      if limit <> 10 then fail "got %d" limit);
  test "a time limit in a package's manifest that is not its project's is a problem" (fun () ->
      let root =
        directory
          [
            ("truss.toml", "[project]\n");
            ("one/truss.toml", manifest_of "one" ^ "[test]\ntime_limit = 3\n");
          ]
      in
      let project = Project.load root in
      if
        not
          (List.exists
             (fun problem ->
               contains problem "one/truss.toml: A test's time limit is its project's")
             (Database.problems project.session))
      then fail "problems: %s" (String.concat "; " (Database.problems project.session)));
  test "a time limit of 0 is malformed, at its line" (fun () ->
      match Manifest.parse "[package]\nname = \"a\"\n[test]\ntime_limit = 0\n" with
      | exception Manifest.Malformed (4, _) -> ()
      | _ -> fail "accepted")

(* Checking and fixing *)

let edit start stop replacement = Diagnostic.replace (Source.span start stop) replacement

let diagnostic ?(fixes = []) start stop =
  Diagnostic.make ~fixes ~code:(Usage Unused_variable) (Source.span start stop) "x."

let () =
  test "edits apply from the last to the first, so each one's offsets hold" (fun () ->
      expect_string ~expected:"A bb C" (Check_command.apply "a bb c" [ edit 0 1 "A"; edit 5 6 "C" ]));
  test "a fix that overlaps an earlier one waits for the next round" (fun () ->
      let first = diagnostic ~fixes:[ Diagnostic.fix "one" [ edit 0 3 "x" ] ] 0 3 in
      let second = diagnostic ~fixes:[ Diagnostic.fix "two" [ edit 2 4 "y" ] ] 2 4 in
      if Check_command.chosen [ first; second ] <> [ first ] then fail "chose both");
  test "a diagnostic with several fixes is left for the person or agent to choose" (fun () ->
      let choice =
        diagnostic
          ~fixes:[ Diagnostic.fix "one" [ edit 0 1 "x" ]; Diagnostic.fix "two" [ edit 0 1 "y" ] ]
          0 1
      in
      if Check_command.chosen [ choice ] <> [] then fail "chose one");
  test "check --fix writes the only fix and leaves no diagnostic" (fun () ->
      let root =
        package
          [
            ( "main.truss",
              "fn twice(value: Int64) -> Int64\n\
              \  requires value < 1000 && value > -1000\n\
               {\n\
              \  let unused = value\n\
              \  value * 2\n\
               }\n" );
          ]
      in
      let status = quietly (fun () -> Check_command.run ~directory:root ~fix:true ~json:false) in
      if status <> 0 then fail "status %d" status;
      if not (contains (read root "main.truss") "let _ = value") then
        fail "wrote %s" (read root "main.truss"))

let () =
  test "check proves, and reports what it cannot prove" (fun () ->
      let root = package [ ("main.truss", "fn next(count: UInt8) -> UInt8 {\n  count + 1\n}\n") ] in
      let status, output =
        captured (fun () -> Check_command.run ~directory:root ~fix:false ~json:false)
      in
      if status <> 1 then fail "status %d" status;
      if not (contains output "prover.overflow") then fail "%s" output);
  test "build refuses a program that can reach a hole in a proof" (fun () ->
      let root =
        package
          [
            ( "main.truss",
              "fn main(arguments: List[String]) -> ExitCode {\n\
              \  proof {\n\
              \    todo\n\
              \  }\n\
              \  ExitCode.success\n\
               }\n" );
          ]
      in
      let outcome, output =
        captured (fun () -> Program_command.build ~directory:root ~output:None ~json:false)
      in
      if outcome <> Outcome.Exit 1 then fail "did not refuse";
      if not (contains output "a `todo` in a proof") then fail "%s" output)

(* The test runner's report *)

let () =
  test "a report's records come back in the order of the tests, however they ended" (fun () ->
      let records =
        Compile.parse_report
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
        (List.map Test_command.duration [ 2_310_000; 42_000; 87 ]));
  test "the status line is cut by characters, never inside one" (fun () ->
      expect_string ~expected:"café" (Status_line.cut "café au lait" 4))

(* Selecting tests *)

let suite =
  {|fn double(value: Int64) -> Int64 {
  value * 2
}

test "doubles two" {
  assert double(2) == 4
}

test "doubles three" {
  assert double(3) == 6
}

test "halves" {
  assert double(1) == 2
}
|}

let () =
  test "--match keeps the tests whose names contain the text" (fun () ->
      let project = Project.load (package [ ("main.truss", suite) ]) in
      expect_strings
        ~expected:[ "doubles two"; "doubles three" ]
        (List.map
           (fun (t : Test_command.test) -> t.name)
           (Test_command.select project ~paths:[] ~match_:(Some "doubles"))));
  test "a file narrows the tests to those defined in it" (fun () ->
      let root = package [ ("main.truss", suite); ("other.truss", "test \"elsewhere\" {\n}\n") ] in
      let project = Project.load root in
      expect_strings ~expected:[ "elsewhere" ]
        (List.map
           (fun (t : Test_command.test) -> t.name)
           (Test_command.select project ~paths:[ Filename.concat root "other.truss" ] ~match_:None)))

(* Signatures *)

let () =
  test "a function's signature is its text without its body" (fun () ->
      let root =
        package
          [
            ( "main.truss",
              "public fn double(value: Int64) -> Int64\n  requires value < 100\n{\n  value * 2\n}\n"
            );
          ]
      in
      let project = Project.load root in
      match Show_command.find project ~body:false "demo::main::double" with
      | [ found ] ->
          expect_string ~expected:"public fn double(value: Int64) -> Int64\n  requires value < 100"
            found.text
      | found -> fail "found %d" (List.length found));
  test "a type is shown with its methods" (fun () ->
      let root =
        package
          [
            ( "main.truss",
              "public type Point(x: Int64, y: Int64)\n\n\
               public fn Point.sum(self) -> Int64 {\n\
              \  self.x + self.y\n\
               }\n" );
          ]
      in
      let project = Project.load root in
      expect_strings
        ~expected:[ "public type Point(x: Int64, y: Int64)"; "public fn Point.sum(self) -> Int64" ]
        (List.map
           (fun (f : Show_command.found) -> f.text)
           (Show_command.find project ~body:false "demo::main::Point")))

(* Holes *)

let unfinished =
  {|fn render(title: String, count: Int64) -> String {
  let header = "${title}: ${count}"
  let _ = header
  todo
}

test "renders" {
  assert render("a", count: 1) == "a: 1"
}

test "counts" {
  assert 1 + 1 == 2
}
|}

let () =
  test "a hole has the type it must have and the names in scope with theirs" (fun () ->
      let project = Project.load (package [ ("main.truss", unfinished) ]) in
      match Holes_command.gather project [] with
      | [ hole ] ->
          if hole.type_ <> Some "String" then fail "the type is not String";
          expect_strings
            ~expected:[ "count: Int64"; "header: String"; "title: String" ]
            (List.map (fun (name, ty) -> name ^ ": " ^ ty) hole.in_scope)
      | holes -> fail "found %d holes" (List.length holes));
  test "a hole blocks the tests that can reach it, and only those" (fun () ->
      let project = Project.load (package [ ("main.truss", unfinished) ]) in
      let holes = Holes_command.gather project [] in
      Holes_command.fill_blocks project holes;
      match holes with
      | [ hole ] -> expect_strings ~expected:[ "test demo::main \"renders\"" ] hole.blocks
      | _ -> fail "found %d holes" (List.length holes));
  test "a hole whose type nothing fixes, such as one interpolated, is not decided yet" (fun () ->
      let project =
        Project.load (package [ ("main.truss", "fn show() -> String {\n  \"${todo}\"\n}\n") ])
      in
      match Holes_command.gather project [] with
      | [ { type_ = Some "not decided yet"; _ } ] -> ()
      | [ { type_ = Some other; _ } ] -> fail "type %s" other
      | holes -> fail "found %d holes" (List.length holes));
  test "a type defined as todo is a hole" (fun () ->
      let project = Project.load (package [ ("main.truss", "type Session = todo\n") ]) in
      match Holes_command.gather project [] with
      | [ { type_ = None; _ } ] -> ()
      | holes -> fail "found %d holes" (List.length holes))

(* Building *)

(* Lowers code and compiles nothing, so it needs no C compiler. *)
let lowering (project : Project.t) =
  Compile.create project.context (Compiler.target ())
    { compiler = "cc"; identity = "lowering only" }
    (Build.cache (Database.objects_directory ()))
    { build = Development; optimization = O1; extra = [] }

let () =
  test "a todo main can reach is refused, with the way from main to it" (fun () ->
      let project =
        Project.load
          (package
             [
               ( "main.truss",
                 "fn main(arguments: List[String]) -> ExitCode {\n\
                 \  helper()\n\
                  }\n\n\
                  fn helper() -> ExitCode {\n\
                 \  todo\n\
                  }\n" );
             ])
      in
      match
        Compile.unshippable (lowering project)
          ~main:(List.hd (Program_command.mains project))
          ~echo:false
      with
      | Ok [ { failure = `Todo; line = 6; way; _ } ] ->
          expect_strings
            ~expected:[ "demo::main::main"; "demo::main::helper" ]
            (List.map Path.show way)
      | Ok found -> fail "found %d" (List.length found)
      | Error message -> fail "%s" message);
  test "a todo in a capability's method counts only where the method is called" (fun () ->
      let program called =
        Project.load
          (package
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
                    }\n"
                   called );
             ])
      in
      let found called =
        let project = program called in
        match
          Compile.unshippable (lowering project)
            ~main:(List.hd (Program_command.mains project))
            ~echo:false
        with
        | Ok found -> found
        | Error message -> failwith message
      in
      (match found "say" with [] -> () | _ -> fail "a method nothing calls stops the program");
      match found "shout" with
      | [ { failure = `Todo; line = 12; way; _ } ] -> (
          match List.map Path.show way with
          | "demo::main::main" :: "demo::main::speak" :: _ -> ()
          | way -> fail "reached by %s" (String.concat ", " way))
      | found -> fail "found %d" (List.length found));
  test "a package's program is the main of its main module, and of no other" (fun () ->
      let main_text = "fn main(arguments: List[String]) -> ExitCode {\n  ExitCode.success\n}\n" in
      let with_main = Project.load (package [ ("main.truss", main_text) ]) in
      expect_strings ~expected:[ "demo::main::main" ]
        (List.map Path.show (Program_command.mains with_main));
      let elsewhere = Project.load (package [ ("start.truss", main_text) ]) in
      if Program_command.mains elsewhere <> [] then fail "took a main from another module");
  test "a function named main outside the main module is an ordinary function" (fun () ->
      let project =
        Project.load
          (package [ ("menu.truss", "fn main(course: Int64) -> Int64 {\n  course\n}\n") ])
      in
      if not (Report.clean (Report.gather project)) then fail "has diagnostics");
  test "an echo is refused only by a build that ships" (fun () ->
      let project =
        Project.load
          (package
             [
               ( "main.truss",
                 "fn main(arguments: List[String]) -> ExitCode {\n  echo ExitCode.success\n}\n" );
             ])
      in
      let main = List.hd (Program_command.mains project) in
      let compile = lowering project in
      match
        (Compile.unshippable compile ~main ~echo:false, Compile.unshippable compile ~main ~echo:true)
      with
      | Ok [], Ok [ { failure = `Echo; _ } ] -> ()
      | _ -> fail "refused differently")

(* Renaming *)

let two_files =
  [
    ("weather.truss", "public fn total(values: List[Int64]) -> USize {\n  values.length()\n}\n");
    ( "main.truss",
      "use demo::weather\n\n\
       fn main(arguments: List[String]) -> ExitCode {\n\
      \  let _ = weather::total([1]) + demo::weather::total([2])\n\
      \  ExitCode.success\n\
       }\n" );
  ]

let rename root from_ to_ =
  quietly (fun () -> Rename_command.run ~directory:root ~from_ ~to_ ~json:false)

let () =
  test "renaming a function rewrites every reference in the package" (fun () ->
      let root = package two_files in
      if rename root "demo::weather::total" "sum" <> 0 then fail "refused";
      if
        not
          (contains (read root "main.truss") "weather::sum([1]) + demo::weather::sum([2])"
          && contains (read root "weather.truss") "public fn sum(")
      then fail "wrote %s" (read root "main.truss"));
  test "a rename that would cause a diagnostic changes nothing" (fun () ->
      let root =
        package
          [
            ( "main.truss",
              "fn first() -> Int64 {\n  1\n}\n\nfn second() -> Int64 {\n  first() + 1\n}\n" );
          ]
      in
      let before = read root "main.truss" in
      if rename root "demo::main::first" "second" <> 1 then fail "not refused";
      expect_string ~expected:before (read root "main.truss"));
  test "renaming a module moves its file and rewrites its uses and full paths" (fun () ->
      let root = package two_files in
      if rename root "demo::weather" "demo::outlook" <> 0 then fail "refused";
      if Sys.file_exists (Filename.concat root "weather.truss") then fail "kept the old file";
      let main = read root "main.truss" in
      if
        not
          (contains main "use demo::outlook"
          && contains main "outlook::total([1]) + demo::outlook::total([2])")
      then fail "wrote %s" main);
  test "renaming in a package with an owner rewrites a full path into it" (fun () ->
      let root = directory owned in
      if rename root "acme::geometry::vector::double" "twice" <> 0 then fail "refused";
      let main = read root "app/main.truss" in
      if
        not
          (contains main "let _ = vector::twice(1)"
          && contains main "  acme::geometry::vector::twice(2)")
      then fail "wrote %s" main);
  test "renaming a module of a package with an owner rewrites its uses and full paths" (fun () ->
      let root = directory owned in
      if rename root "acme::geometry::vector" "acme::geometry::arrow" <> 0 then fail "refused";
      if not (Sys.file_exists (Filename.concat root "geometry/arrow.truss")) then
        fail "did not move the file";
      let main = read root "app/main.truss" in
      if
        not
          (contains main "use acme::geometry::arrow"
          && contains main "let _ = arrow::double(1)"
          && contains main "  acme::geometry::arrow::double(2)")
      then fail "wrote %s" main);
  test "renaming a method rewrites its calls" (fun () ->
      let root =
        package
          [
            ( "main.truss",
              "type Point(x: Int64)\n\n\
               fn Point.get(self) -> Int64 {\n\
              \  self.x\n\
               }\n\n\
               fn read() -> Int64 {\n\
              \  Point(x: 1).get()\n\
               }\n" );
          ]
      in
      if rename root "demo::main::Point.get" "value" <> 0 then fail "refused";
      let text = read root "main.truss" in
      if not (contains text "fn Point.value(self)" && contains text "Point(x: 1).value()") then
        fail "wrote %s" text)

(* Comparing with a commit, and other worktrees *)

let git root arguments =
  let command =
    String.concat " "
      (List.map Filename.quote
         ([ "git"; "-C"; root; "-c"; "user.name=test"; "-c"; "user.email=test@example.com" ]
         @ arguments))
  in
  if Sys.command (command ^ " >/dev/null 2>&1") <> 0 then
    fail "git %s failed" (String.concat " " arguments)

let doubling =
  {|internal fn double(value: Int64) -> Int64
  requires value < 1000 && value > -1000
{
  value * 2
}

fn four() -> Int64 {
  double(2)
}

test "doubles" {
  assert double(2) == 4
}
|}

(* A repository whose one commit holds the package. *)
let repository text =
  let root = package [ ("main.truss", text) ] in
  git root [ "init"; "-q"; "-b"; "main" ];
  git root [ "add"; "-A" ];
  git root [ "commit"; "-q"; "-m"; "base" ];
  root

(* The text with its one occurrence of [part] replaced. *)
let replace text part by =
  let n = String.length part in
  let rec at i = if String.sub text i n = part then i else at (i + 1) in
  let i = at 0 in
  String.sub text 0 i ^ by ^ String.sub text (i + n) (String.length text - i - n)

let rewrite root path text =
  Out_channel.with_open_bin (Filename.concat root path) (fun out -> output_string out text);
  (* A rewrite within one second must still look changed. *)
  let now = Unix.gettimeofday () in
  Unix.utimes (Filename.concat root path) now (now +. 10.)

let impact root =
  let project = Project.load root in
  match Database.base_commit project.session None with
  | None ->
      fail "no base";
      []
  | Some commit -> (
      match Database.open_commit_of project.session commit with
      | Ok base -> Impact_command.changes project base
      | Error message ->
          fail "%s" message;
          [])

(* A repository whose one commit holds the package in a directory below
   its top, with another project beside it. *)
let nested_repository text =
  let top =
    directory
      [
        ("services/demo/truss.toml", manifest_of "demo");
        ("services/demo/main.truss", text);
        ("tools/truss.toml", manifest_of "tools");
        ("tools/main.truss", "fn broken() -> Int64 {\n  true\n}\n");
      ]
  in
  git top [ "init"; "-q"; "-b"; "main" ];
  git top [ "add"; "-A" ];
  git top [ "commit"; "-q"; "-m"; "base" ];
  top

let () =
  test "a project below the top of its repository is compared with its own files at a commit"
    (fun () ->
      let top = nested_repository doubling in
      let root = Filename.concat top "services/demo" in
      rewrite root "main.truss" (replace doubling "value * 2" "value + value");
      match impact root with
      | [ { path; status = `Changed parts; _ } ] ->
          expect_string ~expected:"demo::main::double" (Path.show path);
          if not (List.mem "body" parts) then fail "parts [%s]" (String.concat "; " parts)
      | changes -> fail "found %d changes" (List.length changes));
  test "a change to a body alone is a change of the body, which nothing reads" (fun () ->
      let root = repository doubling in
      rewrite root "main.truss" (replace doubling "value * 2" "value + value");
      match impact root with
      | [ { status = `Changed parts; read_by = []; _ } ] when not (List.mem "signature" parts) ->
          if not (List.mem "body" parts) then fail "parts [%s]" (String.concat "; " parts)
      | changes ->
          fail "found [%s]"
            (String.concat "; "
               (List.map
                  (fun (c : Impact_command.change) ->
                    Path.show c.path ^ " "
                    ^ match c.status with `Changed parts -> String.concat "," parts | _ -> "?")
                  changes)));
  test "a changed signature is shown before and after, with what reads it" (fun () ->
      let root = repository doubling in
      rewrite root "main.truss"
        (replace doubling "fn double(value: Int64) -> Int64"
           "fn double(value: Int64, by: Int64 = 2) -> Int64");
      match
        List.find_opt
          (fun (c : Impact_command.change) -> Path.show c.path = "demo::main::double")
          (impact root)
      with
      | Some { before = Some before; after = Some after; read_by; _ } ->
          if not (contains before "(value: Int64)" && contains after "by: Int64 = 2") then
            fail "signatures %s, %s" before after;
          if not (List.exists (fun (reader, _, _) -> Path.show reader = "demo::main::four") read_by)
          then fail "four does not read it"
      | _ -> fail "double did not change its signature");
  test "moving a definition within its file changes nothing" (fun () ->
      let one = "fn one() -> Int64 {\n  1\n}\n" and two = "fn two() -> Int64 {\n  2\n}\n" in
      let root = repository (one ^ "\n" ^ two) in
      rewrite root "main.truss" (two ^ "\n" ^ one);
      match impact root with [] -> () | changes -> fail "found %d changes" (List.length changes))

(* What reads what, and positions *)

let () =
  test "references list what reads a definition, part by part" (fun () ->
      let root = package [ ("main.truss", doubling) ] in
      let status, output =
        captured (fun () ->
            Graph_command.run ~directory:root ~direction:References ~name:"double" ~json:false)
      in
      if status <> 0 then fail "status %d" status;
      if
        not (contains output "demo::main::four: its body reads the signature of demo::main::double")
      then fail "wrote %s" output);
  test "a position's line and column count characters, as diagnostics do" (fun () ->
      if Explain_command.offset_of "ab\ncé x" ~line:2 ~column:4 <> 7 then fail "wrong offset");
  test "explaining a name gives its meaning and the signature it refers to" (fun () ->
      let root = package [ ("main.truss", doubling) ] in
      let status, output =
        captured (fun () ->
            Explain_command.run ~directory:root
              ~position:(Filename.concat root "main.truss" ^ ":8:3")
              ~json:false)
      in
      if status <> 0 then fail "status %d" status;
      if
        not
          (contains output "means the definition demo::main::double"
          && contains output "internal fn double(value: Int64) -> Int64")
      then fail "wrote %s" output);
  test "an overlap is told as a sentence about the parts that meet" (fun () ->
      let place path part : Database.place =
        {
          path =
            Some (Path.Top { module_ = { package = "demo"; modules = [ "main" ] }; name = path });
          part = Some part;
          label = "";
        }
      in
      expect_string
        ~expected:
          "this worktree's change to the body of demo::main::four reads the signature of \
           demo::main::double, which the other changes"
        (Overlap_command.sentence
           (Reads
              {
                this_worktree = true;
                change = place "four" "body";
                reads = place "double" "signature";
              })))

(* Registry packages *)

(* A registry in a directory of its own, which commands then use. *)
let registry () =
  let registry = Registry.Index.at (directory []) in
  Registry.Index.configure (Some (Registry.Index.root registry));
  registry

(* Adds a version of a package to a registry: its modules, the packages it
   depends on, each with what it grants, and the versions it was published
   with, which the registry must hold already. *)
let publish registry name version ?(dependencies = []) ?(record = []) modules =
  let manifest =
    manifest_of name
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
           | None -> failwith (dependency ^ " is not in the registry"))
         record)
  in
  Registry.Index.add registry name version
    ((("truss.toml", manifest) :: (if record = [] then [] else [ ("truss.lock", lock) ])) @ modules)

let units text =
  [ ("lengths.truss", Printf.sprintf "public fn meter() -> Int64 {\n  %s\n}\n" text) ]

let geometry =
  [
    ( "vector.truss",
      "use acme::units::lengths\n\npublic fn length() -> Int64 {\n  lengths::meter()\n}\n" );
  ]

(* A registry with [acme::units] at 1.0.0 and 1.1.0, and [acme::geometry]
   1.0.0, published with the first. *)
let stocked () =
  let registry = registry () in
  publish registry "acme::units" (1, 0, 0) (units "1");
  publish registry "acme::units" (1, 1, 0) (units "100");
  publish registry "acme::geometry" (1, 0, 0)
    ~dependencies:[ ("acme::units", []) ]
    ~record:[ ("acme::units", (1, 0, 0)) ]
    geometry;
  registry

let uses_geometry =
  ("main.truss", "use acme::geometry::vector\n\nfn length() -> Int64 {\n  vector::length()\n}\n")

let add root names = quietly (fun () -> Add_command.run ~directory:root ~names ~json:false)
let lock_lines root = String.split_on_char '\n' (String.trim (read root "truss.lock"))

let versions root =
  List.map
    (fun (entry : Registry.Lock.entry) -> (entry.name, Registry.Version.show entry.version))
    (Registry.Lock.parse (read root "truss.lock"))

let expect_versions root expected =
  let found = versions root in
  if found <> expected then
    fail "the lock file has [%s]"
      (String.concat "; " (List.map (fun (name, version) -> name ^ " " ^ version) found))

let clean root = Report.clean (Report.gather (Project.load root))

let () =
  test "adding a package writes its entry, and a line for it and for each package it brings"
    (fun () ->
      let _ = stocked () in
      let root = package [ uses_geometry ] in
      if add root [ "acme::geometry" ] <> 0 then fail "not added";
      if not (contains (read root "truss.toml") "\"acme::geometry\" = []") then
        fail "the manifest is %s" (read root "truss.toml");
      expect_versions root [ ("acme::geometry", "1.0.0"); ("acme::units", "1.0.0") ];
      if not (clean root) then fail "has diagnostics");
  test "a package is added at the version it was published with, and nothing newer" (fun () ->
      let registry = stocked () in
      let root = package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      (* A package published with a newer version of what the build has
         brings that version with it. *)
      publish registry "acme::shapes" (1, 0, 0)
        ~dependencies:[ ("acme::units", []) ]
        ~record:[ ("acme::units", (1, 1, 0)) ]
        [ ("square.truss", "public fn sides() -> Int64 {\n  4\n}\n") ];
      rewrite root "main.truss"
        (snd uses_geometry ^ "\nfn sides() -> Int64 {\n  acme::shapes::square::sides()\n}\n");
      if add root [ "acme::shapes" ] <> 0 then fail "not added";
      expect_versions root
        [ ("acme::geometry", "1.0.0"); ("acme::shapes", "1.0.0"); ("acme::units", "1.1.0") ];
      if not (clean root) then fail "has diagnostics");
  test "a package is added at the version written after @" (fun () ->
      let _ = stocked () in
      let root =
        package [ ("main.truss", "fn meter() -> Int64 {\n  acme::units::lengths::meter()\n}\n") ]
      in
      if add root [ "acme::units@1.0.0" ] <> 0 then fail "not added";
      expect_versions root [ ("acme::units", "1.0.0") ]);
  test "a package the registry does not hold is not added, and the manifest is left as it was"
    (fun () ->
      let _ = stocked () in
      let root = package [ ("main.truss", "") ] in
      let before = read root "truss.toml" in
      (match add root [ "acme::nothing" ] with
      | exception Project.Cannot_run _ -> ()
      | _ -> fail "added");
      expect_string ~expected:before (read root "truss.toml");
      if Sys.file_exists (Filename.concat root "truss.lock") then fail "wrote a lock file");
  test "a dependency with no line in the lock file is a problem that says to add it" (fun () ->
      let _ = stocked () in
      let root =
        directory [ ("truss.toml", manifest_of "demo" ^ "[dependencies]\n\"acme::units\" = []\n") ]
      in
      expect_problem_in root "Run `truss add acme::units`");
  test "a lock file that is not the one the manifests give is a problem, which check --fix fixes"
    (fun () ->
      let _ = stocked () in
      let root = package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      (* Granting a package a capability changes what it holds. *)
      rewrite root "truss.toml"
        (manifest_of "demo" ^ "[dependencies]\n\"acme::geometry\" = [\"Clock\"]\n");
      expect_problem_in root
        "`acme::geometry` is said to hold nothing, and the manifests grant it Clock";
      if quietly (fun () -> Check_command.run ~directory:root ~fix:true ~json:false) <> 0 then
        fail "still has errors";
      if
        not
          (List.exists
             (fun line -> contains line "acme::geometry 1.0.0" && contains line " holds Clock")
             (lock_lines root))
      then fail "the lock file is %s" (read root "truss.lock"));
  test "a line that no package uses is a problem, which check --fix fixes by deleting it" (fun () ->
      let _ = stocked () in
      let root = package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      rewrite root "main.truss" "";
      rewrite root "truss.toml" (manifest_of "demo");
      expect_problem_in root "Nothing in the build uses `acme::geometry`";
      if quietly (fun () -> Check_command.run ~directory:root ~fix:true ~json:false) <> 0 then
        fail "still has errors";
      expect_versions root []);
  test "files in the registry that do not have the lock file's hash are not used" (fun () ->
      let registry = stocked () in
      publish registry "acme::angles" (1, 0, 0) [ ("degrees.truss", "") ];
      let root = package [ ("main.truss", "") ] in
      let hash = Option.get (Registry.Index.hash_of registry "acme::angles" (1, 0, 0)) in
      rewrite root "truss.toml" (manifest_of "demo" ^ "[dependencies]\n\"acme::angles\" = []\n");
      rewrite root "truss.lock" (Printf.sprintf "format 1\nacme::angles 1.0.0 %s\n" hash);
      Out_channel.with_open_bin
        (Filename.concat
           (Registry.Index.version_directory registry "acme::angles" (1, 0, 0))
           "degrees.truss")
        (fun channel -> output_string channel "fn stolen() {}\n");
      expect_problem_in root "do not have the hash the lock file names");
  test "a package that is not in the store cannot be had without a registry" (fun () ->
      let registry = stocked () in
      publish registry "acme::tides" (1, 0, 0) [ ("moon.truss", "") ];
      let root = package [ ("main.truss", "") ] in
      let hash = Option.get (Registry.Index.hash_of registry "acme::tides" (1, 0, 0)) in
      rewrite root "truss.toml" (manifest_of "demo" ^ "[dependencies]\n\"acme::tides\" = []\n");
      rewrite root "truss.lock" (Printf.sprintf "format 1\nacme::tides 1.0.0 %s\n" hash);
      Registry.Index.configure (Some "");
      expect_problem_in root "no registry is set");
  test "a project's package takes the place of the registry's package of its name" (fun () ->
      let _ = stocked () in
      let root =
        directory
          [
            ("truss.toml", "[project]\n");
            ("app/truss.toml", manifest_of "app" ^ "[dependencies]\n\"acme::geometry\" = []\n");
            ("app/main.truss", snd uses_geometry);
            ("units/truss.toml", manifest_of "acme::units");
            ("units/lengths.truss", "public fn meter() -> Int64 {\n  7\n}\n");
          ]
      in
      let app = Filename.concat root "app" in
      if add app [ "acme::geometry" ] <> 0 then fail "not added";
      expect_versions root [ ("acme::geometry", "1.0.0") ];
      if not (clean root) then fail "has diagnostics";
      let project = Project.load root in
      if
        not
          (List.mem "units/lengths.truss"
             (List.map (Database.module_file project.session) (Project.modules project)))
      then fail "the project's package is not the one in the build")

(* Upgrading *)

let upgrade root names = captured (fun () -> Upgrade_command.run ~directory:root ~names ~json:false)

let () =
  test "upgrading moves a package to its newest version and says so" (fun () ->
      let _ = stocked () in
      let root = package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      let status, output = upgrade root [] in
      if status <> 0 then fail "status %d: %s" status output;
      if not (contains output "`acme::units` goes from 1.0.0 to 1.1.0") then fail "said %s" output;
      expect_versions root [ ("acme::geometry", "1.0.0"); ("acme::units", "1.1.0") ]);
  test "upgrading a package that is at its newest version changes nothing" (fun () ->
      let _ = stocked () in
      let root = package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      let before = read root "truss.lock" in
      let status, output = upgrade root [ "acme::geometry" ] in
      if status <> 0 || not (contains output "Every package is at the version asked for") then
        fail "status %d: %s" status output;
      expect_string ~expected:before (read root "truss.lock"));
  test "an upgrade says which signatures the project reads change, and what breaks" (fun () ->
      let registry = stocked () in
      let root =
        package [ ("main.truss", "fn meter() -> Int64 {\n  acme::units::lengths::meter()\n}\n") ]
      in
      ignore (add root [ "acme::units" ]);
      publish registry "acme::units" (1, 2, 0)
        [ ("lengths.truss", "public fn meter(scale: Int64) -> Int64 {\n  scale\n}\n") ];
      let status, output = upgrade root [ "acme::units" ] in
      if status <> 1 then fail "status %d: %s" status output;
      List.iter
        (fun part -> if not (contains output part) then fail "%s is not in: %s" part output)
        [
          "`acme::units` goes from 1.1.0 to 1.2.0";
          "acme::units::lengths::meter";
          "was: public fn meter() -> Int64";
          "now: public fn meter(scale: Int64) -> Int64";
          "read by: demo::main::meter";
          "errors it does not have now";
        ]);
  test "an upgrade says which packages would hold a capability they did not" (fun () ->
      let registry = stocked () in
      let root = package [ uses_geometry ] in
      ignore (add root [ "acme::geometry" ]);
      rewrite root "truss.toml"
        (manifest_of "demo" ^ "[dependencies]\n\"acme::geometry\" = [\"Clock\"]\n");
      ignore (quietly (fun () -> Check_command.run ~directory:root ~fix:true ~json:false));
      publish registry "acme::geometry" (1, 1, 0)
        ~dependencies:[ ("acme::units", [ "Clock" ]) ]
        ~record:[ ("acme::units", (1, 0, 0)) ]
        geometry;
      let _, output = upgrade root [ "acme::geometry" ] in
      if not (contains output "`acme::units` would hold Clock, which it did not") then
        fail "said %s" output)

(* Publishing *)

let publish_from root = captured (fun () -> Publish_command.run ~directory:root ~json:false)

(* A package of its own project, named [acme::angles], with one module. *)
let angles text = directory [ ("truss.toml", manifest_of "acme::angles"); ("degrees.truss", text) ]
let turn = "public fn turn() -> Int64 {\n  360\n}\n"

let published registry name =
  List.map
    (fun (version, _) -> Registry.Version.show version)
    (Registry.Index.versions registry name)

let expect_published registry name expected = expect_strings ~expected (published registry name)

(* Publishes a package and expects it to be refused, with the reason. *)
let expect_refused root part =
  let status, output = publish_from root in
  if status <> 1 then fail "status %d: %s" status output;
  if not (contains output part) then fail "said %s" output

let () =
  test "a package's first version is 1.0.0, and holds its files" (fun () ->
      let registry = registry () in
      let root = angles turn in
      let status, output = publish_from root in
      if status <> 0 then fail "status %d: %s" status output;
      if not (contains output "Published `acme::angles` 1.0.0") then fail "said %s" output;
      expect_published registry "acme::angles" [ "1.0.0" ];
      let files =
        Registry.Content.files ~all:true
          (Registry.Index.version_directory registry "acme::angles" (1, 0, 0))
      in
      expect_strings ~expected:[ "degrees.truss"; "truss.toml" ] (List.map fst files));
  test "a package whose name ends in _v2 starts at 2.0.0" (fun () ->
      let registry = registry () in
      let root =
        directory [ ("truss.toml", manifest_of "acme::angles_v2"); ("degrees.truss", turn) ]
      in
      ignore (publish_from root);
      expect_published registry "acme::angles_v2" [ "2.0.0" ]);
  test "a release that changes only a body gets the next patch number" (fun () ->
      let registry = registry () in
      let root = angles turn in
      ignore (publish_from root);
      rewrite root "degrees.truss" "public fn turn() -> Int64 {\n  180 + 180\n}\n";
      let status, output = publish_from root in
      if status <> 0 then fail "status %d: %s" status output;
      expect_published registry "acme::angles" [ "1.0.0"; "1.0.1" ]);
  test "a release that adds a public definition gets the next minor number, and says what is new"
    (fun () ->
      let registry = registry () in
      let root = angles turn in
      ignore (publish_from root);
      rewrite root "degrees.truss" (turn ^ "\npublic fn half() -> Int64 {\n  180\n}\n");
      let status, output = publish_from root in
      if status <> 0 then fail "status %d: %s" status output;
      if not (contains output "acme::angles::degrees::half is new") then fail "said %s" output;
      expect_published registry "acme::angles" [ "1.0.0"; "1.1.0" ]);
  test "files that are a version already are not published again" (fun () ->
      let registry = registry () in
      let root = angles turn in
      ignore (publish_from root);
      let status, output = publish_from root in
      if status <> 0 || not (contains output "`acme::angles` 1.0.0 is these files already") then
        fail "status %d: %s" status output;
      expect_published registry "acme::angles" [ "1.0.0" ]);
  test "a release that changes a public signature is refused, with the signature as it was and is"
    (fun () ->
      let registry = registry () in
      let root = angles turn in
      ignore (publish_from root);
      rewrite root "degrees.truss" "public fn turn(times: Int64) -> Int64 {\n  times\n}\n";
      expect_refused root "acme::angles::degrees::turn has other parameters or another result";
      let _, output = publish_from root in
      List.iter
        (fun part -> if not (contains output part) then fail "%s is not in: %s" part output)
        [
          "was: public fn turn() -> Int64";
          "now: public fn turn(times: Int64) -> Int64";
          "Publish it under a new name, such as `acme::angles_v2`";
        ];
      expect_published registry "acme::angles" [ "1.0.0" ]);
  test "a release that takes a public definition away is refused" (fun () ->
      let _ = registry () in
      let root = angles (turn ^ "\npublic fn half() -> Int64 {\n  180\n}\n") in
      ignore (publish_from root);
      rewrite root "degrees.truss" turn;
      expect_refused root "acme::angles::degrees::half is gone, or is no longer public");
  test "a private definition can change freely" (fun () ->
      let registry = registry () in
      let root = angles (turn ^ "\nfn half() -> Int64 {\n  180\n}\n") in
      ignore (publish_from root);
      rewrite root "degrees.truss" (turn ^ "\nfn third(of: Int64) -> Int64 {\n  of\n}\n");
      let status, output = publish_from root in
      if status <> 0 then fail "status %d: %s" status output;
      expect_published registry "acme::angles" [ "1.0.0"; "1.0.1" ]);
  test "a package with no owner in its name is not published" (fun () ->
      let _ = registry () in
      match publish_from (package [ ("degrees.truss", turn) ]) with
      | exception Project.Cannot_run message ->
          if not (contains message "has no owner in its name") then fail "said %s" message
      | _ -> fail "published");
  test "a package with an error is not published" (fun () ->
      let _ = registry () in
      expect_refused
        (angles "public fn turn() -> Int64 {\n  true\n}\n")
        "A package is published only when it has no errors");
  test "a package with a todo or an echo is not published, and each is listed" (fun () ->
      let registry = registry () in
      let root =
        angles
          "public fn turn() -> Int64 {\n  todo\n}\n\npublic fn half() -> Int64 {\n  echo 180\n}\n"
      in
      expect_refused root "degrees.truss:2:3: `todo` is not finished code";
      expect_refused root "degrees.truss:6:3: `echo` is not finished code";
      expect_published registry "acme::angles" []);
  test "a package whose test fails is not published" (fun () ->
      let registry = registry () in
      let root =
        angles (turn ^ "\ntest \"a turn is a right angle\" {\n  assert turn() == 90\n}\n")
      in
      expect_refused root "A package is published only when its tests pass";
      expect_published registry "acme::angles" []);
  test "a package whose tests pass is published" (fun () ->
      let registry = registry () in
      let root = angles (turn ^ "\ntest \"a turn is whole\" {\n  assert turn() == 360\n}\n") in
      let status, output = publish_from root in
      if status <> 0 then fail "status %d: %s" status output;
      expect_published registry "acme::angles" [ "1.0.0" ])

(* What a package is published with *)

let () =
  test "a package is published with the versions of the packages its code uses" (fun () ->
      let registry = stocked () in
      let root =
        directory
          [
            ("truss.toml", manifest_of "acme::walls");
            ( "height.truss",
              "use acme::geometry::vector\n\npublic fn height() -> Int64 {\n  vector::length()\n}\n"
            );
          ]
      in
      ignore (add root [ "acme::geometry" ]);
      let status, output = publish_from root in
      if status <> 0 then fail "status %d: %s" status output;
      let record =
        Registry.Lock.parse
          (In_channel.with_open_bin
             (Filename.concat
                (Registry.Index.version_directory registry "acme::walls" (1, 0, 0))
                "truss.lock")
             In_channel.input_all)
      in
      match record with
      | [
       { name = "acme::geometry"; version = 1, 0, 0; holds = []; _ };
       { name = "acme::units"; version = 1, 0, 0; holds = []; _ };
      ] ->
          ()
      | _ -> fail "published with other versions");
  test "a published package is used by another project, with what it was published with" (fun () ->
      let _ = stocked () in
      let walls =
        directory
          [
            ("truss.toml", manifest_of "acme::walls");
            ( "height.truss",
              "use acme::geometry::vector\n\npublic fn height() -> Int64 {\n  vector::length()\n}\n"
            );
          ]
      in
      ignore (add walls [ "acme::geometry" ]);
      ignore (publish_from walls);
      let root =
        package [ ("main.truss", "fn tall() -> Int64 {\n  acme::walls::height::height()\n}\n") ]
      in
      if add root [ "acme::walls" ] <> 0 then fail "not added";
      expect_versions root
        [ ("acme::geometry", "1.0.0"); ("acme::units", "1.0.0"); ("acme::walls", "1.0.0") ];
      if not (clean root) then fail "has diagnostics");
  test "a dependency that only a package's tests use is not one of what it is published with"
    (fun () ->
      let registry = stocked () in
      let root =
        directory
          [
            ("truss.toml", manifest_of "acme::walls");
            ( "height.truss",
              "public fn height() -> Int64 {\n\
              \  3\n\
               }\n\n\
               test \"a wall is taller than a meter\" {\n\
              \  assert height() > acme::units::lengths::meter()\n\
               }\n" );
          ]
      in
      ignore (add root [ "acme::units@1.0.0" ]);
      let status, output = publish_from root in
      if status <> 0 then fail "status %d: %s" status output;
      if
        Sys.file_exists
          (Filename.concat
             (Registry.Index.version_directory registry "acme::walls" (1, 0, 0))
             "truss.lock")
      then fail "published with a package only its test uses";
      let user =
        package [ ("main.truss", "fn tall() -> Int64 {\n  acme::walls::height::height()\n}\n") ]
      in
      ignore (add user [ "acme::walls" ]);
      expect_versions user [ ("acme::walls", "1.0.0") ];
      if not (clean user) then fail "has diagnostics");
  test "a package that depends on one of its project's that is not published is refused" (fun () ->
      let _ = registry () in
      let root =
        directory
          [
            ("truss.toml", "[project]\n");
            ("angles/truss.toml", manifest_of "acme::angles");
            ("angles/degrees.truss", turn);
            ( "walls/truss.toml",
              manifest_of "acme::walls" ^ "[dependencies]\n\"acme::angles\" = []\n" );
            ( "walls/corner.truss",
              "public fn corner() -> Int64 {\n  acme::angles::degrees::turn()\n}\n" );
          ]
      in
      let walls = Filename.concat root "walls" in
      expect_refused walls "publish `acme::angles` first";
      (* Once it is published, the project's copy is that version. *)
      ignore (publish_from (Filename.concat root "angles"));
      let status, output = publish_from walls in
      if status <> 0 then fail "status %d: %s" status output)

(* The command line as a whole *)

let () =
  test "a command line is parsed and run as the client would run it" (fun () ->
      let root = package [ ("main.truss", doubling) ] in
      let outcome, _ = captured (fun () -> Main.evaluate [ "check"; "-C"; root ]) in
      if outcome <> Outcome.Exit 0 then fail "did not succeed");
  test "an unknown command is a bad argument" (fun () ->
      let outcome, _ = captured (fun () -> Main.evaluate [ "bogus" ]) in
      if outcome <> Outcome.Exit 2 then fail "did not exit with 2")

(* Making a package *)

let () =
  test "a name that is not a package's makes nothing" (fun () ->
      let root = directory [] in
      List.iter
        (fun name ->
          match New_command.run ~directory:root ~name with
          | exception Project.Cannot_run _ -> ()
          | _ -> fail "made %s" name)
        [ "Weather"; "weather__x"; "1st"; ""; "a::b::c" ]);
  test "a new package with an owner is made in a directory named without it" (fun () ->
      let root = directory [] in
      if quietly (fun () -> New_command.run ~directory:root ~name:"acme::weather") <> 0 then
        fail "not made";
      let project = Project.load (Filename.concat root "weather") in
      expect_strings ~expected:[ "acme::weather" ] (names project);
      if not (Report.clean (Report.gather ~proofs:true project)) then fail "has diagnostics");
  test "a new package checks cleanly" (fun () ->
      let root = directory [] in
      if quietly (fun () -> New_command.run ~directory:root ~name:"weather") <> 0 then
        fail "not made";
      let project = Project.load (Filename.concat root "weather") in
      if not (Report.clean (Report.gather ~proofs:true project)) then fail "has diagnostics")

(* The language server *)

let () =
  test "JSON with escapes and a surrogate pair is read" (fun () ->
      match Json.parse {|{"a": [1, -2, true, null], "b": "x\né😀"}|} with
      | Json.Object [ ("a", Json.List [ Int 1; Int -2; Bool true; Null ]); ("b", String text) ] ->
          expect_string ~expected:"x\n\xc3\xa9\xf0\x9f\x98\x80" text
      | _ -> fail "not read");
  test "a position counts UTF-16 code units, and an offset is its inverse" (fun () ->
      let text = "a\n\xf0\x9f\x98\x80b" in
      let offset = String.length text - 1 in
      (match Lsp_command.position Utf_16 text offset with
      | 1, 2 -> ()
      | line, column -> fail "line %d, column %d" line column);
      if Lsp_command.offset Utf_16 text ~line:1 ~column:2 <> offset then fail "not the inverse");
  test "an open file's text is checked in place of the file on disk" (fun () ->
      let root =
        package
          [
            ("main.truss", "fn main(arguments: List[String]) -> ExitCode {\n  ExitCode.success\n}\n");
          ]
      in
      let uri = "file://" ^ Filename.concat root "main.truss" in
      let answer =
        quietly (fun () ->
            Lsp_command.check ~root Utf_16
              [ (uri, "fn next(count: UInt8) -> UInt8 {\n  count + 1\n}\n") ])
      in
      match Json.field "files" answer with
      | Json.List [ file ] -> (
          match (Json.field "diagnostics" file, Json.field "states" file) with
          | Json.List [ diagnostic ], Json.List [ state ] ->
              if Json.field "code" diagnostic <> Json.String "prover.overflow" then
                fail "diagnostic %s" (Json.to_string diagnostic);
              if Json.field "proven" state <> Json.Bool false then
                fail "state %s" (Json.to_string state);
              if
                Json.field "range" diagnostic
                <> Json.Object
                     [
                       ("start", Json.Object [ ("line", Json.Int 1); ("character", Json.Int 2) ]);
                       ("end", Json.Object [ ("line", Json.Int 1); ("character", Json.Int 11) ]);
                     ]
              then fail "range %s" (Json.to_string (Json.field "range" diagnostic))
          | _ -> fail "%s" (Json.to_string file))
      | _ -> fail "%s" (Json.to_string answer));
  test "the server answers initialize, an unsupported request, and shutdown" (fun () ->
      let message body = Printf.sprintf "Content-Length: %d\r\n\r\n%s" (String.length body) body in
      let input_file = Filename.temp_file "lsp-input" ""
      and output_file = Filename.temp_file "lsp-output" "" in
      Out_channel.with_open_bin input_file (fun channel ->
          List.iter
            (fun body -> output_string channel (message body))
            [
              {|{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"rootUri":"file:///project","capabilities":{"general":{"positionEncodings":["utf-8"]}}}}|};
              {|{"jsonrpc":"2.0","id":2,"method":"textDocument/hover","params":{}}|};
              {|{"jsonrpc":"2.0","id":3,"method":"shutdown"}|};
              {|{"jsonrpc":"2.0","method":"exit"}|};
            ]);
      let status =
        In_channel.with_open_bin input_file (fun input ->
            Out_channel.with_open_bin output_file (fun output ->
                Lsp_command.serve ~input ~output ~check:(fun ~root:_ _ _ -> None)))
      in
      let written = In_channel.with_open_bin output_file In_channel.input_all in
      if status <> 0 then fail "status %d" status;
      List.iter
        (fun part -> if not (contains written part) then fail "no %s in %s" part written)
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
        Lsp_command.create ~write:(fun value -> written := Json.to_string value :: !written) ~check
      in
      let handle text = ignore (Lsp_command.handle server (Json.parse text)) in
      handle
        {|{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"rootUri":"file:///project"}}|};
      handle
        {|{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///project/a%20b.truss","text":"x"}}}|};
      Lsp_command.refresh server;
      (match !asked with
      | [ ("/project", Utf_16, [ ("file:///project/a%20b.truss", "x") ]) ] -> ()
      | _ -> fail "asked %d times, or with other buffers" (List.length !asked));
      handle
        {|{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///project/a%20b.truss"}}}|};
      Lsp_command.refresh server;
      let all = String.concat "\n" (List.rev !written) in
      List.iter
        (fun part -> if not (contains all part) then fail "no %s in %s" part all)
        [
          {|"method":"textDocument/publishDiagnostics"|};
          {|"method":"truss/proofStates"|};
          {|"params":{"uri":"file:///project/a%20b.truss","diagnostics":[]}|};
        ];
      if List.length !asked <> 1 then fail "a check with no open file")

let () = Harness.finish ()
