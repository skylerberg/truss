(* The command line's tests. Each gives a small package or input and states
   one fact about what a command makes of it. See CLI.md and
   IMPLEMENTATION.md, "Testing". *)

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

let manifest = ("truss.toml", "[package]\nname = \"demo\"\n")
let package files = directory (manifest :: files)
let read root path = In_channel.with_open_bin (Filename.concat root path) In_channel.input_all

(* Runs [f] with its standard output and error sent nowhere, so a command
   under test prints nothing. *)
let quietly f =
  let null = Unix.openfile "/dev/null" [ O_WRONLY ] 0 in
  let saved_out = Unix.dup Unix.stdout and saved_err = Unix.dup Unix.stderr in
  flush stdout;
  flush stderr;
  Unix.dup2 null Unix.stdout;
  Unix.dup2 null Unix.stderr;
  Fun.protect
    ~finally:(fun () ->
      flush stdout;
      flush stderr;
      Unix.dup2 saved_out Unix.stdout;
      Unix.dup2 saved_err Unix.stderr;
      Unix.close null;
      Unix.close saved_out;
      Unix.close saved_err)
    f

let module_ modules : Path.module_ = { package = "demo"; modules }

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

let () =
  test "the package is found from a directory below its manifest" (fun () ->
      let root = package [ ("forecast/hourly.truss", "") ] in
      expect_string ~expected:root (Project.find (Filename.concat root "forecast")));
  test "a directory with no manifest above it cannot run a command" (fun () ->
      let root = directory [ ("main.truss", "") ] in
      (* The temporary directory is not inside a package. *)
      match Project.find root with
      | exception Project.Cannot_run _ -> ()
      | found -> fail "found %s" found);
  test "a directory with its own manifest is another package's, not modules of this one" (fun () ->
      let root =
        package
          [
            ("main.truss", "");
            ("vendor/truss.toml", "[package]\nname = \"other\"\n");
            ("vendor/x.truss", "");
          ]
      in
      expect_strings ~expected:[ "demo::main" ]
        (List.map Path.show_module (Project.modules (Project.load root))));
  test "a directory whose name starts with a dot is not read" (fun () ->
      let root = package [ ("main.truss", ""); (".hidden/x.truss", "") ] in
      expect_strings ~expected:[ "demo::main" ]
        (List.map Path.show_module (Project.modules (Project.load root))));
  test "a path is shown relative to the directory it is read from" (fun () ->
      expect_string ~expected:"../weather/forecast.truss"
        (Project.relative ~from:"/code/app" "/code/weather/forecast.truss"))

(* The manifest's time limit *)

let () =
  test "a manifest's [test] time_limit gives each test's limit in seconds" (fun () ->
      let manifest =
        Type_checker.Manifest.parse "[package]\nname = \"a\"\n[test]\ntime_limit = 3\n"
      in
      if manifest.time_limit <> 3 then fail "got %d" manifest.time_limit);
  test "a manifest without a time limit gives tests 10 seconds" (fun () ->
      let manifest = Type_checker.Manifest.parse "[package]\nname = \"a\"\n" in
      if manifest.time_limit <> 10 then fail "got %d" manifest.time_limit);
  test "a time limit of 0 is malformed, at its line" (fun () ->
      match Type_checker.Manifest.parse "[package]\nname = \"a\"\n[test]\ntime_limit = 0\n" with
      | exception Type_checker.Manifest.Malformed (4, _) -> ()
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
              "fn twice(value: Int64) -> Int64 {\n  let unused = value\n  value * 2\n}\n" );
          ]
      in
      let status = quietly (fun () -> Check_command.run ~directory:root ~fix:true ~json:false) in
      if status <> 0 then fail "status %d" status;
      if not (contains (read root "main.truss") "let _ = value") then
        fail "wrote %s" (read root "main.truss"))

(* The test runner's report *)

let () =
  test "a report's records come back in the order of the tests, however they ended" (fun () ->
      let records =
        Compile.parse_report
          "start 0\nstart 1\nmessage 4\nboom\ntest 1 panicked 30\ntest 0 passed 12\n"
      in
      match records with
      | [
       { outcome = Passed; microseconds = 12; _ }; { outcome = Panicked; message = Some "boom"; _ };
      ] ->
          ()
      | _ -> fail "read %d records differently" (List.length records));
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
            (List.map (fun (name, ty) -> name ^ ": " ^ Option.value ty ~default:"?") hole.in_scope)
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
        Compile.unshippable (Compiler.lowering_only project)
          ~main:(List.hd (Program_command.mains project))
          ~echo:false
      with
      | Ok [ { failure = `Todo; line = 6; way; _ } ] ->
          expect_strings
            ~expected:[ "demo::main::main"; "demo::main::helper" ]
            (List.map Path.show way)
      | Ok found -> fail "found %d" (List.length found)
      | Error message -> fail "%s" message);
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
      let compile = Compiler.lowering_only project in
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

(* Impact *)

(* A database of the package with these files in place of its own, as the
   package was at an earlier revision. *)
let earlier files =
  let database = Query.create () in
  Type_checker.load_standard database;
  Type_checker.load_package database ~name:"demo" ~dependencies:[]
    (List.map (fun (name, text) -> (module_ [ Filename.chop_suffix name ".truss" ], text)) files);
  database

let () =
  test "a change to a body alone is a change of the body" (fun () ->
      let before = [ ("main.truss", "fn double(value: Int64) -> Int64 {\n  value * 2\n}\n") ] in
      let project =
        Project.load
          (package [ ("main.truss", "fn double(value: Int64) -> Int64 {\n  value + value\n}\n") ])
      in
      match Impact_command.compare_with project (earlier before) with
      | [ { status = `Changed [ Body ]; read_by = []; _ } ] -> ()
      | changes -> fail "found %d changes" (List.length changes));
  test "a changed interface lists what reads it" (fun () ->
      let before =
        [
          ( "main.truss",
            "fn double(value: Int64) -> Int64 {\n\
            \  value * 2\n\
             }\n\n\
             fn four() -> Int64 {\n\
            \  double(2)\n\
             }\n" );
        ]
      in
      let project =
        Project.load
          (package
             [
               ( "main.truss",
                 "fn double(value: Int64, by: Int64 = 2) -> Int64 {\n\
                 \  value * by\n\
                  }\n\n\
                  fn four() -> Int64 {\n\
                 \  double(2)\n\
                  }\n" );
             ])
      in
      match Impact_command.compare_with project (earlier before) with
      | [ { status = `Changed kinds; read_by; _ } ] ->
          if not (List.mem Impact_command.Interface kinds) then fail "not an interface change";
          expect_strings ~expected:[ "demo::main::four" ] (List.map Path.show read_by)
      | changes -> fail "found %d changes" (List.length changes));
  test "moving a definition within its file changes nothing" (fun () ->
      let one = "fn one() -> Int64 {\n  1\n}\n" and two = "fn two() -> Int64 {\n  2\n}\n" in
      let project = Project.load (package [ ("main.truss", two ^ "\n" ^ one) ]) in
      match Impact_command.compare_with project (earlier [ ("main.truss", one ^ "\n" ^ two) ]) with
      | [] -> ()
      | changes -> fail "found %d changes" (List.length changes))

(* Making a package *)

let () =
  test "a package's name must be a lower_snake_case name" (fun () ->
      if
        List.map New_command.valid_name
          [ "weather"; "weather_report"; "Weather"; "weather__x"; "1st"; "" ]
        <> [ true; true; false; false; false; false ]
      then fail "judged differently");
  test "a new package checks cleanly" (fun () ->
      let root = directory [] in
      if quietly (fun () -> New_command.run ~directory:root ~name:"weather") <> 0 then
        fail "not made";
      let project = Project.load (Filename.concat root "weather") in
      if Report.gather project <> [] then fail "has diagnostics")

let () = Harness.finish ()
