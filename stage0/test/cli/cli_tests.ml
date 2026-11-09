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
  test "a directory above several packages is about all of them" (fun () ->
      let root =
        directory
          [
            ("one/truss.toml", "[package]\nname = \"one\"\n");
            ("two/truss.toml", "[package]\nname = \"two\"\n");
          ]
      in
      expect_strings ~expected:[ "one"; "two" ] (names (Project.load root)));
  test "a directory with its own manifest is another package's, not modules of this one" (fun () ->
      let root =
        package
          [
            ("main.truss", "");
            ("vendor/truss.toml", "[package]\nname = \"other\"\n");
            ("vendor/x.truss", "");
          ]
      in
      let project = Project.load root in
      expect_strings ~expected:[ "demo::main"; "other::x" ]
        (List.sort compare (List.map Path.show_module (Project.modules project))));
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
  Compile.create project.context Memory_layout.target_64
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
  {|internal fn double(value: Int64) -> Int64 {
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

let () =
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
              ~position:(Filename.concat root "main.truss" ^ ":6:3")
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
      if not (Report.clean (Report.gather project)) then fail "has diagnostics")

let () = Harness.finish ()
