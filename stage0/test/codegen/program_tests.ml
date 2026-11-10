(* Test results kept by key, the checks in place of proofs, and whole programs. *)

open Memory_layout
open Codegen_support

(* Test results kept by key *)

let () =
  test "a passing test's result is kept by its key, and only a changed test runs again" (fun () ->
      incr counter;
      let table = Hashtbl.create 4 in
      let results : Compile.results =
        { find = Hashtbl.find_opt table; add = (fun key value -> Hashtbl.replace table key value) }
      in
      let run text =
        let database, compile = load text in
        match Compile.run_tests ~results compile ~time_limit:2000 (tests_of database) with
        | Ok records ->
            ( (if List.for_all (fun (r : Compile.record) -> r.outcome = Passed) records then 0 else 1),
              render_records records )
        | Error message -> failwith message
      in
      let kept () = Hashtbl.length table in
      let source =
        {|test "passes" {
  assert 1 + 1 == 2
}

test "fails" {
  assert 1 + 1 == 3
}
|}
      in
      let first = run source in
      expect_int ~expected:1 (kept ());
      let second = run source in
      if first <> second then fail "the report changed when kept:\n%s\n%s" (snd first) (snd second);
      expect_int ~expected:1 (fst second);
      let _ = run {|test "passes" {
  assert 2 + 2 == 4
}
|} in
      expect_int ~expected:2 (kept ()))

let () =
  test "an external test gets the real capabilities it uses, and its result is never kept"
    (fun () ->
      let table = Hashtbl.create 4 in
      let results : Compile.results =
        { find = Hashtbl.find_opt table; add = (fun key value -> Hashtbl.replace table key value) }
      in
      let database, compile =
        load {|test "reads the clock"
  uses Clock
{
  let _ = Clock.now()
}
|}
      in
      let run () =
        match Compile.run_tests ~results compile ~time_limit:2000 (tests_of database) with
        | Ok records -> records
        | Error message -> failwith message
      in
      ignore (run ());
      match run () with
      | [ { outcome = Passed; cached = false; _ } ] ->
          if Hashtbl.length table > 0 then fail "kept a result"
      | _ -> fail "did not pass, or came from the kept results")

(* Checks a build makes in place of proofs *)

let () =
  test "a build checks requires clauses, overflow, and division, which stage0 cannot prove"
    (fun () ->
      let output =
        run_source
          {|test "overflow" {
  let big: Int64 = 9223372036854775807
  let _ = big + 1
}

test "division" {
  let zero: Int64 = 0
  let _ = 5 / zero
}

test "index" {
  let items: List[Int64] = [1, 2]
  let _ = items[2]
}

test "fine" {
  let items: List[Int64] = [1, 2]
  assert items[1] + 1 == 3
}
|}
      in
      let contains text =
        let n = String.length text and m = String.length output in
        let rec go i = i + n <= m && (String.sub output i n = text || go (i + 1)) in
        if not (go 0) then fail "%S is not in the output:\n%s" text output
      in
      List.iter contains
        [
          "test 0 panicked\n";
          "arithmetic overflow\n";
          "test 1 panicked\n";
          "division by zero\n";
          "test 2 panicked\n";
          "requirement not met: requires key < self.length()\n";
          "test 3 passed\n";
        ])

(* Programs *)

let () =
  test "a program prints through the real console and exits with its code" (fun () ->
      let status, output, _ =
        run_main ~arguments:[ "one"; "two" ]
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  Console.print_line("hello")
  Console.print_line("${arguments.length()} arguments, then ${arguments[1]}")
  ExitCode(3)
}
|}
      in
      expect_int ~expected:3 status;
      expect_string ~expected:"hello\n3 arguments, then one\n" output)

let () =
  test "a program writes a file, reads it back, and reports a missing one" (fun () ->
      let path = Filename.concat (Lazy.force scratch) "written.txt" in
      let status, output, _ =
        run_main ~arguments:[ path ]
          {|use standard::files

fn main(arguments: List[String]) -> ExitCode
  uses Console, FileRead, FileWrite, Handles
{
  let path = Path.new(arguments[1].slice())
  if FileWrite.write_text(path, contents: "first\nsecond line\nlast".slice()) is Err(_) {
    return ExitCode(1)
  }
  if FileRead.read_text(path) is Ok(text) {
    Console.print_line("${text.length()} bytes".slice())
  }
  let streamed = Path.new("${arguments[1]}.streamed".slice())
  let wrote = files::write_with(streamed, write: fn(writer) {
    mut writer.write("one ".slice())?
    mut writer.write_line("two".slice())?
    mut writer.write_bytes("three".slice().bytes())
  })
  if wrote is Ok(_) && FileRead.read_text(streamed) is Ok(text) {
    Console.print_line("streamed ${text}".slice())
  }
  match FileRead.open(path) {
    Ok(file) => {
      var reader = own file
      if mut reader.read_line() is Ok(Some(line)) {
        Console.print_line("${line}".slice())
      }
      if mut reader.read_line() is Ok(Some(line)) {
        Console.print_line("${line}".slice())
      }
    }
    Err(_) => {}
  }
  if FileRead.read_text(Path.new("/nonexistent/truss".slice())) is Err(NotFound) {
    Console.print_line("missing".slice())
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"22 bytes\nstreamed one two\nthree\nfirst\nsecond line\nmissing\n"
        output)

let () =
  test "a program opens a file to update it, writes and reads at offsets, and closes it" (fun () ->
      let path = Filename.concat (Lazy.force scratch) "updated.bin" in
      let status, output, _ =
        run_main ~arguments:[ path ]
          {|use standard::files
use standard::streams

fn report(label: String, outcome: Result[USize, SystemError]) uses Console {
  match outcome {
    Ok(count) => Console.print_line("${label} ${count}".slice())
    Err(_) => Console.print_line("${label} failed".slice())
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, FileRead, FileWrite, Handles
{
  let path = Path.new(arguments[1].slice())
  var file = match FileWrite.open(path, mode: files::WriteMode.Update) {
    Ok(file) => own file
    Err(_) => {
      return ExitCode(1)
    }
  }
  let hello_world: List[UInt8] = [104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100]
  let there: List[UInt8] = [116, 104, 101, 114, 101]
  report("wrote", outcome: mut file.write(hello_world.slice()))
  report("wrote at", outcome: mut file.write_at(6, bytes: there.slice()))
  var read: List[UInt8] = []
  report("read at", outcome: mut file.read_at(0, buffer: mut read, limit: 5))
  report("read at again", outcome: mut file.read_at(6, buffer: mut read, limit: 100))
  Console.print_line("${read.length()} bytes read".slice())
  if mut file.seek(streams::Position.FromEnd(offset: -5)) is Ok(position) {
    Console.print_line("at ${position}".slice())
  }
  var tail: List[UInt8] = []
  report("read", outcome: mut file.read(mut tail, limit: 100))
  if mut file.set_length(4) is Ok(_) && mut file.synchronize() is Ok(_) {
    Console.print_line("shortened".slice())
  }
  if own file.close() is Ok(_) {
    Console.print_line("closed".slice())
  }
  if FileRead.read_text(path) is Ok(text) {
    Console.print_line("now ${text}".slice())
  }
  if FileWrite.open(path, mode: files::WriteMode.CreateNew) is Err(AlreadyExists) {
    Console.print_line("exists".slice())
  }
  match FileWrite.open(path, mode: files::WriteMode.Append) {
    Ok(appended) => {
      var appending = own appended
      let mark: List[UInt8] = [33]
      report("appended", outcome: mut appending.write(mark.slice()))
    }
    Err(_) => {}
  }
  if FileRead.read_text(path) is Ok(text) {
    Console.print_line("then ${text}".slice())
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string
        ~expected:
          "wrote 11\n\
           wrote at 5\n\
           read at 5\n\
           read at again 5\n\
           10 bytes read\n\
           at 6\n\
           read 5\n\
           shortened\n\
           closed\n\
           now hell\n\
           exists\n\
           appended 1\n\
           then hell!\n"
        output)

let () =
  test "a program reads the metadata of a file, of a directory, and of an open file" (fun () ->
      let directory = Lazy.force scratch in
      let path = Filename.concat directory "measured.txt" in
      let status, output, _ =
        run_main ~arguments:[ directory; path ]
          {|use standard::files

fn main(arguments: List[String]) -> ExitCode
  uses Console, FileRead, FileWrite, Handles
{
  let directory = Path.new(arguments[1].slice())
  let file = Path.new(arguments[2].slice())
  if FileWrite.write_text(file, contents: "twelve bytes".slice()) is Err(_) {
    return ExitCode(1)
  }
  match FileRead.metadata(file, follow_links: true) {
    Ok(metadata) => {
      Console.print_line("file ${metadata.is_file()} ${metadata.length}".slice())
      Console.print_line("recent ${metadata.modified.unix_nanoseconds() > 1577836800000000000}".slice())
      Console.print_line("accessed ${metadata.accessed.is_some()}".slice())
      Console.print_line("owner can write ${!metadata.permissions.is_read_only()}".slice())
    }
    Err(_) => Console.print_line("no file".slice())
  }
  match FileRead.metadata(directory, follow_links: false) {
    Ok(metadata) => {
      Console.print_line("directory ${metadata.is_directory()} ${metadata.is_file()}".slice())
    }
    Err(_) => Console.print_line("no directory".slice())
  }
  if FileRead.metadata(Path.new("/nonexistent/truss".slice()), follow_links: true) is Err(NotFound) {
    Console.print_line("missing".slice())
  }
  match FileWrite.open(file, mode: files::WriteMode.Update) {
    Ok(opened) => {
      if opened.metadata() is Ok(metadata) {
        Console.print_line("open ${metadata.length}".slice())
      }
    }
    Err(_) => {}
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string
        ~expected:
          "file true 12\n\
           recent true\n\
           accessed true\n\
           owner can write true\n\
           directory true false\n\
           missing\n\
           open 12\n"
        output)

let () =
  test "a program makes a directory, renames, links, sets permissions and times, and removes"
    (fun () ->
      let status, output, _ =
        run_main
          ~arguments:[ Lazy.force scratch ]
          {|use standard::files

fn say(text: String) uses Console {
  Console.print_line(text.slice())
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, FileRead, FileWrite, Handles, Clock
{
  let directory = Path.new("${arguments[1]}/made".slice())
  let file = Path.new("${arguments[1]}/made/first.txt".slice())
  let renamed = Path.new("${arguments[1]}/made/second.txt".slice())
  let symbolic = Path.new("${arguments[1]}/made/link".slice())
  let hard = Path.new("${arguments[1]}/made/hard.txt".slice())
  if FileWrite.create_directory(directory) is Ok(_) {
    say("made")
  }
  if FileWrite.create_directory(directory) is Err(AlreadyExists) {
    say("exists")
  }
  if FileWrite.write_text(file, contents: "contents".slice()) is Err(_) {
    return ExitCode(1)
  }
  if FileWrite.rename(file, to: renamed) is Ok(_) && FileRead.metadata(file) is Err(NotFound) {
    say("renamed")
  }
  if FileWrite.link(renamed, link: symbolic, kind: files::LinkKind.Symbolic) is Ok(_) {
    if FileRead.metadata(symbolic, follow_links: false) is Ok(metadata) {
      say("symbolic ${metadata.kind == files::FileKind.SymbolicLink}")
    }
    if FileRead.read_link(symbolic) is Ok(target) && FileRead.read_text(target) is Ok(text) {
      say("target holds ${text}")
    }
    if FileRead.resolve(symbolic) is Ok(resolved) && FileRead.metadata(resolved, follow_links: false) is Ok(metadata) {
      say("resolved to a file ${metadata.is_file()}")
    }
  }
  if FileWrite.link(renamed, link: hard, kind: files::LinkKind.Hard) is Ok(_) && FileRead.read_text(hard) is Ok(text) {
    say("hard ${text}")
  }
  if FileWrite.set_modified(renamed, time: Instant.from_unix_nanoseconds(1000000000123456789)) is Ok(_) {
    if FileRead.metadata(renamed) is Ok(metadata) {
      say("modified ${metadata.modified.unix_nanoseconds()}")
    }
  }
  if FileWrite.set_permissions(renamed, permissions: files::Permissions.from_mode(0o444)) is Ok(_) {
    if FileRead.metadata(renamed) is Ok(metadata) {
      say("read only ${metadata.permissions.is_read_only()}")
    }
  }
  if FileWrite.remove(directory) is Err(DirectoryNotEmpty) {
    say("not empty")
  }
  if FileWrite.remove(symbolic) is Ok(_) && FileWrite.remove(hard) is Ok(_) && FileWrite.remove(renamed) is Ok(_) {
    say("emptied")
  }
  if FileWrite.remove(directory) is Ok(_) && FileRead.metadata(directory) is Err(NotFound) {
    say("removed")
  }
  let before = Clock.monotonic()
  Clock.sleep(Duration.nanoseconds(20000000))
  let after = Clock.monotonic()
  say("slept ${after.total_nanoseconds() - before.total_nanoseconds() >= 20000000}")
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string
        ~expected:
          "made\n\
           exists\n\
           renamed\n\
           symbolic true\n\
           target holds contents\n\
           resolved to a file true\n\
           hard contents\n\
           modified 1000000000123456789\n\
           read only true\n\
           not empty\n\
           emptied\n\
           removed\n\
           slept true\n"
        output)

let () =
  test "a program reads its variables, directory, platform, locations, and time zone" (fun () ->
      let home = Lazy.force scratch in
      Unix.putenv "TRUSS_TEST_MARK" "first=second";
      Unix.putenv "HOME" home;
      Unix.putenv "TMPDIR" "";
      Unix.putenv "XDG_CACHE_HOME" "/caches";
      Unix.putenv "TZ" ":Europe/Paris";
      let status, output, _ =
        run_main
          {|use standard::environment

fn say(text: String) uses Console {
  Console.print_line(text.slice())
}

fn shown(path: Option[Path]) -> String {
  if path is Some(found) && found.text() is Some(text) { "${text}" } else { "none".copy() }
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, Environment, FileRead
{
  var marked = 0
  for variable in Environment.variables() {
    if variable.name == "TRUSS_TEST_MARK" {
      say("${variable.name} is ${variable.value}")
      marked += 1
    }
  }
  say("marked ${marked}")
  if Environment.variable("TRUSS_TEST_MARK".slice()) is Some(value) {
    say("read ${value}")
  }
  if Environment.current_directory() is Ok(directory) {
    say("in ${shown(Some(directory.copy()))}")
  }
  let platform = Environment.platform()
  let known = platform.operating_system == environment::OperatingSystem.Linux
    || platform.operating_system == environment::OperatingSystem.MacOs
  say("system known ${known}, processors ${platform.processor_count > 0}")
  say("host named ${!platform.host_name.is_empty()}, process ${platform.process_identifier > 1}")
  say("home ${shown(Environment.location(environment::Location.Home))}")
  say("temporary ${shown(Environment.location(environment::Location.Temporary))}")
  if Environment.location(environment::Location.Executable) is Some(program)
    && FileRead.metadata(program) is Ok(metadata)
  {
    say("executable is a file ${metadata.is_file()}")
  }
  if platform.operating_system == environment::OperatingSystem.Linux {
    say("cache ${shown(Environment.location(environment::Location.Cache))}")
  } else {
    say("cache /caches")
  }
  say("data set ${Environment.location(environment::Location.Data) is Some(_)}")
  if Environment.local_zone() is Some(zone) {
    say("zone ${zone}")
  }
  if Environment.zone_rules("UTC".slice()) is Some(rules) && rules.length() > 4 {
    say("rules start ${rules[0]} ${rules[1]} ${rules[2]} ${rules[3]}")
  }
  say("outside ${Environment.zone_rules("../../../etc/hosts".slice()) is Some(_)}")
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string
        ~expected:
          (String.concat "\n"
             [
               "TRUSS_TEST_MARK is first=second";
               "marked 1";
               "read first=second";
               "in " ^ Sys.getcwd ();
               "system known true, processors true";
               "host named true, process true";
               "home " ^ home;
               "temporary /tmp";
               "executable is a file true";
               "cache /caches";
               "data set true";
               "zone Europe/Paris";
               "rules start 84 90 105 102";
               "outside false";
               "";
             ])
        output)

let () =
  test "a path that holds a zero byte opens nothing, where C would open the path before it"
    (fun () ->
      let path = Filename.concat (Lazy.force scratch) "before-zero.txt" in
      Out_channel.with_open_text path (fun channel -> output_string channel "found");
      let status, output, _ =
        run_main ~arguments:[ path ]
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console, FileRead
{
  if FileRead.read_text(Path.new(arguments[1].slice())) is Ok(text) {
    Console.print_line("${text}".slice())
  }
  if FileRead.read_text(Path.new("${arguments[1]}\0.hidden".slice())) is Err(_) {
    Console.print_line("refused".slice())
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"found\nrefused\n" output)

let () =
  test "a program runs other programs and reads their exit status" (fun () ->
      let status, output, _ =
        run_main
          {|use standard::processes

fn main(arguments: List[String]) -> ExitCode
  uses Console, Processes
{
  if Processes.run(processes::Command.new("sh").argument("-c").argument("exit 7")) is Ok(ended)
    && ended.status is Exited(code)
  {
    Console.print_line("exited ${code}".slice())
  }
  if Processes.run(processes::Command.new("truss-no-such-program")) is Err(NotFound) {
    Console.print_line("missing".slice())
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"exited 7\nmissing\n" output)

let () =
  test "a program run with an argument that holds a zero byte is not started" (fun () ->
      let status, output, _ =
        run_main
          {|use standard::processes

fn main(arguments: List[String]) -> ExitCode
  uses Console, Processes
{
  if Processes.run(processes::Command.new("sh").argument("-c").argument("exit 3\0; exit 4")) is Err(_) {
    Console.print_line("refused".slice())
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"refused\n" output);
  test "a program that a signal ends is told which signal" (fun () ->
      let status, output, _ =
        run_main
          {|use standard::processes

fn main(arguments: List[String]) -> ExitCode
  uses Console, Processes
{
  if Processes.run(processes::Command.new("sh").argument("-c").argument("kill -9 $$")) is Ok(ended)
    && ended.status is Signaled(Kill)
  {
    Console.print_line("ended by a kill".slice())
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"ended by a kill\n" output);
  test "a program is given its arguments, with bytes that are not UTF-8 replaced" (fun () ->
      let _, output, _ =
        run_main ~arguments:[ "caf\xff"; "" ]
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  Console.print_line("${arguments.length()} [${arguments[1]}] [${arguments[2]}]".slice())
  ExitCode(0)
}
|}
      in
      expect_string ~expected:"3 [caf\xef\xbf\xbd] []\n" output);
  test "a variable that is set to nothing is told from one that is not set" (fun () ->
      Unix.putenv "TRUSS_TEST_EMPTY" "";
      let _, output, _ =
        run_main
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console, Environment
{
  if Environment.variable("TRUSS_TEST_EMPTY".slice()) is Some(value) {
    Console.print_line("set to [${value}]".slice())
  }
  if Environment.variable("TRUSS\0_TEST_EMPTY".slice()) is None {
    Console.print_line("no such name".slice())
  }
  ExitCode(0)
}
|}
      in
      expect_string ~expected:"set to []\nno such name\n" output)

let () =
  test "a program reads environment variables" (fun () ->
      Unix.putenv "TRUSS_TEST_VARIABLE" "caf\xc3\xa9";
      let status, output, _ =
        run_main
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console, Environment
{
  if Environment.variable("TRUSS_TEST_VARIABLE".slice()) is Some(value) {
    Console.print_line("${value}".slice())
  }
  if Environment.variable("TRUSS_TEST_UNSET".slice()) is None {
    Console.print_line("unset".slice())
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"caf\xc3\xa9\nunset\n" output)

let () =
  test "a program reads the real clock and random numbers" (fun () ->
      let status, output, _ =
        run_main
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console, Clock, Random
{
  let now = Clock.now()
  let first = Random.next()
  let second = Random.next()
  let late = now.unix_nanoseconds() > 1600000000000000000
  Console.print_line("${late} ${first != second}".slice())
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"true true\n" output)

let () =
  test "a program reads its input a line at a time, with bad bytes replaced" (fun () ->
      let status, output, _ =
        run_main ~input:"first\nsecond \xff line\nlast"
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  var count: UInt8 = 0
  while Console.read_line() is Some(line) {
    Console.print_line("${count}: ${line}")
    count += 1
  }
  ExitCode(count)
}
|}
      in
      expect_int ~expected:3 status;
      expect_string ~expected:"0: first\n1: second \xef\xbf\xbd line\n2: last\n" output)

let () =
  test "a line longer than a block is read whole, and what follows it is kept" (fun () ->
      let long = String.make 150_000 'x' in
      let status, output, _ =
        run_main
          ~input:(long ^ "\nshort\n" ^ long)
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  while Console.read_line() is Some(line) {
    Console.print_line("${line.length()}")
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"150000\n5\n150000\n" output);
  test "the console a program is given is a value its start owns and drops" (fun () ->
      let _, compile =
        load {|fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  ExitCode(0)
}
|}
      in
      match Compile.compiled compile (Program_main (Top { module_ = example; name = "main" })) with
      | Code instance ->
          let console local =
            match instance.main.locals.(local).ty with
            | Value (Named { path = Top { name = "SystemConsole"; _ }; _ }) -> true
            | _ -> false
          in
          let dropped =
            Array.exists
              (fun (block : Lir.basic_block) ->
                List.exists
                  (function
                    | Lir.Drop { root = Local local; projections = [] } -> console local
                    | _ -> false)
                  block.statements)
              instance.main.blocks
          in
          if not dropped then fail "no drop of the console:\n%s" (Lir.to_string instance)
      | _ -> fail "expected code")

let () =
  test "a capability parameter stands for what the code it is given uses, wherever its type goes"
    (fun () ->
      let status, output, errors =
        run_main
          {|fn apply[capability Granted](run: (fn() uses Granted))
  uses Granted
{
  run()
}

fn later[capability Granted](run: (fn() uses Granted)) -> (fn() uses Granted) {
  run
}

fn shout()
  uses Console
{
  Console.print_line("named")
}

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  apply(fn() { Console.print_line("inside") })
  apply(shout)
  let kept = later(fn() { Console.print_line("kept") })
  kept()
  ExitCode(0)
}
|}
      in
      if status <> 0 then fail "status %d: %s" status errors;
      expect_string ~expected:"inside\nnamed\nkept\n" output)

(* The documents' examples: in every block that checks cleanly, each
   function that is not generic, and not only for specifications, lowers, and each test passes or reaches a
   [todo]. Most blocks are excerpts, which do not check alone. *)
let () =
  let root = "../../.." in
  Sys.readdir root |> Array.to_list
  |> List.filter (fun name -> Filename.check_suffix name ".md")
  |> List.sort compare
  |> List.iter (fun name ->
      List.iteri
        (fun index text ->
          let database = Engine.context (Engine.create ~bases:[ Lazy.force checked_standard ] ()) in
          Database.load_package (Engine.of_context database) ~name:"example" ~dependencies:[]
            [ (example, text) ];
          if Type_checker.diagnostics database example = [] then
            test
              (Printf.sprintf "%s block %d lowers, and its tests pass" name (index + 1))
              (fun () ->
                let database, compile = load text in
                List.iter
                  (fun (d : Resolve.Names.declaration) ->
                    match
                      (d.path, Query.demand database Interface.Environment.signature d.path)
                    with
                    | Top _, Some { generics = []; specification_only = false; _ } ->
                        ignore
                          (Compile.compiled compile (Code { path = d.path; type_arguments = [] }))
                    | _ -> ())
                  (Query.demand database Resolve.Names.declarations example);
                if tests_of database <> [] then
                  String.split_on_char '\n' (run_source text)
                  |> List.iter (fun line ->
                      match String.split_on_char ' ' line with
                      | [ "test"; _; ("passed" | "incomplete") ] | [ "test"; _ ] -> ()
                      | [ "test"; _; outcome ] -> fail "a test %s" outcome
                      | _ -> ())))
        (Documents.truss_blocks (Documents.read (Filename.concat root name))))

let () = Harness.finish ()
