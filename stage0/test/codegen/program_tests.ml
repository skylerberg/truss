(* Test results kept by key, the checks in place of proofs, and whole programs. *)

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
  test "a build checks each primitive operation that could fail, and evaluates no requires clause"
    (fun () ->
      let output =
        run_source
          {|fn pick(items: List[Int64], top: USize) -> USize
  requires items[top] >= 0
{
  top
}

test "overflow" {
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

test "shift" {
  let one: UInt64 = 1
  let amount: UInt64 = 70
  let _ = one << amount
}

test "slice" {
  let items: List[Int64] = [1, 2]
  let _ = items[1..9]
}

test "swap" {
  var items: List[Int64] = [1, 2]
  mut items.swap(0, second: 7)
}

test "a clause that would fail if it ran" {
  assert pick([1, 2], top: 9) == 9
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
          "index out of bounds\n  at example/main.truss:19:11\n";
          "test 3 panicked\n";
          "shift amount out of range\n";
          "test 4 panicked\n";
          "slice out of bounds\n";
          "test 5 panicked\n";
          "test 6 passed\n";
          "test 7 passed\n";
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
  test "a program's log records go to standard error, one line each" (fun () ->
      let status, output, errors =
        run_main
          {|use standard::log

fn main(arguments: List[String]) -> ExitCode
  uses Log
{
  log::debug("left out")
  log::information(
    "started",
    fields: [
      log::Field.integer("port", value: 8080),
      log::Field.string("host", value: "a \"quoted\" name\n"),
      log::Field.bool("ready", value: true),
      log::Field.float("load", value: 0.5),
      log::Field.duration("took", value: Duration.nanoseconds(1500)),
    ],
  )
  log::error("stopped")
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"" output;
      expect_string
        ~expected:
          (String.concat "\n"
             [
               {|level=information message="started" port=8080 host="a \"quoted\" name\n" ready=true load=0.5 took=1500ns|};
               {|level=error message="stopped"|};
               "";
             ])
        errors)

let () =
  test "a program runs others: their status, output, variables, directory, pipes, and a signal"
    (fun () ->
      let status, output, _ =
        run_main
          {|use standard::processes

fn say(text: String) uses Console {
  Console.print_line(text.slice())
}

fn shown(status: processes::ExitStatus) -> String {
  match status {
    Exited(code) => "exited ${code}"
    Signaled(signal) => if signal == processes::Signal.Terminate {
      "ended by terminate".copy()
    } else {
      "ended by another signal".copy()
    }
  }
}

fn show(label: String, bytes: List[UInt8])
  uses Console, Handles
{
  Console.print(label.slice())
  var out = Console.output()
  let _ = mut out.write(bytes.slice())
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, Processes, Handles
{
  let quiet = processes::Command.new("sh").argument("-c").argument("exit 3")
  if Processes.run(quiet) is Ok(output) {
    say("run ${shown(output.status)}, output ${output.output.length()}")
  }
  let loud = processes::Command.new("sh")
    .argument("-c")
    .argument("echo out; echo err >&2; echo $TRUSS_SPAWNED; pwd")
    .variable("TRUSS_SPAWNED", value: "first")
    .variable("TRUSS_SPAWNED", value: "second")
    .directory(Path.new("/"))
    .output(processes::Redirect.Capture)
    .error_output(processes::Redirect.Capture)
  if Processes.run(loud) is Ok(output) {
    show("captured ", bytes: output.output)
    show("and ", bytes: output.error_output)
  }
  let bare = processes::Command.new("sh")
    .argument("-c")
    .argument("echo home=$HOME.")
    .without_inherited_variables()
    .variable("PATH", value: "/usr/bin:/bin")
    .output(processes::Redirect.Capture)
  if Processes.run(bare) is Ok(output) {
    show("without variables ", bytes: output.output)
  }
  if Processes.run(processes::Command.new("no-such-program-anywhere")) is Err(NotFound) {
    say("not found")
  }
  let copier = processes::Command.new("cat")
    .input(processes::Redirect.Pipe)
    .output(processes::Redirect.Pipe)
  if Processes.spawn(copier) is Ok(started) {
    var child = own started
    if mut child.take_input() is Some(taken) {
      var input = own taken
      let sent: List[UInt8] = [112, 105, 112, 101, 100, 10]
      let _ = mut input.write(sent.slice())
      let _ = own input.close()
    }
    if mut child.take_output() is Some(taken) {
      var output = own taken
      var received: List[UInt8] = []
      var reading = true
      while reading {
        reading = mut output.read(mut received, limit: 100) is Ok(count) && count > 0
      }
      show("through cat ", bytes: received)
    }
    if mut child.wait() is Ok(status) {
      say("cat ${shown(status)}")
    }
  }
  if Processes.spawn(processes::Command.new("sleep").argument("30")) is Ok(started) {
    var sleeper = own started
    say("sleeping ${sleeper.identifier() > 1}")
    if mut sleeper.signal(processes::Signal.Terminate) is Ok(_) && mut sleeper.wait() is Ok(status) {
      say("sleep ${shown(status)}")
    }
  }
  let discarded = processes::Command.new("sh")
    .argument("-c")
    .argument("echo unseen; cat")
    .input(processes::Redirect.Discard)
    .output(processes::Redirect.Discard)
  if Processes.run(discarded) is Ok(output) {
    say("discarded ${shown(output.status)}")
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string
        ~expected:
          (String.concat "\n"
             [
               "run exited 3, output 0";
               "captured out";
               "second";
               "/";
               "and err";
               "without variables home=.";
               "not found";
               "through cat piped";
               "cat exited 0";
               "sleeping true";
               "sleep ended by terminate";
               "discarded exited 0";
               "";
             ])
        output)

let () =
  test "a program lists a directory: its files, directories, and links, however many" (fun () ->
      let status, output, _ =
        run_main
          ~arguments:[ Lazy.force scratch ]
          {|use standard::files

fn say(text: String) uses Console {
  Console.print_line(text.slice())
}

fn kind_of(entries: List[files::DirectoryEntry], name: String) -> String {
  for entry in entries {
    if entry.name == name {
      return if entry.kind == files::FileKind.File {
        "a file".copy()
      } else if entry.kind == files::FileKind.Directory {
        "a directory".copy()
      } else if entry.kind == files::FileKind.SymbolicLink {
        "a link".copy()
      } else {
        "something else".copy()
      }
    }
  }
  "missing".copy()
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, FileRead, FileWrite
{
  let directory = Path.new("${arguments[1]}/listed")
  let file = Path.new("${arguments[1]}/listed/plain.txt")
  let inner = Path.new("${arguments[1]}/listed/inner")
  let link = Path.new("${arguments[1]}/listed/pointer")
  if FileWrite.create_directory(directory) is Err(_) {
    return ExitCode(1)
  }
  if FileRead.list(directory) is Ok(entries) {
    say("empty ${entries.length()}")
  }
  let _ = FileWrite.write_text(file, contents: "contents")
  let _ = FileWrite.create_directory(inner)
  let _ = FileWrite.link(file, link: link, kind: files::LinkKind.Symbolic)
  var count: USize = 0
  while count < 600 {
    let _ = FileWrite.write_text(Path.new("${arguments[1]}/listed/inner/a file with a fairly long name, number ${count}"), contents: "x")
    count += 1
  }
  if FileRead.list(directory) is Ok(entries) {
    say("holds ${entries.length()}")
    say("plain.txt is ${kind_of(entries, name: "plain.txt")}")
    say("inner is ${kind_of(entries, name: "inner")}")
    say("pointer is ${kind_of(entries, name: "pointer")}")
    say(". is ${kind_of(entries, name: ".")}")
  }
  if FileRead.list(inner) is Ok(entries) {
    say("inner holds ${entries.length()}")
    say("number 599 is ${kind_of(entries, name: "a file with a fairly long name, number 599")}")
  }
  if FileRead.list(Path.new("${arguments[1]}/listed/absent")) is Err(NotFound) {
    say("absent is not found")
  }
  if FileRead.list(file) is Err(error) {
    say("a file is no directory ${error == SystemError.NotADirectory}")
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string
        ~expected:
          (String.concat "\n"
             [
               "empty 0";
               "holds 3";
               "plain.txt is a file";
               "inner is a directory";
               "pointer is a link";
               ". is missing";
               "inner holds 600";
               "number 599 is a file";
               "absent is not found";
               "a file is no directory true";
               "";
             ])
        output)

let () =
  test "a program finds its terminal, makes it raw, and restores it, or finds it has none"
    (fun () ->
      let directory = Lazy.force scratch in
      let program = Filename.concat directory "terminal-program" in
      let _, compile =
        load
          {|use standard::processes

fn holds(bytes: List[UInt8], word: String) -> Bool {
  let wanted = word.bytes()
  if wanted.length() > bytes.length() {
    return false
  }
  for start in 0..=(bytes.length() - wanted.length()) {
    var same = true
    for index in 0..wanted.length() {
      if bytes[start + index] != wanted[index] {
        same = false
      }
    }
    if same {
      return true
    }
  }
  false
}

fn settings() -> List[UInt8]
  uses Processes
{
  let asked = processes::Command.new("sh")
    .argument("-c")
    .argument("stty -a < /dev/tty")
    .output(processes::Redirect.Capture)
  match Processes.run(asked) {
    Ok(output) => output.output.copy()
    Err(_) => []
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, Handles, Processes, FileWrite
{
  var report = TextBuilder.new()
  var terminal = Console.terminal()
  mut report.write("interactive ${terminal.is_interactive()}\n")
  mut report.write("size known ${terminal.size() is Ok(_)}\n")
  let before = settings()
  mut report.write("starts raw ${holds(before, word: "-icanon")}\n")
  mut report.write("made raw ${mut terminal.set_raw_mode(true) is Ok(_)}\n")
  let raw = settings()
  mut report.write("raw ${holds(raw, word: "-icanon")} ${holds(raw, word: "-isig")} ${holds(raw, word: "-opost")}\n")
  mut report.write("restored ${mut terminal.set_raw_mode(false) is Ok(_)}\n")
  let after = settings()
  mut report.write("after ${holds(after, word: "-icanon")} ${holds(after, word: "-isig")} ${holds(after, word: "-opost")}\n")
  let text = own report.finish()
  let _ = FileWrite.write_text(Path.new(arguments[1]), contents: text)
  ExitCode(0)
}
|}
      in
      (match
         Compile.build_program compile
           ~main:(Top { module_ = example; name = "main" })
           ~output:program
       with
      | Ok () -> ()
      | Error message -> failwith message);
      let report name =
        let path = Filename.concat directory name in
        (path, fun () -> In_channel.with_open_text path In_channel.input_all)
      in
      (* [script] runs a program with a terminal of its own, which this test
         may not have. *)
      let path, in_terminal = report "terminal-report.txt" in
      let status, _, errors =
        Process.run ~input:"" "script"
          (match host.os with
          | Macos -> [ "-q"; "/dev/null"; program; path ]
          | Linux -> [ "-qec"; Filename.quote_command program [ path ]; "/dev/null" ])
      in
      if status <> 0 then fail "script ended with %d: %s" status errors;
      expect_string
        ~expected:
          (String.concat "\n"
             [
               "interactive true";
               "size known true";
               "starts raw false";
               "made raw true";
               "raw true true true";
               "restored true";
               "after false false false";
               "";
             ])
        (in_terminal ());
      (* Run as it is, the program has this test's terminal, which a run
         under CI lacks. Only there can the test say what it finds. *)
      match Unix.openfile "/dev/tty" [ O_RDWR ] 0 with
      | terminal -> Unix.close terminal
      | exception Unix.Unix_error _ ->
          let path, without = report "no-terminal-report.txt" in
          let status, _, _ = Process.run ~input:"" program [ path ] in
          expect_int ~expected:0 status;
          expect_string
            ~expected:
              (String.concat "\n"
                 [
                   "interactive false";
                   "size known false";
                   "starts raw false";
                   "made raw false";
                   "raw false false false";
                   "restored false";
                   "after false false false";
                   "";
                 ])
            (without ()))

let () =
  test "a program waits for the signals it is sent" (fun () ->
      (* The program is started with the two signals held back, as a child
         is started with its parent's, so that the first, sent before the
         program waits for it, does not end the program. *)
      let before = Unix.sigprocmask SIG_BLOCK [ Sys.sigusr1; Sys.sigterm ] in
      let status, output, _ =
        Fun.protect
          ~finally:(fun () -> ignore (Unix.sigprocmask SIG_SETMASK before))
          (fun () ->
            run_main
              {|use standard::processes

fn name_of(arrived: Option[processes::Signal]) -> String {
  if arrived is Some(signal) && signal == processes::Signal.User1 {
    "user 1".copy()
  } else if arrived is Some(signal) && signal == processes::Signal.Terminate {
    "terminate".copy()
  } else {
    "another".copy()
  }
}

fn send(signal: String) -> Bool
  uses Processes
{
  let sender = processes::Command.new("sh").argument("-c").argument("kill -${signal} $PPID")
  Processes.run(sender) is Ok(output) && output.status.is_success()
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, Processes, Signals
{
  let either = [processes::Signal.User1, processes::Signal.Terminate]
  Console.print_line("sent ${send("USR1")}")
  Console.print_line("first ${name_of(Signals.wait(either.slice()))}")
  Console.print_line("sent ${send("TERM")}")
  Console.print_line("second ${name_of(Signals.wait(either.slice()))}")
  ExitCode(0)
}
|})
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"sent true\nfirst user 1\nsent true\nsecond terminate\n" output)

let () =
  test "a program listens, connects, accepts, and sends datagrams, on the loopback address"
    (fun () ->
      let status, output, _ =
        run_main
          {|use standard::network

fn say(text: String) uses Console {
  Console.print_line(text.slice())
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, NetworkServer, NetworkClient, Handles
{
  let loopback = network::SocketAddress(address: network::IpAddress.loopback, port: 0)
  var unused: UInt16 = 0
  if NetworkServer.listen(loopback) is Ok(opened) {
    var listener = own opened
    let at = listener.local_address()
    unused = at.port
    say("listening on a port ${at.port > 0}")
    if NetworkClient.connect(at, timeout: Some(Duration.nanoseconds(2000000000))) is Ok(made) {
      var client = own made
      say("connected to the port ${client.peer_address().port == at.port}")
      if mut listener.accept() is Ok(taken) {
        var server = own taken
        say("accepted from the client ${server.peer_address().port == client.local_address().port}")
        let request: List[UInt8] = [112, 105, 110, 103]
        let _ = mut client.write(request.slice())
        var heard: List[UInt8] = []
        if mut server.read(mut heard, limit: 100) is Ok(count) {
          say("the server read ${count}, first ${heard[0]}")
        }
        let _ = mut server.write(heard.slice())
        let _ = mut server.shut_down(network::Direction.Sending)
        var answer: List[UInt8] = []
        if mut client.read(mut answer, limit: 100) is Ok(count) {
          say("the client read ${count}")
        }
        if mut client.read(mut answer, limit: 100) is Ok(count) {
          say("and then the end ${count}")
        }
        let _ = mut server.set_read_timeout(Some(Duration.nanoseconds(50000000)))
        if mut server.read(mut heard, limit: 10) is Err(error) {
          say("nothing more in time ${error == SystemError.TimedOut}")
        }
      }
    }
  }
  let closed = network::SocketAddress(address: network::IpAddress.loopback, port: unused)
  if NetworkClient.connect(closed, timeout: None) is Err(error) {
    say("refused ${error == SystemError.ConnectionRefused}")
  }
  if NetworkServer.bind_datagram(loopback) is Ok(bound) && NetworkClient.open_datagram() is Ok(opened) {
    var receiver = own bound
    var sender = own opened
    let message: List[UInt8] = [1, 2, 3]
    if mut sender.send_to(message.slice(), address: receiver.local_address()) is Ok(sent) {
      say("sent ${sent}")
    }
    var packet: List[UInt8] = []
    if mut receiver.receive_from(mut packet, limit: 100) is Ok(datagram) {
      say("received ${datagram.length} from loopback ${datagram.from.address == network::IpAddress.loopback}")
    }
    let _ = mut receiver.set_read_timeout(Some(Duration.nanoseconds(50000000)))
    if mut receiver.receive_from(mut packet, limit: 100) is Err(error) {
      say("no second packet ${error == SystemError.TimedOut}")
    }
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string
        ~expected:
          (String.concat "\n"
             [
               "listening on a port true";
               "connected to the port true";
               "accepted from the client true";
               "the server read 4, first 112";
               "the client read 4";
               "and then the end 0";
               "nothing more in time true";
               "refused true";
               "sent 3";
               "received 3 from loopback true";
               "no second packet true";
               "";
             ])
        output)

let () =
  (* A refusal can arrive before the first system call after [connect]. On
     macOS a [setsockopt] then fails, so a connect that set an option
     before it read its result reported that failure for some of these. *)
  test "every connection to a port that nothing listens on is refused" (fun () ->
      let status, output, _ =
        run_main
          {|use standard::network

fn main(arguments: List[String]) -> ExitCode
  uses Console, NetworkServer, NetworkClient, Handles
{
  let loopback = network::SocketAddress(address: network::IpAddress.loopback, port: 0)
  var unused: UInt16 = 0
  if NetworkServer.listen(loopback) is Ok(opened) {
    let listener = own opened
    unused = listener.local_address().port
  }
  let closed = network::SocketAddress(address: network::IpAddress.loopback, port: unused)
  var refused = 0
  for attempt in 0..2000 {
    let limit = if attempt % 2 == 0 { None } else { Some(Duration.nanoseconds(2000000000)) }
    if NetworkClient.connect(closed, timeout: limit) is Err(error) {
      if error == SystemError.ConnectionRefused {
        refused += 1
      }
    }
  }
  Console.print_line("refused ${refused} of 2000")
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"refused 2000 of 2000\n" output)

let () =
  test "a program finds a host's addresses by its name" (fun () ->
      (* Only names the system answers by itself, so that the test asks no
         server: addresses, [localhost], and a name too long to be asked
         about. *)
      let status, output, _ =
        run_main
          {|use standard::network

fn say(text: String) uses Console {
  Console.print_line(text.slice())
}

fn loops_back(address: network::IpAddress) -> Bool {
  address == network::IpAddress.loopback
    || address == network::IpAddress.Version6([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, NetworkClient
{
  if NetworkClient.resolve("127.0.0.1") is Ok(addresses) {
    say("an address is itself ${addresses.length() == 1 && addresses[0] == network::IpAddress.loopback}")
  }
  if NetworkClient.resolve("::1") is Ok(addresses) {
    say("so is an IPv6 address ${addresses.length() == 1 && loops_back(addresses[0])}")
  }
  if NetworkClient.resolve("localhost") is Ok(addresses) {
    var all = addresses.length() > 0
    for address in addresses {
      if !loops_back(address) {
        all = false
      }
    }
    say("localhost loops back ${all}")
  }
  if NetworkClient.resolve("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx") is Err(error) {
    say("an unknown host is an error ${error == SystemError.HostNotFound || error == SystemError.Unreachable}")
  }
  if NetworkClient.resolve("with a\0zero") is Err(error) {
    say("a name with a zero byte ${error == SystemError.InvalidInput}")
  }
  ExitCode(0)
}
|}
      in
      expect_int ~expected:0 status;
      expect_string
        ~expected:
          (String.concat "\n"
             [
               "an address is itself true";
               "so is an IPv6 address true";
               "localhost loops back true";
               "an unknown host is an error true";
               "a name with a zero byte true";
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
   function that is not generic, and not only for specifications, lowers,
   and each test passes or reaches a [todo]. Most blocks are excerpts,
   which do not check alone. *)
let () =
  let root = Harness.workspace_path "." in
  Sys.readdir root |> Array.to_list
  |> List.filter (fun name -> Filename.check_suffix name ".md")
  |> List.sort compare
  |> List.iter (fun name ->
      List.iteri
        (fun index text ->
          let database = Engine.context (Engine.create ~bases:[ Lazy.force checked_standard ] ()) in
          Database.load_package (Engine.of_context database)
            ~name:{ owner = None; name = "example" }
            ~dependencies:[]
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

let () =
  test "a function value whose type uses Panic is called without evidence for Panic" (fun () ->
      let source =
        {|fn fail(message: StringSlice)
  uses Panic
{
  Panic.crash(message)
}

fn report(count: USize) -> USize
  uses Console, Panic
{
  if count > 5 {
    Panic.crash("too many to report")
  }
  Console.print_line("counted ${count}")
  count
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, Panic
{
  let crash = fail
  let counted = report
  let checked: (fn(USize) -> USize uses Panic) = fn(count) {
    if count > 9 {
      Panic.crash("far too many")
    }
    count + 1
  }
  let total = counted(arguments.length()) + checked(arguments.length())
  if arguments.length() > 3 {
    crash("many arguments")
  }
  Console.print_line("done ${total}")
  ExitCode.success
}
|}
      in
      (match run_main source with
      | 0, output, _ -> expect_string ~expected:"counted 1\ndone 3\n" output
      | status, _, errors -> fail "ended with status %d: %s" status errors);
      match run_main ~arguments:[ "a"; "b"; "c"; "d" ] source with
      | 101, output, errors ->
          expect_string ~expected:"counted 5\n" output;
          if not (contains errors "many arguments") then fail "panicked with %S" errors
      | status, _, errors -> fail "ended with status %d: %s" status errors)
