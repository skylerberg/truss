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
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console, FileRead, FileWrite, Handles
{
  let path = Path.new(arguments[1].slice())
  if FileWrite.write_text(path, contents: "first\nsecond line\nlast".slice()) is Err(_) {
    return ExitCode(1)
  }
  if FileRead.read_text(path) is Ok(text) {
    Console.print_line("${text.length()} bytes".slice())
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
      expect_string ~expected:"22 bytes\nfirst\nsecond line\nmissing\n" output)

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
          let database = Engine.context (Engine.create ()) in
          Database.load_standard (Engine.of_context database);
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
