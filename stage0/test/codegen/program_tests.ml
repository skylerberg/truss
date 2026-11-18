let () =
  Codegen_support.test
    "a passing test's result is kept by its key, and only a changed test runs again" (fun () ->
      incr Codegen_support.counter;
      let table = Hashtbl.create 4 in
      let results : Backend.results =
        { find = Hashtbl.find_opt table; add = (fun key value -> Hashtbl.replace table key value) }
      in
      let run text =
        let database, backend = Codegen_support.load ~results text in
        match
          Backend.run_tests backend ~time_limit_ms:2000 (Codegen_support.list_tests database)
        with
        | Ok records ->
            ( (if
                 List.for_all
                   (fun (record : Backend.Test_report.record) -> record.outcome = Passed)
                   records
               then 0
               else 1),
              Codegen_support.render_records records )
        | Error message -> failwith message
      in
      let count_stored () = Hashtbl.length table in
      let source = Fixtures.Program.passing_tests in
      let first = run source in
      Codegen_support.expect_int ~expected:1 (count_stored ());
      let second = run source in
      if first <> second then
        Codegen_support.fail "the report changed when kept:\n%s\n%s" (snd first) (snd second);
      Codegen_support.expect_int ~expected:1 (fst second);
      let _ = run Fixtures.Program.passing_test_of_two_plus_two in
      Codegen_support.expect_int ~expected:2 (count_stored ()))

let () =
  Codegen_support.test
    "an external test gets the real capabilities it uses, and its result is never kept" (fun () ->
      let table = Hashtbl.create 4 in
      let results : Backend.results =
        { find = Hashtbl.find_opt table; add = (fun key value -> Hashtbl.replace table key value) }
      in
      let database, backend =
        Codegen_support.load ~results Fixtures.Program.test_reading_the_clock
      in
      let run () =
        match
          Backend.run_tests backend ~time_limit_ms:2000 (Codegen_support.list_tests database)
        with
        | Ok records -> records
        | Error message -> failwith message
      in
      ignore (run ());
      match run () with
      | [ { outcome = Passed; cached = false; _ } ] ->
          if Hashtbl.length table > 0 then Codegen_support.fail "kept a result"
      | _ -> Codegen_support.fail "did not pass, or came from the kept results")

let () =
  Codegen_support.test
    "a test's standard output and standard error come back whole in its own record" (fun () ->
      let database, backend = Codegen_support.load Fixtures.Program.tests_writing_to_the_console in
      let tests = Codegen_support.list_tests database in
      match Backend.run_tests backend ~time_limit_ms:2000 tests with
      | Error message -> Codegen_support.fail "%s" message
      | Ok records -> (
          let results_by_name =
            List.map2
              (fun (test : Path.t) (record : Backend.Test_report.record) ->
                match test with
                | Test { name; _ } -> (name, (record.outcome, record.output))
                | _ -> failwith "list_tests gave a path that is not a test")
              tests records
          in
          let expected_long_output =
            String.concat "" (List.init 10000 (Printf.sprintf "line %d\n"))
          in
          match
            List.map
              (fun name -> List.assoc_opt name results_by_name)
              [
                "writes to standard output and standard error";
                "writes more than a pipe's capacity";
                "writes nothing";
              ]
          with
          | [
           Some (Passed, Some both_streams); Some (Passed, Some long_output); Some (Passed, None);
          ] ->
              Codegen_support.expect_string ~expected:"to standard output\nto standard error\n"
                both_streams;
              if long_output <> expected_long_output then
                Codegen_support.fail "%d of %d bytes of the long output came back"
                  (String.length long_output)
                  (String.length expected_long_output)
          | _ -> Codegen_support.fail "%s" (Codegen_support.render_records records)))

let with_standard_input text work =
  let read_end, write_end = Unix.pipe ~cloexec:true () in
  ignore (Unix.write_substring write_end text 0 (String.length text));
  Unix.close write_end;
  let saved = Unix.dup ~cloexec:true Unix.stdin in
  Unix.dup2 ~cloexec:false read_end Unix.stdin;
  Unix.close read_end;
  Fun.protect
    ~finally:(fun () ->
      Unix.dup2 ~cloexec:false saved Unix.stdin;
      Unix.close saved)
    work

let () =
  Codegen_support.test
    "a test's standard input is empty, whatever the runner's standard input holds" (fun () ->
      let database, backend =
        Codegen_support.load Fixtures.Program.test_reading_its_standard_input
      in
      match
        with_standard_input "typed at the terminal\n" (fun () ->
            Backend.run_tests backend ~time_limit_ms:2000 (Codegen_support.list_tests database))
      with
      | Ok [ { outcome = Passed; _ } ] -> ()
      | Ok records -> Codegen_support.fail "%s" (Codegen_support.render_records records)
      | Error message -> Codegen_support.fail "%s" message)

let () =
  Codegen_support.test
    "a build checks each primitive operation that could fail, and evaluates no requires clause"
    (fun () ->
      let output = Codegen_support.run_source Fixtures.Program.pick_and_primitive_operations in
      List.iter
        (fun text ->
          if not (String.includes ~affix:text output) then
            Codegen_support.fail "%S is not in the output:\n%s" text output)
        [
          "test 0 passed\n";
          "test 1 panicked\n";
          "division by zero\n";
          "test 2 passed\n";
          "test 3 panicked\n";
          "index out of bounds\n  at example/main.truss:19:11\n";
          "test 4 panicked\n";
          "arithmetic overflow\n";
          "test 5 panicked\n";
          "shift amount out of range\n";
          "test 6 panicked\n";
          "slice out of bounds\n";
          "test 7 panicked\n";
        ])

let () =
  Codegen_support.test "a program prints through the real console and exits with its code"
    (fun () ->
      let status, output, _ =
        Codegen_support.run_main ~arguments:[ "one"; "two" ] Fixtures.Program.hello
      in
      Codegen_support.expect_int ~expected:3 status;
      Codegen_support.expect_string ~expected:"hello\n3 arguments, then one\n" output)

let () =
  Codegen_support.test
    "a release build stops a function that declares `uses Panic` at an operation that fails"
    (fun () ->
      let _, backend =
        Codegen_support.load ~checks:false Fixtures.Program.operations_that_stop_the_program
      in
      let run operation =
        match
          Backend.For_testing.run_program backend
            ~main:(Top { module_ = Codegen_support.example; name = "main" })
            ~arguments:[ operation ]
        with
        | Ok result -> result
        | Error message -> failwith message
      in
      List.iter
        (fun (operation, failure) ->
          let status, _, errors = run operation in
          Codegen_support.expect_int ~expected:101 status;
          if not (String.includes ~affix:("panic: " ^ failure) errors) then
            Codegen_support.fail "%s stopped with %S" operation errors)
        [
          ("overflow", "arithmetic overflow");
          ("division", "division by zero");
          ("shift", "shift amount out of range");
          ("index", "index out of bounds");
          ("slice", "slice out of bounds");
          ("key", "index out of bounds");
        ];
      let status, output, _ = run "none" in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"9223372036854775807 0 1\n" output)

let () =
  Codegen_support.test "a program writes a file, reads it back, and reports a missing one"
    (fun () ->
      let path = Filename.concat (Lazy.force Codegen_support.scratch) "written.txt" in
      let status, output, _ =
        Codegen_support.run_main ~arguments:[ path ] Fixtures.Program.file_written_and_read_back
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
        ~expected:"22 bytes\nstreamed one two\nthree\nfirst\nsecond line\nmissing\n" output)

let () =
  Codegen_support.test
    "a program opens a file to update it, writes and reads at offsets, and closes it" (fun () ->
      let path = Filename.concat (Lazy.force Codegen_support.scratch) "updated.bin" in
      let status, output, _ =
        Codegen_support.run_main ~arguments:[ path ] Fixtures.Program.file_updated_at_offsets
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
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
  Codegen_support.test "a program reads the metadata of a file, of a directory, and of an open file"
    (fun () ->
      let directory = Lazy.force Codegen_support.scratch in
      let path = Filename.concat directory "measured.txt" in
      let status, output, _ =
        Codegen_support.run_main ~arguments:[ directory; path ] Fixtures.Program.file_metadata
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
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
  Codegen_support.test
    "a program makes a directory, renames, links, sets permissions and times, and removes"
    (fun () ->
      let status, output, _ =
        Codegen_support.run_main
          ~arguments:[ Lazy.force Codegen_support.scratch ]
          Fixtures.Program.directory_and_file_operations
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
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
  Codegen_support.test
    "a program reads its variables, directory, platform, locations, and time zone" (fun () ->
      let home = Lazy.force Codegen_support.scratch in
      Unix.putenv "TRUSS_TEST_MARK" "first=second";
      Unix.putenv "HOME" home;
      Unix.putenv "TMPDIR" "";
      Unix.putenv "XDG_CACHE_HOME" "/caches";
      Unix.putenv "TZ" ":Europe/Paris";
      let status, output, _ = Codegen_support.run_main Fixtures.Program.environment_report in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
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
  Codegen_support.test "a program's log records go to standard error, one line each" (fun () ->
      let status, output, errors = Codegen_support.run_main Fixtures.Program.log_records in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"" output;
      Codegen_support.expect_string
        ~expected:
          (String.concat "\n"
             [
               {|level=information message="started" port=8080 host="a \"quoted\" name\n" ready=true load=0.5 took=1500ns|};
               {|level=error message="stopped"|};
               "";
             ])
        errors)

let () =
  Codegen_support.test
    "a program runs others: their status, output, variables, directory, pipes, and a signal"
    (fun () ->
      let status, output, _ = Codegen_support.run_main Fixtures.Program.process_operations in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
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
  Codegen_support.test
    "a program lists a directory: its files, directories, and links, however many" (fun () ->
      let status, output, _ =
        Codegen_support.run_main
          ~arguments:[ Lazy.force Codegen_support.scratch ]
          Fixtures.Program.directory_listing
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
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
  Codegen_support.test
    "a program finds its terminal, makes it raw, and restores it, or finds it has none" (fun () ->
      let directory = Lazy.force Codegen_support.scratch in
      let program = Filename.concat directory "terminal-program" in
      let _, backend = Codegen_support.load Fixtures.Program.raw_terminal in
      (match
         Backend.build_program backend
           ~main:(Top { module_ = Codegen_support.example; name = "main" })
           ~output:program
       with
      | Ok () -> ()
      | Error message -> failwith message);
      let report name =
        let path = Filename.concat directory name in
        (path, fun () -> In_channel.with_open_text path In_channel.input_all)
      in
      let path, read_terminal_report = report "terminal-report.txt" in
      let status, _, errors =
        Process.run ~input:"" "script"
          (match Codegen_support.host.os with
          | Macos -> [ "-q"; "/dev/null"; program; path ]
          | Linux -> [ "-qec"; Filename.quote_command program [ path ]; "/dev/null" ])
      in
      if status <> 0 then Codegen_support.fail "script ended with %d: %s" status errors;
      Codegen_support.expect_string
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
        (read_terminal_report ());
      match Unix.openfile "/dev/tty" [ O_RDWR ] 0 with
      | terminal -> Unix.close terminal
      | exception Unix.Unix_error _ ->
          let path, read_plain_report = report "no-terminal-report.txt" in
          let status, _, _ = Process.run ~input:"" program [ path ] in
          Codegen_support.expect_int ~expected:0 status;
          Codegen_support.expect_string
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
            (read_plain_report ()))

let () =
  Codegen_support.test "a program waits for the signals it is sent" (fun () ->
      let before = Unix.sigprocmask SIG_BLOCK [ Sys.sigusr1; Sys.sigterm ] in
      let status, output, _ =
        Fun.protect
          ~finally:(fun () -> ignore (Unix.sigprocmask SIG_SETMASK before))
          (fun () -> Codegen_support.run_main Fixtures.Program.signal_wait)
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
        ~expected:"sent true\nfirst user 1\nsent true\nsecond terminate\n" output)

let () =
  Codegen_support.test
    "a program listens, connects, accepts, and sends datagrams, on the loopback address" (fun () ->
      let status, output, _ =
        Codegen_support.run_main Fixtures.Program.loopback_sockets_and_datagrams
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
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
  Codegen_support.test "a program serves on a local socket, and sets a connection's TCP options"
    (fun () ->
      let path = Filename.concat (Lazy.force Codegen_support.scratch) "served.socket" in
      let status, output, _ =
        Codegen_support.run_main ~arguments:[ path ]
          {|use standard::network

fn say(text: String) uses Console {
  Console.print_line(text.slice())
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, NetworkServer, NetworkClient, Handles
{
  let path = Path.new(arguments[1].slice())
  match NetworkServer.listen_local(path) {
    Ok(opened) => {
      var listener = own opened
      say("listening at the path ${listener.path() == path}")
      if NetworkClient.connect_local(path) is Ok(made) {
        var client = own made
        if mut listener.accept() is Ok(moved) {
          var server = own moved
          let _ = mut client.write("ping".bytes())
          var heard: List[UInt8] = []
          if mut server.read(mut heard, limit: 100) is Ok(count) {
            say("the server read ${count}")
          }
        }
      }
      if NetworkServer.listen_local(path) is Err(error) {
        say("the path is taken ${error == SystemError.AddressInUse}")
      }
    }
    Err(error) => say("listening failed: ${error}")
  }
  if NetworkClient.connect_local(Path.new("${arguments[1]}.missing".slice())) is Err(_) {
    say("a missing path is refused")
  }
  let loopback = network::SocketAddress(address: network::IpAddress.loopback, port: 0)
  let shared = network::ListenOptions(backlog: 16, reuse_port: true)
  if NetworkServer.listen(loopback, options: shared) is Ok(opened) {
    let listener = own opened
    if NetworkClient.connect(listener.local_address(), timeout: None) is Ok(made) {
      var client = own made
      say("no delay ${mut client.set_no_delay(true) is Ok(_)}")
      say("keep alive ${mut client.set_keep_alive(Some(Duration.seconds(30))) is Ok(_)}")
      say("keep alive off ${mut client.set_keep_alive(None) is Ok(_)}")
    }
  }
  ExitCode(0)
}
|}
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
        ~expected:
          (String.concat "\n"
             [
               "listening at the path true";
               "the server read 4";
               "the path is taken true";
               "a missing path is refused";
               "no delay true";
               "keep alive true";
               "keep alive off true";
               "";
             ])
        output)

let () =
  Codegen_support.test "every connection to a port that nothing listens on is refused" (fun () ->
      let status, output, _ =
        Codegen_support.run_main Fixtures.Program.connections_to_an_unused_port
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"refused 2000 of 2000\n" output)

let () =
  Codegen_support.test "a program finds a host's addresses by its name" (fun () ->
      let status, output, _ = Codegen_support.run_main Fixtures.Program.host_address_lookup in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string
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
  Codegen_support.test
    "a path that holds a zero byte opens nothing, where C would open the path before it" (fun () ->
      let path = Filename.concat (Lazy.force Codegen_support.scratch) "before-zero.txt" in
      Out_channel.with_open_text path (fun channel -> output_string channel "found");
      let status, output, _ =
        Codegen_support.run_main ~arguments:[ path ] Fixtures.Program.file_read_of_an_argument_path
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"found\nrefused\n" output)

let () =
  Codegen_support.test "a program runs other programs and reads their exit status" (fun () ->
      let status, output, _ = Codegen_support.run_main Fixtures.Program.process_exit_statuses in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"exited 7\nmissing\n" output)

let () =
  Codegen_support.test "a program run with an argument that holds a zero byte is not started"
    (fun () ->
      let status, output, _ =
        Codegen_support.run_main Fixtures.Program.process_run_with_an_argument
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"refused\n" output);
  Codegen_support.test "a program that a signal ends is told which signal" (fun () ->
      let status, output, _ = Codegen_support.run_main Fixtures.Program.process_ended_by_a_signal in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"ended by a kill\n" output);
  Codegen_support.test "a program is given its arguments, with bytes that are not UTF-8 replaced"
    (fun () ->
      let _, output, _ =
        Codegen_support.run_main ~arguments:[ "caf\xff"; "" ] Fixtures.Program.arguments_printed
      in
      Codegen_support.expect_string ~expected:"3 [caf\xef\xbf\xbd] []\n" output);
  Codegen_support.test "a variable that is set to nothing is told from one that is not set"
    (fun () ->
      Unix.putenv "TRUSS_TEST_EMPTY" "";
      let _, output, _ =
        Codegen_support.run_main Fixtures.Program.empty_environment_variable_read
      in
      Codegen_support.expect_string ~expected:"set to []\nno such name\n" output)

let () =
  Codegen_support.test "a program reads environment variables" (fun () ->
      Unix.putenv "TRUSS_TEST_VARIABLE" "caf\xc3\xa9";
      let status, output, _ = Codegen_support.run_main Fixtures.Program.environment_variable_read in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"caf\xc3\xa9\nunset\n" output)

let () =
  Codegen_support.test "a program reads the real clock and random numbers" (fun () ->
      let status, output, _ = Codegen_support.run_main Fixtures.Program.clock_and_random_numbers in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"true true\n" output)

let () =
  Codegen_support.test "a program reads its input a line at a time, with bad bytes replaced"
    (fun () ->
      let status, output, _ =
        Codegen_support.run_main ~input:"first\nsecond \xff line\nlast"
          Fixtures.Program.input_lines_counted
      in
      Codegen_support.expect_int ~expected:3 status;
      Codegen_support.expect_string ~expected:"0: first\n1: second \xef\xbf\xbd line\n2: last\n"
        output)

let () =
  Codegen_support.test "a line longer than a block is read whole, and the text after it is kept"
    (fun () ->
      let long = String.make 150_000 'x' in
      let status, output, _ =
        Codegen_support.run_main ~input:(long ^ "\nshort\n" ^ long) Fixtures.Program.line_echo
      in
      Codegen_support.expect_int ~expected:0 status;
      Codegen_support.expect_string ~expected:"150000\n5\n150000\n" output);
  Codegen_support.test "the console a program is given is a value its start owns and drops"
    (fun () ->
      let _, backend = Codegen_support.load Fixtures.Program.main_using_the_console in
      let fragment =
        Backend.For_testing.compile_fragment backend
          (Generated (Program_main (Top { module_ = Codegen_support.example; name = "main" })))
      in
      let is_console_drop : Instance.key -> bool = function
        | Drop (Named { path = Top { name = "SystemConsole"; _ }; _ }) -> true
        | _ -> false
      in
      if not (List.exists is_console_drop (Emit_c.references fragment)) then
        Codegen_support.fail "no drop of the console:\n%s" (Emit_c.For_testing.render_c fragment))

let () =
  Codegen_support.test
    "a capability parameter stands for the capabilities its argument uses, wherever its type goes"
    (fun () ->
      let status, output, errors =
        Codegen_support.run_main Fixtures.Program.apply_with_a_capability_parameter
      in
      if status <> 0 then Codegen_support.fail "status %d: %s" status errors;
      Codegen_support.expect_string ~expected:"inside\nnamed\nkept\n" output)

let () =
  Harness.list_markdown_documents ()
  |> List.iter (fun name ->
      List.iteri
        (fun index text ->
          let packages =
            Codegen_support.make_example_package [ (Codegen_support.example_file, text) ]
          in
          if
            Codegen_support.list_diagnostics
              (Codegen_support.make_database packages)
              Codegen_support.example_file
            = []
          then
            Codegen_support.test
              (Printf.sprintf "%s block %d lowers, and its tests pass" name (index + 1))
              (fun () ->
                let checked = Codegen_support.make_database packages in
                let interface =
                  Database.make_interface_lookups checked
                    [ Codegen_support.example_file.module_.package ]
                in
                let functions =
                  List.filter_map
                    (fun (declaration : Resolve.Names.declaration) ->
                      match
                        ( declaration.path,
                          Interface.Definition.find_declared_signature interface declaration.path )
                      with
                      | ( Top _,
                          Some
                            {
                              generics = [];
                              capability_parameters = [];
                              specification_only = false;
                              _;
                            } ) ->
                          Some
                            (Instance.Code
                               { path = declaration.path; instantiation = Ground.no_instantiation })
                      | _ -> None)
                    ((Database.make_name_lookups checked [ Codegen_support.example.package ])
                       .list_declarations Codegen_support.example)
                in
                let database, backend = Codegen_support.load ~roots:functions text in
                List.iter
                  (fun key -> ignore (Backend.For_testing.compile_fragment backend key))
                  functions;
                match Codegen_support.list_tests database with
                | [] -> ()
                | tests ->
                    String.split_on_char '\n'
                      (match Backend.run_tests backend ~time_limit_ms:2000 tests with
                      | Ok records -> Codegen_support.render_records records
                      | Error message -> failwith message)
                    |> List.iter (fun line ->
                        match String.split_on_char ' ' line with
                        | [ "test"; _; ("passed" | "incomplete") ] | [ "test"; _ ] -> ()
                        | [ "test"; _; outcome ] -> Codegen_support.fail "a test %s" outcome
                        | _ -> ())))
        (Documents.list_truss_blocks (File_system.read (Harness.make_workspace_path name))))

let () =
  Codegen_support.test "a function value whose type uses Panic is called without evidence for Panic"
    (fun () ->
      let source = Fixtures.Program.function_value_using_panic in
      (match Codegen_support.run_main source with
      | 0, output, _ -> Codegen_support.expect_string ~expected:"counted 1\ndone 3\n" output
      | status, _, errors -> Codegen_support.fail "ended with status %d: %s" status errors);
      match Codegen_support.run_main ~arguments:[ "a"; "b"; "c"; "d" ] source with
      | 101, output, errors ->
          Codegen_support.expect_string ~expected:"counted 5\n" output;
          if not (String.includes ~affix:"many arguments" errors) then
            Codegen_support.fail "panicked with %S" errors
      | status, _, errors -> Codegen_support.fail "ended with status %d: %s" status errors)

let () =
  Codegen_support.test "a program whose capability method lends is not built yet" (fun () ->
      let _, backend = Codegen_support.load Fixtures.Program.store_lending_its_value in
      match
        Backend.For_testing.run_program backend
          ~main:(Top { module_ = Codegen_support.example; name = "main" })
          ~arguments:[]
      with
      | Ok _ -> Codegen_support.fail "the program ran"
      | Error message ->
          if
            not
              (String.includes ~affix:"Stage0 cannot build this yet" message
              && String.includes ~affix:"a capability method that lends" message)
          then Codegen_support.fail "failed with: %s" message)
