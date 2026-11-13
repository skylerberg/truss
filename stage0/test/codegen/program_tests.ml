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
        let database, compile = load ~results text in
        match Compile.run_tests compile ~time_limit:2000 (tests_of database) with
        | Ok records ->
            ( (if List.for_all (fun (record : Compile.record) -> record.outcome = Passed) records
               then 0
               else 1),
              render_records records )
        | Error message -> failwith message
      in
      let stored_count () = Hashtbl.length table in
      let source = Fixtures.Program.passing_tests_result_is_kept_by_its_key_and_only_a in
      let first = run source in
      expect_int ~expected:1 (stored_count ());
      let second = run source in
      if first <> second then fail "the report changed when kept:\n%s\n%s" (snd first) (snd second);
      expect_int ~expected:1 (fst second);
      let _ = run Fixtures.Program.passing_tests_result_is_kept_by_its_key_and_only_a_2 in
      expect_int ~expected:2 (stored_count ()))

let () =
  test "an external test gets the real capabilities it uses, and its result is never kept"
    (fun () ->
      let table = Hashtbl.create 4 in
      let results : Compile.results =
        { find = Hashtbl.find_opt table; add = (fun key value -> Hashtbl.replace table key value) }
      in
      let database, compile =
        load ~results Fixtures.Program.external_test_gets_the_real_capabilities_it_uses
      in
      let run () =
        match Compile.run_tests compile ~time_limit:2000 (tests_of database) with
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
      let output = run_source Fixtures.Program.build_checks_each_primitive_operation_that_could in
      let contains text =
        let text_length = String.length text and output_length = String.length output in
        let rec occurs_at position =
          position + text_length <= output_length
          && (String.sub output position text_length = text || occurs_at (position + 1))
        in
        if not (occurs_at 0) then fail "%S is not in the output:\n%s" text output
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
          Fixtures.Program.program_prints_through_the_real_console_and_exits
      in
      expect_int ~expected:3 status;
      expect_string ~expected:"hello\n3 arguments, then one\n" output)

let () =
  test "a program writes a file, reads it back, and reports a missing one" (fun () ->
      let path = Filename.concat (Lazy.force scratch) "written.txt" in
      let status, output, _ =
        run_main ~arguments:[ path ]
          Fixtures.Program.program_writes_a_file_reads_it_back_and_reports_a
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"22 bytes\nstreamed one two\nthree\nfirst\nsecond line\nmissing\n"
        output)

let () =
  test "a program opens a file to update it, writes and reads at offsets, and closes it" (fun () ->
      let path = Filename.concat (Lazy.force scratch) "updated.bin" in
      let status, output, _ =
        run_main ~arguments:[ path ]
          Fixtures.Program.program_opens_a_file_to_update_it_writes_and_reads
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
          Fixtures.Program.program_reads_the_metadata_of_a_file_of_a
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
          Fixtures.Program.program_makes_a_directory_renames_links_sets
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
        run_main Fixtures.Program.program_reads_its_variables_directory_platform
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
        run_main Fixtures.Program.programs_log_records_go_to_standard_error_one_line
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
        run_main Fixtures.Program.program_runs_others_their_status_output_variables
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
          Fixtures.Program.program_lists_a_directory_its_files_directories
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
      let _, compile = load Fixtures.Program.program_finds_its_terminal_makes_it_raw_and in
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
         under CI lacks. Only there can the test report its findings. *)
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
          (fun () -> run_main Fixtures.Program.program_waits_for_the_signals_it_is_sent)
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"sent true\nfirst user 1\nsent true\nsecond terminate\n" output)

let () =
  test "a program listens, connects, accepts, and sends datagrams, on the loopback address"
    (fun () ->
      let status, output, _ =
        run_main Fixtures.Program.program_listens_connects_accepts_and_sends
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
  test "a program serves on a local socket, and sets a connection's TCP options" (fun () ->
      let path = Filename.concat (Lazy.force scratch) "served.socket" in
      let status, output, _ =
        run_main ~arguments:[ path ]
          {|use standard::network

fn say(text: String) uses Console {
  Console.print_line(text.slice())
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, NetworkServer, NetworkClient, Handles
{
  let path = Path.new(arguments[1].slice())
  if NetworkServer.listen_local(path) is Ok(opened) {
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
      expect_int ~expected:0 status;
      expect_string
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
  (* A refusal can arrive before the first system call after [connect]. On
     macOS a [setsockopt] then fails, so a connect that set an option
     before it read its result reported that failure for some of these. *)
  test "every connection to a port that nothing listens on is refused" (fun () ->
      let status, output, _ =
        run_main Fixtures.Program.every_connection_to_a_port_that_nothing_listens_on
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"refused 2000 of 2000\n" output)

let () =
  test "a program finds a host's addresses by its name" (fun () ->
      (* Only names the system answers by itself, so that the test asks no
         server: addresses, [localhost], and a name too long to be asked
         about. *)
      let status, output, _ =
        run_main Fixtures.Program.program_finds_a_hosts_addresses_by_its_name
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
          Fixtures.Program.path_that_holds_a_zero_byte_opens_nothing_where_c
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"found\nrefused\n" output)

let () =
  test "a program runs other programs and reads their exit status" (fun () ->
      let status, output, _ =
        run_main Fixtures.Program.program_runs_other_programs_and_reads_their_exit
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"exited 7\nmissing\n" output)

let () =
  test "a program run with an argument that holds a zero byte is not started" (fun () ->
      let status, output, _ =
        run_main Fixtures.Program.program_run_with_an_argument_that_holds_a_zero
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"refused\n" output);
  test "a program that a signal ends is told which signal" (fun () ->
      let status, output, _ =
        run_main Fixtures.Program.program_that_a_signal_ends_is_told_which_signal
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"ended by a kill\n" output);
  test "a program is given its arguments, with bytes that are not UTF-8 replaced" (fun () ->
      let _, output, _ =
        run_main ~arguments:[ "caf\xff"; "" ]
          Fixtures.Program.program_is_given_its_arguments_with_bytes_that_are
      in
      expect_string ~expected:"3 [caf\xef\xbf\xbd] []\n" output);
  test "a variable that is set to nothing is told from one that is not set" (fun () ->
      Unix.putenv "TRUSS_TEST_EMPTY" "";
      let _, output, _ =
        run_main Fixtures.Program.variable_that_is_set_to_nothing_is_told_from_one
      in
      expect_string ~expected:"set to []\nno such name\n" output)

let () =
  test "a program reads environment variables" (fun () ->
      Unix.putenv "TRUSS_TEST_VARIABLE" "caf\xc3\xa9";
      let status, output, _ = run_main Fixtures.Program.program_reads_environment_variables in
      expect_int ~expected:0 status;
      expect_string ~expected:"caf\xc3\xa9\nunset\n" output)

let () =
  test "a program reads the real clock and random numbers" (fun () ->
      let status, output, _ =
        run_main Fixtures.Program.program_reads_the_real_clock_and_random_numbers
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"true true\n" output)

let () =
  test "a program reads its input a line at a time, with bad bytes replaced" (fun () ->
      let status, output, _ =
        run_main ~input:"first\nsecond \xff line\nlast"
          Fixtures.Program.program_reads_its_input_a_line_at_a_time_with_bad
      in
      expect_int ~expected:3 status;
      expect_string ~expected:"0: first\n1: second \xef\xbf\xbd line\n2: last\n" output)

let () =
  test "a line longer than a block is read whole, and the text after it is kept" (fun () ->
      let long = String.make 150_000 'x' in
      let status, output, _ =
        run_main
          ~input:(long ^ "\nshort\n" ^ long)
          Fixtures.Program.line_longer_than_a_block_is_read_whole_and_the
      in
      expect_int ~expected:0 status;
      expect_string ~expected:"150000\n5\n150000\n" output);
  test "the console a program is given is a value its start owns and drops" (fun () ->
      let _, compile = load Fixtures.Program.console_a_program_is_given_is_a_value_its_start in
      let fragment =
        Compile.For_testing.compiled compile
          (Program_main (Top { module_ = example; name = "main" }))
      in
      let is_console_drop : Instance.key -> bool = function
        | Drop (Named { path = Top { name = "SystemConsole"; _ }; _ }) -> true
        | _ -> false
      in
      if not (List.exists is_console_drop (Emit_c.references fragment)) then
        fail "no drop of the console:\n%s" (Emit_c.For_testing.c fragment))

let () =
  test
    "a capability parameter stands for the capabilities its argument uses, wherever its type goes"
    (fun () ->
      let status, output, errors =
        run_main Fixtures.Program.capability_parameter_stands_for_the_capabilities
      in
      if status <> 0 then fail "status %d: %s" status errors;
      expect_string ~expected:"inside\nnamed\nkept\n" output)

(* The documents' examples: in every block that checks cleanly, each
   function that is not generic, and not only for specifications, lowers,
   and each test passes or reaches a [todo]. Most blocks are excerpts,
   which do not check alone. *)
let () =
  Harness.markdown_documents ()
  |> List.iter (fun name ->
      List.iteri
        (fun index text ->
          let database = Engine.context (Engine.create ~bases:[ Lazy.force checked_standard ] ()) in
          Database.load_package (Engine.of_context database)
            ~name:{ owner = None; name = "example" }
            ~dependencies:[]
            [ (example_file, text) ];
          if Checks.diagnostics database example_file = [] then
            test
              (Printf.sprintf "%s block %d lowers, and its tests pass" name (index + 1))
              (fun () ->
                let database, compile = load text in
                List.iter
                  (fun (declaration : Resolve.Names.declaration) ->
                    match
                      ( declaration.path,
                        Query.demand database Interface.Environment.signature declaration.path )
                    with
                    | Top _, Some { generics = []; specification_only = false; _ } ->
                        ignore
                          (Compile.For_testing.compiled compile
                             (Code { path = declaration.path; type_arguments = [] }))
                    | _ -> ())
                  (Query.demand database Resolve.Names.declarations example);
                if tests_of database <> [] then
                  String.split_on_char '\n' (run_source text)
                  |> List.iter (fun line ->
                      match String.split_on_char ' ' line with
                      | [ "test"; _; ("passed" | "incomplete") ] | [ "test"; _ ] -> ()
                      | [ "test"; _; outcome ] -> fail "a test %s" outcome
                      | _ -> ())))
        (Documents.truss_blocks (Documents.read (Harness.workspace_path name))))

let () =
  test "a function value whose type uses Panic is called without evidence for Panic" (fun () ->
      let source = Fixtures.Program.function_value_whose_type_uses_panic_is_called in
      (match run_main source with
      | 0, output, _ -> expect_string ~expected:"counted 1\ndone 3\n" output
      | status, _, errors -> fail "ended with status %d: %s" status errors);
      match run_main ~arguments:[ "a"; "b"; "c"; "d" ] source with
      | 101, output, errors ->
          expect_string ~expected:"counted 5\n" output;
          if not (contains errors "many arguments") then fail "panicked with %S" errors
      | status, _, errors -> fail "ended with status %d: %s" status errors)
