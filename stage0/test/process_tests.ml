let mebibyte = String.make 1_048_576 'x'

let () =
  Harness.test "a program that fills standard error before it reads its input does not deadlock"
    (fun () ->
      let status, output, errors =
        Process.run ~input:mebibyte "/bin/sh"
          [ "-c"; "head -c 1048576 /dev/zero | tr '\\000' x >&2; cat" ]
      in
      if status <> 0 then Harness.fail "status %d" status;
      if output <> mebibyte then Harness.fail "%d bytes of output" (String.length output);
      if errors <> mebibyte then Harness.fail "%d bytes of errors" (String.length errors));
  Harness.test "a program that exits without reading its input does not end this process by SIGPIPE"
    (fun () ->
      Sys.set_signal Sys.sigpipe Sys.Signal_default;
      let status, _, _ = Process.run ~input:mebibyte "/bin/sh" [ "-c"; "exit 3" ] in
      if status <> 3 then Harness.fail "status %d" status);
  Harness.test "a process that has run a program can still fork" (fun () ->
      ignore (Process.run ~input:"" ~on_output:ignore "/bin/sh" [ "-c"; "echo" ]);
      match Unix.fork () with 0 -> Unix._exit 0 | child -> ignore (Unix.waitpid [] child));
  Harness.test "a coprocess answers each text up to the line that ends its answer" (fun () ->
      let echo = Process.start "/bin/cat" [] in
      let first = Process.converse echo "one\nend\n" ~until:"end" in
      let second = Process.converse echo "two\nwithout end\nend\n" ~until:"end" in
      Process.stop echo;
      if (first, second) <> (Ok "one\n", Ok "two\nwithout end\n") then
        Harness.fail "the coprocess did not answer both texts");
  Harness.test "a coprocess that exits before its answer ends gives what it wrote" (fun () ->
      let quitter = Process.start "/bin/sh" [ "-c"; "echo partial" ] in
      let answer = Process.converse quitter "ignored\n" ~until:"end" in
      Process.stop quitter;
      if answer <> Error "partial\n" then Harness.fail "expected the partial output");
  Harness.test "a coprocess that writes before it has read its whole input does not deadlock"
    (fun () ->
      let echo = Process.start "/bin/cat" [] in
      let answer = Process.converse echo (mebibyte ^ "\nend\n") ~until:"end" in
      Process.stop echo;
      if answer <> Ok (mebibyte ^ "\n") then Harness.fail "the megabyte did not come back")
