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
      match Unix.fork () with 0 -> Unix._exit 0 | child -> ignore (Unix.waitpid [] child))
