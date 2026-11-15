open Harness

let mebibyte = String.make 1_048_576 'x'
let fills_both_outputs = "TRUSS_PROCESS_TESTS_FILLS_BOTH_OUTPUTS"

let () =
  if Option.is_some (Sys.getenv_opt fills_both_outputs) then begin
    Out_channel.output_string stderr mebibyte;
    Out_channel.flush stderr;
    Out_channel.output_string stdout (In_channel.input_all stdin);
    Out_channel.flush stdout;
    Unix._exit 0
  end

let () =
  test "a program still running at its time limit is stopped, though its child holds its output"
    (fun () ->
      let started = Unix.gettimeofday () in
      (match
         Process.run_with_time_limit ~time_limit_ms:100 "/bin/sh" [ "-c"; "sleep 5 & sleep 5" ]
       with
      | None -> ()
      | Some (status, _, _) -> fail "it finished with status %d" status);
      if Unix.gettimeofday () -. started > 2. then fail "it was not stopped");
  test "a program that exits before it is stopped at its time limit is past it, not finished"
    (fun () ->
      match Process.run_with_time_limit ~time_limit_ms:0 "/bin/sh" [ "-c"; "echo finished" ] with
      | None -> ()
      | Some (status, output, _) -> fail "it finished with status %d and output %S" status output);
  test "a program that fills both outputs before it reads its input does not deadlock" (fun () ->
      match
        Process.run_with_time_limit
          ~environment:[ (fills_both_outputs, "") ]
          ~input:mebibyte ~time_limit_ms:10_000 Sys.executable_name []
      with
      | None -> fail "it ran past its time limit"
      | Some (status, output, errors) ->
          if status <> 0 then fail "status %d" status;
          if output <> mebibyte then fail "%d bytes of output" (String.length output);
          if errors <> mebibyte then fail "%d bytes of errors" (String.length errors));
  test "a program that exits without reading its input does not end this process by SIGPIPE"
    (fun () ->
      Sys.set_signal Sys.sigpipe Sys.Signal_default;
      let status, _, _ = Process.run ~input:mebibyte "/bin/sh" [ "-c"; "exit 3" ] in
      if status <> 3 then fail "status %d" status);
  test "a process that has run a program can still fork" (fun () ->
      ignore
        (Process.run_with_time_limit ~input:"" ~on_output:ignore ~time_limit_ms:10_000 "/bin/sh"
           [ "-c"; "echo" ]);
      match Unix.fork () with 0 -> Unix._exit 0 | child -> ignore (Unix.waitpid [] child))
