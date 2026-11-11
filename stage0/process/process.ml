let read_all channel =
  let buffer = Buffer.create 256 in
  (try
     while true do
       Buffer.add_channel buffer channel 1
     done
   with End_of_file -> ());
  Buffer.contents buffer

(* A process's status as a shell reports it: its exit code, or [128 +
   signal] for a process a signal ended. *)
let exit_code (status : Unix.process_status) =
  match status with
  | WEXITED code -> code
  | WSIGNALED signal | WSTOPPED signal ->
      (* OCaml numbers signals its own way; report the system's number. *)
      let system =
        List.assoc_opt signal
          [
            (Sys.sigabrt, 6);
            (Sys.sigsegv, 11);
            (Sys.sigkill, 9);
            (Sys.sigbus, 10);
            (Sys.sigfpe, 8);
            (Sys.sigill, 4);
            (Sys.sigterm, 15);
          ]
      in
      128 + Option.value system ~default:signal

(* Reads a channel to its end, handing each piece to [on_output] as it
   arrives. *)
let read_streaming channel on_output =
  let buffer = Buffer.create 256 in
  let piece = Bytes.create 65536 in
  let rec loop () =
    match input channel piece 0 (Bytes.length piece) with
    | 0 -> ()
    | n ->
        let text = Bytes.sub_string piece 0 n in
        Buffer.add_string buffer text;
        on_output text;
        loop ()
  in
  loop ();
  Buffer.contents buffer

(* The program is run with its arguments and no shell. *)
let run ?input ?on_output ?time_limit program arguments =
  let stdout_read, stdout_write = Unix.pipe ~cloexec:true () in
  let stderr_read, stderr_write = Unix.pipe ~cloexec:true () in
  let stdin_read, stdin_write =
    match input with
    | Some _ ->
        let read, write = Unix.pipe ~cloexec:true () in
        (read, Some write)
    | None -> (Unix.stdin, None)
  in
  let pid =
    Unix.create_process program
      (Array.of_list (program :: arguments))
      stdin_read stdout_write stderr_write
  in
  Unix.close stdout_write;
  Unix.close stderr_write;
  (* Write the input on another domain too, and close it, so the program
     sees its end. *)
  let writer =
    match (input, stdin_write) with
    | Some text, Some write ->
        (* A program that ends without reading it all closes the pipe, which
           must not end this process. *)
        Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
        Unix.close stdin_read;
        Some
          (Domain.spawn (fun () ->
               let channel = Unix.out_channel_of_descr write in
               (try output_string channel text with Sys_error _ -> ());
               try close_out channel with Sys_error _ -> ()))
    | _ -> None
  in
  (* A program that runs past its time limit is killed, and its status is
     that of [SIGKILL]. *)
  let ended = Atomic.make false in
  let watchdog =
    Option.map
      (fun limit ->
        Domain.spawn (fun () ->
            let deadline = Unix.gettimeofday () +. (float_of_int limit /. 1000.) in
            while (not (Atomic.get ended)) && Unix.gettimeofday () < deadline do
              Unix.sleepf 0.01
            done;
            if not (Atomic.get ended) then
              try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ()))
      time_limit
  in
  (* Read standard error on another domain, so neither pipe fills while the
     other is read. *)
  let errors = Domain.spawn (fun () -> read_all (Unix.in_channel_of_descr stderr_read)) in
  let output =
    let channel = Unix.in_channel_of_descr stdout_read in
    match on_output with
    | Some on_output -> read_streaming channel on_output
    | None -> read_all channel
  in
  let errors = Domain.join errors in
  Option.iter Domain.join writer;
  Unix.close stdout_read;
  Unix.close stderr_read;
  let _, status = Unix.waitpid [] pid in
  Atomic.set ended true;
  Option.iter Domain.join watchdog;
  (exit_code status, output, errors)

let run_attached program arguments =
  let pid =
    Unix.create_process program
      (Array.of_list (program :: arguments))
      Unix.stdin Unix.stdout Unix.stderr
  in
  let _, status = Unix.waitpid [] pid in
  exit_code status
