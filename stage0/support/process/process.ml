let exit_code (status : Unix.process_status) =
  match status with
  | WEXITED code -> code
  | WSIGNALED signal | WSTOPPED signal -> 128 + Sys.signal_to_int signal

type reader = {
  descriptor : Unix.file_descr;
  contents : Buffer.t;
  on_read : (string -> unit) option;
}

type writer = {
  stdin : Unix.file_descr;
  text : string;
  mutable written : int;
  mutable is_open : bool;
}

let piece_length = 65536

let read_piece piece reader =
  match Unix.read reader.descriptor piece 0 piece_length with
  | 0 -> false
  | count ->
      Buffer.add_subbytes reader.contents piece 0 count;
      Option.iter (fun on_read -> on_read (Bytes.sub_string piece 0 count)) reader.on_read;
      true
  | exception Unix.Unix_error (EINTR, _, _) -> true

let close_stdin writer =
  writer.is_open <- false;
  Unix.close writer.stdin

let write_piece writer =
  match
    Unix.single_write_substring writer.stdin writer.text writer.written
      (min piece_length (String.length writer.text - writer.written))
  with
  | count ->
      writer.written <- writer.written + count;
      if writer.written < String.length writer.text then true
      else begin
        close_stdin writer;
        false
      end
  | exception Unix.Unix_error ((EAGAIN | EWOULDBLOCK | EINTR), _, _) -> true
  | exception Unix.Unix_error (EPIPE, _, _) ->
      close_stdin writer;
      false

let kill pid = try Unix.kill pid Sys.sigkill with Unix.Unix_error (ESRCH, _, _) -> ()

type deadline = Unlimited | Until of float | Passed

let stop_at_deadline pid deadline =
  match deadline with
  | Until at when Unix.gettimeofday () >= at ->
      kill pid;
      Passed
  | Unlimited | Until _ | Passed -> deadline

let rec exchange piece pid ~readers ~writer ~deadline =
  match (readers, writer) with
  | [], None -> deadline
  | _ -> (
      let timeout =
        match deadline with
        | Until at -> Float.max 0. (at -. Unix.gettimeofday ())
        | Unlimited | Passed -> -1.
      in
      let readable, writable =
        match
          Unix.select
            (List.map (fun reader -> reader.descriptor) readers)
            (Option.to_list (Option.map (fun writer -> writer.stdin) writer))
            [] timeout
        with
        | readable, writable, _ -> (readable, writable)
        | exception Unix.Unix_error (EINTR, _, _) -> ([], [])
      in
      match stop_at_deadline pid deadline with
      | Passed -> Passed
      | (Unlimited | Until _) as deadline ->
          let readers =
            List.filter
              (fun reader -> (not (List.mem reader.descriptor readable)) || read_piece piece reader)
              readers
          in
          let writer =
            Option.bind writer (fun writer ->
                if (not (List.mem writer.stdin writable)) || write_piece writer then Some writer
                else None)
          in
          exchange piece pid ~readers ~writer ~deadline)

let rec await pid deadline =
  match
    Unix.waitpid (match deadline with Until _ -> [ WNOHANG ] | Unlimited | Passed -> []) pid
  with
  | exception Unix.Unix_error (EINTR, _, _) -> await pid deadline
  | 0, _ -> (
      match stop_at_deadline pid deadline with
      | Passed -> await pid Passed
      | (Unlimited | Until _) as deadline ->
          Unix.sleepf 0.01;
          await pid deadline)
  | _, status -> (deadline, status)

let execute ?input ?on_output ~deadline program arguments =
  let stdout_read, stdout_write = Unix.pipe ~cloexec:true () in
  let stderr_read, stderr_write = Unix.pipe ~cloexec:true () in
  let stdin_pipe = Option.map (fun _ -> Unix.pipe ~cloexec:true ()) input in
  let pid =
    Fun.protect
      ~finally:(fun () ->
        Unix.close stdout_write;
        Unix.close stderr_write;
        Option.iter (fun (stdin_read, _) -> Unix.close stdin_read) stdin_pipe)
      (fun () ->
        try
          Unix.create_process program
            (Array.of_list (program :: arguments))
            (Option.fold ~none:Unix.stdin ~some:fst stdin_pipe)
            stdout_write stderr_write
        with error ->
          Unix.close stdout_read;
          Unix.close stderr_read;
          Option.iter (fun (_, stdin_write) -> Unix.close stdin_write) stdin_pipe;
          raise error)
  in
  let output = { descriptor = stdout_read; contents = Buffer.create 4096; on_read = on_output } in
  let errors = { descriptor = stderr_read; contents = Buffer.create 256; on_read = None } in
  let writer =
    match (input, stdin_pipe) with
    | Some text, Some (_, stdin) ->
        Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
        Unix.set_nonblock stdin;
        Some { stdin; text; written = 0; is_open = true }
    | _ -> None
  in
  let deadline_after_reading =
    Fun.protect
      ~finally:(fun () ->
        Unix.close stdout_read;
        Unix.close stderr_read;
        Option.iter (fun writer -> if writer.is_open then close_stdin writer) writer)
      (fun () ->
        exchange (Bytes.create piece_length) pid ~readers:[ output; errors ] ~writer ~deadline)
  in
  let deadline, status = await pid deadline_after_reading in
  (deadline, (exit_code status, Buffer.contents output.contents, Buffer.contents errors.contents))

let run ?input ?on_output program arguments =
  snd (execute ?input ?on_output ~deadline:Unlimited program arguments)

let run_with_time_limit ?input ~time_limit_ms program arguments =
  let deadline = Until (Unix.gettimeofday () +. (Float.of_int time_limit_ms /. 1000.)) in
  match execute ?input ~deadline program arguments with
  | Passed, _ -> None
  | (Unlimited | Until _), result -> Some result

let run_attached program arguments =
  let pid =
    Unix.create_process program
      (Array.of_list (program :: arguments))
      Unix.stdin Unix.stdout Unix.stderr
  in
  let _, status = Unix.waitpid [] pid in
  exit_code status
