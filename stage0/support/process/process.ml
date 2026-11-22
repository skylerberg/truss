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

let rec exchange piece ~readers ~writer =
  match (readers, writer) with
  | [], None -> ()
  | _ ->
      let readable, writable =
        match
          Unix.select
            (List.map (fun reader -> reader.descriptor) readers)
            (Option.to_list (Option.map (fun writer -> writer.stdin) writer))
            [] (-1.)
        with
        | readable, writable, _ -> (readable, writable)
        | exception Unix.Unix_error (EINTR, _, _) -> ([], [])
      in
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
      exchange piece ~readers ~writer

let rec await pid =
  match Unix.waitpid [] pid with
  | exception Unix.Unix_error (EINTR, _, _) -> await pid
  | _, status -> status

let run ?input ?on_output program arguments =
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
  Fun.protect
    ~finally:(fun () ->
      Unix.close stdout_read;
      Unix.close stderr_read;
      Option.iter (fun writer -> if writer.is_open then close_stdin writer) writer)
    (fun () -> exchange (Bytes.create piece_length) ~readers:[ output; errors ] ~writer);
  (exit_code (await pid), Buffer.contents output.contents, Buffer.contents errors.contents)

let run_attached program arguments =
  let pid =
    Unix.create_process program
      (Array.of_list (program :: arguments))
      Unix.stdin Unix.stdout Unix.stderr
  in
  let _, status = Unix.waitpid [] pid in
  exit_code status
