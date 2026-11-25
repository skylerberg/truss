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
  closes_after_text : bool;
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
        if writer.closes_after_text then close_stdin writer;
        false
      end
  | exception Unix.Unix_error ((EAGAIN | EWOULDBLOCK | EINTR), _, _) -> true
  | exception Unix.Unix_error (EPIPE, _, _) ->
      if writer.closes_after_text then close_stdin writer;
      false

let rec exchange ?(is_answered = fun () -> false) piece ~readers ~writer =
  match (readers, writer) with
  | [], None -> ()
  | _, None when is_answered () -> ()
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
      exchange ~is_answered piece ~readers ~writer

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
        Some { stdin; text; written = 0; is_open = true; closes_after_text = true }
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

type coprocess = { pid : int; standard_input : Unix.file_descr; standard_output : Unix.file_descr }

let start program arguments =
  let stdin_read, standard_input = Unix.pipe ~cloexec:true () in
  let standard_output, stdout_write = Unix.pipe ~cloexec:true () in
  let close_all descriptors = List.iter Unix.close descriptors in
  match
    Unix.create_process program
      (Array.of_list (program :: arguments))
      stdin_read stdout_write Unix.stderr
  with
  | pid ->
      close_all [ stdin_read; stdout_write ];
      Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
      Unix.set_nonblock standard_input;
      { pid; standard_input; standard_output }
  | exception error ->
      close_all [ stdin_read; standard_input; standard_output; stdout_write ];
      raise error

let converse coprocess text ~until =
  let output =
    { descriptor = coprocess.standard_output; contents = Buffer.create 4096; on_read = None }
  in
  let last_line = until ^ "\n" in
  let is_answered () =
    let length = Buffer.length output.contents and line_length = String.length last_line in
    length >= line_length
    && Buffer.sub output.contents (length - line_length) line_length = last_line
    && (length = line_length || Buffer.nth output.contents (length - line_length - 1) = '\n')
  in
  exchange ~is_answered (Bytes.create piece_length) ~readers:[ output ]
    ~writer:
      (Some
         {
           stdin = coprocess.standard_input;
           text;
           written = 0;
           is_open = true;
           closes_after_text = false;
         });
  if is_answered () then
    Ok (Buffer.sub output.contents 0 (Buffer.length output.contents - String.length last_line))
  else Error (Buffer.contents output.contents)

let stop coprocess =
  Unix.close coprocess.standard_input;
  Unix.close coprocess.standard_output;
  (try Unix.kill coprocess.pid Sys.sigkill with Unix.Unix_error (ESRCH, _, _) -> ());
  ignore (await coprocess.pid)
