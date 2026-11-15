let executable () =
  try Unix.realpath Sys.executable_name with Unix.Unix_error _ -> Sys.executable_name

let executable_identity () =
  let directory = Store.default_directory () in
  let path = executable () in
  match Unix.stat path with
  | exception Unix.Unix_error _ -> "unknown"
  | stat -> (
      let tag =
        Printf.sprintf "%s %d %h %h %d" path stat.st_size stat.st_mtime stat.st_ctime stat.st_ino
      in
      let remembered = Filename.concat directory "identities" in
      let known =
        try
          In_channel.with_open_bin remembered In_channel.input_lines
          |> List.find_map (fun line ->
              match String.index_opt line '\t' with
              | Some separator when String.sub line 0 separator = tag ->
                  Some (String.sub line (separator + 1) (String.length line - separator - 1))
              | _ -> None)
        with Sys_error _ -> None
      in
      match known with
      | Some identity -> identity
      | None ->
          let identity = Blake3.hex_digest (File_system.read path) in
          (try
             Out_channel.with_open_gen [ Open_append; Open_creat; Open_binary ] 0o644 remembered
               (fun out -> Printf.fprintf out "%s\t%s\n" tag identity)
           with Sys_error _ -> ());
          identity)

let short identity = if String.length identity > 16 then String.sub identity 0 16 else identity

let private_directory directory =
  File_system.make_directory (Filename.dirname directory);
  (try Unix.mkdir directory 0o700 with Unix.Unix_error _ -> ());
  match Unix.lstat directory with
  | { st_kind = S_DIR; st_uid; st_perm; _ } when st_uid = Unix.getuid () && st_perm land 0o077 = 0
    ->
      Ok directory
  | _ | (exception Unix.Unix_error _) ->
      Error (directory ^ " is not a directory that only this user can use; try --no-server.")

let servers_directory () =
  private_directory (Filename.concat (Store.default_directory ()) "servers")

let server_path directory identity key =
  Filename.concat directory (short identity ^ "-" ^ Blake3.hex_digest ~digits:16 key)

let socket_path server_path =
  let path = server_path ^ ".socket" in
  if String.length path < 100 then Ok path
  else
    Result.map
      (fun directory -> Filename.concat directory (Blake3.hex_digest ~digits:16 path ^ ".socket"))
      (private_directory (Printf.sprintf "/tmp/truss-%d" (Unix.getuid ())))

let locked path =
  match Unix.openfile path [ O_RDWR; O_CLOEXEC ] 0 with
  | exception Unix.Unix_error _ -> false
  | descriptor ->
      Fun.protect
        ~finally:(fun () -> Unix.close descriptor)
        (fun () ->
          match Unix.lockf descriptor F_TEST 0 with
          | () -> false
          | exception Unix.Unix_error _ -> true)

let served : string option ref = ref None

let running key =
  !served = Some key
  ||
  match servers_directory () with
  | Ok directory -> locked (server_path directory (executable_identity ()) key ^ ".lock")
  | Error _ -> false

let serving () =
  match servers_directory () with
  | Error _ -> []
  | Ok directory ->
      let prefix = short (executable_identity ()) ^ "-" in
      Array.to_list (Sys.readdir directory)
      |> List.filter_map (fun entry ->
          if String.starts_with ~prefix entry && Filename.check_suffix entry ".key" then
            let path = Filename.concat directory entry in
            match File_system.read path with
            | key when running key -> Some key
            | _ | (exception Sys_error _) -> None
          else None)
      |> List.sort compare

let idle_limit = 3. *. 3600.

let send channel value =
  Marshal.to_channel channel value [];
  flush channel

type 'response message = Progress of string | Final of 'response

let stopping = ref false
let stop () = stopping := true

let serve_at ~key ~identity ~alive ~collect ~watched ~changed ~handle server_path path =
  let lock = Unix.openfile (server_path ^ ".lock") [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644 in
  match Unix.lockf lock F_TLOCK 0 with
  | exception Unix.Unix_error _ -> ()
  | () ->
      served := Some key;
      Out_channel.with_open_bin (server_path ^ ".key") (fun out -> output_string out key);
      (try Unix.unlink path with Unix.Unix_error _ -> ());
      let socket = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
      Unix.bind socket (ADDR_UNIX path);
      Unix.listen socket 16;
      let last = ref (Unix.time ()) in
      let last_collection = ref 0. in
      while (not !stopping) && Unix.time () -. !last < idle_limit && alive () do
        match Unix.select (socket :: watched ()) [] [] 1.0 with
        | exception Unix.Unix_error (EINTR, _, _) -> ()
        | [], _, _ ->
            let now = Unix.time () in
            if now -. !last_collection > 60. then begin
              last_collection := now;
              if executable_identity () <> identity then stopping := true;
              collect ()
            end
        | ready, _, _ when not (List.mem socket ready) -> List.iter changed ready
        | _ -> (
            match Unix.accept ~cloexec:true socket with
            | exception Unix.Unix_error _ -> ()
            | client, _ -> (
                last := Unix.time ();
                let input = Unix.in_channel_of_descr client in
                let output = Unix.out_channel_of_descr client in
                (try
                   let request = Marshal.from_channel input in
                   let progress text = send output (Progress text) in
                   send output (Final (handle ~progress request))
                 with _ -> ());
                try Unix.close client with Unix.Unix_error _ -> ()))
      done;
      (try Unix.unlink path with Unix.Unix_error _ -> ());
      (try Sys.remove (server_path ^ ".key") with Sys_error _ -> ());
      Unix.close lock

let serve ~key ~alive ~collect ~watched ~changed ~handle =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  match servers_directory () with
  | Error message -> prerr_endline message
  | Ok directory -> (
      let identity = executable_identity () in
      let server_path = server_path directory identity key in
      match socket_path server_path with
      | Error message -> prerr_endline message
      | Ok path ->
          serve_at ~key ~identity ~alive ~collect ~watched ~changed ~handle server_path path)

let start directory program key =
  let log = Filename.concat directory "server.log" in
  match Unix.fork () with
  | 0 -> (
      ignore (Unix.setsid ());
      match Unix.fork () with
      | 0 ->
          let null = Unix.openfile "/dev/null" [ O_RDONLY ] 0 in
          let out = Unix.openfile log [ O_WRONLY; O_CREAT; O_APPEND ] 0o644 in
          Unix.dup2 null Unix.stdin;
          Unix.dup2 out Unix.stdout;
          Unix.dup2 out Unix.stderr;
          (try Unix.execv program [| program; "__serve"; key |] with _ -> ());
          Unix._exit 1
      | _ -> Unix._exit 0)
  | child -> ignore (Unix.waitpid [] child)

let connect path =
  let socket = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
  match Unix.connect socket (ADDR_UNIX path) with
  | () -> Some socket
  | exception Unix.Unix_error _ ->
      Unix.close socket;
      None

let call ?program ?(start_server = true) ~key ~progress request =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let identity = executable_identity () in
  let program = Option.value program ~default:(executable ()) in
  let ( let* ) = Result.bind in
  let* directory = servers_directory () in
  let* path = socket_path (server_path directory identity key) in
  let rec attempt tries =
    match connect path with
    | Some socket -> Some socket
    | None ->
        if tries = 0 || not start_server then None
        else begin
          if tries = 50 then start directory program key;
          Unix.sleepf 0.1;
          attempt (tries - 1)
        end
  in
  match attempt 50 with
  | None when not start_server -> Error "No background process is running."
  | None -> Error "could not start or reach the background process; try --no-server."
  | Some socket -> (
      let input = Unix.in_channel_of_descr socket in
      let output = Unix.out_channel_of_descr socket in
      let rec receive () =
        match Marshal.from_channel input with
        | Progress text ->
            progress text;
            receive ()
        | Final response -> response
      in
      match
        send output request;
        receive ()
      with
      | response ->
          Unix.close socket;
          Ok response
      | exception _ ->
          (try Unix.close socket with Unix.Unix_error _ -> ());
          Error
            "the background process ended while answering; see its log in the store's servers \
             directory.")
