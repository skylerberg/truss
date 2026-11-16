let locate_executable () =
  try Unix.realpath Sys.executable_name with Unix.Unix_error _ -> Sys.executable_name

let read_stamp path =
  match Unix.stat path with
  | stat -> Some (Printf.sprintf "%d %h %h %d" stat.st_size stat.st_mtime stat.st_ctime stat.st_ino)
  | exception Unix.Unix_error _ -> None

let make_cache_root () = Result.bind (Cache.locate_default_directory ()) Cache.make_root

let compute_executable_identity () =
  let path = locate_executable () in
  let digest_executable () = Blake3.hash_to_hex (File_system.read path) in
  match (read_stamp path, make_cache_root ()) with
  | None, _ -> "unknown"
  | Some _, Error _ -> digest_executable ()
  | Some current, Ok root -> (
      let remembered = Filename.concat root "identities" in
      let entries =
        (try In_channel.with_open_bin remembered In_channel.input_lines with Sys_error _ -> [])
        |> List.filter_map (fun line ->
            match String.split_on_char '\t' line with
            | [ path; stamp; identity ] -> Some (path, stamp, identity)
            | _ -> None)
      in
      match
        List.find_opt (fun (known, known_stamp, _) -> known = path && known_stamp = current) entries
      with
      | Some (_, _, identity) -> identity
      | None ->
          let identity = digest_executable () in
          let existing =
            List.filter
              (fun (known, known_stamp, _) -> known <> path && read_stamp known = Some known_stamp)
              entries
          in
          (try
             File_system.write_atomically remembered
               (String.concat ""
                  (List.map
                     (fun (path, stamp, identity) ->
                       Printf.sprintf "%s\t%s\t%s\n" path stamp identity)
                     (existing @ [ (path, current, identity) ])))
           with Sys_error _ -> ());
          identity)

let shorten identity = if String.length identity > 16 then String.sub identity 0 16 else identity

let make_private_directory directory =
  (try Unix.mkdir directory 0o700 with Unix.Unix_error _ -> ());
  match Unix.lstat directory with
  | { st_kind = S_DIR; st_uid; st_perm; _ } when st_uid = Unix.getuid () && st_perm land 0o077 = 0
    ->
      Ok directory
  | _ | (exception Unix.Unix_error _) ->
      Error (directory ^ " is not a directory that only this user can use; try --no-server.")

let make_servers_directory () =
  Result.bind (make_cache_root ()) (fun root ->
      make_private_directory (Filename.concat root "servers"))

let make_server_path directory identity key =
  Filename.concat directory (shorten identity ^ "-" ^ Blake3.hash_to_hex ~digits:16 key)

let make_socket_path server_path =
  let path = server_path ^ ".socket" in
  if String.length path < 100 then Ok path
  else
    Result.map
      (fun directory -> Filename.concat directory (Blake3.hash_to_hex ~digits:16 path ^ ".socket"))
      (make_private_directory (Printf.sprintf "/tmp/truss-%d" (Unix.getuid ())))

let make_server_paths identity key =
  Result.bind (make_servers_directory ()) (fun directory ->
      let server_path = make_server_path directory identity key in
      Result.map (fun path -> (directory, server_path, path)) (make_socket_path server_path))

let is_locked path =
  match Unix.openfile path [ O_RDWR; O_CLOEXEC ] 0 with
  | exception Unix.Unix_error _ -> false
  | descriptor ->
      Fun.protect
        ~finally:(fun () -> Unix.close descriptor)
        (fun () ->
          match Unix.lockf descriptor F_TEST 0 with
          | () -> false
          | exception Unix.Unix_error _ -> true)

let with_lock path work =
  let descriptor = Unix.openfile path [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644 in
  Fun.protect
    ~finally:(fun () -> Unix.close descriptor)
    (fun () ->
      Unix.lockf descriptor F_LOCK 0;
      work ())

let served : string option ref = ref None

let is_running key =
  !served = Some key
  ||
  match make_servers_directory () with
  | Ok directory ->
      is_locked (make_server_path directory (compute_executable_identity ()) key ^ ".lock")
  | Error _ -> false

let list_servers () =
  match make_servers_directory () with
  | Error _ -> []
  | Ok directory ->
      let prefix = shorten (compute_executable_identity ()) ^ "-" in
      Array.to_list (Sys.readdir directory)
      |> List.filter_map (fun entry ->
          if String.starts_with ~prefix entry && Filename.check_suffix entry ".key" then
            let path = Filename.concat directory entry in
            match File_system.read path with
            | key when is_running key -> Some key
            | _ | (exception Sys_error _) -> None
          else None)
      |> List.sort compare

let wait_until_ended ~key =
  match make_server_paths (compute_executable_identity ()) key with
  | Ok (_, server_path, _) -> with_lock (server_path ^ ".lock") ignore
  | Error _ -> ()

let idle_limit = 3. *. 3600.
let backlog = 128

let bind server_path path =
  with_lock (server_path ^ ".lock") ignore;
  (try Unix.unlink path with Unix.Unix_error _ -> ());
  let socket = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
  match
    Unix.bind socket (ADDR_UNIX path);
    Unix.listen socket backlog
  with
  | () -> Ok socket
  | exception Unix.Unix_error (error, _, _) ->
      Unix.close socket;
      Error (Printf.sprintf "Cannot listen on %s: %s." path (Unix.error_message error))

let listen ~key =
  Result.bind
    (make_server_paths (compute_executable_identity ()) key)
    (fun (_, server_path, path) ->
      with_lock (server_path ^ ".start") (fun () -> bind server_path path))

let send channel value =
  Marshal.to_channel channel value [];
  flush channel

type 'response message = Progress of string | Final of 'response

let stopping = ref false
let stop () = stopping := true

let serve_on ~key ~identity ~is_alive ~collect ~list_watcher_descriptors ~propagate ~handle ~save
    ~close server_path path socket =
  let lock = Unix.openfile (server_path ^ ".lock") [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644 in
  Unix.lockf lock F_LOCK 0;
  served := Some key;
  Out_channel.with_open_bin (server_path ^ ".key") (fun out -> output_string out key);
  let last = ref (Unix.time ()) in
  let last_collection = ref 0. in
  while
    (not !stopping) && Unix.time () -. !last < idle_limit && is_alive () && Sys.file_exists path
  do
    match Unix.select (socket :: list_watcher_descriptors ()) [] [] 1.0 with
    | exception Unix.Unix_error (EINTR, _, _) -> ()
    | [], _, _ ->
        let now = Unix.time () in
        if now -. !last_collection > 60. then begin
          last_collection := now;
          if compute_executable_identity () <> identity then stopping := true;
          collect ()
        end
    | ready, _, _ when not (List.mem socket ready) -> List.iter propagate ready
    | _ -> (
        match Unix.accept ~cloexec:true socket with
        | exception Unix.Unix_error _ -> ()
        | client, _ -> (
            last := Unix.time ();
            let input = Unix.in_channel_of_descr client in
            let output = Unix.out_channel_of_descr client in
            (try
               let request = Marshal.from_channel input in
               let report_progress text = send output (Progress text) in
               send output (Final (handle ~report_progress request))
             with _ -> ());
            (try Unix.close client with Unix.Unix_error _ -> ());
            try save () with failure -> prerr_endline (Printexc.to_string failure)))
  done;
  (try Unix.unlink path with Unix.Unix_error _ -> ());
  Unix.close socket;
  close ();
  (try Sys.remove (server_path ^ ".key") with Sys_error _ -> ());
  Unix.close lock

let find_inherited_socket () =
  match Unix.fstat Unix.stdin with
  | { st_kind = S_SOCK; _ } ->
      let socket = Unix.dup ~cloexec:true Unix.stdin in
      let null = Unix.openfile "/dev/null" [ O_RDONLY; O_CLOEXEC ] 0 in
      Unix.dup2 null Unix.stdin;
      Unix.close null;
      Some socket
  | _ | (exception Unix.Unix_error _) -> None

let serve ~key ~is_alive ~collect ~list_watcher_descriptors ~propagate ~handle ~save ~close =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let identity = compute_executable_identity () in
  match (make_server_paths identity key, find_inherited_socket ()) with
  | Error message, _ -> prerr_endline message
  | Ok _, None -> prerr_endline "The background process was started without its socket."
  | Ok (_, server_path, path), Some socket ->
      serve_on ~key ~identity ~is_alive ~collect ~list_watcher_descriptors ~propagate ~handle ~save
        ~close server_path path socket

let start directory program key socket =
  let log = Filename.concat directory "server.log" in
  match Unix.fork () with
  | 0 -> (
      ignore (Unix.setsid ());
      match Unix.fork () with
      | 0 ->
          let out = Unix.openfile log [ O_WRONLY; O_CREAT; O_APPEND ] 0o644 in
          Unix.dup2 socket Unix.stdin;
          Unix.dup2 out Unix.stdout;
          Unix.dup2 out Unix.stderr;
          (try Unix.execv program [| program; "__serve"; key |]
           with Unix.Unix_error (error, _, _) ->
             File_system.write_all Unix.stderr
               (Printf.sprintf "Cannot start %s: %s.\n" program (Unix.error_message error)));
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

let connect_or_start ~program ~key directory server_path path =
  match connect path with
  | Some socket -> Ok socket
  | None ->
      with_lock (server_path ^ ".start") (fun () ->
          match connect path with
          | Some socket -> Ok socket
          | None when Sys.file_exists path && is_locked (server_path ^ ".lock") ->
              Error "The background process refused the connection; try again, or try --no-server."
          | None ->
              Result.bind (bind server_path path) (fun listening ->
                  Fun.protect
                    ~finally:(fun () -> Unix.close listening)
                    (fun () ->
                      start directory program key listening;
                      Option.to_result ~none:"Cannot reach the background process; try --no-server."
                        (connect path))))

let call_starting ~program ?(start_server = true) ~key ~report_progress request =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let ( let* ) = Result.bind in
  let* directory, server_path, path = make_server_paths (compute_executable_identity ()) key in
  let* socket =
    if start_server then connect_or_start ~program ~key directory server_path path
    else Option.to_result ~none:"No background process is running." (connect path)
  in
  let input = Unix.in_channel_of_descr socket in
  let output = Unix.out_channel_of_descr socket in
  let rec receive () =
    match Marshal.from_channel input with
    | Progress text ->
        report_progress text;
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
        "the background process ended while answering; see its log in the cache's servers \
         directory."

let call ?start_server ~key ~report_progress request =
  call_starting ~program:(locate_executable ()) ?start_server ~key ~report_progress request

module For_testing = struct
  let call_starting = call_starting
end
