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

let hash_key key = Blake3.hash_to_hex ~digits:16 key

let make_server_path directory identity key =
  Filename.concat directory (shorten identity ^ "-" ^ hash_key key)

let locate_socket server_path =
  let path = server_path ^ ".socket" in
  if String.length path < 100 then path
  else
    Filename.concat
      (Printf.sprintf "/tmp/truss-%d" (Unix.getuid ()))
      (Blake3.hash_to_hex ~digits:16 path ^ ".socket")

let make_socket_path server_path =
  let path = locate_socket server_path in
  Result.map (fun _ -> path) (make_private_directory (Filename.dirname path))

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

let is_current descriptor path =
  match (Unix.fstat descriptor, Unix.stat path) with
  | held, named -> held.st_dev = named.st_dev && held.st_ino = named.st_ino
  | exception Unix.Unix_error (ENOENT, _, _) -> false

let rec acquire path =
  let descriptor = Unix.openfile path [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644 in
  match Unix.lockf descriptor F_LOCK 0 with
  | () when is_current descriptor path -> descriptor
  | () ->
      Unix.close descriptor;
      acquire path
  | exception failure ->
      Unix.close descriptor;
      raise failure

let with_start_lock server_path work =
  let path = server_path ^ ".start" in
  let descriptor = acquire path in
  Fun.protect
    ~finally:(fun () ->
      (try Unix.unlink path with Unix.Unix_error (ENOENT, _, _) -> ());
      Unix.close descriptor)
    work

let wait_until_released path =
  match Unix.openfile path [ O_RDWR; O_CLOEXEC ] 0 with
  | exception Unix.Unix_error (ENOENT, _, _) -> ()
  | descriptor ->
      Fun.protect
        ~finally:(fun () -> Unix.close descriptor)
        (fun () -> Unix.lockf descriptor F_LOCK 0)

let served : string option ref = ref None

let list_other_servers directory ~suffix =
  Array.to_list (Sys.readdir directory)
  |> List.filter_map (fun entry ->
      if Filename.check_suffix entry (suffix ^ ".key") then
        let server_path = Filename.concat directory (Filename.chop_suffix entry ".key") in
        if !served <> Some server_path && is_locked (server_path ^ ".lock") then Some server_path
        else None
      else None)

let list_servers () =
  match make_servers_directory () with
  | Error _ -> []
  | Ok directory ->
      let identity = compute_executable_identity () in
      list_other_servers directory ~suffix:""
      |> List.filter_map (fun server_path ->
          match File_system.read (server_path ^ ".key") with
          | key when make_server_path directory identity key = server_path -> Some key
          | _ | (exception Sys_error _) -> None)
      |> List.sort compare

let stop_servers ?key ~wait () =
  match make_servers_directory () with
  | Error _ -> false
  | Ok directory ->
      let suffix = Option.fold ~none:"" ~some:(fun key -> "-" ^ hash_key key) key in
      let running = list_other_servers directory ~suffix in
      List.iter
        (fun server_path ->
          try Unix.unlink (locate_socket server_path) with Unix.Unix_error (ENOENT, _, _) -> ())
        running;
      if wait then
        List.iter (fun server_path -> wait_until_released (server_path ^ ".lock")) running;
      running <> []

let idle_limit = 3. *. 3600.
let backlog = 128

let bind server_path path =
  wait_until_released (server_path ^ ".lock");
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
    (fun (_, server_path, path) -> with_start_lock server_path (fun () -> bind server_path path))

let connect path =
  let socket = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
  match Unix.connect socket (ADDR_UNIX path) with
  | () -> Some socket
  | exception Unix.Unix_error _ ->
      Unix.close socket;
      None

type claim = Claimed of Unix.file_descr | Held_elsewhere

let claim_without_waiting path =
  let descriptor = Unix.openfile path [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644 in
  match Unix.lockf descriptor F_TLOCK 0 with
  | () when is_current descriptor path -> Claimed descriptor
  | () | (exception Unix.Unix_error ((EAGAIN | EACCES), _, _)) ->
      Unix.close descriptor;
      Held_elsewhere

let remove_if_present path = try Unix.unlink path with Unix.Unix_error (ENOENT, _, _) -> ()

let accepts_connections path =
  match connect path with
  | Some socket ->
      Unix.close socket;
      true
  | None -> false

let list_server_paths directory =
  Array.to_list (Sys.readdir directory)
  |> List.filter_map (fun entry ->
      List.find_map
        (fun suffix ->
          if Filename.check_suffix entry suffix then
            Some (Filename.concat directory (Filename.chop_suffix entry suffix))
          else None)
        [ ".key"; ".lock"; ".start"; ".socket" ])
  |> List.sort_uniq String.compare

let remove_ended_server server_path =
  match claim_without_waiting (server_path ^ ".start") with
  | Held_elsewhere -> ()
  | Claimed start ->
      Fun.protect
        ~finally:(fun () ->
          remove_if_present (server_path ^ ".start");
          Unix.close start)
        (fun () ->
          match claim_without_waiting (server_path ^ ".lock") with
          | Held_elsewhere -> ()
          | Claimed lock ->
              Fun.protect
                ~finally:(fun () -> Unix.close lock)
                (fun () ->
                  let socket = locate_socket server_path in
                  if not (accepts_connections socket) then
                    List.iter remove_if_present
                      [ server_path ^ ".key"; socket; server_path ^ ".lock" ]))

let remove_ended_servers directory =
  List.iter
    (fun server_path ->
      if !served <> Some server_path then
        try remove_ended_server server_path with Unix.Unix_error _ | Sys_error _ -> ())
    (list_server_paths directory)

let send channel value =
  Marshal.to_channel channel value [];
  flush channel

type 'response message = Progress of string | Final of 'response

let serve_on ~key ~identity ~is_alive ~collect ~list_watcher_descriptors ~propagate ~handle ~save
    ~close server_path path socket =
  let lock = acquire (server_path ^ ".lock") in
  served := Some server_path;
  Out_channel.with_open_bin (server_path ^ ".key") (fun out -> output_string out key);
  let last = ref (Unix.time ()) in
  let last_collection = ref 0. in
  let is_replaced = ref false in
  while
    (not !is_replaced) && Unix.time () -. !last < idle_limit && is_alive () && Sys.file_exists path
  do
    match Unix.select (socket :: list_watcher_descriptors ()) [] [] 1.0 with
    | exception Unix.Unix_error (EINTR, _, _) -> ()
    | [], _, _ ->
        let now = Unix.time () in
        if now -. !last_collection > 60. then begin
          last_collection := now;
          is_replaced := compute_executable_identity () <> identity;
          collect ();
          remove_ended_servers (Filename.dirname server_path)
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
  (try Unix.unlink (server_path ^ ".lock") with Unix.Unix_error _ -> ());
  Unix.close lock;
  served := None

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

let connect_or_start ~program ~key directory server_path path =
  match connect path with
  | Some socket -> Ok socket
  | None ->
      with_start_lock server_path (fun () ->
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
  let remove_ended_servers () = Result.iter remove_ended_servers (make_servers_directory ())
end
