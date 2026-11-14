(* The background process: one per user and compiler, which holds sessions
   between commands. *)

(* Only the user may reach the background process: the data on its
   socket is marshaled, and reading marshaled bytes from another user would
   let that user run code as this one. *)
let servers_directory () =
  let directory = Filename.concat (Store.default_directory ()) "servers" in
  File_system.make_directory directory;
  (try Unix.chmod directory 0o700 with Unix.Unix_error _ -> ());
  directory

(* A directory in /tmp that is the user's alone. Another user could have
   made one of this name first, so it is used only if it is a directory,
   this user's, and closed to everyone else. *)
let private_temporary_directory () =
  let directory = Printf.sprintf "/tmp/truss-%d" (Unix.getuid ()) in
  (try Unix.mkdir directory 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  match Unix.lstat directory with
  | { st_kind = S_DIR; st_uid; st_perm; _ } when st_uid = Unix.getuid () && st_perm land 0o077 = 0
    ->
      Ok directory
  | _ | (exception Unix.Unix_error _) ->
      Error (directory ^ " is not a directory that only this user can use; try --no-server.")

(* A background process serves one key, which a client gives: a project's
   root. Its socket and its lock are named by the compiler's identity and a
   hash of the key, and a file beside them says the key. A socket's path
   has a short limit, about 100 bytes, so one under a long store path goes
   in a directory of the user's own in /tmp, named by a hash of where it
   would have been. *)
let server_path identity key =
  Filename.concat (servers_directory ())
    (Identity.short identity ^ "-" ^ Blake3.hex_digest ~digits:16 key)

let socket_path identity key =
  let path = server_path identity key ^ ".socket" in
  if String.length path < 100 then Ok path
  else
    Result.map
      (fun directory -> Filename.concat directory (Blake3.hex_digest ~digits:16 path ^ ".socket"))
      (private_temporary_directory ())

(* Whether a process holds a lock file's lock. *)
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

(* The key this process serves, if it is a background process. *)
let served : string option ref = ref None

(* Whether a background process of this compiler serves a key now. A
   process does not test its own lock: closing any descriptor of a file
   releases the process's lock on it. *)
let running key =
  !served = Some key
  || locked (server_path (Identity.compute (Store.default_directory ())) key ^ ".lock")

(* The keys that background processes of this compiler serve now. *)
let serving () =
  let identity = Identity.compute (Store.default_directory ()) in
  let prefix = Identity.short identity ^ "-" in
  let directory = servers_directory () in
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

(* A lock that is held only while [work] runs. Closing the descriptor
   releases it. *)
let holding path work =
  let descriptor = Unix.openfile path [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644 in
  Fun.protect
    ~finally:(fun () -> Unix.close descriptor)
    (fun () ->
      Unix.lockf descriptor F_LOCK 0;
      work ())

(* The queue of connections that wait to be accepted. macOS refuses a
   connection once the queue is full, which a client would take for a
   process that is gone. *)
let backlog = 128

(* Binds a key's socket, for one process to serve. Clients start the
   process under the start lock, so two never bind the socket at once. A
   process that still holds the key's lock has closed its socket and is
   saving its sessions; the new socket waits for it, so its sessions are
   saved before the next process opens them. *)
let bind identity key path =
  holding (server_path identity key ^ ".lock") ignore;
  (try Unix.unlink path with Unix.Unix_error _ -> ());
  let socket = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
  match
    Unix.bind socket (ADDR_UNIX path);
    Unix.listen socket backlog
  with
  | () -> Ok socket
  | exception Unix.Unix_error (error, _, _) ->
      Unix.close socket;
      Error (Printf.sprintf "cannot listen on %s: %s" path (Unix.error_message error))

let start_lock identity key = server_path identity key ^ ".start"

let listen ~key =
  let identity = Identity.compute (Store.default_directory ()) in
  Result.bind (socket_path identity key) (fun path ->
      holding (start_lock identity key) (fun () -> bind identity key path))

let serve_on ~key ~alive ~idle ~answered ~keep ~handle identity path socket =
  let lock =
    Unix.openfile (server_path identity key ^ ".lock") [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644
  in
  (* The client bound the socket once the previous process of the key let
     go of the lock, so the lock is free, or is being let go of. *)
  Unix.lockf lock F_LOCK 0;
  Core.serving := true;
  served := Some key;
  Out_channel.with_open_bin (server_path identity key ^ ".key") (fun out -> output_string out key);
  let last = ref (Unix.time ()) in
  let last_collection = ref 0. in
  while (not !stopping) && Unix.time () -. !last < idle_limit && alive () do
    match Unix.select [ socket ] [] [] 1.0 with
    | exception Unix.Unix_error (EINTR, _, _) -> ()
    | [], _, _ ->
        let now = Unix.time () in
        Core.drop_idle ();
        idle ();
        if now -. !last_collection > 60. then begin
          last_collection := now;
          (* A compiler that was built again has another identity, and
             its clients start a process of their own, so this one would
             only scan worktrees for no one. *)
          if Identity.compute (Store.default_directory ()) <> Core.identity () then stopping := true;
          Core.collect ~keep
        end
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
            (try Unix.close client with Unix.Unix_error _ -> ());
            (* The client has its response, so it does not wait for the
               request's sessions to reach the disk. *)
            try answered () with _ -> ()))
  done;
  (* A client that finds no socket starts the next process, whose socket
     waits for this one's lock, so the sessions are saved before it opens
     them. *)
  (try Unix.unlink path with Unix.Unix_error _ -> ());
  Unix.close socket;
  Core.reset ();
  (try Sys.remove (server_path identity key ^ ".key") with Sys_error _ -> ());
  Unix.close lock

(* The socket that the client which started this process bound, which it
   passes as standard input. *)
let inherited_socket () =
  match Unix.fstat Unix.stdin with
  | { st_kind = S_SOCK; _ } ->
      let socket = Unix.dup ~cloexec:true Unix.stdin in
      let null = Unix.openfile "/dev/null" [ O_RDONLY; O_CLOEXEC ] 0 in
      Unix.dup2 ~cloexec:false null Unix.stdin;
      Unix.close null;
      Some socket
  | _ | (exception Unix.Unix_error _) -> None

let serve ~key ?socket ~alive ~idle ~answered ~keep ~handle () =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let identity = Core.identity () in
  match
    (socket_path identity key, match socket with Some _ -> socket | None -> inherited_socket ())
  with
  | Error message, _ -> prerr_endline message
  | Ok _, None -> prerr_endline "The background process was started without its socket."
  | Ok path, Some socket -> serve_on ~key ~alive ~idle ~answered ~keep ~handle identity path socket

(* Starts the background process, detached from the client's terminal,
   with the socket as its standard input. *)
let spawn program key socket =
  let log = Filename.concat (servers_directory ()) "server.log" in
  match Unix.fork () with
  | 0 -> (
      ignore (Unix.setsid ());
      match Unix.fork () with
      | 0 ->
          let out = Unix.openfile log [ O_WRONLY; O_CREAT; O_APPEND ] 0o644 in
          Unix.dup2 ~cloexec:false socket Unix.stdin;
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

(* A connection to a key's process, which is started if none listens. The
   client binds the socket before it starts the process, so it connects at
   once, and the request waits in the socket's queue until the process
   accepts it. If the process fails to start, the socket's last
   descriptor closes, and the request fails. *)
let connect_or_start ~program identity key path =
  match connect path with
  | Some socket -> Ok socket
  | None ->
      holding (start_lock identity key) (fun () ->
          match connect path with
          | Some socket -> Ok socket
          | None ->
              Result.bind (bind identity key path) (fun listening ->
                  Fun.protect
                    ~finally:(fun () -> Unix.close listening)
                    (fun () ->
                      spawn program key listening;
                      match connect path with
                      | Some socket -> Ok socket
                      | None -> Error "could not reach the background process; try --no-server.")))

let store_directory () = Store.default_directory ()

(* Answers a request through the background process that serves a key,
   starting it if it is not running. *)
let call ?program ?(start_server = true) ~key ~progress request =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let identity = Identity.compute (Store.default_directory ()) in
  let program = Option.value program ~default:(Identity.executable ()) in
  let ( let* ) = Result.bind in
  let* path = socket_path identity key in
  let* socket =
    if start_server then connect_or_start ~program identity key path
    else Option.to_result ~none:"No background process is running." (connect path)
  in
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
         directory."
