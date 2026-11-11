(* The background process: one per user and compiler, which holds sessions
   between commands. *)

let rec make_directory path =
  if not (Sys.file_exists path) then begin
    make_directory (Filename.dirname path);
    try Unix.mkdir path 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* Only the user may reach the background process: what travels over its
   socket is marshaled, and reading marshaled bytes from another user would
   let that user run code as this one. *)
let servers_directory () =
  let directory = Filename.concat (Store.default_directory ()) "servers" in
  make_directory directory;
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
      directory
  | _ | (exception Unix.Unix_error _) ->
      failwith (directory ^ " is not a directory that only this user can use.")

(* The socket's address, and its lock beside it in the store. A socket's
   path has a short limit, about 100 bytes, so one under a long store path
   goes in a directory of the user's own in /tmp, named by a hash of where it
   would have been. *)
let server_path identity = Filename.concat (servers_directory ()) (Identity.short identity)

let socket_path identity =
  let path = server_path identity ^ ".socket" in
  if String.length path < 100 then path
  else
    Filename.concat (private_temporary_directory ())
      (String.sub (Blake3.to_hex (Blake3.hash path)) 0 16 ^ ".socket")

let idle_limit = 3. *. 3600.

let send channel value =
  Marshal.to_channel channel value [];
  flush channel

type 'response message = Progress of string | Final of 'response

let stopping = ref false
let stop () = stopping := true

let serve ~idle ~keep ~handle =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let identity = Core.identity () in
  let path = socket_path identity in
  let lock = Unix.openfile (server_path identity ^ ".lock") [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644 in
  match Unix.lockf lock F_TLOCK 0 with
  | exception Unix.Unix_error _ -> ()
  | () ->
      Core.serving := true;
      (try Unix.unlink path with Unix.Unix_error _ -> ());
      let socket = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
      Unix.bind socket (ADDR_UNIX path);
      Unix.listen socket 16;
      let last = ref (Unix.time ()) in
      let last_collection = ref 0. in
      while (not !stopping) && Unix.time () -. !last < idle_limit do
        match Unix.select [ socket ] [] [] 1.0 with
        | exception Unix.Unix_error (EINTR, _, _) -> ()
        | [], _, _ ->
            let now = Unix.time () in
            Core.drop_idle ();
            idle ();
            List.iter Core.fold (Core.all ());
            if now -. !last_collection > 60. then begin
              last_collection := now;
              (* A compiler that was built again has another identity, and
                 its clients start a process of their own, so this one would
                 only scan worktrees for no one. *)
              if Identity.compute (Store.default_directory ()) <> Core.identity () then
                stopping := true;
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
                   send output (Final (Core.recovering (fun () -> handle ~progress request)))
                 with _ -> ());
                try Unix.close client with Unix.Unix_error _ -> ()))
      done;
      Core.reset ();
      (try Unix.unlink path with Unix.Unix_error _ -> ());
      Unix.close lock

(* Starts the background process, detached from the client's terminal. *)
let start program =
  let log = Filename.concat (servers_directory ()) "server.log" in
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
          (try Unix.execv program [| program; "__serve" |] with _ -> ());
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

let store_directory () = Store.default_directory ()

let call ?program ?(start_server = true) ~progress request =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let identity = Identity.compute (Store.default_directory ()) in
  let path = socket_path identity in
  let program = Option.value program ~default:(Identity.executable ()) in
  let rec attempt tries =
    match connect path with
    | Some socket -> Some socket
    | None ->
        if tries = 0 || not start_server then None
        else begin
          if tries = 50 then start program;
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
            "the background process ended while answering; see its log in the store's \
             servers              directory.")
