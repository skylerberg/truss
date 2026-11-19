type t = { path : string; descriptor : Unix.file_descr; identity : int * int }

let held = ref (Unix.getpid (), Hashtbl.create 8)

let read_held () =
  match !held with
  | owner, table when owner = Unix.getpid () -> table
  | _ ->
      let table = Hashtbl.create 8 in
      held := (Unix.getpid (), table);
      table

let read_identity (stats : Unix.stats) = (stats.st_dev, stats.st_ino)

let is_current descriptor path =
  match (Unix.fstat descriptor, Unix.stat path) with
  | locked, named -> read_identity locked = read_identity named
  | exception Unix.Unix_error (ENOENT, _, _) -> false

let is_held_by_this_process path =
  match Unix.stat path with
  | stats -> Hashtbl.mem (read_held ()) (read_identity stats)
  | exception Unix.Unix_error (ENOENT, _, _) -> false

let rec lock ~is_waiting path =
  if is_held_by_this_process path then
    Compiler_bug.raise_bug ~stage:"Lock_file" "this process already holds %s" path;
  let descriptor = Unix.openfile path [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644 in
  match Unix.lockf descriptor (if is_waiting then F_LOCK else F_TLOCK) 0 with
  | () when is_current descriptor path ->
      let identity = read_identity (Unix.fstat descriptor) in
      Hashtbl.replace (read_held ()) identity ();
      Some { path; descriptor; identity }
  | () ->
      Unix.close descriptor;
      lock ~is_waiting path
  | exception Unix.Unix_error ((EAGAIN | EACCES), _, _) when not is_waiting ->
      Unix.close descriptor;
      None
  | exception failure ->
      Unix.close descriptor;
      raise failure

let acquire path =
  match lock ~is_waiting:true path with
  | Some lock -> lock
  | None -> Compiler_bug.raise_bug ~stage:"Lock_file" "a wait for %s gave no lock" path

let acquire_if_free path = lock ~is_waiting:false path

let release lock =
  (if is_current lock.descriptor lock.path then
     try Unix.unlink lock.path with Unix.Unix_error (ENOENT, _, _) -> ());
  Hashtbl.remove (read_held ()) lock.identity;
  Unix.close lock.descriptor

let with_lock path work =
  let lock = acquire path in
  Fun.protect ~finally:(fun () -> release lock) work

let is_held path =
  is_held_by_this_process path
  ||
  match Unix.openfile path [ O_RDWR; O_CLOEXEC ] 0 with
  | exception Unix.Unix_error _ -> false
  | descriptor ->
      Fun.protect
        ~finally:(fun () -> Unix.close descriptor)
        (fun () ->
          match Unix.lockf descriptor F_TEST 0 with
          | () -> false
          | exception Unix.Unix_error _ -> true)
