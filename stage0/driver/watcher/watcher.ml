type handle

external open_handle : string -> handle = "truss_watcher_open"
external is_recursive : unit -> bool = "truss_watcher_is_recursive"
external add : handle -> string -> unit = "truss_watcher_add"
external handle_descriptor : handle -> Unix.file_descr = "truss_watcher_descriptor"
external take : handle -> string list * bool = "truss_watcher_take"
external close : handle -> unit = "truss_watcher_close"

type t = {
  root : string;
  handle : handle;
  skipped : string -> bool;
  cookie_directory : string;
  mutable cookies : int;
}

type changes = Changed of string list | Overflow

let synchronization_limit = 2.0

let is_directory path =
  match (Unix.lstat path).st_kind with
  | S_DIR -> true
  | _ -> false
  | exception Unix.Unix_error _ -> false

let rec watch_tree watcher directory =
  add watcher.handle directory;
  Array.iter
    (fun entry ->
      let path = Filename.concat directory entry in
      if (not (watcher.skipped entry)) && is_directory path then watch_tree watcher path)
    (try Sys.readdir directory with Sys_error _ -> [||])

let start ~skipped ~cookie_directory root =
  let root = Unix.realpath root in
  let cookies = Filename.concat root cookie_directory in
  (try Unix.mkdir cookies 0o755 with Unix.Unix_error (EEXIST, _, _) -> ());
  let watcher = { root; handle = open_handle root; skipped; cookie_directory; cookies = 0 } in
  if not (is_recursive ()) then begin
    watch_tree watcher root;
    add watcher.handle cookies
  end;
  watcher

let descriptor watcher = handle_descriptor watcher.handle

let relative watcher path =
  if path = watcher.root then Some ""
  else
    let prefix = watcher.root ^ "/" in
    if String.starts_with ~prefix path then
      Some (String.sub path (String.length prefix) (String.length path - String.length prefix))
    else None

let is_skipped watcher relative = List.exists watcher.skipped (String.split_on_char '/' relative)

let taken watcher =
  let paths, is_overflowed = take watcher.handle in
  let relatives = List.filter_map (relative watcher) paths in
  if not (is_recursive ()) then
    List.iter
      (fun relative ->
        let path = Filename.concat watcher.root relative in
        if relative <> "" && (not (is_skipped watcher relative)) && is_directory path then
          watch_tree watcher path)
      relatives;
  (relatives, is_overflowed)

let changes watcher =
  watcher.cookies <- watcher.cookies + 1;
  let cookie =
    Printf.sprintf "%s/sync-%d-%d" watcher.cookie_directory (Unix.getpid ()) watcher.cookies
  in
  let cookie_path = Filename.concat watcher.root cookie in
  Out_channel.with_open_bin cookie_path ignore;
  let deadline = Unix.gettimeofday () +. synchronization_limit in
  let rec wait paths is_overflowed =
    let remaining = deadline -. Unix.gettimeofday () in
    if remaining <= 0. then Overflow
    else
      match Unix.select [ descriptor watcher ] [] [] remaining with
      | exception Unix.Unix_error (EINTR, _, _) -> wait paths is_overflowed
      | [], _, _ -> Overflow
      | _ ->
          let relatives, overflowed = taken watcher in
          let is_overflowed = is_overflowed || overflowed in
          let paths =
            List.filter
              (fun relative ->
                not (String.starts_with ~prefix:(watcher.cookie_directory ^ "/") relative))
              relatives
            @ paths
          in
          if List.mem cookie relatives then
            if is_overflowed then Overflow else Changed (List.sort_uniq compare paths)
          else wait paths is_overflowed
  in
  let changes = wait [] false in
  (try Sys.remove cookie_path with Sys_error _ -> ());
  changes

let stop watcher = close watcher.handle
