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
  is_skipped_name : string -> bool;
  cookie_directory : string;
  mutable cookies : int;
}

type changes = Changed of string list | Rescan | Removed

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
      if (not (watcher.is_skipped_name entry)) && is_directory path then watch_tree watcher path)
    (try Sys.readdir directory with Sys_error _ -> [||])

let start ~is_skipped_name ~cookie_directory root =
  let root = Unix.realpath root in
  let cookies = Filename.concat root cookie_directory in
  (try Unix.mkdir cookies 0o755 with Unix.Unix_error (EEXIST, _, _) -> ());
  let watcher =
    { root; handle = open_handle root; is_skipped_name; cookie_directory; cookies = 0 }
  in
  if not (is_recursive ()) then begin
    watch_tree watcher root;
    add watcher.handle cookies
  end;
  watcher

let extract_descriptor watcher = handle_descriptor watcher.handle

let find_relative_path watcher path =
  if path = watcher.root then Some ""
  else
    let prefix = watcher.root ^ "/" in
    if String.starts_with ~prefix path then Some (String.drop_first (String.length prefix) path)
    else None

let is_skipped watcher relative =
  List.exists watcher.is_skipped_name (String.split_on_char '/' relative)

let drain watcher =
  let paths, is_overflowed = take watcher.handle in
  let relatives = List.filter_map (find_relative_path watcher) paths in
  if not (is_recursive ()) then
    List.iter
      (fun relative ->
        let path = Filename.concat watcher.root relative in
        if relative <> "" && (not (is_skipped watcher relative)) && is_directory path then
          watch_tree watcher path)
      relatives;
  (relatives, is_overflowed)

let list_relevant watcher relatives =
  List.filter (fun relative -> relative = "" || not (is_skipped watcher relative)) relatives

let synchronize watcher ~pending_paths ~is_overflowed =
  watcher.cookies <- watcher.cookies + 1;
  let cookie =
    Printf.sprintf "%s/sync-%d-%d" watcher.cookie_directory (Unix.getpid ()) watcher.cookies
  in
  let cookie_path = Filename.concat watcher.root cookie in
  let rec wait ~deadline paths is_overflowed =
    let remaining = deadline -. Unix.gettimeofday () in
    if remaining <= 0. then Rescan
    else
      match Unix.select [ extract_descriptor watcher ] [] [] remaining with
      | exception Unix.Unix_error (EINTR, _, _) -> wait ~deadline paths is_overflowed
      | [], _, _ -> Rescan
      | _ ->
          let relatives, has_overflowed = drain watcher in
          let is_overflowed = is_overflowed || has_overflowed in
          let paths = list_relevant watcher relatives @ paths in
          if List.mem cookie relatives then
            if is_overflowed then Rescan else Changed (List.sort_uniq compare paths)
          else wait ~deadline paths is_overflowed
  in
  match Unix.openfile cookie_path [ O_WRONLY; O_CREAT; O_CLOEXEC ] 0o644 with
  | exception Unix.Unix_error (ENOENT, _, _) -> Removed
  | descriptor ->
      Unix.close descriptor;
      let changes =
        wait ~deadline:(Unix.gettimeofday () +. synchronization_limit) pending_paths is_overflowed
      in
      (try Sys.remove cookie_path with Sys_error _ -> ());
      changes

let read_changes watcher = synchronize watcher ~pending_paths:[] ~is_overflowed:false

let read_pending_changes watcher =
  let relatives, is_overflowed = drain watcher in
  match list_relevant watcher relatives with
  | [] when not is_overflowed -> Changed []
  | pending_paths -> synchronize watcher ~pending_paths ~is_overflowed

let stop watcher = close watcher.handle

module For_testing = struct
  let is_delivered_before_synchronizing () = not (is_recursive ())
end
