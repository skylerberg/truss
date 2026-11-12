(* A worktree on disk: the packages in it, the modules of each, and the
   metadata that tells whether a file changed without reading it. *)

type stamp = { size : int; modified : float; inode : int }

let stamp_of (stat : Unix.stats) =
  { size = stat.st_size; modified = stat.st_mtime; inode = stat.st_ino }

let skipped = Registry.Content.skipped

(* Every manifest and module file under the root, by path relative to it,
   with its stamp, in order. *)
let files root =
  let found = ref [] in
  let rec walk relative =
    let absolute = if relative = "" then root else Filename.concat root relative in
    match Sys.readdir absolute with
    | exception Sys_error _ -> ()
    | entries ->
        Array.sort compare entries;
        Array.iter
          (fun entry ->
            let path = if relative = "" then entry else relative ^ "/" ^ entry in
            match Unix.lstat (Filename.concat root path) with
            | exception Unix.Unix_error _ -> ()
            | { st_kind = S_DIR; _ } -> if not (skipped entry) then walk path
            | { st_kind = S_REG; _ } as stat ->
                if
                  entry = "truss.toml" || entry = "truss.lock"
                  || Filename.check_suffix entry ".truss"
                then found := (path, stamp_of stat) :: !found
            | _ -> ())
          entries
  in
  walk "";
  List.rev !found

(* The directory a relative file is in, "" for the root. *)
let parent path = match String.rindex_opt path '/' with Some i -> String.sub path 0 i | None -> ""
let segments path = if path = "" then [] else String.split_on_char '/' path

(* The package directory a module file belongs to: the nearest directory
   above it with a manifest. *)
let owner package_directories path =
  let rec up directory =
    if List.mem directory package_directories then Some directory
    else if directory = "" then None
    else up (parent directory)
  in
  up (parent path)
