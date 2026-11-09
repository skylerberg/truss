(* A worktree on disk: the packages in it, the modules of each, and the
   metadata that tells whether a file changed without reading it. See
   DATABASE.md, "Watching files". *)

type stamp = { size : int; modified : float; inode : int }

let stamp_of (stat : Unix.stats) =
  { size = stat.st_size; modified = stat.st_mtime; inode = stat.st_ino }

(* Directories that never hold a package's modules. *)
let skipped name = name = "" || name.[0] = '.' || name = "_build" || name = "node_modules"

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
                if entry = "truss.toml" || Filename.check_suffix entry ".truss" then
                  found := (path, stamp_of stat) :: !found
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

(* A module file's path under its package's directory, as module names. *)
let module_names ~package_directory path =
  let inside =
    if package_directory = "" then path
    else
      String.sub path
        (String.length package_directory + 1)
        (String.length path - String.length package_directory - 1)
  in
  segments (Filename.chop_suffix inside ".truss")

let module_file ~package_directory (module_ : Path.module_) =
  let file = String.concat "/" module_.modules ^ ".truss" in
  if package_directory = "" then file else package_directory ^ "/" ^ file
