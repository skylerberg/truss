type t = { root : string }

let directory cache = cache.root

let find_home_directory () =
  match Sys.getenv_opt "HOME" with
  | Some home when home <> "" -> Some home
  | _ -> (
      match Unix.getpwuid (Unix.getuid ()) with
      | { pw_dir; _ } when pw_dir <> "" -> Some pw_dir
      | _ | (exception Not_found) -> None)

let locate_default_directory () =
  match Sys.getenv_opt "TRUSS_CACHE" with
  | Some directory when directory <> "" -> Ok directory
  | _ -> (
      match Sys.getenv_opt "XDG_CACHE_HOME" with
      | Some cache when cache <> "" -> Ok (Filename.concat cache "truss")
      | _ -> (
          match find_home_directory () with
          | Some home -> Ok (Filename.concat (Filename.concat home ".cache") "truss")
          | None ->
              Error "This user has no home directory for the cache; set TRUSS_CACHE to a directory."
          ))

let make_root root =
  match
    File_system.make_directory (Filename.dirname root);
    (try Unix.mkdir root 0o700 with Unix.Unix_error (EEXIST, _, _) -> ());
    Unix.stat root
  with
  | { st_kind = S_DIR; st_uid; _ } when st_uid <> Unix.getuid () ->
      Error
        (Printf.sprintf
           "The cache %s belongs to another user, who could plant compiled objects in it that this \
            user's builds would trust. Set TRUSS_CACHE to a directory of this user's own."
           root)
  | { st_kind = S_DIR; st_perm; _ } when st_perm land 0o022 <> 0 ->
      Error
        (Printf.sprintf
           "Users other than its owner can write the cache %s, so they could plant compiled \
            objects in it that this user's builds would trust. Delete it with `truss clean`, or \
            set TRUSS_CACHE to another directory."
           root)
  | { st_kind = S_DIR; _ } -> Ok root
  | _ -> Error (Printf.sprintf "The cache %s is not a directory." root)
  | exception Unix.Unix_error (error, _, _) ->
      Error (Printf.sprintf "Cannot make the cache %s: %s." root (Unix.error_message error))

let open_ root = Result.map (fun root -> { root }) (make_root root)

let make_directory path =
  File_system.make_directory path;
  path

let make_evictable_directory cache = Filename.concat cache.root "caches"

let make_objects_directory cache =
  make_directory (Filename.concat (make_evictable_directory cache) "objects")

let make_package_databases_directory cache =
  make_directory (Filename.concat (make_evictable_directory cache) "package-databases")

let make_packages_directory cache = make_directory (Filename.concat cache.root "packages")
let make_programs_directory cache = make_directory (Filename.concat cache.root "programs")

let list_evictable_files cache =
  let rec walk directory files =
    match Sys.readdir directory with
    | exception Sys_error _ -> files
    | names ->
        Array.fold_left
          (fun files name ->
            let path = Filename.concat directory name in
            match Unix.lstat path with
            | { st_kind = S_DIR; _ } -> walk path files
            | { st_kind = S_REG; st_size; st_mtime; _ } -> (path, st_size, st_mtime) :: files
            | _ -> files
            | exception Unix.Unix_error _ -> files)
          files names
  in
  walk (make_evictable_directory cache) []

let collect cache ~budget =
  let files = list_evictable_files cache in
  let excess = List.fold_left (fun total (_, size, _) -> total + size) 0 files - budget in
  let rec remove_least_recent freed = function
    | (path, size, _) :: rest when freed < excess ->
        (try Sys.remove path with Sys_error _ -> ());
        remove_least_recent (freed + size) rest
    | _ -> ()
  in
  remove_least_recent 0
    (List.sort (fun (_, _, left) (_, _, right) -> Float.compare left right) files)
