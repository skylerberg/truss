(* Where results are kept: [$TRUSS_CACHE], or else [$XDG_CACHE_HOME/truss],
   or else [~/.cache/truss]. Every entry is named by a key of what it was
   made from, so nothing there is ever needed for a correct answer. See
   CLI.md, "The cache". *)

let set name = match Sys.getenv_opt name with Some "" | None -> None | Some value -> Some value

let root () =
  match set "TRUSS_CACHE" with
  | Some directory -> directory
  | None -> (
      match set "XDG_CACHE_HOME" with
      | Some directory -> Filename.concat directory "truss"
      | None ->
          let home = Option.value (set "HOME") ~default:(Filename.get_temp_dir_name ()) in
          Filename.concat home ".cache/truss")

let objects () = Filename.concat (root ()) "objects"
let results () = Filename.concat (root ()) "results"

let rec remove path =
  match (Unix.lstat path).st_kind with
  | S_DIR ->
      Array.iter (fun entry -> remove (Filename.concat path entry)) (Sys.readdir path);
      Unix.rmdir path
  | _ -> Sys.remove path
  | exception Unix.Unix_error (ENOENT, _, _) -> ()

(* [truss clean]: deletes the cache, which costs only time. *)
let clean () =
  let root = root () in
  (try remove root
   with Unix.Unix_error (error, _, _) ->
     Project.cannot_run "Cannot delete %s: %s" root (Unix.error_message error));
  0
