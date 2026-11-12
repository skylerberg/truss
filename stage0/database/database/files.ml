(* A set of files: a project's manifests, lock file, and module files, by
   their paths from its root. A worktree's directory, a commit, and texts in
   memory are each one, so a session is opened and kept current the same way
   whatever its files come from. *)

type t = {
  list : unit -> (string * string) list;
      (** Each file's path and stamp. A file whose stamp is unchanged has not changed. *)
  read : string -> string option;  (** A file's text; [None] for one that cannot be read *)
}

let stamp_of_text text = Blake3.hex_digest text

let of_directory root =
  {
    list =
      (fun () ->
        List.map
          (fun (path, (stamp : Worktree.stamp)) ->
            (path, Printf.sprintf "%d %h %d" stamp.size stamp.modified stamp.inode))
          (Worktree.files root));
    read =
      (fun path ->
        try Some (In_channel.with_open_bin (Filename.concat root path) In_channel.input_all)
        with Sys_error _ -> None);
  }

let of_texts (texts : (string * string) list) =
  {
    list = (fun () -> List.map (fun (path, text) -> (path, stamp_of_text text)) texts);
    read = (fun path -> List.assoc_opt path texts);
  }

(* The files of a commit under a directory of its repository. *)
let of_commit ~directory commit = Option.map of_texts (Git.files ~directory commit)

(* A set of files with some replaced, added, or, with [None], removed. *)
let with_changes base (changes : (string * string option) list) =
  let changed = Hashtbl.create (List.length changes) in
  List.iter (fun (path, text) -> Hashtbl.replace changed path text) changes;
  {
    list =
      (fun () ->
        List.sort compare
          (List.filter (fun (path, _) -> not (Hashtbl.mem changed path)) (base.list ())
          @ List.filter_map
              (fun (path, text) -> Option.map (fun text -> (path, stamp_of_text text)) text)
              changes));
    read =
      (fun path ->
        match Hashtbl.find_opt changed path with Some text -> text | None -> base.read path);
  }
