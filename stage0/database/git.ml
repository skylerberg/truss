(* Reading commits from git, for sessions opened for a commit rather than a
   directory. *)

let run ?(environment = []) ~directory arguments =
  let command =
    String.concat " "
      (List.map (fun (k, v) -> k ^ "=" ^ Filename.quote v) environment
      @ List.map Filename.quote ("git" :: "-C" :: directory :: arguments))
  in
  let input = Unix.open_process_in (command ^ " 2>/dev/null") in
  let output = In_channel.input_all input in
  match Unix.close_process_in input with Unix.WEXITED 0 -> Some output | _ -> None

let trim text = String.trim text

(* The top of the worktree a directory is in, or [None] outside git. *)
let toplevel directory = Option.map trim (run ~directory [ "rev-parse"; "--show-toplevel" ])

let common_directory directory =
  Option.map
    (fun path ->
      let path = trim path in
      if Filename.is_relative path then Filename.concat directory path else path)
    (run ~directory [ "rev-parse"; "--git-common-dir" ])

let resolve ~directory revision =
  Option.map trim (run ~directory [ "rev-parse"; "--verify"; revision ^ "^{commit}" ])

let head ~directory = resolve ~directory "HEAD"

(* The default branch: [origin/HEAD]'s target, else [main], else [master]. *)
let default_branch ~directory =
  match run ~directory [ "symbolic-ref"; "--quiet"; "refs/remotes/origin/HEAD" ] with
  | Some reference when trim reference <> "" -> Some (trim reference)
  | _ ->
      List.find_opt
        (fun branch -> resolve ~directory branch <> None)
        [ "main"; "master"; "origin/main"; "origin/master" ]

let merge_base ~directory left right =
  Option.map trim (run ~directory [ "merge-base"; left; right ])

(* Every manifest and module file of a commit, with its text. *)
let files ~directory commit =
  match run ~directory [ "ls-tree"; "-r"; "-z"; "--full-tree"; commit ] with
  | None -> None
  | Some listing ->
      let entries =
        String.split_on_char '\000' listing
        |> List.filter_map (fun entry ->
            match String.index_opt entry '\t' with
            | None -> None
            | Some tab ->
                let meta = String.split_on_char ' ' (String.sub entry 0 tab) in
                let path = String.sub entry (tab + 1) (String.length entry - tab - 1) in
                let base = Filename.basename path in
                let skipped =
                  List.exists Worktree.skipped (Worktree.segments (Worktree.parent path))
                in
                if
                  (not skipped)
                  && (base = "truss.toml" || Filename.check_suffix base ".truss")
                  && match meta with [ _; "blob"; _ ] -> true | _ -> false
                then Some (path, List.nth meta 2)
                else None)
      in
      let texts =
        List.filter_map
          (fun (path, blob) ->
            Option.map (fun text -> (path, text)) (run ~directory [ "cat-file"; "blob"; blob ]))
          entries
      in
      Some texts

(* Merges two commits' trees without a checkout, and gives the merged
   tree's files; [None] when the merge has a textual conflict. *)
let merged_files ~directory left right =
  match run ~directory [ "merge-tree"; "--write-tree"; left; right ] with
  | Some output -> (
      match String.split_on_char '\n' (trim output) with
      | tree :: _ when tree <> "" -> files ~directory tree
      | _ -> None)
  | None -> None

(* A commit holding a worktree's files as they are now, tracked or not,
   made with an index of its own so that the worktree, its index, and its
   branches are untouched. *)
let snapshot ~directory =
  (* The index must not exist yet: git reads an empty file as a broken
     index, and makes a new one only where there is none. *)
  let index = Filename.temp_file "truss-index" "" in
  (try Sys.remove index with Sys_error _ -> ());
  let environment = [ ("GIT_INDEX_FILE", index) ] in
  let result =
    match head ~directory with
    | None -> None
    | Some head -> (
        match
          ( run ~environment ~directory [ "read-tree"; head ],
            run ~environment ~directory [ "add"; "-A" ],
            run ~environment ~directory [ "write-tree" ] )
        with
        | Some _, Some _, Some tree ->
            (* A snapshot is the database's own, so it names its own author
               rather than needing the user's to be set. *)
            let author =
              [
                ("GIT_AUTHOR_NAME", "truss");
                ("GIT_AUTHOR_EMAIL", "truss@localhost");
                ("GIT_COMMITTER_NAME", "truss");
                ("GIT_COMMITTER_EMAIL", "truss@localhost");
              ]
            in
            Option.map trim
              (run ~environment:author ~directory
                 [ "commit-tree"; trim tree; "-p"; head; "-m"; "truss snapshot" ])
        | _ -> None)
  in
  (try Sys.remove index with Sys_error _ -> ());
  result
