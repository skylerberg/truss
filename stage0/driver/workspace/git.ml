let run ?environment ?input ~directory arguments =
  match Process.run ?environment ?input "git" ("-C" :: directory :: arguments) with
  | 0, output, _ -> Some output
  | _ | (exception Unix.Unix_error _) -> None

let trimmed ?environment ~directory arguments =
  Option.map String.trim (run ?environment ~directory arguments)

let common_directory directory =
  Option.map
    (fun path ->
      let path = if Filename.is_relative path then Filename.concat directory path else path in
      try Unix.realpath path with Unix.Unix_error _ -> path)
    (trimmed ~directory [ "rev-parse"; "--git-common-dir" ])

let prefix directory = trimmed ~directory [ "rev-parse"; "--show-prefix" ]

let resolve ~directory revision =
  trimmed ~directory [ "rev-parse"; "--verify"; "--quiet"; revision ^ "^{commit}" ]

let head ~directory = resolve ~directory "HEAD"

let default_branch ~directory =
  match trimmed ~directory [ "symbolic-ref"; "--quiet"; "refs/remotes/origin/HEAD" ] with
  | Some reference when reference <> "" -> Some reference
  | _ ->
      List.find_opt
        (fun branch -> resolve ~directory branch <> None)
        [ "main"; "master"; "origin/main"; "origin/master" ]

let merge_base ~directory left right = trimmed ~directory [ "merge-base"; left; right ]

let is_input path =
  match List.rev (String.split_on_char '/' path) with
  | name :: directories ->
      Registry.Content.is_input name && not (List.exists Registry.Content.skipped directories)
  | [] -> false

let blobs listing =
  List.filter_map
    (fun entry ->
      match String.index_opt entry '\t' with
      | None -> None
      | Some tab -> (
          let path = String.sub entry (tab + 1) (String.length entry - tab - 1) in
          match String.split_on_char ' ' (String.sub entry 0 tab) with
          | [ _; "blob"; blob ] when is_input path -> Some (path, blob)
          | _ -> None))
    (String.split_on_char '\000' listing)

let contents batch =
  let rec read at texts =
    if at >= String.length batch then Some (List.rev texts)
    else
      match String.index_from_opt batch at '\n' with
      | None -> None
      | Some line_end -> (
          match String.split_on_char ' ' (String.sub batch at (line_end - at)) with
          | [ _; "blob"; size ] -> (
              match int_of_string_opt size with
              | Some size when line_end + 1 + size <= String.length batch ->
                  read (line_end + size + 2) (String.sub batch (line_end + 1) size :: texts)
              | Some _ | None -> None)
          | _ -> None)
  in
  read 0 []

let files ~directory tree =
  Option.bind
    (run ~directory [ "ls-tree"; "-r"; "-z"; tree ])
    (fun listing ->
      match blobs listing with
      | [] -> Some []
      | blobs ->
          Option.bind
            (run ~directory
               ~input:(String.concat "" (List.map (fun (_, blob) -> blob ^ "\n") blobs))
               [ "cat-file"; "--batch" ])
            (fun batch ->
              Option.bind (contents batch) (fun texts ->
                  if List.length texts = List.length blobs then
                    Some (List.combine (List.map fst blobs) texts)
                  else None)))

let merged_files ~directory left right =
  match trimmed ~directory [ "merge-tree"; "--write-tree"; left; right ] with
  | Some output -> (
      match String.split_on_char '\n' output with
      | tree :: _ when tree <> "" -> files ~directory tree
      | _ -> None)
  | None -> None

let snapshot ~directory =
  let index = Filename.temp_file "truss-index" "" in
  Sys.remove index;
  let environment = [ ("GIT_INDEX_FILE", index) ] in
  let commit =
    Option.bind (head ~directory) (fun head ->
        match
          ( run ~environment ~directory [ "read-tree"; head ],
            run ~environment ~directory [ "add"; "-A" ],
            trimmed ~environment ~directory [ "write-tree" ] )
        with
        | Some _, Some _, Some tree ->
            trimmed
              ~environment:
                [
                  ("GIT_AUTHOR_NAME", "truss");
                  ("GIT_AUTHOR_EMAIL", "truss@localhost");
                  ("GIT_COMMITTER_NAME", "truss");
                  ("GIT_COMMITTER_EMAIL", "truss@localhost");
                ]
              ~directory
              [ "commit-tree"; tree; "-p"; head; "-m"; "truss snapshot" ]
        | _ -> None)
  in
  (try Sys.remove index with Sys_error _ -> ());
  commit
