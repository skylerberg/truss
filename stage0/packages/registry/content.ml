let is_skipped name = name = "" || name.[0] = '.' || name = "_build" || name = "node_modules"

let hash files =
  let lines =
    List.map
      (fun (path, bytes) -> Printf.sprintf "%s %s\n" path (Blake3.hash_to_hex bytes))
      (List.sort (fun (left, _) (right, _) -> String.compare left right) files)
  in
  Blake3.hash_to_hex (String.concat "" lines)

let is_hash text =
  String.length text = 64
  && String.for_all (function '0' .. '9' | 'a' .. 'f' -> true | _ -> false) text

let is_input name =
  name = "truss.toml" || name = "truss.lock" || Filename.check_suffix name ".truss"

let walk ~enters_directory ~keeps_file directory =
  let files = ref [] in
  let rec visit relative =
    let entries =
      try Sys.readdir (File_system.join_path directory relative) with Sys_error _ -> [||]
    in
    Array.sort String.compare entries;
    Array.iter
      (fun entry ->
        let path = File_system.join_path relative entry in
        let full = File_system.join_path directory path in
        match (Unix.lstat full).st_kind with
        | exception Unix.Unix_error _ -> ()
        | S_DIR -> if enters_directory ~entry ~full then visit path
        | S_REG ->
            if keeps_file ~relative ~entry then files := (path, File_system.read full) :: !files
        | _ -> ())
      entries
  in
  visit "";
  List.rev !files

let is_other_package directory = Sys.file_exists (Filename.concat directory "truss.toml")
let is_published name = is_input name || Filename.check_suffix name ".md"

let list_published_files =
  walk
    ~enters_directory:(fun ~entry ~full -> not (is_skipped entry || is_other_package full))
    ~keeps_file:(fun ~relative ~entry ->
      is_published entry && (entry <> "truss.lock" || relative = ""))

let list_input_files =
  walk
    ~enters_directory:(fun ~entry ~full:_ -> not (is_skipped entry))
    ~keeps_file:(fun ~relative:_ ~entry -> is_input entry)

let list_all_files =
  walk
    ~enters_directory:(fun ~entry:_ ~full:_ -> true)
    ~keeps_file:(fun ~relative:_ ~entry:_ -> true)
