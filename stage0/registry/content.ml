let skipped name = name = "" || name.[0] = '.' || name = "_build" || name = "node_modules"

let hash files =
  let lines =
    List.map
      (fun (path, bytes) -> Printf.sprintf "%s %s\n" path (Blake3.to_hex (Blake3.hash bytes)))
      (List.sort (fun (left, _) (right, _) -> String.compare left right) files)
  in
  Blake3.to_hex (Blake3.hash (String.concat "" lines))

let is_hash text =
  String.length text = 64
  && String.for_all (function '0' .. '9' | 'a' .. 'f' -> true | _ -> false) text

let published name =
  name = "truss.toml" || name = "truss.lock"
  || Filename.check_suffix name ".truss"
  || Filename.check_suffix name ".md"

let read path = In_channel.with_open_bin path In_channel.input_all

let files ?(all = false) directory =
  let found = ref [] in
  let rec walk relative =
    let absolute = if relative = "" then directory else Filename.concat directory relative in
    let entries = try Sys.readdir absolute with Sys_error _ -> [||] in
    Array.sort String.compare entries;
    Array.iter
      (fun entry ->
        let path = if relative = "" then entry else relative ^ "/" ^ entry in
        let full = Filename.concat directory path in
        match (Unix.lstat full).st_kind with
        | exception Unix.Unix_error _ -> ()
        | S_DIR ->
            (* A directory with a manifest of its own is another package. *)
            if all || not (skipped entry || Sys.file_exists (Filename.concat full "truss.toml"))
            then walk path
        | S_REG ->
            if all || (published entry && (entry <> "truss.lock" || relative = "")) then
              found := (path, read full) :: !found
        | _ -> ())
      entries
  in
  walk "";
  List.rev !found
