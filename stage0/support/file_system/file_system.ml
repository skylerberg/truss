let read path = In_channel.with_open_bin path In_channel.input_all
let write path text = Out_channel.with_open_bin path (fun channel -> output_string channel text)
let write_all descriptor text = ignore (Unix.write_substring descriptor text 0 (String.length text))

let write_atomically path text =
  let temporary, channel =
    Filename.open_temp_file ~mode:[ Open_binary ] ~perms:0o666 ~temp_dir:(Filename.dirname path)
      (Filename.basename path) ".partial"
  in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () ->
      output_string channel text;
      flush channel);
  Sys.rename temporary path

let make_directory path =
  let create path =
    match Unix.mkdir path 0o755 with () | (exception Unix.Unix_error (EEXIST, _, _)) -> ()
  in
  let rec make path =
    match create path with
    | () -> ()
    | exception Unix.Unix_error (ENOENT, _, _) when Filename.dirname path <> path ->
        make (Filename.dirname path);
        create path
  in
  make path

let rec remove path =
  match (Unix.lstat path).st_kind with
  | exception Unix.Unix_error (ENOENT, _, _) -> ()
  | S_DIR ->
      Array.iter (fun entry -> remove (Filename.concat path entry)) (Sys.readdir path);
      Unix.rmdir path
  | _ -> Sys.remove path

let write_directory path files =
  List.iter
    (fun (file, bytes) ->
      let target = Filename.concat path file in
      make_directory (Filename.dirname target);
      write target bytes)
    files

let write_directory_atomically path files =
  let temporary = Printf.sprintf "%s.%d.partial" path (Unix.getpid ()) in
  remove temporary;
  write_directory temporary files;
  try Sys.rename temporary path with Sys_error _ -> remove temporary
