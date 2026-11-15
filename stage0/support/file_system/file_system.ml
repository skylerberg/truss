let read path = In_channel.with_open_bin path In_channel.input_all
let write path text = Out_channel.with_open_bin path (fun channel -> output_string channel text)

let write_all descriptor text =
  let rec from offset =
    if offset < String.length text then
      from (offset + Unix.write_substring descriptor text offset (String.length text - offset))
  in
  from 0

let write_atomically ?(durable = false) path text =
  let temporary, channel =
    Filename.open_temp_file ~mode:[ Open_binary ] ~perms:0o666 ~temp_dir:(Filename.dirname path)
      (Filename.basename path) ".partial"
  in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () ->
      output_string channel text;
      flush channel;
      if durable then Unix.fsync (Unix.descr_of_out_channel channel));
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
