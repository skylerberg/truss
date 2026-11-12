let read path = In_channel.with_open_bin path In_channel.input_all
let write path text = Out_channel.with_open_bin path (fun channel -> output_string channel text)

let write_all descriptor text =
  let rec from offset =
    if offset < String.length text then
      from (offset + Unix.write_substring descriptor text offset (String.length text - offset))
  in
  from 0

let write_durably path text =
  let descriptor = Unix.openfile path [ O_WRONLY; O_CLOEXEC; O_CREAT; O_TRUNC ] 0o644 in
  Fun.protect
    ~finally:(fun () -> Unix.close descriptor)
    (fun () ->
      write_all descriptor text;
      Unix.fsync descriptor)

let write_atomically ?(durable = false) path text =
  let temporary = Printf.sprintf "%s.%d.partial" path (Unix.getpid ()) in
  if durable then write_durably temporary text else write temporary text;
  Sys.rename temporary path

let rec make_directory path =
  if not (Sys.file_exists path) then begin
    make_directory (Filename.dirname path);
    try Sys.mkdir path 0o755 with Sys_error _ when Sys.file_exists path -> ()
  end

let rec remove path =
  match (Unix.lstat path).st_kind with
  | exception Unix.Unix_error (ENOENT, _, _) -> ()
  | S_DIR ->
      Array.iter (fun entry -> remove (Filename.concat path entry)) (Sys.readdir path);
      Unix.rmdir path
  | _ -> Sys.remove path
