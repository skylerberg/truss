(* The compiler's identity: the BLAKE3 hash of its executable, in hex. A
   saved result means something only to the compiler that saved it, so the
   key of every fact holds it, and each worktree's pointer and the
   background process's socket are named by it. *)

let executable () =
  try Unix.realpath Sys.executable_name with Unix.Unix_error _ -> Sys.executable_name

(* An executable's size, modification and change times, and inode: a
   rebuild in place changes them. *)
let stamp path =
  match Unix.stat path with
  | stat -> Some (Printf.sprintf "%d %h %h %d" stat.st_size stat.st_mtime stat.st_ctime stat.st_ino)
  | exception Unix.Unix_error _ -> None

(* The hash of each executable, by its path and stamp, so that it is
   computed once per build. Each line is a path, a stamp, and an identity,
   separated by tabs. A line whose executable has been rebuilt or removed is
   dropped when a new one is added, so the file holds one line for each
   executable that exists. *)
let compute directory =
  let path = executable () in
  match stamp path with
  | None -> "unknown"
  | Some current -> (
      let remembered = Filename.concat directory "identities" in
      let entries =
        (try In_channel.with_open_bin remembered In_channel.input_lines with Sys_error _ -> [])
        |> List.filter_map (fun line ->
            match String.split_on_char '\t' line with
            | [ path; stamp; identity ] -> Some (path, stamp, identity)
            | _ -> None)
      in
      match
        List.find_opt (fun (known, known_stamp, _) -> known = path && known_stamp = current) entries
      with
      | Some (_, _, identity) -> identity
      | None ->
          let identity = Blake3.hex_digest (File_system.read path) in
          let live =
            List.filter
              (fun (known, known_stamp, _) -> known <> path && stamp known = Some known_stamp)
              entries
          in
          (try
             File_system.write_atomically remembered
               (String.concat ""
                  (List.map
                     (fun (path, stamp, identity) ->
                       Printf.sprintf "%s\t%s\t%s\n" path stamp identity)
                     (live @ [ (path, current, identity) ])))
           with Sys_error _ | Unix.Unix_error _ -> ());
          identity)

let short identity = if String.length identity > 16 then String.sub identity 0 16 else identity
