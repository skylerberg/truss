(* The compiler's identity: the BLAKE3 hash of its executable, in hex. A
   saved result means something only to the compiler that saved it, so the
   key of every fact holds it, and each worktree's pointer and the
   background process's socket are named by it. The hash is remembered by
   the executable's path, size, modification and change times, and inode, so that it is
   computed once per build of the compiler. *)

let executable () =
  try Unix.realpath Sys.executable_name with Unix.Unix_error _ -> Sys.executable_name

let compute directory =
  let path = executable () in
  match Unix.stat path with
  | exception Unix.Unix_error _ -> "unknown"
  | stat -> (
      let tag =
        Printf.sprintf "%s %d %h %h %d" path stat.st_size stat.st_mtime stat.st_ctime stat.st_ino
      in
      let remembered = Filename.concat directory "identities" in
      let known =
        try
          In_channel.with_open_bin remembered In_channel.input_lines
          |> List.find_map (fun line ->
              match String.index_opt line '\t' with
              | Some separator when String.sub line 0 separator = tag ->
                  Some (String.sub line (separator + 1) (String.length line - separator - 1))
              | _ -> None)
        with Sys_error _ -> None
      in
      match known with
      | Some identity -> identity
      | None ->
          let identity = Blake3.hex_digest (File_system.read path) in
          (try
             Out_channel.with_open_gen [ Open_append; Open_creat; Open_binary ] 0o644 remembered
               (fun out -> Printf.fprintf out "%s\t%s\n" tag identity)
           with Sys_error _ -> ());
          identity)

let short identity = if String.length identity > 16 then String.sub identity 0 16 else identity
