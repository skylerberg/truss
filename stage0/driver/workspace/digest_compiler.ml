let skipped_directories = [ "test"; "tools" ]

let is_source name =
  name = "dune"
  || List.exists (Filename.check_suffix name) [ ".ml"; ".mli"; ".mly"; ".mll"; ".c"; ".h" ]

let rec list_files directory relative sources =
  let entries = Sys.readdir directory in
  Array.sort compare entries;
  Array.fold_left
    (fun sources entry ->
      let path = Filename.concat directory entry in
      let relative = File_system.join_path relative entry in
      if Sys.is_directory path then
        if List.mem entry skipped_directories || entry.[0] = '.' then sources
        else list_files path relative sources
      else if is_source entry then (relative, path) :: sources
      else sources)
    sources entries

let () =
  match Array.to_list Sys.argv with
  | _ :: root :: built_with ->
      let buffer = Buffer.create 65536 in
      let add text =
        Buffer.add_string buffer (string_of_int (String.length text));
        Buffer.add_char buffer ':';
        Buffer.add_string buffer text
      in
      List.iter add built_with;
      List.iter
        (fun (relative, path) ->
          add relative;
          add (In_channel.with_open_bin path In_channel.input_all))
        (List.rev (list_files root "" []));
      Printf.printf "let digest = %S\n"
        (Digest.BLAKE256.to_hex (Digest.BLAKE256.string (Buffer.contents buffer)))
  | _ ->
      prerr_endline "usage: digest_compiler DIRECTORY BUILT-WITH...";
      exit 2
