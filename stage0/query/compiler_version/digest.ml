(* Writes the module [Compiler_version]: a digest of the compiler's source
   under a directory, and of the other arguments, which name the toolchain
   and settings the source is built with. Tests and tools are left out, since they are not part of
   the compiler, and so is every file that is not OCaml source or a build
   rule, so the standard library's text changes nothing. *)

let skipped_directories = [ "test"; "tools" ]

let is_source name =
  name = "dune"
  || List.exists (Filename.check_suffix name) [ ".ml"; ".mli"; ".mly"; ".mll"; ".c"; ".h" ]

let rec files directory relative sources =
  let entries = Sys.readdir directory in
  Array.sort compare entries;
  Array.fold_left
    (fun sources entry ->
      let path = Filename.concat directory entry in
      let relative = if relative = "" then entry else relative ^ "/" ^ entry in
      if Sys.is_directory path then
        if List.mem entry skipped_directories || entry.[0] = '.' then sources
        else files path relative sources
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
        (List.rev (files root "" []));
      Printf.printf "let digest = %S\n"
        (Digest.BLAKE256.to_hex (Digest.BLAKE256.string (Buffer.contents buffer)))
  | _ ->
      prerr_endline "usage: digest DIRECTORY BUILT-WITH...";
      exit 2
