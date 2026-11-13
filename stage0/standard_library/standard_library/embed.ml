(* Writes the standard library's source files into an OCaml module, so the
   compiler and its tests carry them and never look for them on disk. Each
   file's module comes from its directory under [standard/], and its name
   from the file's own name. *)

let () =
  let files = List.sort compare (List.tl (Array.to_list Sys.argv)) in
  print_string "let files = [\n";
  List.iter
    (fun file ->
      let text = In_channel.with_open_bin file In_channel.input_all in
      let rec after_standard = function
        | "standard" :: rest -> rest
        | _ :: rest -> after_standard rest
        | [] -> failwith ("not under standard/: " ^ file)
      in
      let names = after_standard (String.split_on_char '/' file) in
      let modules = List.filteri (fun index _ -> index < List.length names - 1) names in
      Printf.printf "  ([ %s ], %S, %S);\n"
        (String.concat "; " (List.map (Printf.sprintf "%S") modules))
        (Filename.chop_suffix (Filename.basename file) ".truss")
        text)
    files;
  print_string "]\n"
