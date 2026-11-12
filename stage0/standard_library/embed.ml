(* Writes the standard library's source files into an OCaml module, so the
   compiler and its tests carry them and never look for them on disk. Each
   file's module path comes from its path under [standard/]. *)

let () =
  let files = List.sort compare (List.tl (Array.to_list Sys.argv)) in
  print_string "let files = [\n";
  List.iter
    (fun file ->
      let text = In_channel.with_open_bin file In_channel.input_all in
      let parts = String.split_on_char '/' file in
      let rec after_standard = function
        | "standard" :: rest -> rest
        | _ :: rest -> after_standard rest
        | [] -> failwith ("not under standard/: " ^ file)
      in
      let modules = after_standard parts in
      let modules =
        List.mapi
          (fun index part ->
            if index = List.length modules - 1 then Filename.chop_suffix part ".truss" else part)
          modules
      in
      Printf.printf "  ([ %s ], %S);\n"
        (String.concat "; " (List.map (Printf.sprintf "%S") modules))
        text)
    files;
  print_string "]\n"
