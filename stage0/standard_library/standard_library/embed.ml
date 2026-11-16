let () =
  let files = List.sort compare (List.tl (Array.to_list Sys.argv)) in
  print_string "let files = [\n";
  List.iter
    (fun file ->
      let text = In_channel.with_open_bin file In_channel.input_all in
      let rec strip_to_standard = function
        | "standard" :: rest -> rest
        | _ :: rest -> strip_to_standard rest
        | [] -> failwith ("not under standard/: " ^ file)
      in
      let names = strip_to_standard (String.split_on_char '/' file) in
      let modules = List.take (List.length names - 1) names in
      Printf.printf "  ([ %s ], %S, %S);\n"
        (String.concat "; " (List.map (Printf.sprintf "%S") modules))
        (Filename.chop_suffix (Filename.basename file) ".truss")
        text)
    files;
  print_string "]\n"
