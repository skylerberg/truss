let rec strip_to_fixtures = function
  | "fixtures" :: rest -> rest
  | _ :: rest -> strip_to_fixtures rest
  | [] -> failwith "a fixture is not under fixtures/"

let () =
  let files =
    List.tl (Array.to_list Sys.argv)
    |> List.map (fun file -> (strip_to_fixtures (String.split_on_char '/' file), file))
    |> List.sort compare
  in
  let rec print open_module = function
    | ([ directory; name ], file) :: rest ->
        if open_module <> Some directory then begin
          Option.iter (fun _ -> print_string "end\n") open_module;
          Printf.printf "module %s = struct\n" (String.capitalize_ascii directory)
        end;
        Printf.printf "  let %s = %S\n"
          (Filename.chop_suffix name ".truss")
          (In_channel.with_open_bin file In_channel.input_all);
        print (Some directory) rest
    | (_, file) :: _ ->
        failwith ("a fixture is not in a directory directly under fixtures/: " ^ file)
    | [] -> Option.iter (fun _ -> print_string "end\n") open_module
  in
  print None files
