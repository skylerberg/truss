(* Writes a directory of Truss fixtures into an OCaml module, so a test names
   each fixture by an identifier and a fixture that is missing fails to
   compile. The file [fixtures/prover/overflow.truss] becomes the string
   [Prover.overflow], and [fixtures/overflow.truss] becomes [overflow]. *)

let rec under_fixtures = function
  | "fixtures" :: rest -> rest
  | _ :: rest -> under_fixtures rest
  | [] -> failwith "a fixture is not under fixtures/"

let () =
  let files =
    List.tl (Array.to_list Sys.argv)
    |> List.map (fun file -> (under_fixtures (String.split_on_char '/' file), file))
    |> List.sort compare
  in
  let print_value indent name file =
    Printf.printf "%slet %s = %S\n" indent
      (Filename.chop_suffix name ".truss")
      (In_channel.with_open_bin file In_channel.input_all)
  in
  let rec print open_module = function
    | ([ name ], file) :: rest ->
        Option.iter (fun _ -> print_string "end\n") open_module;
        print_value "" name file;
        print None rest
    | ([ directory; name ], file) :: rest ->
        if open_module <> Some directory then begin
          Option.iter (fun _ -> print_string "end\n") open_module;
          Printf.printf "module %s = struct\n" (String.capitalize_ascii directory)
        end;
        print_value "  " name file;
        print (Some directory) rest
    | (_, file) :: _ -> failwith ("a fixture is nested too deep: " ^ file)
    | [] -> Option.iter (fun _ -> print_string "end\n") open_module
  in
  print None files
