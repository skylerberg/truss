(* Writes the standard library's manifest and source files into an OCaml
   module, so the compiler and its tests carry them and never look for them
   on disk. The first argument is the manifest. Each source file's module
   path comes from its path under [standard/]. *)

let read file = In_channel.with_open_bin file In_channel.input_all

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [] -> failwith "no manifest given"
  | manifest :: sources ->
      Printf.printf "let manifest = %S\n\nlet files = [\n" (read manifest);
      List.iter
        (fun file ->
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
            (read file))
        (List.sort compare sources);
      print_string "]\n"
