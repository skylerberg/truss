(* truss-check: type-checks the packages in a directory and prints every
   diagnostic, for people or, with --json, for tools. It is [truss check
   --no-server]. It exits 0 when there are none, 1 when there are, and 2
   when it could not check. *)

let () =
  let json = Array.exists (( = ) "--json") Sys.argv in
  let directory =
    match List.filter (( <> ) "--json") (List.tl (Array.to_list Sys.argv)) with
    | [ directory ] -> directory
    | _ ->
        prerr_endline "usage: truss-check [--json] <package-directory>";
        exit 2
  in
  let directory =
    if Filename.is_relative directory then Filename.concat (Sys.getcwd ()) directory else directory
  in
  let response = Database.handle { directory; command = Check; json } in
  Database.reset ();
  print_string response.output;
  prerr_string response.errors;
  exit response.status
