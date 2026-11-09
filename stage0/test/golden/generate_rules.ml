(* Writes the dune rules for the golden tests: for each NAME.truss here, the
   output of truss-lex --tokens is compared with NAME.expected. To add a
   test, add NAME.truss and run `dune build @runtest --auto-promote`, then
   review the new NAME.expected. *)

let () =
  Sys.readdir "."
  |> Array.to_list
  |> List.filter (fun file -> Filename.check_suffix file ".truss")
  |> List.sort compare
  |> List.iter (fun file ->
         let name = Filename.chop_suffix file ".truss" in
         Printf.printf
           "(rule\n\
           \ (with-stdout-to\n\
           \  %s.output\n\
           \  (with-accepted-exit-codes\n\
           \   (or 0 1)\n\
           \   (run %%{exe:../../bin/truss_lex.exe} --tokens %%{dep:%s}))))\n\n\
            (rule\n\
           \ (alias runtest)\n\
           \ (action\n\
           \  (diff %s.expected %s.output)))\n\n"
           name file name name)
