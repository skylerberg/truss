(* The documents' examples, type-checked: every ```truss block that is a
   whole file checks through every stage. See TYPECHECKER.md, "Testing". *)

open Harness

let markdown_files =
  Sys.readdir "../.." |> Array.to_list
  |> List.filter (fun name -> Filename.check_suffix name ".md")
  |> List.sort compare

let () =
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          let database = Support.setup [ ("example::main", text) ] in
          let module_ = Support.module_of "example::main" in
          let file = Query.demand database Workspace.file module_ in
          if file.diagnostics = [] then
            test
              (Printf.sprintf "%s block %d type-checks" name (index + 1))
              (fun () ->
                match Type_checker.diagnostics database module_ with
                | [] -> ()
                | diagnostics ->
                    fail "%s"
                      (String.concat "" (List.map (Diagnostic.render file.source) diagnostics))))
        (Documents.truss_blocks (Documents.read (Filename.concat "../.." name))))
    markdown_files

let () = finish ()
