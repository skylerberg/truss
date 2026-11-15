open Harness

let solver = Lazy.force Support.solver
let markdown_files = Harness.markdown_documents ()
let source_of database file = Query.demand database Packages.source file

let excerpt_codes =
  [
    "resolve.unknown_name";
    "resolve.unknown_module";
    "resolve.shadowed_name";
    "types.method_outside_package";
    "package.impl_location";
  ]

let () =
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          let database = Support.setup [ ("example", text) ] in
          let file = Support.file_of "example" in
          if (Query.demand database Parsed.file file).diagnostics = [] then
            test
              (Printf.sprintf "%s block %d checks and proves unless it is an excerpt" name
                 (index + 1))
              (fun () ->
                let diagnostics = Checks.diagnostics database file in
                if
                  not
                    (List.exists
                       (fun code -> List.mem code excerpt_codes)
                       (Support.codes diagnostics))
                then
                  match diagnostics with
                  | [] -> (
                      match
                        Prover.diagnostics ~record:(Support.record database) database solver file
                      with
                      | [] -> ()
                      | unproven ->
                          fail "%s"
                            (String.concat ""
                               (List.map (Diagnostic.render (source_of database file)) unproven)))
                  | diagnostics ->
                      fail "%s"
                        (String.concat ""
                           (List.map (Diagnostic.render (source_of database file)) diagnostics))))
        (Documents.truss_blocks (Documents.read (Harness.workspace_path name))))
    markdown_files
