let markdown_files = Harness.list_markdown_documents ()
let make_source = Support.read_source

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
          let packages = Support.setup [ ("example", text) ] in
          let file = Support.parse_file "example" in
          if Support.parse_errors packages file = [] then
            Harness.test
              (Printf.sprintf "%s block %d checks and proves unless it is an excerpt" name
                 (index + 1))
              (fun () ->
                let database = Support.make_database packages in
                let diagnostics = Support.list_fragment_diagnostics database file in
                if
                  not
                    (List.exists
                       (fun code -> List.mem code excerpt_codes)
                       (Support.list_codes diagnostics))
                then
                  match diagnostics with
                  | [] -> (
                      match Support.list_proof_diagnostics database file with
                      | [] -> ()
                      | unproven ->
                          Harness.fail "%s"
                            (String.concat ""
                               (List.map (Diagnostic.render (make_source packages file)) unproven)))
                  | diagnostics ->
                      Harness.fail "%s"
                        (String.concat ""
                           (List.map (Diagnostic.render (make_source packages file)) diagnostics))))
        (Documents.list_truss_blocks (File_system.read (Harness.make_workspace_path name))))
    markdown_files
