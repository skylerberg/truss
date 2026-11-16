open Harness

let markdown_files = Harness.markdown_documents ()
let source_of = Support.source

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
          let file = Support.file_of "example" in
          if Support.parse_errors packages file = [] then
            test
              (Printf.sprintf "%s block %d checks and proves unless it is an excerpt" name
                 (index + 1))
              (fun () ->
                let pipeline = Support.pipeline packages in
                let diagnostics = Support.diagnostics pipeline file in
                if
                  not
                    (List.exists
                       (fun code -> List.mem code excerpt_codes)
                       (Support.codes diagnostics))
                then
                  match diagnostics with
                  | [] -> (
                      match Support.proof_diagnostics pipeline file with
                      | [] -> ()
                      | unproven ->
                          fail "%s"
                            (String.concat ""
                               (List.map (Diagnostic.render (source_of packages file)) unproven)))
                  | diagnostics ->
                      fail "%s"
                        (String.concat ""
                           (List.map (Diagnostic.render (source_of packages file)) diagnostics))))
        (Documents.truss_blocks (File_system.read (Harness.workspace_path name))))
    markdown_files
