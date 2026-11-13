(* The documents' examples, type-checked and proven. Every ```truss block
   that parses as a file is checked through every stage. Most blocks are
   excerpts: they use names defined elsewhere, show a definition of the
   standard library's, or redefine a prelude name to show how it is written.
   Those diagnostics say the block is an excerpt, and such a block is
   skipped, as is one that uses a feature stage0 has not built. Every other block
   is a whole program and must check cleanly and prove. *)

open Harness

let solver = Lazy.force Support.solver
let markdown_files = Harness.markdown_documents ()

(* The codes that mean the block needs context it does not have. *)
let source_of database file = (Query.demand database Workspace.file file).source

let excerpt_codes =
  [
    "resolve.unknown_name";
    "resolve.unknown_module";
    "resolve.hides_name";
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
          if (Query.demand database Workspace.file file).diagnostics = [] then
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
