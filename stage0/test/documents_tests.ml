(* The documents' examples, type-checked. Every ```truss block that parses as
   a file is checked through every stage. Most blocks are excerpts: they use
   names defined elsewhere, show a definition of the standard library's, or
   redefine a prelude name to show how it is written. Those diagnostics say
   the block is an excerpt, and such a block is skipped. Every other block is
   a whole program and must check cleanly. *)

open Harness

let markdown_files =
  Sys.readdir "../.." |> Array.to_list
  |> List.filter (fun name -> Filename.check_suffix name ".md")
  |> List.sort compare

(* The codes that mean the block needs context it does not have. *)
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
          let database = Support.setup [ ("example::main", text) ] in
          let module_ = Support.module_of "example::main" in
          let file = Query.demand database Workspace.file module_ in
          if file.diagnostics = [] then
            test
              (Printf.sprintf "%s block %d type-checks unless it is an excerpt" name (index + 1))
              (fun () ->
                let diagnostics = Type_checker.diagnostics database module_ in
                if
                  not
                    (List.exists
                       (fun code -> List.mem code excerpt_codes)
                       (Support.codes diagnostics))
                then
                  match diagnostics with
                  | [] -> ()
                  | diagnostics ->
                      fail "%s"
                        (String.concat "" (List.map (Diagnostic.render file.source) diagnostics))))
        (Documents.truss_blocks (Documents.read (Filename.concat "../.." name))))
    markdown_files

let () = finish ()
