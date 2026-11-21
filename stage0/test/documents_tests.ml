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

let statement_codes = [ "usage.unused_variable"; "types.unused_value" ]

type block = Definitions of string | Statements of string

let parses text =
  let packages = Support.setup [ ("example", text) ] in
  Support.parse_errors packages (Support.parse_file "example") = []

let classify_block text =
  if parses text then Some (Definitions text)
  else
    let wrapped = "fn example() {\n" ^ text ^ "\n}\n" in
    if parses wrapped then Some (Statements wrapped) else None

let check_block name index block =
  let text, tolerated, title =
    match block with
    | Definitions text -> (text, excerpt_codes, "checks and proves unless it is an excerpt")
    | Statements text -> (text, excerpt_codes @ statement_codes, "checks as the body of a function")
  in
  Harness.test
    (Printf.sprintf "%s block %d %s" name (index + 1) title)
    (fun () ->
      let packages = Support.setup [ ("example", text) ] in
      let file = Support.parse_file "example" in
      let database = Support.make_database packages in
      let diagnostics =
        Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers database file
      in
      let is_tolerated (diagnostic : Diagnostic.t) =
        List.mem (Diagnostic.Code.name diagnostic.code) tolerated
      in
      let render diagnostics =
        String.concat ""
          (List.map (Diagnostic.render ~is_colored:false (make_source packages file)) diagnostics)
      in
      match (List.filter (fun diagnostic -> not (is_tolerated diagnostic)) diagnostics, block) with
      | [], Definitions _ when not (List.exists is_tolerated diagnostics) -> (
          match Support.list_proof_diagnostics database file with
          | [] -> ()
          | unproven -> Harness.fail "%s" (render unproven))
      | [], (Definitions _ | Statements _) -> ()
      | unexpected, _ -> Harness.fail "%s" (render unexpected))

let () =
  List.iter
    (fun name ->
      List.iteri
        (fun index text -> Option.iter (check_block name index) (classify_block text))
        (Documents.list_truss_blocks (File_system.read (Harness.make_workspace_path name))))
    markdown_files
