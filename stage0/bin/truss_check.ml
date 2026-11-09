(* truss-check: type-checks the package in a directory, with its truss.toml,
   and prints every diagnostic, for people or, with --json, for tools. It
   exits 0 when there are none, 1 when there are, and 2 when it could not
   check. *)

let fail format =
  Printf.ksprintf
    (fun message ->
      prerr_endline message;
      exit 2)
    format

let () =
  let json = Array.exists (( = ) "--json") Sys.argv in
  let directory =
    match List.filter (( <> ) "--json") (List.tl (Array.to_list Sys.argv)) with
    | [ directory ] -> directory
    | _ -> fail "usage: truss-check [--json] <package-directory>"
  in
  let manifest_path = Filename.concat directory "truss.toml" in
  if not (Sys.file_exists manifest_path) then fail "%s: no truss.toml." directory;
  let manifest =
    try Type_checker.Manifest.parse (Source.text (Source.read_file manifest_path))
    with Type_checker.Manifest.Malformed (line, expected) ->
      fail "%s:%d: expected %s." manifest_path line expected
  in
  let engine = Engine.create ~shared:(Database.standard_layer ()) () in
  let modules = Database.read_directory ~package:manifest.name directory in
  Database.load_package engine ~name:manifest.name ~dependencies:manifest.dependencies modules;
  let database = Engine.context engine in
  let found =
    List.concat_map
      (fun ((module_ : Path.module_), _) ->
        let source = (Query.demand database Workspace.file module_).source in
        List.map
          (fun diagnostic -> (source, diagnostic))
          (Diagnostic.shown (Type_checker.diagnostics database module_)))
      modules
  in
  if json then
    print_string
      ("["
      ^ String.concat ",\n" (List.map (fun (source, d) -> Diagnostic.to_json_object source d) found)
      ^ "]\n")
  else
    List.iter (fun (source, diagnostic) -> print_string (Diagnostic.render source diagnostic)) found;
  exit (if found = [] then 0 else 1)
