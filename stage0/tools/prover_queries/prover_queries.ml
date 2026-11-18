let exit_with_error format =
  Printf.ksprintf
    (fun message ->
      prerr_endline message;
      exit 2)
    format

let read_position part =
  match int_of_string_opt part with Some number when number > 0 -> Some number | _ -> None

let parse_target text =
  let join_path reversed_parts = String.concat ":" (List.rev reversed_parts) in
  match List.rev (String.split_on_char ':' text) with
  | last :: before_last :: (_ :: _ as path)
    when Option.is_some (read_position before_last) && Option.is_some (read_position last) ->
      (join_path path, read_position before_last, read_position last)
  | last :: (_ :: _ as path) when Option.is_some (read_position last) ->
      (join_path path, read_position last, None)
  | _ -> (text, None, None)

let find_package_file path =
  match Workspace.take_snapshot (Filename.dirname path) with
  | Error message -> exit_with_error "%s" message
  | Ok (snapshot, _) -> (
      let real_path = Unix.realpath path in
      let root = Workspace.locate_root snapshot in
      match
        List.find_opt
          (fun file -> Filename.concat root (Workspace.locate_file snapshot file) = real_path)
          (List.concat_map
             (fun (_, package) -> Workspace.list_package_files snapshot package)
             (Workspace.list_packages snapshot))
      with
      | Some file -> (Workspace.open_database snapshot, file)
      | None -> exit_with_error "%s is not a file of a package in its project." path)

let open_file path =
  match
    List.find_opt (fun ((file : Path.file), _) -> Path.show_file file = path) Standard_library.files
  with
  | Some (file, _) ->
      ( Database.create
          [ { name = Path.standard_package; dependencies = []; files = Standard_library.files } ],
        file )
  | None when Sys.file_exists path -> find_package_file path
  | None ->
      exit_with_error
        "%s is neither a file of the standard library, written as `standard/list/list.truss`, nor \
         a file that exists."
        path

let quote_string text = "\"" ^ String.concat "\"\"" (String.split_on_char '"' text) ^ "\""

let () =
  let path, line, column =
    match Sys.argv with
    | [| _; target |] -> parse_target target
    | _ -> exit_with_error "usage: prover_queries FILE[:LINE[:COLUMN]]"
  in
  let database, file = open_file path in
  let source = Database.read_source database file in
  let queries =
    List.filter_map
      (fun ((site : Source.span Prover.site), input) ->
        let site_line, site_column = Source.compute_position source site.span.start in
        if
          Option.fold ~none:true ~some:(( = ) site_line) line
          && Option.fold ~none:true ~some:(( = ) site_column) column
        then Some (site_line, site_column, site, input)
        else None)
      (Prover.list_queries ~runs:[]
         (Database.make_proof_lookups database)
         (Database.list_proofs (Database.prove database [ file ]))
         file)
  in
  if queries = [] then exit_with_error "No obligation of %s starts there." path;
  List.iter
    (fun (site_line, site_column, (site : Source.span Prover.site), input) ->
      Printf.printf "(echo %s)\n%s(reset)\n"
        (quote_string
           (Printf.sprintf "%s:%d:%d %s: %s" path site_line site_column
              (Diagnostic.Code.name (Prover site.code))
              site.shows))
        input)
    queries
