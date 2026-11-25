let list_mains snapshot packages =
  List.filter_map (Database.find_main (Workspace.open_database snapshot)) packages

let require_main database packages =
  let package = Command_packages.require_one packages in
  match Database.find_main database package with
  | Some main -> main
  | None ->
      Outcome.raise_cannot_run
        "The package %s has no `main` in its root module, a file in its top directory, so it has \
         no program."
        (Path.show_package package)

let refuse_unshippable snapshot lookups main proofs =
  let in_code =
    List.map
      (fun ({ failure; location = { file; line; column }; way } : Backend.unshippable) ->
        ( Workspace.locate_file snapshot file,
          line,
          column,
          Project_catalog.Problem.Reached (match failure with `Todo -> Todo | `Echo -> Echo),
          way ))
      (Backend.list_unshippable lookups ~main)
  in
  let refused_positions = Hashtbl.create 16 in
  List.iter
    (fun (file, line, column, _, _) -> Hashtbl.replace refused_positions (file, line, column) ())
    in_code;
  let in_proofs =
    List.filter_map
      (fun (file, line, column, way) ->
        if Hashtbl.mem refused_positions (file, line, column) then None
        else begin
          Hashtbl.replace refused_positions (file, line, column) ();
          Some (file, line, column, Project_catalog.Problem.Unfinished_proof, way)
        end)
      (Proofs.list_holes snapshot proofs ~reached:(Backend.list_reached_definitions lookups main))
  in
  match List.sort compare (in_code @ in_proofs) with
  | [] -> ()
  | refusals ->
      let show_kind : Project_catalog.Problem.unshippable -> string = function
        | Reached Todo -> "todo"
        | Reached Echo -> "echo"
        | Unfinished_proof -> "proof hole"
      in
      if Output.json () then
        Json.print
          (Json.make_document ~diagnostics:[]
             [
               ( "unshippable",
                 Json.List
                   (List.map
                      (fun (file, line, column, failure, way) ->
                        Json.Object
                          [
                            ("kind", Json.String (show_kind failure));
                            ("file", Json.String file);
                            ("line", Json.Int line);
                            ("column", Json.Int column);
                            ( "way",
                              Json.List (List.map (fun path -> Json.String (Path.show path)) way) );
                          ])
                      refusals) );
             ])
      else
        List.iter
          (fun (path, line, column, unshippable, way) ->
            Output.eprint_line
              (Project_catalog.describe
                 (Unshippable { unshippable; location = { path; line; column }; way })))
          refusals;
      raise (Outcome.Stop 1)

let build_program ?output snapshot packages (profile : Backend.profile) ~is_kept =
  let database = Workspace.open_database snapshot in
  let report = Report.gather ~proofs:true database snapshot packages in
  Report.require_no_errors report;
  let main = require_main database packages in
  let lookups = Workspace_backend.require_lowered_lookups database packages in
  (match profile with
  | Release -> Option.iter (refuse_unshippable snapshot lookups main) (Report.force_proofs report)
  | Development -> ());
  let backend = Workspace_backend.create snapshot lookups profile in
  let output = Option.value output ~default:(Backend.make_program_path backend) in
  match Backend.build_program backend ~main ~output ~is_kept with
  | Error failure -> Outcome.raise_cannot_run "%s" (Backend.describe_failure backend failure)
  | Ok () -> (output, report)

let run ~release ~arguments =
  let snapshot, packages = Command_packages.load_current () in
  let program, _ =
    build_program snapshot packages (if release then Release else Development) ~is_kept:false
  in
  Outcome.Run_program { program; arguments }

let build ~output =
  let snapshot, packages = Command_packages.load_current () in
  let package = Command_packages.require_one packages in
  let output = Shown_path.normalize (Option.value output ~default:(Path.show_package package)) in
  let _, report = build_program snapshot packages Release ~output ~is_kept:true in
  if Output.json () then
    Json.print
      (Report.make_document report [ ("output", Json.String (Shown_path.show_path output)) ])
  else Output.printf "Built %s.\n" (Shown_path.show_path output);
  Outcome.Exit 0
