let main_of session packages (package : Path.package) =
  let module_ : Path.module_ = { package; modules = [] } in
  if not (List.mem module_ (Command_packages.modules session packages)) then None
  else
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        match declaration.path with
        | Top { name = "main"; _ } when declaration.kind = Function && declaration.ordinal = 0 ->
            Some declaration.path
        | _ -> None)
      (Query.demand (Database.context session) Resolve.Names.declarations module_)

let mains session packages = List.filter_map (main_of session packages) packages

let main session packages =
  let package = Command_packages.one packages in
  match main_of session packages package with
  | Some main -> main
  | None ->
      Outcome.cannot_run
        "The package %s has no `main` in its root module, a file in its top directory, so it has \
         no program."
        (Path.show_package package)

let refuse_unshippable session packages compile main =
  let in_code =
    match Compile.unshippable compile ~main with
    | Error message -> Outcome.cannot_run "%s" message
    | Ok unshippable ->
        List.map
          (fun ({ failure; file; line; column; way } : Compile.unshippable) ->
            ( Command_packages.shown_workspace_path session packages file,
              line,
              column,
              (failure :> [ `Todo | `Echo | `Proof_hole ]),
              way ))
          unshippable
  in
  let in_proofs =
    List.map
      (fun (definition, file, line, column) -> (file, line, column, `Proof_hole, [ definition ]))
      (Proofs.holes_reached session packages main)
  in
  match List.sort_uniq compare (in_code @ in_proofs) with
  | [] -> ()
  | refusals ->
      let kind = function `Todo -> "todo" | `Echo -> "echo" | `Proof_hole -> "proof hole" in
      let shown = function
        | `Todo -> "`todo`"
        | `Echo -> "`echo`"
        | `Proof_hole -> "`todo` in a proof"
      in
      if Output.json () then
        Json.print
          (Json.document ~diagnostics:[]
             [
               ( "unshippable",
                 Json.List
                   (List.map
                      (fun (file, line, column, failure, way) ->
                        Json.Object
                          [
                            ("kind", Json.String (kind failure));
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
          (fun (file, line, column, failure, way) ->
            Output.eprintf
              "%s:%d:%d: %s can be reached from `main`, so the program cannot be built.\n    %s\n"
              file line column (shown failure)
              (String.concat " -> " (List.map Path.show way)))
          refusals;
      raise (Outcome.Stop 1)

let build_program ?output session packages (build : Compiler.build) =
  let is_release = build = Release in
  let report = Report.gather ~proofs:is_release session packages in
  if not (Report.clean report) then raise (Report.Errors report);
  let main = main session packages in
  let compile = Compiler.create ~checks:(not is_release) session packages build in
  if is_release then refuse_unshippable session packages compile main;
  let output = Option.value output ~default:(Compile.fresh_program compile) in
  match Compile.build_program compile ~main ~output with
  | Error message -> Outcome.cannot_run "%s" message
  | Ok () -> output

let run ~release ~arguments =
  let session, packages = Command_packages.current () in
  let program = build_program session packages (if release then Release else Development) in
  Outcome.Run_program { program; arguments }

let build ~output =
  let session, packages = Command_packages.current () in
  let package = Command_packages.one packages in
  let output = Shown_path.normalize (Option.value output ~default:(Path.show_package package)) in
  ignore (build_program session packages Release ~output);
  if Output.json () then
    Json.print (Json.document ~diagnostics:[] [ ("output", Json.String (Shown_path.shown output)) ])
  else Output.printf "Built %s.\n" (Shown_path.shown output);
  Outcome.Exit 0
