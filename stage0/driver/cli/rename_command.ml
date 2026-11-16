module Names = Resolve.Names
module References = Inspect.References

type target = Definition of Path.t | Module of Path.module_

type plan = {
  edits : (Path.file * Source.span Diagnostic.edit list) list;
  moved : (Path.module_ * Path.module_) option;
}

let module_exists snapshot packages (module_ : Path.module_) =
  List.mem module_ (Command_packages.modules snapshot packages)

let moved_file plan (file : Path.file) =
  match plan.moved with
  | Some (old_module, new_module) when file.module_ = old_module ->
      { file with module_ = new_module }
  | _ -> file

let by_file edits =
  List.map
    (fun file ->
      ( file,
        List.filter_map
          (fun (edit_file, edit) -> if edit_file = file then Some edit else None)
          edits ))
    (List.sort_uniq compare (List.map fst edits))

let in_package packages from_ =
  let is_package package = List.mem package packages in
  let argument = Path_argument.parse from_ in
  match Path.split_module ~is_package argument.names with
  | Some module_ -> (module_, argument.member)
  | None when argument.names = [] -> Outcome.cannot_run "`%s` names nothing." from_
  | None ->
      Outcome.cannot_run
        "Only the definitions of this project's packages can be renamed, and `%s` is not in one."
        from_

let target_of snapshot pipeline packages from_ =
  let { Path.package; modules = names }, member = in_package packages from_ in
  let package_name = Path.show_package package in
  if member = None && module_exists snapshot packages { package; modules = names } then
    Module { package; modules = names }
  else
    match List.rev names with
    | last :: rest when module_exists snapshot packages { package; modules = List.rev rest } ->
        let module_ : Path.module_ = { package; modules = List.rev rest } in
        let declared path =
          List.exists
            (fun (declaration : Names.declaration) ->
              match (declaration.path, path) with
              | Method { owner; name; _ }, Path.Method { owner = other_owner; name = other_name; _ }
                ->
                  Path.equal owner other_owner && name = other_name
              | candidate, path -> Path.equal candidate path)
            (List.concat_map (Pipeline.names pipeline packages).declarations
               (Command_packages.modules snapshot packages))
        in
        let path : Path.t =
          match member with
          | None -> Top { module_; name = last }
          | Some name -> Method { owner = Top { module_; name = last }; name; receiver = Static }
        in
        if declared path then Definition path
        else Outcome.cannot_run "Nothing named `%s` is defined in %s." from_ package_name
    | _ -> Outcome.cannot_run "Nothing named `%s` is defined in %s." from_ package_name

let new_name ~from_ to_ =
  let written = Path_argument.parse to_ and old = Path_argument.parse from_ in
  let owner_and_name (argument : Path_argument.t) =
    let last = match List.rev argument.names with last :: _ -> last | [] -> "" in
    match argument.member with Some member -> (last, member) | None -> ("", last)
  in
  let from_owner, _ = owner_and_name old in
  if List.length written.names > 1 && Path_argument.prefix written <> Path_argument.prefix old then
    Outcome.cannot_run
      "A rename keeps a definition in its module, and `%s` is in another one than `%s`." to_ from_;
  let owner, name = owner_and_name written in
  if written.member <> None && owner <> from_owner then
    Outcome.cannot_run "A rename keeps a method with its type, and `%s` is not under `%s`." to_
      from_owner;
  if name = "" then Outcome.cannot_run "`%s` gives no new name." to_;
  name

let occurrences pipeline snapshot packages =
  let names = Pipeline.names pipeline packages in
  List.concat_map
    (fun file ->
      List.concat_map
        (fun declaration ->
          let key = Names.key_of declaration in
          match
            (names.place key, names.definition key, names.spans key, Pipeline.resolved pipeline key)
          with
          | Some { file; base }, Some definition, Some spans, Some resolved ->
              let tables = Pipeline.tables pipeline key in
              List.map
                (fun ({ span; target } : References.occurrence) ->
                  (file, Source.Definition_span.to_file ~base span, target))
                (References.occurrences ~path:key.path spans definition resolved tables)
          | _ -> [])
        (names.declarations_in file))
    (Command_packages.files snapshot packages)

let plan_definition pipeline snapshot packages path name =
  let edits =
    List.filter_map
      (fun (file, span, target) ->
        if References.names_definition path target then Some (file, Diagnostic.replace span name)
        else None)
      (occurrences pipeline snapshot packages)
  in
  { edits = by_file edits; moved = None }

let plan_module pipeline snapshot packages (old_module : Path.module_) to_ =
  let package = old_module.package in
  let modules =
    match in_package packages to_ with
    | { package = named; modules = _ :: _ as modules }, None when named = package -> modules
    | _ | (exception Outcome.Cannot_run _) ->
        let package = Path.show_package package in
        Outcome.cannot_run "`%s` is not a module path in %s, such as `%s::name`." to_ package
          package
  in
  List.iter
    (fun name ->
      if not (Manifest.valid_name name) then
        Outcome.cannot_run "`%s` is not a lower_snake_case name, which a module's must be." name)
    modules;
  let new_module : Path.module_ = { package; modules } in
  if module_exists snapshot packages new_module then Outcome.cannot_run "`%s` already exists." to_;
  let full = Path.show_module new_module in
  let last = List.nth modules (List.length modules - 1) in
  let edits =
    List.filter_map
      (fun (file, (span : Source.span), (target : References.target)) ->
        match target with
        | Module edit_module when edit_module = old_module ->
            let text = Source.text (Workspace.source snapshot file) in
            let written = String.sub text span.start (span.stop - span.start) in
            Some (file, Diagnostic.replace span (if String.contains written ':' then full else last))
        | _ -> None)
      (occurrences pipeline snapshot packages)
    @ List.concat_map
        (fun (file : Path.file) ->
          List.filter_map
            (fun (module_, span) ->
              if module_ = old_module then Some (file, Diagnostic.replace span full) else None)
            (References.uses
               ~used_module:
                 (Names.used_module (Pipeline.names pipeline packages) ~from:file.module_)
               (Pipeline.parsed pipeline file).file.uses))
        (Command_packages.files snapshot packages)
  in
  { edits = by_file edits; moved = Some (old_module, new_module) }

let text_of snapshot file = Source.text (Workspace.source snapshot file)

let applied snapshot packages plan =
  List.map
    (fun file ->
      let text =
        match List.assoc_opt file plan.edits with
        | Some edits -> Diagnostic.apply_edits (text_of snapshot file) edits
        | None -> text_of snapshot file
      in
      (file, moved_file plan file, text))
    (Command_packages.files snapshot packages)

let directory_of snapshot packages (module_ : Path.module_) =
  if List.mem module_.package packages then
    List.fold_left Filename.concat
      (Command_packages.directory snapshot module_.package)
      module_.modules
  else Outcome.cannot_run "%s is not in this project." (Path.show_module module_)

let path_of snapshot packages (file : Path.file) =
  Filename.concat (directory_of snapshot packages file.module_) (file.name ^ ".truss")

let trial snapshot after =
  let path file = Workspace.file_path snapshot file in
  let written = List.map (fun (_, file, text) -> (path file, Some text)) after in
  let removed =
    List.filter_map
      (fun (old_file, _, _) ->
        let old_path = path old_file in
        if List.mem_assoc old_path written then None else Some (old_path, None))
      after
  in
  Workspace.trial snapshot (written @ removed)

let edits_json snapshot packages plan =
  List.concat_map
    (fun (file, edits) ->
      let source = Command_packages.source snapshot packages file in
      List.map
        (fun (edit : Source.span Diagnostic.edit) ->
          Json.Object
            [
              ("file", Json.String (Source.path source));
              ("start", Json.Int edit.span.start);
              ("stop", Json.Int edit.span.stop);
              ("replacement", Json.String edit.replacement);
            ])
        edits)
    plan.edits

let run ~from_ ~to_ =
  let json = Output.json () in
  let snapshot, packages = Command_packages.worktree () in
  let pipeline = Workspace.pipeline snapshot in
  let report = Report.gather pipeline snapshot packages in
  if not (Report.clean report) then raise (Report.Errors report);
  let plan =
    match target_of snapshot pipeline packages from_ with
    | Definition path -> plan_definition pipeline snapshot packages path (new_name ~from_ to_)
    | Module module_ -> plan_module pipeline snapshot packages module_ to_
  in
  let after = applied snapshot packages plan in
  let pipeline = Workspace.pipeline (trial snapshot after) in
  Pipeline.check pipeline packages;
  let caused =
    List.filter_map
      (fun (_, file, text) ->
        match Diagnostic.shown (Pipeline.file_diagnostics pipeline file) with
        | [] -> None
        | diagnostics ->
            Some
              {
                Report.file;
                source =
                  Source.create ~path:(Shown_path.shown (path_of snapshot packages file)) text;
                diagnostics;
              })
      after
  in
  match caused with
  | _ :: _ ->
      let caused = Report.of_files caused in
      if json then Json.print (Report.document caused [])
      else begin
        Report.print caused;
        Output.eprintf "Renaming %s to %s would cause these, so nothing was changed.\n" from_ to_
      end;
      1
  | [] ->
      let edits = edits_json snapshot packages plan in
      List.iter
        (fun (old_file, file, text) ->
          if List.mem_assoc old_file plan.edits || old_file <> file then begin
            let path = path_of snapshot packages file in
            File_system.make_directory (Filename.dirname path);
            Command_packages.write_file path text;
            if old_file <> file then Sys.remove (Command_packages.path snapshot old_file)
          end)
        after;
      let count = List.length edits in
      if json then
        Json.print
          (Json.document ~diagnostics:[]
             [
               ("edits", Json.List edits);
               ( "moved",
                 match plan.moved with
                 | Some (old_m, new_m) ->
                     let directory module_ =
                       Json.String (Shown_path.shown (directory_of snapshot packages module_))
                     in
                     Json.Object [ ("from", directory old_m); ("to", directory new_m) ]
                 | None -> Json.Null );
             ])
      else
        Output.printf "Renamed %s to %s: %s in %s.\n" from_ to_
          (Report.plural count "edit" "edits")
          (Report.plural (List.length plan.edits) "file" "files");
      0
