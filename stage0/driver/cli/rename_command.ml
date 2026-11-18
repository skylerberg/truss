type target = Definition of Path.t | Module of Path.module_

type plan = {
  edits : (Path.file * Source.span Diagnostic.edit list) list;
  moved : (Path.module_ * Path.module_) option;
}

let has_module snapshot packages (module_ : Path.module_) =
  List.mem module_ (Command_packages.list_modules snapshot packages)

let compute_moved_file plan (file : Path.file) =
  match plan.moved with
  | Some (old_module, new_module) when file.module_ = old_module ->
      { file with module_ = new_module }
  | _ -> file

let group_by_file edits =
  List.map
    (fun file ->
      ( file,
        List.filter_map
          (fun (edit_file, edit) -> if edit_file = file then Some edit else None)
          edits ))
    (List.sort_uniq compare (List.map fst edits))

let locate_in_package packages from_ =
  let is_package package = List.mem package packages in
  let argument = Path_argument.parse from_ in
  match Path.split_module ~is_package (argument.prefix @ [ argument.last ]) with
  | Some module_ -> (module_, argument.member)
  | None ->
      Outcome.raise_cannot_run
        "Only the definitions of this project's packages can be renamed, and `%s` is not in one."
        from_

let resolve_target snapshot database packages from_ =
  let { Path.package; modules = names }, member = locate_in_package packages from_ in
  let package_name = Path.show_package package in
  if member = None && has_module snapshot packages { package; modules = names } then
    Module { package; modules = names }
  else
    match List.rev names with
    | last :: rest when has_module snapshot packages { package; modules = List.rev rest } ->
        let module_ : Path.module_ = { package; modules = List.rev rest } in
        let is_declared path =
          List.exists
            (fun (declaration : Resolve.Names.declaration) ->
              match (declaration.path, path) with
              | Method { owner; name; _ }, Path.Method { owner = other_owner; name = other_name; _ }
                ->
                  Path.equal owner other_owner && name = other_name
              | candidate, path -> Path.equal candidate path)
            (List.concat_map (Database.make_name_lookups database packages).list_declarations
               (Command_packages.list_modules snapshot packages))
        in
        let path : Path.t =
          match member with
          | None -> Top { module_; name = last }
          | Some name -> Method { owner = Top { module_; name = last }; name; receiver = Static }
        in
        if is_declared path then Definition path
        else Outcome.raise_cannot_run "Nothing named `%s` is defined in %s." from_ package_name
    | _ -> Outcome.raise_cannot_run "Nothing named `%s` is defined in %s." from_ package_name

let compute_new_name ~from_ to_ =
  let written = Path_argument.parse to_ and old = Path_argument.parse from_ in
  let split_owner_and_name (argument : Path_argument.t) =
    match argument.member with Some member -> (argument.last, member) | None -> ("", argument.last)
  in
  let from_owner, _ = split_owner_and_name old in
  if written.prefix <> [] && written.prefix <> old.prefix then
    Outcome.raise_cannot_run
      "A rename keeps a definition in its module, and `%s` is in another one than `%s`." to_ from_;
  let owner, name = split_owner_and_name written in
  if written.member <> None && owner <> from_owner then
    Outcome.raise_cannot_run "A rename keeps a method with its type, and `%s` is not under `%s`."
      to_ from_owner;
  name

let list_occurrences database snapshot packages =
  let names = Database.make_name_lookups database packages in
  List.concat_map
    (fun file ->
      List.concat_map
        (fun declaration ->
          let key = Resolve.Names.make_key declaration in
          match Database.read_resolved database key with
          | Some resolved ->
              let ({ file; base } : Resolve.Names.place) = names.read_place key in
              let tables =
                Option.map
                  (fun (checked : Infer.checked) -> checked.tables)
                  (Database.read_checked_body database key)
              in
              List.map
                (fun ({ span; target } : Inspect.References.occurrence) ->
                  (file, Source.Definition_span.to_file ~base span, target))
                (Inspect.References.list_occurrences ~path:key.path (names.read_spans key)
                   (names.read_definition key) resolved tables)
          | None -> [])
        (names.list_declarations_in file))
    (Command_packages.list_files snapshot packages)

let plan_definition database snapshot packages path name =
  let edits =
    List.filter_map
      (fun (file, span, target) ->
        if Inspect.References.is_named_by path target then Some (file, Diagnostic.replace span name)
        else None)
      (list_occurrences database snapshot packages)
  in
  { edits = group_by_file edits; moved = None }

let plan_module database snapshot packages (old_module : Path.module_) to_ =
  let package = old_module.package in
  let modules =
    match locate_in_package packages to_ with
    | { package = named; modules = _ :: _ as modules }, None when named = package -> modules
    | _ | (exception Outcome.Cannot_run _) ->
        let package = Path.show_package package in
        Outcome.raise_cannot_run "`%s` is not a module path in %s, such as `%s::name`." to_ package
          package
  in
  List.iter
    (fun name ->
      if not (Manifest.is_valid_name name) then
        Outcome.raise_cannot_run "`%s` is not a lower_snake_case name, which a module's must be."
          name)
    modules;
  let new_module : Path.module_ = { package; modules } in
  if has_module snapshot packages new_module then
    Outcome.raise_cannot_run "`%s` already exists." to_;
  let full = Path.show_module new_module in
  let last = List.nth modules (List.length modules - 1) in
  let edits =
    List.filter_map
      (fun (file, (span : Source.span), (target : Inspect.References.target)) ->
        match target with
        | Module edit_module when edit_module = old_module ->
            let text = Source.text (Database.read_source database file) in
            let written = String.sub text span.start (span.stop - span.start) in
            Some (file, Diagnostic.replace span (if String.contains written ':' then full else last))
        | _ -> None)
      (list_occurrences database snapshot packages)
    @ List.concat_map
        (fun (file : Path.file) ->
          List.filter_map
            (fun (module_, span) ->
              if module_ = old_module then Some (file, Diagnostic.replace span full) else None)
            (Inspect.References.list_uses
               ~resolve_module:
                 (Resolve.Names.resolve_used_module
                    (Database.make_name_lookups database packages)
                    ~from:file.module_)
               (Database.read_parsed database file).uses))
        (Command_packages.list_files snapshot packages)
  in
  { edits = group_by_file edits; moved = Some (old_module, new_module) }

let apply_plan database snapshot packages plan =
  List.map
    (fun file ->
      let text = Source.text (Database.read_source database file) in
      let text =
        match List.assoc_opt file plan.edits with
        | Some edits -> Diagnostic.apply_edits text edits
        | None -> text
      in
      (file, compute_moved_file plan file, text))
    (Command_packages.list_files snapshot packages)

let locate_directory snapshot packages (module_ : Path.module_) =
  if List.mem module_.package packages then
    List.fold_left Filename.concat
      (Command_packages.locate_directory snapshot module_.package)
      module_.modules
  else Outcome.raise_cannot_run "%s is not in this project." (Path.show_module module_)

let locate_path snapshot packages (file : Path.file) =
  Filename.concat (locate_directory snapshot packages file.module_) (file.name ^ ".truss")

let make_trial_snapshot snapshot after =
  let locate_file file = Workspace.locate_file snapshot file in
  let written = List.map (fun (_, file, text) -> (locate_file file, Some text)) after in
  let removed =
    List.filter_map
      (fun (old_file, _, _) ->
        let old_path = locate_file old_file in
        if List.mem_assoc old_path written then None else Some (old_path, None))
      after
  in
  Workspace.make_trial snapshot (written @ removed)

let encode_edits snapshot packages plan =
  List.concat_map
    (fun (file, edits) ->
      let path = Command_packages.show_file snapshot packages file in
      List.map
        (fun (edit : Source.span Diagnostic.edit) ->
          Json.Object
            [
              ("file", Json.String path);
              ("start", Json.Int edit.span.start);
              ("stop", Json.Int edit.span.stop);
              ("replacement", Json.String edit.replacement);
            ])
        edits)
    plan.edits

let run ~from_ ~to_ =
  let json = Output.json () in
  let snapshot, packages = Command_packages.load_worktree () in
  let database = Workspace.open_database snapshot in
  let report = Report.gather database snapshot packages in
  if not (Report.clean report) then raise (Report.Errors report);
  let plan =
    match resolve_target snapshot database packages from_ with
    | Definition path ->
        plan_definition database snapshot packages path (compute_new_name ~from_ to_)
    | Module module_ -> plan_module database snapshot packages module_ to_
  in
  let after = apply_plan database snapshot packages plan in
  let database = Workspace.open_database (make_trial_snapshot snapshot after) in
  Database.check database packages;
  let caused =
    List.filter_map
      (fun (_, file, text) ->
        match Diagnostic.select_shown (Database.list_file_diagnostics database file) with
        | [] -> None
        | diagnostics ->
            Some
              {
                Report.file;
                source =
                  Source.create
                    ~path:(Shown_path.show_path (locate_path snapshot packages file))
                    text;
                diagnostics;
              })
      after
  in
  match caused with
  | _ :: _ ->
      let caused = Report.of_files caused in
      if json then Json.print (Report.make_document caused [])
      else begin
        Report.print caused;
        Output.eprintf "Renaming %s to %s would cause these, so nothing was changed.\n" from_ to_
      end;
      1
  | [] ->
      let edits = encode_edits snapshot packages plan in
      List.iter
        (fun (old_file, file, text) ->
          if List.mem_assoc old_file plan.edits || old_file <> file then begin
            let path = locate_path snapshot packages file in
            File_system.make_directory (Filename.dirname path);
            Command_packages.write_file path text;
            if old_file <> file then Sys.remove (Command_packages.locate_file snapshot old_file)
          end)
        after;
      let count = List.length edits in
      if json then
        Json.print
          (Json.make_document ~diagnostics:[]
             [
               ("edits", Json.List edits);
               ( "moved",
                 match plan.moved with
                 | Some (old_m, new_m) ->
                     let encode_directory module_ =
                       Json.String
                         (Shown_path.show_path (locate_directory snapshot packages module_))
                     in
                     Json.Object
                       [ ("from", encode_directory old_m); ("to", encode_directory new_m) ]
                 | None -> Json.Null );
             ])
      else
        Output.printf "Renamed %s to %s: %s in %s.\n" from_ to_
          (Diagnostic.show_count count "edit" "edits")
          (Diagnostic.show_count (List.length plan.edits) "file" "files");
      0
