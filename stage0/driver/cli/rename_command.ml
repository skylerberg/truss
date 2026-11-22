type target =
  | Definition of { path : Path.t; module_ : Path.module_; owner : string option }
  | Module of Path.module_

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

let find_renamed (names : Resolve.Names.lookups) packages : Path_argument.target -> target option =
  function
  | Module module_ when List.mem module_.package packages -> Some (Module module_)
  | Definition path -> (
      let is_declared_here =
        match names.find_key path with
        | Some key -> List.mem key.module_.package packages
        | None -> false
      in
      match path with
      | Top { module_; _ } when is_declared_here ->
          Some (Definition { path; module_; owner = None })
      | Method { owner = Top { module_; name }; _ }
      | Member_constant { owner = Top { module_; name }; _ }
        when is_declared_here ->
          Some (Definition { path; module_; owner = Some name })
      | _ -> None)
  | Package _ | Module _ -> None

let show_target = function
  | Definition { path; _ } -> Path.show path
  | Module module_ -> Path.show_module module_

let resolve_target database packages from_ =
  let names = Database.make_name_lookups database in
  match
    List.filter_map (find_renamed names packages)
      (Path_argument.resolve names packages (Path_argument.parse from_))
  with
  | [ target ] -> target
  | [] -> Outcome.raise_cannot_run "Nothing named `%s` is defined in this project's packages." from_
  | targets ->
      Outcome.raise_cannot_run "`%s` names %d definitions: %s. Rename one by its full path." from_
        (List.length targets)
        (String.concat ", " (List.map show_target targets))

let compute_new_name ~from_ ~(module_ : Path.module_) ~owner to_ =
  let written = Path_argument.parse to_ in
  if written.prefix <> [] && written.prefix <> Path.list_module_parts module_ then
    Outcome.raise_cannot_run
      "A rename keeps a definition in its module, and `%s` is in another one than `%s`." to_ from_;
  match (written.member, owner) with
  | None, _ -> written.last
  | Some member, Some owner when written.last = owner -> member
  | Some _, Some owner ->
      Outcome.raise_cannot_run "A rename keeps a member with its type, and `%s` is not under `%s`."
        to_ owner
  | Some _, None ->
      Outcome.raise_cannot_run
        "A rename keeps a definition outside a type, and `%s` names a member of `%s`." to_
        written.last

let parse_module_path package text =
  match Path_argument.parse text with
  | { prefix; last; member = None } -> (
      match Path.split_module ~is_package:(( = ) package) (prefix @ [ last ]) with
      | Some { modules = _ :: _ as modules; _ } -> Some modules
      | Some _ | None -> None)
  | { member = Some _; _ } | (exception Outcome.Cannot_run _) -> None

let list_occurrences database snapshot packages =
  let names = Database.make_name_lookups database in
  List.concat_map
    (fun file ->
      List.concat_map
        (fun (declaration : Resolve.Names.declaration) ->
          let key = declaration.key in
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

let list_parts_below (ancestor : Path.module_) (module_ : Path.module_) =
  let count = List.length ancestor.modules in
  if
    ancestor.package = module_.package
    && List.length module_.modules > count
    && List.take count module_.modules = ancestor.modules
  then Some (List.drop count module_.modules)
  else None

let find_module_replacement ~(old_module : Path.module_) ~(new_module : Path.module_)
    (written : Path.module_) (imported : Path.module_ option) =
  let read_last_name module_ = List.nth (List.rev (Path.list_module_parts module_)) 0 in
  match imported with
  | None when written = old_module -> Some (Path.show_module new_module)
  | Some imported when written = old_module && imported = old_module ->
      Some (read_last_name new_module)
  | Some imported when written = old_module -> (
      match list_parts_below imported new_module with
      | Some parts -> Some (String.concat "." (read_last_name imported :: parts))
      | None -> Some (Path.show_module new_module))
  | Some imported when imported = old_module -> Some (Path.show_module written)
  | None | Some _ -> None

let plan_module database snapshot packages (old_module : Path.module_) to_ =
  let package = old_module.package in
  let modules =
    match parse_module_path package to_ with
    | Some modules -> modules
    | None ->
        let package = Path.show_package package in
        Outcome.raise_cannot_run "`%s` is not a module path in %s, such as `%s.name`." to_ package
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
  let edits =
    List.filter_map
      (fun (file, (span : Source.span), (target : Inspect.References.target)) ->
        match target with
        | Module { module_ = written; imported } ->
            Option.map
              (fun replacement -> (file, Diagnostic.replace span replacement))
              (find_module_replacement ~old_module ~new_module written imported)
        | Definition _ -> None)
      (list_occurrences database snapshot packages)
    @ List.concat_map
        (fun (file : Path.file) ->
          List.filter_map
            (fun (module_, span) ->
              if module_ = old_module then Some (file, Diagnostic.replace span full) else None)
            (Inspect.References.list_uses
               ~resolve_module:
                 (Resolve.Names.resolve_used_module
                    (Database.make_name_lookups database)
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

let encode_edits snapshot plan =
  List.concat_map
    (fun (file, edits) ->
      let path = Workspace.locate_file snapshot file in
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
  let report = Report.gather ~proofs:false database snapshot packages in
  Report.require_no_errors report;
  let plan =
    match resolve_target database packages from_ with
    | Definition { path; module_; owner } ->
        plan_definition database snapshot packages path
          (compute_new_name ~from_ ~module_ ~owner to_)
    | Module module_ -> plan_module database snapshot packages module_ to_
  in
  let after = apply_plan database snapshot packages plan in
  let database = Workspace.open_database (make_trial_snapshot snapshot after) in
  let caused =
    List.filter_map
      (fun (_, file, text) ->
        match Diagnostic.select_shown (Database.list_file_diagnostics database file) with
        | [] -> None
        | diagnostics ->
            Some
              {
                Report.file;
                source = Source.create ~path:(Workspace.locate_file snapshot file) text;
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
      let edits = encode_edits snapshot plan in
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
          (Report.make_document report
             [
               ("edits", Json.List edits);
               ( "moved",
                 match plan.moved with
                 | Some (old_m, new_m) ->
                     let encode_directory module_ =
                       Json.String
                         (Command_packages.show_project_path snapshot
                            (locate_directory snapshot packages module_))
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
