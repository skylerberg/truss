(* [truss rename]: renames a definition, a method, or a module, and every
   reference to it in the package.

   The rename is made in memory first and the package checked: if it would
   cause any diagnostic, such as a name already taken, one that breaks a
   naming rule, or one that hides another, nothing is written. Each edit
   replaces a name's tokens alone, so the files need no formatting
   afterward. *)

module Names = Resolve.Names

type what =
  | Definition of Path.t  (** A top-level definition, or every version of a method *)
  | Module of Path.module_

type plan = {
  edits : (Path.module_ * Diagnostic.span Diagnostic.edit list) list;
  moved : (Path.module_ * Path.module_) option;  (** A renamed module's old and new paths *)
}

let module_exists (project : Project.t) (module_ : Path.module_) =
  List.mem_assoc module_ project.files

(* The project's package that [from_] starts with the name of, and the
   names after it, as a module of it. *)
let in_package (project : Project.t) from_ =
  let is_package package =
    List.exists (fun (p : Project.package) -> p.name = package) project.packages
  in
  let argument = Path_argument.parse from_ in
  match Path.split_module ~is_package argument.names with
  | Some module_ -> (module_, argument.member)
  | None when argument.names = [] -> Project.cannot_run "`%s` names nothing." from_
  | None ->
      Project.cannot_run
        "Only the definitions of this project's packages can be renamed, and `%s` is not in one."
        from_

(* What [from_] names. *)
let what (project : Project.t) from_ =
  let { Path.package; modules = names }, member = in_package project from_ in
  let package_name = Path.show_package package in
  if member = None && module_exists project { package; modules = names } then
    Module { package; modules = names }
  else
    match List.rev names with
    | last :: rest when module_exists project { package; modules = List.rev rest } ->
        let module_ : Path.module_ = { package; modules = List.rev rest } in
        let declared path =
          List.exists
            (fun (d : Names.declaration) ->
              match (d.path, path) with
              | Method { owner; name; _ }, Path.Method { owner = o; name = n; _ } ->
                  Path.equal owner o && name = n
              | p, path -> Path.equal p path)
            (List.concat_map
               (Query.demand project.context Names.declarations)
               (Project.modules project))
        in
        let path : Path.t =
          match member with
          | None -> Top { module_; name = last }
          | Some name -> Method { owner = Top { module_; name = last }; name; receiver = Static }
        in
        if declared path then Definition path
        else Project.cannot_run "Nothing named `%s` is defined in %s." from_ package_name
    | _ -> Project.cannot_run "Nothing named `%s` is defined in %s." from_ package_name

(* The new last name, from a full path or a bare name. A definition keeps
   its module and a method its type, so a full path must say the same
   ones. *)
let new_name ~from_ to_ =
  let written = Path_argument.parse to_ and old = Path_argument.parse from_ in
  (* A method's type and name, or a definition's name alone. *)
  let owner_and_name (argument : Path_argument.t) =
    let last = match List.rev argument.names with last :: _ -> last | [] -> "" in
    match argument.member with Some member -> (last, member) | None -> ("", last)
  in
  let from_owner, _ = owner_and_name old in
  if List.length written.names > 1 && Path_argument.prefix written <> Path_argument.prefix old then
    Project.cannot_run
      "A rename keeps a definition in its module, and `%s` is in another one than `%s`." to_ from_;
  let owner, name = owner_and_name written in
  if written.member <> None && owner <> from_owner then
    Project.cannot_run "A rename keeps a method with its type, and `%s` is not under `%s`." to_
      from_owner;
  if name = "" then Project.cannot_run "`%s` gives no new name." to_;
  name

let plan_definition (project : Project.t) path name =
  let occurrences = References.all project in
  let edits =
    List.filter (References.names_definition path) occurrences
    |> List.map (fun (o : References.occurrence) -> (o.module_, Diagnostic.replace o.span name))
  in
  {
    edits =
      List.map
        (fun module_ ->
          (module_, List.filter_map (fun (m, e) -> if m = module_ then Some e else None) edits))
        (List.sort_uniq compare (List.map fst edits));
    moved = None;
  }

let plan_module (project : Project.t) (old_module : Path.module_) to_ =
  let package = old_module.package in
  let modules =
    match in_package project to_ with
    | { package = named; modules = _ :: _ as modules }, None when named = package -> modules
    | _ | (exception Project.Cannot_run _) ->
        let package = Path.show_package package in
        Project.cannot_run "`%s` is not a module path in %s, such as `%s::name`." to_ package
          package
  in
  List.iter
    (fun name ->
      if not (Manifest.valid_name name) then
        Project.cannot_run "`%s` is not a lower_snake_case name, which a module's must be." name)
    modules;
  let new_module : Path.module_ = { package; modules } in
  if module_exists project new_module then Project.cannot_run "`%s` already exists." to_;
  let full = Path.show_module new_module in
  let last = List.nth modules (List.length modules - 1) in
  let edits =
    List.filter_map
      (fun (o : References.occurrence) ->
        match o.target with
        | Module m when m = old_module ->
            (* Written through its import, one name, or as a full path. *)
            let text = Source.text (Project.parsed project o.module_).source in
            let written = String.sub text o.span.start (o.span.stop - o.span.start) in
            Some
              ( o.module_,
                Diagnostic.replace o.span (if String.contains written ':' then full else last) )
        | _ -> None)
      (References.all project)
    @ List.map
        (fun (module_, span) -> (module_, Diagnostic.replace span full))
        (References.uses project old_module)
  in
  let files = List.sort_uniq compare (old_module :: List.map fst edits) in
  {
    edits =
      List.map
        (fun module_ ->
          (module_, List.filter_map (fun (m, e) -> if m = module_ then Some e else None) edits))
        files;
    moved = Some (old_module, new_module);
  }

let text_of (project : Project.t) module_ = Source.text (Project.parsed project module_).source

(* Each module and its text after the plan, under its new path. *)
let applied (project : Project.t) plan =
  List.map
    (fun module_ ->
      let text =
        match List.assoc_opt module_ plan.edits with
        | Some edits -> Check_command.apply (text_of project module_) edits
        | None -> text_of project module_
      in
      let module_ =
        match plan.moved with Some (old_m, new_m) when old_m = module_ -> new_m | _ -> module_
      in
      (module_, text))
    (Project.modules project)

(* A session of the worktree with the plan made, for checking it: a trial
   that starts from the session's state, so only what the rename changes is
   checked, and which is dropped after. Each module's text is given under
   the file it has after the plan, and the file of a module that moves is
   removed. *)
let trial (project : Project.t) after =
  let file module_ = Database.module_file project.session module_ in
  let written = List.map (fun (module_, text) -> (file module_, Some text)) after in
  let removed =
    List.filter_map
      (fun module_ ->
        let file = file module_ in
        if List.mem_assoc file written then None else Some (file, None))
      (Project.modules project)
  in
  Database.trial project.session (written @ removed)

let file_of (project : Project.t) (module_ : Path.module_) =
  match List.find_opt (fun (p : Project.package) -> p.name = module_.package) project.packages with
  | Some package -> Filename.concat package.directory (String.concat "/" module_.modules ^ ".truss")
  | None -> Project.file project module_

let edits_json (project : Project.t) plan =
  List.concat_map
    (fun (module_, edits) ->
      let source = Project.source project module_ in
      List.map
        (fun (edit : Diagnostic.span Diagnostic.edit) ->
          Json.Object
            [
              ("file", Json.String (Source.path source));
              ("start", Json.Int edit.span.start);
              ("stop", Json.Int edit.span.stop);
              ("replacement", Json.String edit.replacement);
            ])
        edits)
    plan.edits

(* A rename reaches every package of the worktree, whichever directory it
   is run from, since any of them may name what it renames. *)
let run ~directory ~from_ ~to_ ~json =
  let here = Project.load directory in
  let project = Project.load (Database.root here.session) in
  let report = Report.gather project in
  if not (Report.clean report) then begin
    (* References are found through checked code, which a package with
       errors does not fully have. *)
    if json then Json.print (Report.document report [])
    else begin
      Report.print report;
      Output.eprint_line "Fix these first: a rename finds references through checked code."
    end;
    1
  end
  else
    let plan =
      match what project from_ with
      | Definition path -> plan_definition project path (new_name ~from_ to_)
      | Module module_ -> plan_module project module_ to_
    in
    let after = applied project plan in
    let checked = Database.context (trial project after) in
    let caused =
      List.filter_map
        (fun (module_, text) ->
          match Diagnostic.shown (Type_checker.diagnostics checked module_) with
          | [] -> None
          | diagnostics ->
              let path =
                match plan.moved with
                | Some (_, new_m) when new_m = module_ -> file_of project module_
                | _ -> Project.file project module_
              in
              Some
                {
                  Report.module_;
                  source = Source.create ~path:(Project.shown path) text;
                  diagnostics;
                })
        after
    in
    match caused with
    | _ :: _ ->
        let caused = { Report.files = caused; problems = [] } in
        if json then Json.print (Report.document caused [])
        else begin
          Report.print caused;
          Output.eprintf "Renaming %s to %s would cause these, so nothing was changed.\n" from_ to_
        end;
        1
    | [] ->
        let edits = edits_json project plan in
        List.iter
          (fun (module_, text) ->
            let old_module =
              match plan.moved with
              | Some (old_m, new_m) when new_m = module_ -> old_m
              | _ -> module_
            in
            if List.mem_assoc old_module plan.edits || old_module <> module_ then begin
              let path = file_of project module_ in
              let rec make directory =
                if not (Sys.file_exists directory) then begin
                  make (Filename.dirname directory);
                  Sys.mkdir directory 0o755
                end
              in
              make (Filename.dirname path);
              Project.write_file path text;
              if old_module <> module_ then Sys.remove (Project.file project old_module)
            end)
          after;
        Project.reload project;
        let count = List.length edits in
        if json then
          Json.print
            (Json.document ~diagnostics:[]
               [
                 ("edits", Json.List edits);
                 ( "moved",
                   match plan.moved with
                   | Some (old_m, new_m) ->
                       Json.Object
                         [
                           ("from", Json.String (Project.shown (Project.file project old_m)));
                           ("to", Json.String (Project.shown (file_of project new_m)));
                         ]
                   | None -> Json.Null );
               ])
        else
          Output.printf "Renamed %s to %s: %s in %s.\n" from_ to_
            (Report.plural count "edit" "edits")
            (Report.plural (List.length plan.edits) "file" "files");
        0
