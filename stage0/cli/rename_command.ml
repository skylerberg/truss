(* [truss rename]: renames a definition, a method, or a module, and every
   reference to it in the project. Renaming a module moves its directory's
   files.

   The rename is made in a trial session and checked there first. If the
   result has any diagnostic, such as a name that is taken, a name that
   breaks a naming rule, or a name that shadows another, no file is
   written. Each edit replaces only a name's tokens, so the files need no
   formatting afterward. *)

module Names = Resolve.Names

type target =
  | Definition of Path.t  (** A top-level definition, or every version of a method *)
  | Module of Path.module_

type plan = {
  edits : (Path.file * Diagnostic.span Diagnostic.edit list) list;
  moved : (Path.module_ * Path.module_) option;  (** A renamed module's old and new paths *)
}

let module_exists session packages (module_ : Path.module_) =
  List.mem module_ (Command_packages.modules session packages)

(* The file after the rename: a file of a renamed module moves with it. *)
let moved_file plan (file : Path.file) =
  match plan.moved with
  | Some (old_module, new_module) when file.module_ = old_module ->
      { file with module_ = new_module }
  | _ -> file

(* The edits grouped by file, in order of file. *)
let by_file edits =
  List.map
    (fun file ->
      ( file,
        List.filter_map
          (fun (edit_file, edit) -> if edit_file = file then Some edit else None)
          edits ))
    (List.sort_uniq compare (List.map fst edits))

(* The module of a project package that [from_] names, and the member
   after it. [from_] must start with the package's name. *)
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

(* The definition or module that [from_] names. *)
let target_of session packages from_ =
  let { Path.package; modules = names }, member = in_package packages from_ in
  let package_name = Path.show_package package in
  if member = None && module_exists session packages { package; modules = names } then
    Module { package; modules = names }
  else
    match List.rev names with
    | last :: rest when module_exists session packages { package; modules = List.rev rest } ->
        let module_ : Path.module_ = { package; modules = List.rev rest } in
        let declared path =
          List.exists
            (fun (declaration : Names.declaration) ->
              match (declaration.path, path) with
              | Method { owner; name; _ }, Path.Method { owner = other_owner; name = other_name; _ }
                ->
                  Path.equal owner other_owner && name = other_name
              | candidate, path -> Path.equal candidate path)
            (List.concat_map
               (Query.demand (Database.context session) Names.declarations)
               (Command_packages.modules session packages))
        in
        let path : Path.t =
          match member with
          | None -> Top { module_; name = last }
          | Some name -> Method { owner = Top { module_; name = last }; name; receiver = Static }
        in
        if declared path then Definition path
        else Outcome.cannot_run "Nothing named `%s` is defined in %s." from_ package_name
    | _ -> Outcome.cannot_run "Nothing named `%s` is defined in %s." from_ package_name

(* The new last segment, from a full path or a bare name. A definition
   stays in its module and a method on its type, so a full path must name
   the same module or type. *)
let new_name ~from_ to_ =
  let written = Path_argument.parse to_ and old = Path_argument.parse from_ in
  (* A method's type and name, or a definition's name alone. *)
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

let plan_definition session packages path name =
  let occurrences = References.all session packages in
  let edits =
    List.filter (References.names_definition path) occurrences
    |> List.map (fun (occurrence : References.occurrence) ->
        (occurrence.file, Diagnostic.replace occurrence.span name))
  in
  { edits = by_file edits; moved = None }

let plan_module session packages (old_module : Path.module_) to_ =
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
  if module_exists session packages new_module then Outcome.cannot_run "`%s` already exists." to_;
  let full = Path.show_module new_module in
  let last = List.nth modules (List.length modules - 1) in
  let edits =
    List.filter_map
      (fun (occurrence : References.occurrence) ->
        match occurrence.target with
        | Module edit_module when edit_module = old_module ->
            (* Written as its import's name, one segment, or as a full path. *)
            let text =
              Source.text (Query.demand (Database.context session) Packages.source occurrence.file)
            in
            let written =
              String.sub text occurrence.span.start (occurrence.span.stop - occurrence.span.start)
            in
            Some
              ( occurrence.file,
                Diagnostic.replace occurrence.span
                  (if String.contains written ':' then full else last) )
        | _ -> None)
      (References.all session packages)
    @ List.map
        (fun (file, span) -> (file, Diagnostic.replace span full))
        (References.uses session packages old_module)
  in
  { edits = by_file edits; moved = Some (old_module, new_module) }

let text_of session file =
  Source.text (Query.demand (Database.context session) Packages.source file)

(* Each file, the file it becomes, and its text after the rename. *)
let applied session packages plan =
  List.map
    (fun file ->
      let text =
        match List.assoc_opt file plan.edits with
        | Some edits -> Check_command.apply (text_of session file) edits
        | None -> text_of session file
      in
      (file, moved_file plan file, text))
    (Command_packages.files session packages)

(* A module's directory, which a rename creates for a module it moves. *)
let directory_of session packages (module_ : Path.module_) =
  if List.mem module_.package packages then
    List.fold_left Filename.concat
      (Command_packages.directory session module_.package)
      module_.modules
  else Outcome.cannot_run "%s is not in this project." (Path.show_module module_)

let path_of session packages (file : Path.file) =
  Filename.concat (directory_of session packages file.module_) (file.name ^ ".truss")

(* A trial session of the worktree with the rename applied, for checking
   it. It starts from the worktree's session, so only the edited files and
   their dependents are checked, and it is discarded afterward. Each file's
   text is placed at its path after the rename, and a moved file's old path
   is removed. *)
let trial session after =
  let path file = Database.file_path session file in
  let written = List.map (fun (_, file, text) -> (path file, Some text)) after in
  let removed =
    List.filter_map
      (fun (old_file, _, _) ->
        let old_path = path old_file in
        if List.mem_assoc old_path written then None else Some (old_path, None))
      after
  in
  Database.trial session (written @ removed)

let edits_json session packages plan =
  List.concat_map
    (fun (file, edits) ->
      let source = Command_packages.source session packages file in
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

(* A rename edits every package of the worktree, regardless of the current
   directory, since any of them may refer to the renamed definition. *)
let run ~from_ ~to_ =
  let json = Output.json () in
  let session, packages = Command_packages.worktree () in
  let report = Report.gather session packages in
  if not (Report.clean report) then raise (Report.Errors report);
  let plan =
    match target_of session packages from_ with
    | Definition path -> plan_definition session packages path (new_name ~from_ to_)
    | Module module_ -> plan_module session packages module_ to_
  in
  let after = applied session packages plan in
  let checked = Database.context (trial session after) in
  let caused =
    List.filter_map
      (fun (_, file, text) ->
        match Diagnostic.shown (Checks.diagnostics checked file) with
        | [] -> None
        | diagnostics ->
            Some
              {
                Report.file;
                source = Source.create ~path:(Shown_path.shown (path_of session packages file)) text;
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
      let edits = edits_json session packages plan in
      List.iter
        (fun (old_file, file, text) ->
          if List.mem_assoc old_file plan.edits || old_file <> file then begin
            let path = path_of session packages file in
            File_system.make_directory (Filename.dirname path);
            Command_packages.write_file path text;
            if old_file <> file then Sys.remove (Command_packages.path session old_file)
          end)
        after;
      Database.refresh session;
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
                       Json.String (Shown_path.shown (directory_of session packages module_))
                     in
                     Json.Object [ ("from", directory old_m); ("to", directory new_m) ]
                 | None -> Json.Null );
             ])
      else
        Output.printf "Renamed %s to %s: %s in %s.\n" from_ to_
          (Report.plural count "edit" "edits")
          (Report.plural (List.length plan.edits) "file" "files");
      0
