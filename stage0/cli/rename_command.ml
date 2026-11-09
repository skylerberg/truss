(* [truss rename]: renames a definition, a method, or a module, and every
   reference to it in the package. See CLI.md, "truss rename".

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
  edits : (Path.module_ * Diagnostic.edit list) list;
  moved : (Path.module_ * Path.module_) option;  (** A renamed module's old and new paths *)
}

let split text = String.split_on_char ':' text |> List.filter (( <> ) "")

let module_exists (project : Project.t) (module_ : Path.module_) =
  List.mem_assoc module_ project.files

(* What [from_] names in this package. *)
let what (project : Project.t) from_ =
  let parts = split from_ in
  let package = project.manifest.name in
  match parts with
  | first :: modules when first = package && module_exists project { package; modules } ->
      Module { package; modules }
  | first :: _ when first <> package ->
      Project.cannot_run "Only this package's definitions can be renamed, and `%s` is not in %s."
        from_ package
  | _ -> (
      match List.rev parts with
      | last :: (_ :: _ as rest)
        when module_exists project { package; modules = List.tl (List.rev rest) } -> (
          let module_ : Path.module_ = { package; modules = List.tl (List.rev rest) } in
          let declared path =
            List.exists
              (fun (d : Names.declaration) ->
                match (d.path, path) with
                | Method { owner; name; _ }, Path.Method { owner = o; name = n; _ } ->
                    Path.equal owner o && name = n
                | p, path -> Path.equal p path)
              (List.concat_map
                 (Query.demand project.database Names.declarations)
                 (Project.modules project))
          in
          let path : Path.t =
            match String.index_opt last '.' with
            | None -> Top { module_; name = last }
            | Some dot ->
                Method
                  {
                    owner = Top { module_; name = String.sub last 0 dot };
                    name = String.sub last (dot + 1) (String.length last - dot - 1);
                    receiver = Static;
                  }
          in
          match path with
          | (Top _ | Method _) when declared path -> Definition path
          | _ -> Project.cannot_run "Nothing named `%s` is defined in %s." from_ package)
      | _ -> Project.cannot_run "Nothing named `%s` is defined in %s." from_ package)

(* The new last name, from a full path or a bare name. A definition keeps
   its module and a method its type, so a full path must say the same
   ones. *)
let new_name ~from_ to_ =
  let last text = match List.rev (split text) with last :: _ -> last | [] -> text in
  let member text =
    match String.index_opt text '.' with
    | Some dot -> (String.sub text 0 dot, String.sub text (dot + 1) (String.length text - dot - 1))
    | None -> ("", text)
  in
  let prefix text = match List.rev (split text) with _ :: rest -> List.rev rest | [] -> [] in
  let from_owner, _ = member (last from_) in
  if String.contains to_ ':' && prefix to_ <> prefix from_ then
    Project.cannot_run
      "A rename keeps a definition in its module, and `%s` is in another one than `%s`." to_ from_;
  let owner, name = member (last to_) in
  if String.contains (last to_) '.' && owner <> from_owner then
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
  let package = project.manifest.name in
  let modules =
    match split to_ with
    | first :: modules when first = package && modules <> [] -> modules
    | _ ->
        Project.cannot_run "`%s` is not a module path in %s, such as `%s::name`." to_ package
          package
  in
  List.iter
    (fun name ->
      if not (New_command.valid_name name) then
        Project.cannot_run "`%s` is not a lower_snake_case name, which a module's must be." name)
    modules;
  let new_module : Path.module_ = { package; modules } in
  if module_exists project new_module then Project.cannot_run "`%s` already exists." to_;
  let full = String.concat "::" (package :: modules) in
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

let load (project : Project.t) modules =
  Type_checker.load_package project.database ~name:project.manifest.name
    ~dependencies:project.manifest.dependencies modules

let file_of (project : Project.t) (module_ : Path.module_) =
  Filename.concat project.root (String.concat "/" module_.modules ^ ".truss")

let edits_json (project : Project.t) plan =
  List.concat_map
    (fun (module_, edits) ->
      let source = Project.source project module_ in
      List.map
        (fun (edit : Diagnostic.edit) ->
          Json.Object
            [
              ("file", Json.String (Source.path source));
              ("start", Json.Int edit.span.start);
              ("stop", Json.Int edit.span.stop);
              ("replacement", Json.String edit.replacement);
            ])
        edits)
    plan.edits

let run ~directory ~from_ ~to_ ~json =
  let project = Project.load directory in
  match Report.gather project with
  | _ :: _ as files ->
      (* References are found through checked code, which a package with
         errors does not fully have. *)
      if json then Json.print (Json.document ~diagnostics:(Report.to_json files) [])
      else begin
        Report.print files;
        prerr_endline "Fix these first: a rename finds references through checked code."
      end;
      1
  | [] -> (
      let plan =
        match what project from_ with
        | Definition path -> plan_definition project path (new_name ~from_ to_)
        | Module module_ -> plan_module project module_ to_
      in
      let original = List.map (fun m -> (m, text_of project m)) (Project.modules project) in
      let after = applied project plan in
      load project after;
      let caused =
        List.filter_map
          (fun (module_, text) ->
            match Diagnostic.shown (Type_checker.diagnostics project.database module_) with
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
          load project original;
          if json then Json.print (Json.document ~diagnostics:(Report.to_json caused) [])
          else begin
            Report.print caused;
            Printf.eprintf "Renaming %s to %s would cause these, so nothing was changed.\n%!" from_
              to_
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
            Printf.printf "Renamed %s to %s: %s in %s.\n" from_ to_
              (Report.plural count "edit" "edits")
              (Report.plural (List.length plan.edits) "file" "files");
          0)
