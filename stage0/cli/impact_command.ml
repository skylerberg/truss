(* [truss impact]: what changed since a git revision and what the change
   reaches, or what depends on a definition now. See CLI.md, "truss
   impact".

   A change is found by comparing each definition's hashes, part by part,
   with the package as it was at the revision, so reformatting, or moving a
   definition within its file, changes nothing. *)

module Names = Resolve.Names

(* Git *)

let git (project : Project.t) arguments =
  match Toolchain.run "git" ("-C" :: project.root :: arguments) with
  | exception Unix.Unix_error _ -> Project.cannot_run "Cannot run git, which `--since` reads."
  | status, output, errors -> (status, output, errors)

(* The package's files at a revision, each with its text, by the same rules
   as on disk: no directory whose name starts with [.], and none that holds
   its own manifest. [None] if the package has no manifest there. *)
let files_at (project : Project.t) revision =
  match git project [ "ls-tree"; "-r"; "--name-only"; revision; "--"; "." ] with
  | 0, listing, _ ->
      let paths = List.filter (( <> ) "") (String.split_on_char '\n' listing) in
      let show path =
        match git project [ "show"; revision ^ ":./" ^ path ] with
        | 0, text, _ -> text
        | _, _, errors -> Project.cannot_run "git show %s:%s failed: %s" revision path errors
      in
      if not (List.mem Project.manifest_name paths) then None
      else
        let nested directory = List.mem (directory ^ "/" ^ Project.manifest_name) paths in
        let modules =
          List.filter_map
            (fun path ->
              let parts = String.split_on_char '/' path in
              let directories = List.rev (List.tl (List.rev parts)) in
              let prefixes =
                List.mapi
                  (fun i _ -> String.concat "/" (List.filteri (fun j _ -> j <= i) directories))
                  directories
              in
              if
                Filename.check_suffix path ".truss"
                && (not (List.exists (String.starts_with ~prefix:".") parts))
                && not (List.exists nested prefixes)
              then
                Some
                  ( directories
                    @ [ Filename.chop_suffix (List.nth parts (List.length parts - 1)) ".truss" ],
                    path )
              else None)
            paths
        in
        Some
          ( show Project.manifest_name,
            List.map (fun (modules, path) -> (modules, show path)) modules )
  | _, _, errors ->
      Project.cannot_run "Cannot read the package at %s: %s" revision (String.trim errors)

(* A database of the package as it was at the revision. *)
let database_at (project : Project.t) revision =
  let database = Query.create () in
  Type_checker.load_standard database;
  (match files_at project revision with
  | None -> Type_checker.load_package database ~name:project.manifest.name ~dependencies:[] []
  | Some (manifest, modules) ->
      let manifest =
        try Type_checker.Manifest.parse manifest
        with Type_checker.Manifest.Malformed _ -> project.manifest
      in
      Type_checker.load_package database ~name:project.manifest.name
        ~dependencies:manifest.dependencies
        (List.map
           (fun (modules, text) ->
             (({ package = project.manifest.name; modules } : Path.module_), text))
           modules));
  database

(* Comparing *)

type kind = Interface | Contract | Default | Body

let rec kind_of : Hash.part -> kind = function
  | Interface | Shape -> Interface
  | Contract | Invariant _ | Potential | Law _ -> Contract
  | Default _ -> Default
  | Body | Proof _ | Value -> Body
  | Member (_, _, part) -> kind_of part

let kind_word = function
  | Interface -> "interface"
  | Contract -> "contract"
  | Default -> "default"
  | Body -> "body"

type change = {
  path : Path.t;
  status : [ `Added | `Removed | `Changed of kind list ];
  before : string option;  (** The signature at the revision *)
  after : string option;  (** The signature now *)
  read_by : Path.t list;
}

let definitions database =
  let package_modules package =
    match Workspace.package database package with Some p -> p.modules | None -> []
  in
  fun package ->
    List.concat_map
      (fun module_ ->
        List.filter_map
          (fun (d : Names.declaration) ->
            if d.ordinal = 0 then Some (d.path, Names.key_of d) else None)
          (Query.demand database Names.declarations module_))
      (package_modules package)

let parts database key = Option.value (Query.demand database Hash.parts key) ~default:[]

(* The kinds of the parts that differ, each once, in order. *)
let differing before after =
  let changed =
    List.filter_map
      (fun (part, digest) ->
        if List.assoc_opt part after = Some digest then None else Some (kind_of part))
      before
    @ List.filter_map
        (fun (part, _) -> if List.mem_assoc part before then None else Some (kind_of part))
        after
  in
  List.filter (fun kind -> List.mem kind changed) [ Interface; Contract; Default; Body ]

let compare_with (project : Project.t) old_database =
  let package = project.manifest.name in
  let old_definitions = definitions old_database package in
  let new_definitions = definitions project.database package in
  let occurrences = References.all project in
  let signature database key = Signatures.text database ~body:false ~opaque:false key in
  let changed =
    List.filter_map
      (fun (path, key) ->
        match List.find_opt (fun (p, _) -> Path.equal p path) old_definitions with
        | None ->
            Some
              {
                path;
                status = `Added;
                before = None;
                after = signature project.database key;
                read_by = [];
              }
        | Some (_, old_key) -> (
            match differing (parts old_database old_key) (parts project.database key) with
            | [] -> None
            | kinds ->
                let signature_changed =
                  List.exists (fun k -> k = Interface || k = Contract) kinds
                in
                Some
                  {
                    path;
                    status = `Changed kinds;
                    before = (if signature_changed then signature old_database old_key else None);
                    after = (if signature_changed then signature project.database key else None);
                    read_by =
                      (if signature_changed then References.dependents occurrences path else []);
                  }))
      new_definitions
  in
  let removed =
    List.filter_map
      (fun (path, old_key) ->
        if List.exists (fun (p, _) -> Path.equal p path) new_definitions then None
        else
          Some
            {
              path;
              status = `Removed;
              before = signature old_database old_key;
              after = None;
              read_by = [];
            })
      old_definitions
  in
  changed @ removed

(* Tests that reach *)

type reaching = { test : Test_command.test; kept : bool }

(* The tests that can run any of [paths], with whether each one's result is
   already kept for its code now. This lowers the code, so it is worked out
   only for a package without errors. *)
let tests_reaching (project : Project.t) paths =
  let compile = Compiler.lowering_only project in
  let results = Cache.results () in
  List.filter_map
    (fun (test : Test_command.test) ->
      match Compiler.reached compile (Compile.test_root test.path) with
      | Some reached
        when List.exists (fun p -> List.exists (Path.equal p) (test.path :: reached)) paths ->
          let kept =
            try Compile.kept_result compile ~results test.path with Invalid_argument _ -> false
          in
          Some { test; kept }
      | _ -> None)
    (Test_command.select project ~paths:[] ~match_:None)

(* Output *)

let paths_json paths = Json.List (List.map (fun p -> Json.String (Path.show p)) paths)

let reaching_json reaching =
  Json.List
    (List.map
       (fun r ->
         Json.Object
           [
             ("module", Json.String (Path.show_module r.test.module_));
             ("name", Json.String r.test.name);
             ("kept", Json.Bool r.kept);
           ])
       reaching)

let print_tests ?(indent = "") heading reaching =
  if reaching <> [] then begin
    let kept = List.length (List.filter (fun r -> r.kept) reaching) in
    Printf.printf "%s%s: %d%s\n" indent heading (List.length reaching)
      (if kept > 0 then Printf.sprintf " (%d kept)" kept else "");
    List.iter
      (fun r ->
        Printf.printf "%s  %s%s\n" indent (Test_command.label r.test)
          (if r.kept then "  kept" else ""))
      reaching
  end

let indent_signature label text =
  match String.split_on_char '\n' text with
  | first :: rest ->
      Printf.printf "    %s %s\n" label first;
      List.iter
        (fun line -> Printf.printf "    %s %s\n" (String.make (String.length label) ' ') line)
        rest
  | [] -> ()

let since_revision (project : Project.t) ~since ~json files =
  let changes = compare_with project (database_at project since) in
  let reaching =
    if files = [] then
      tests_reaching project
        (List.filter_map (fun c -> if c.status = `Removed then None else Some c.path) changes)
    else []
  in
  if json then
    Json.print
      (Json.document ~diagnostics:(Report.to_json files)
         [
           ( "changes",
             Json.List
               (List.map
                  (fun c ->
                    Json.Object
                      [
                        ("path", Json.String (Path.show c.path));
                        ( "change",
                          Json.String
                            (match c.status with
                            | `Added -> "added"
                            | `Removed -> "removed"
                            | `Changed _ -> "changed") );
                        ( "parts",
                          Json.List
                            (match c.status with
                            | `Changed kinds -> List.map (fun k -> Json.String (kind_word k)) kinds
                            | _ -> []) );
                        ("before", Json.option (fun s -> Json.String s) c.before);
                        ("after", Json.option (fun s -> Json.String s) c.after);
                        ("read_by", paths_json c.read_by);
                      ])
                  changes) );
           ("tests", reaching_json reaching);
         ])
  else begin
    Report.print files;
    if changes = [] then Printf.printf "Nothing changed since %s.\n" since
    else begin
      Printf.printf "Changed since %s:\n" since;
      List.iter
        (fun c ->
          Printf.printf "  %s: %s\n" (Path.show c.path)
            (match c.status with
            | `Added -> "added"
            | `Removed -> "removed"
            | `Changed kinds -> String.concat ", " (List.map kind_word kinds));
          Option.iter (indent_signature "was:")
            (match c.status with `Changed _ -> c.before | _ -> None);
          Option.iter (indent_signature "now:")
            (match c.status with `Changed _ -> c.after | _ -> None);
          if c.read_by <> [] then
            Printf.printf "    read by: %s\n" (String.concat ", " (List.map Path.show c.read_by)))
        changes;
      if reaching <> [] then print_newline ();
      print_tests "Tests that can reach a change" reaching
    end
  end;
  if files = [] then 0 else 1

let of_paths (project : Project.t) ~paths ~json files =
  let occurrences = References.all project in
  let found =
    List.map
      (fun text ->
        let declarations = Show_command.resolve project text in
        ( text,
          List.map
            (fun (d : Names.declaration) ->
              ( d.path,
                References.dependents occurrences d.path,
                if files = [] then tests_reaching project [ d.path ] else [] ))
            declarations ))
      paths
  in
  let missing = List.filter_map (fun (text, f) -> if f = [] then Some text else None) found in
  if json then
    Json.print
      (Json.document ~diagnostics:(Report.to_json files)
         [
           ( "dependents",
             Json.List
               (List.concat_map
                  (fun (_, f) ->
                    List.map
                      (fun (path, read_by, reaching) ->
                        Json.Object
                          [
                            ("path", Json.String (Path.show path));
                            ("read_by", paths_json read_by);
                            ("tests", reaching_json reaching);
                          ])
                      f)
                  found) );
           ("not_found", Json.List (List.map (fun t -> Json.String t) missing));
         ])
  else begin
    Report.print files;
    List.iter
      (fun (_, f) ->
        List.iter
          (fun (path, read_by, reaching) ->
            Printf.printf "%s\n" (Path.show path);
            Printf.printf "  read by: %s\n"
              (if read_by = [] then "nothing" else String.concat ", " (List.map Path.show read_by));
            print_tests ~indent:"  " "tests that can reach it" reaching)
          f)
      found;
    List.iter (fun text -> Printf.eprintf "Nothing named `%s` is visible here.\n" text) missing
  end;
  if missing <> [] then 2 else if files = [] then 0 else 1

let run ~directory ~since ~paths ~json =
  let project = Project.load directory in
  let files = Report.gather project in
  match paths with
  | [] -> since_revision project ~since ~json files
  | paths -> of_paths project ~paths ~json files
