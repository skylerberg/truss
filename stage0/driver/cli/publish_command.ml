module Package_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.package
end))

let list_unfinished snapshot database packages =
  let names = Database.make_name_lookups database in
  List.concat_map
    (fun file ->
      let source = Command_packages.read_source snapshot database file in
      List.concat_map
        (fun (declaration : Resolve.Names.declaration) ->
          let key = declaration.key in
          let ({ base; _ } : Resolve.Names.place) = names.read_place key in
          List.map
            (fun ({ keyword; span; _ } : Inspect.unfinished) ->
              let line, column =
                Source.compute_position source (Source.Definition_span.to_file ~base span).start
              in
              ( (match keyword with `Todo -> "todo" | `Echo -> "echo"),
                Source.path source,
                line,
                column ))
            (Inspect.list_unfinished (names.read_spans key) (names.read_definition key)))
        (names.list_declarations_in file))
    (Command_packages.list_files snapshot packages)

let list_files directory (record : Registry.Lock.t) =
  List.filter
    (fun (path, _) -> path <> "truss.lock")
    (Registry.Content.list_published_files directory)
  @ if record = [] then [] else [ ("truss.lock", Registry.Lock.print record) ]

let record database snapshot registry (package : Path.package) =
  let root = Workspace.locate_root snapshot in
  let built = Workspace.list_registry_packages snapshot in
  let find_directory name =
    Option.map
      (fun (relative, _) -> if relative = "" then root else Filename.concat root relative)
      (List.find_opt (fun (_, other) -> other = name) (Workspace.list_packages snapshot))
  in
  let find_in_registry name = List.find_opt (fun (other, _, _) -> other = name) built in
  let list_dependencies ~code name =
    let used =
      if code then Option.value ~default:[] (Database.find_code_packages database name) else []
    in
    List.filter
      (fun dependency -> (not code) || List.mem dependency used)
      (Workspace.list_dependency_names snapshot name)
  in
  let problems = ref [] in
  let rec compute_closure name : Registry.Lock.t =
    let seen = Package_table.create 16 and entries = ref [] in
    let add name version hash =
      entries := { Registry.Lock.name; version; hash; holds = [] } :: !entries
    in
    let rec visit name =
      if not (Package_table.mem seen name) then begin
        Package_table.replace seen name ();
        match (find_in_registry name, find_directory name) with
        | Some (_, version, hash), _ ->
            add name version hash;
            List.iter
              (fun next ->
                if find_in_registry next <> None || find_directory next <> None then visit next)
              (list_dependencies ~code:false name)
        | None, Some directory -> (
            match find_published_version name directory with
            | Some (version, hash) ->
                add name version hash;
                List.iter visit (list_dependencies ~code:true name)
            | None ->
                problems :=
                  Printf.sprintf
                    "`%s` is a package of this project, and its files are not those of a version \
                     the registry holds. A package is published with registry packages only, so \
                     publish `%s` first."
                    (Path.show_package name) (Path.show_package name)
                  :: !problems)
        | None, None -> ()
      end
    in
    List.iter visit (list_dependencies ~code:true name);
    List.sort
      (fun (left : Registry.Lock.entry) right -> Path.compare_package left.name right.name)
      !entries
  and find_published_version name directory =
    let hash = Registry.Content.hash (list_files directory (compute_closure name)) in
    List.find_map
      (fun (version, version_hash) -> if version_hash = hash then Some (version, hash) else None)
      (Registry.Index.list_versions registry name)
  in
  let entries = compute_closure package in
  (entries, List.sort_uniq compare !problems)

let list_failed_tests database snapshot packages =
  let interface = Database.make_interface_lookups database in
  let tests =
    List.filter
      (fun (test : Test_command.test) ->
        not (Interface.Definition.is_external_test interface test.path))
      (Test_command.select snapshot database packages ~paths:[] ~match_:None)
  in
  List.concat
    (List.map2
       (fun (test : Test_command.test) (record : Backend.Test_report.record) ->
         if record.outcome = Passed then []
         else
           [
             Printf.sprintf "%s: %s" (Test_command.label_test test)
               (Backend.Test_report.show_outcome record.outcome);
           ])
       tests
       (Test_command.run_tests database snapshot packages tests))

let run ~version =
  let json = Output.json () in
  let version = Upgrade_command.read_version version in
  let snapshot, packages = Command_packages.load_current () in
  let name = Command_packages.require_one packages in
  if name.owner = None then
    Outcome.raise_cannot_run
      "`%s` has no owner in its name, which a published package's has, such as `acme.%s`." name.name
      name.name;
  let major, _, _ = version and name_major = Registry.Version.parse_major name in
  if major <> name_major then
    Outcome.raise_cannot_run
      "A version of `%s` starts with %d, the number at the end of its name, or 1 for a name \
       without one. A release with another first number is published under another name, such as \
       `%s`."
      (Path.show_package name) name_major
      (Path.show_package (Registry.Version.make_next_major_name name));
  let registry =
    match Registry.Index.find_current_registry () with
    | Some registry -> registry
    | None ->
        Outcome.raise_cannot_run "No registry is set. Set `%s` to the registry's directory."
          Registry.Index.variable
  in
  (match Registry.Index.find_newest registry name with
  | Some (newest, _) when Registry.Version.compare version newest <= 0 ->
      Outcome.raise_cannot_run
        "The newest release of `%s` is %s, so this release needs a higher version."
        (Path.show_package name) (Registry.Version.show newest)
  | _ -> ());
  let database = Workspace.open_database snapshot in
  let report = Report.gather ~proofs:true database snapshot packages in
  let refuse sentences =
    if json then
      Json.print
        (Report.make_document report
           [ ("refused", Json.List (List.map (fun sentence -> Json.String sentence) sentences)) ])
    else List.iter Output.eprint_line sentences;
    raise (Outcome.Stop 1)
  in
  Report.require_no_errors report;
  (match list_unfinished snapshot database packages with
  | [] -> ()
  | unfinished_code ->
      refuse
        (List.map
           (fun (keyword, file, line, column) ->
             Printf.sprintf "%s:%d:%d: `%s` is not finished code." file line column keyword)
           unfinished_code
        @ [ "Cannot publish a package with a `todo` or an `echo`." ]));
  (match list_failed_tests database snapshot packages with
  | [] -> ()
  | failed -> refuse (failed @ [ "Cannot publish a package whose tests fail." ]));
  match record database snapshot registry name with
  | _, (_ :: _ as problems) -> refuse problems
  | record, [] ->
      let files = list_files (Command_packages.locate_directory snapshot name) record in
      Registry.Index.add registry name version files;
      if json then
        Json.print
          (Report.make_document report
             [
               ("package", Json.String (Path.show_package name));
               ("version", Json.String (Registry.Version.show version));
               ("hash", Json.String (Registry.Content.hash files));
             ])
      else
        Output.printf "Published `%s` %s.\n" (Path.show_package name)
          (Registry.Version.show version);
      0
