module Names = Resolve.Names
module Version = Registry.Version
module Lock = Registry.Lock

let unfinished snapshot database packages =
  let names = Database.make_name_lookups database packages in
  List.concat_map
    (fun file ->
      let source = Command_packages.source snapshot packages file in
      List.concat_map
        (fun declaration ->
          let key = Names.key_of declaration in
          match (names.place key, names.definition key, names.spans key) with
          | Some { base; _ }, Some definition, Some spans ->
              List.map
                (fun ({ keyword; span; _ } : Inspect.unfinished) ->
                  let line, column =
                    Source.position source (Source.Definition_span.to_file ~base span).start
                  in
                  ( (match keyword with `Todo -> "todo" | `Echo -> "echo"),
                    Source.path source,
                    line,
                    column ))
                (Inspect.unfinished spans definition)
          | _ -> [])
        (names.declarations_in file))
    (Command_packages.files snapshot packages)

let files directory (record : Lock.t) =
  List.filter (fun (path, _) -> path <> "truss.lock") (Registry.Content.published_files directory)
  @ if record = [] then [] else [ ("truss.lock", Lock.print record) ]

let record database snapshot registry (package : Path.package) =
  let root = Workspace.root snapshot in
  let built = Workspace.registry_packages snapshot in
  let directory_of name =
    Option.map
      (fun (relative, _) -> if relative = "" then root else Filename.concat root relative)
      (List.find_opt (fun (_, other) -> other = name) (Workspace.packages snapshot))
  in
  let in_registry name = List.find_opt (fun (other, _, _) -> other = name) built in
  let dependencies ~code name =
    let used =
      if code then begin
        Database.check database [ name ];
        Option.value ~default:[] (Database.list_code_packages database name)
      end
      else []
    in
    List.filter
      (fun dependency -> (not code) || List.mem dependency used)
      (Workspace.dependency_names snapshot name)
  in
  let problems = ref [] in
  let rec closure name : Lock.t =
    let seen = Hashtbl.create 16 and entries = ref [] in
    let add name version hash = entries := { Lock.name; version; hash; holds = [] } :: !entries in
    let rec visit name =
      if not (Hashtbl.mem seen name) then begin
        Hashtbl.replace seen name ();
        match (in_registry name, directory_of name) with
        | Some (_, version, hash), _ ->
            add name version hash;
            List.iter
              (fun next -> if in_registry next <> None || directory_of next <> None then visit next)
              (dependencies ~code:false name)
        | None, Some directory -> (
            match published_as name directory with
            | Some (version, hash) ->
                add name version hash;
                List.iter visit (dependencies ~code:true name)
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
    List.iter visit (dependencies ~code:true name);
    List.sort (fun (left : Lock.entry) right -> Path.compare_package left.name right.name) !entries
  and published_as name directory =
    let hash = Registry.Content.hash (files directory (closure name)) in
    List.find_map
      (fun (version, version_hash) -> if version_hash = hash then Some (version, hash) else None)
      (Registry.Index.versions registry name)
  in
  let entries = closure package in
  (entries, List.sort_uniq compare !problems)

let failed_tests database snapshot packages =
  let interface = Database.make_interface_lookups database packages in
  let tests =
    List.filter
      (fun (test : Test_command.test) ->
        Interface.Definition.test_uses interface test.path = Some Types.no_capabilities)
      (Test_command.select snapshot database packages ~paths:[] ~match_:None)
  in
  List.concat
    (List.map2
       (fun (test : Test_command.test) (record : Compile.record) ->
         if record.outcome = Passed then []
         else
           [
             Printf.sprintf "%s: %s" (Test_command.label test) (Compile.show_outcome record.outcome);
           ])
       tests
       (Test_command.run_tests database snapshot packages tests))

let next_name (package : Path.package) =
  let major = Version.major_of_name package in
  let base =
    let suffix = Printf.sprintf "_v%d" major in
    if major > 1 && String.ends_with ~suffix package.name then
      String.sub package.name 0 (String.length package.name - String.length suffix)
    else package.name
  in
  { package with name = Printf.sprintf "%s_v%d" base (major + 1) }

type outcome =
  | Published of {
      version : Version.t;
      files : (string * string) list;
      grows : (Path.t * string) list;
    }
  | Unchanged of Version.t
  | Refused of string list

let decide database snapshot registry (package : Path.package) =
  let name = package in
  match record database snapshot registry package with
  | _, (_ :: _ as problems) -> Refused problems
  | record, [] -> (
      let files = files (Command_packages.directory snapshot package) record in
      let hash = Registry.Content.hash files in
      match Registry.Index.newest registry name with
      | None -> Published { version = Version.first name; files; grows = [] }
      | Some (version, newest) when newest = hash -> Unchanged version
      | Some (((major, minor, patch) as version), _) -> (
          match Workspace.fetch_published name version with
          | Error message -> Refused [ message ]
          | Ok published ->
              let before =
                Database.make_interface_lookups (Workspace.open_database published) [ name ]
              and after = Database.make_interface_lookups database [ name ] in
              let changes = Compatibility.compare ~before ~after name in
              let breaks =
                List.map
                  (fun (path, description) ->
                    let was = Signatures.of_path before.names path
                    and now = Signatures.of_path after.names path in
                    String.concat ""
                      (Printf.sprintf "%s %s." (Path.show path) description
                      ::
                      (if was <> now then
                         List.filter_map Fun.id
                           [
                             Option.map (fun text -> "\n" ^ Signatures.labeled "was:" text) was;
                             Option.map (fun text -> "\n" ^ Signatures.labeled "now:" text) now;
                           ]
                       else [])))
                  (Compatibility.breaks changes)
              in
              if breaks <> [] then
                Refused
                  (Printf.sprintf
                     "This release is incompatible with `%s` %s, so it cannot be published under \
                      that name:"
                     (Path.show_package name) (Version.show version)
                   :: List.map (fun sentence -> "  " ^ sentence) breaks
                  @ [
                      Printf.sprintf "Publish it under a new name, such as `%s`."
                        (Path.show_package (next_name name));
                    ])
              else
                let grows = Compatibility.grows changes in
                Published
                  {
                    version =
                      (if grows = [] then (major, minor, patch + 1) else (major, minor + 1, 0));
                    files;
                    grows;
                  }))

let run () =
  let json = Output.json () in
  let snapshot, packages = Command_packages.current () in
  let name = Command_packages.one packages in
  if name.owner = None then
    Outcome.cannot_run
      "`%s` has no owner in its name, which a published package's has, such as `acme::%s`."
      name.name name.name;
  let registry =
    match Registry.Index.current () with
    | Some registry -> registry
    | None ->
        Outcome.cannot_run "No registry is set. Set `%s` to the registry's directory."
          Registry.Index.variable
  in
  let database = Workspace.open_database snapshot in
  let report = Report.gather ~proofs:true database snapshot packages in
  let refuse sentences =
    if json then
      Json.print
        (Report.document report
           [ ("refused", Json.List (List.map (fun sentence -> Json.String sentence) sentences)) ])
    else List.iter Output.eprint_line sentences;
    raise (Outcome.Stop 1)
  in
  if not (Report.clean report) then raise (Report.Errors report);
  (match unfinished snapshot database packages with
  | [] -> ()
  | unfinished_code ->
      refuse
        (List.map
           (fun (keyword, file, line, column) ->
             Printf.sprintf "%s:%d:%d: `%s` is not finished code." file line column keyword)
           unfinished_code
        @ [ "Cannot publish a package with a `todo` or an `echo`." ]));
  (match failed_tests database snapshot packages with
  | [] -> ()
  | failed -> refuse (failed @ [ "Cannot publish a package whose tests fail." ]));
  match decide database snapshot registry name with
  | Refused sentences -> refuse sentences
  | Unchanged version ->
      if json then
        Json.print (Report.document report [ ("version", Json.String (Version.show version)) ])
      else
        Output.printf "`%s` %s already has these files.\n" (Path.show_package name)
          (Version.show version);
      0
  | Published { version; files; grows } ->
      Registry.Index.add registry name version files;
      let hash = Registry.Content.hash files in
      if json then
        Json.print
          (Report.document report
             [
               ("package", Json.String (Path.show_package name));
               ("version", Json.String (Version.show version));
               ("hash", Json.String hash);
               ( "grows",
                 Json.List
                   (List.map
                      (fun (path, description) ->
                        Json.Object
                          [
                            ("path", Json.String (Path.show path));
                            ("addition", Json.String description);
                          ])
                      grows) );
             ])
      else begin
        Output.printf "Published `%s` %s.\n" (Path.show_package name) (Version.show version);
        List.iter
          (fun (path, description) -> Output.printf "  %s %s.\n" (Path.show path) description)
          grows
      end;
      0
