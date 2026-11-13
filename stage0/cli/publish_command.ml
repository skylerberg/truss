(* [truss publish]: publishes the package the command runs in to the
   registry as its next version, if the package is complete and compatible
   with its previous version. The registry assigns the version number. *)

module Names = Resolve.Names
module Version = Registry.Version
module Lock = Registry.Lock

(* Every [todo] and [echo] of the package, with its position, in order of
   position in each file. A type defined as [todo] is at its name. *)
let unfinished session packages =
  List.concat_map
    (fun file ->
      let source = Command_packages.source session packages file in
      List.concat_map
        (fun (item : Syntax.definition Syntax.item) ->
          List.map
            (fun ({ keyword; span; _ } : Inspect.unfinished) ->
              let line, column =
                Source.position source (Syntax.Span.to_source ~base:item.base span).start
              in
              ( (match keyword with `Todo -> "todo" | `Echo -> "echo"),
                Source.path source,
                line,
                column ))
            (Inspect.unfinished item.value))
        (Query.demand (Database.context session) Workspace.file file).definitions)
    (Command_packages.files session packages)

(* The files to publish: the package's own, with its published lock file
   in place of the project's. *)
let files directory (record : Lock.t) =
  List.filter (fun (path, _) -> path <> "truss.lock") (Registry.Content.files directory)
  @ if record = [] then [] else [ ("truss.lock", Lock.print record) ]

(* The published lock file's entries: each registry package that the
   package's non-test code reaches, at the build's version. A dependency
   that is a project package counts as a registry package only when its
   files match a version the registry holds, which is then its version. Any
   other project package is a problem, since a package may depend only on
   registry packages. *)
let record session registry (package : Path.package) =
  let root = Database.root session in
  let built = Database.registry_packages session in
  let directory_of name =
    Option.map
      (fun (relative, _) -> if relative = "" then root else Filename.concat root relative)
      (List.find_opt (fun (_, other) -> other = name) (Database.packages session))
  in
  let in_registry name = List.find_opt (fun (other, _, _) -> other = name) built in
  let dependencies ~code name =
    let used = if code then Database.code_packages session name else [] in
    List.filter_map
      (fun (dependency : Manifest.dependency) ->
        if (not code) || List.mem dependency.package used then Some dependency.package else None)
      (Query.demand (Database.context session) Workspace.dependencies name)
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
            (* A registry package's own dependencies are already in the build. *)
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

(* The package's failing tests that have no [uses], each with its
   outcome. *)
let failed_tests session packages =
  let tests =
    List.filter
      (fun (test : Test_command.test) ->
        match Query.demand (Database.context session) Interface.Environment.interface test.path with
        | Some (Test_interface uses) -> uses = Types.no_capabilities
        | _ -> false)
      (Test_command.select session packages ~paths:[] ~match_:None)
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
       (Test_command.run_tests session packages tests))

(* The name to publish an incompatible release under: the name with the
   next number after [_v]. *)
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

let decide session registry (package : Path.package) =
  let name = package in
  match record session registry package with
  | _, (_ :: _ as problems) -> Refused problems
  | record, [] -> (
      let files = files (Command_packages.directory session package) record in
      let hash = Registry.Content.hash files in
      match Registry.Index.newest registry name with
      | None -> Published { version = Version.first name; files; grows = [] }
      | Some (version, newest) when newest = hash -> Unchanged version
      | Some (((major, minor, patch) as version), _) -> (
          match Database.published name version with
          | Error message -> Refused [ message ]
          | Ok published ->
              let changes, narrowed =
                Compatibility.compare ~before:(Database.context published)
                  ~after:(Database.context session) name
              in
              let breaks =
                List.map
                  (fun (path, description) ->
                    let was = Signatures.of_path (Database.context published) path
                    and now = Signatures.of_path (Database.context session) path in
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
                @
                if narrowed then
                  [
                    Printf.sprintf "`%s` ran on every target, and now says `usize_bits = 64`."
                      (Path.show_package name);
                  ]
                else []
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
  let session, packages = Command_packages.current () in
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
  let report = Report.gather ~proofs:true session packages in
  let refuse sentences =
    if json then
      Json.print
        (Report.document report
           [ ("refused", Json.List (List.map (fun sentence -> Json.String sentence) sentences)) ])
    else List.iter Output.eprint_line sentences;
    raise (Outcome.Stop 1)
  in
  if not (Report.clean report) then raise (Report.Errors report);
  (match unfinished session packages with
  | [] -> ()
  | unfinished_code ->
      refuse
        (List.map
           (fun (keyword, file, line, column) ->
             Printf.sprintf "%s:%d:%d: `%s` is not finished code." file line column keyword)
           unfinished_code
        @ [ "Cannot publish a package with a `todo` or an `echo`." ]));
  (match failed_tests session packages with
  | [] -> ()
  | failed -> refuse (failed @ [ "Cannot publish a package whose tests fail." ]));
  match decide session registry name with
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
