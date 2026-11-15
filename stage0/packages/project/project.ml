let roots : (unit, string list) Query.input =
  Query.input ~name:"project_roots" ~show:(fun () -> "") ()

let tree : (string, string list) Query.input = Query.input ~name:"project_tree" ~show:Fun.id ()

let text : (string * string, string) Query.input =
  Query.input ~name:"project_text"
    ~show:(fun (root, path) -> if root = "" then path else root ^ ":" ^ path)
    ()

let unavailable : (string, string) Query.input =
  Query.input ~name:"project_unavailable" ~show:Fun.id ()

let project_root = ""
let standard_root = "standard"
let registry_root hash = "registry " ^ hash

let package_root name =
  if name = Path.standard_package then standard_root else "package " ^ Path.show_package name

let lock_file = "truss.lock"
let manifest_file directory = if directory = "" then "truss.toml" else directory ^ "/truss.toml"

let parent path =
  match String.rindex_opt path '/' with Some separator -> String.sub path 0 separator | None -> ""

let segments path = if path = "" then [] else String.split_on_char '/' path

let rec package_directory ~is_package directory =
  if is_package directory then Some directory
  else if directory = "" then None
  else package_directory ~is_package (parent directory)

let file_of_path ~package ~directory path : Path.file =
  let inside =
    if directory = "" then path
    else
      String.sub path
        (String.length directory + 1)
        (String.length path - String.length directory - 1)
  in
  {
    module_ = { package; modules = segments (parent inside) };
    name = Filename.chop_suffix (Filename.basename inside) ".truss";
  }

let file_path ~directory (file : Path.file) =
  let path = String.concat "/" (Path.file_names file) in
  if directory = "" then path else directory ^ "/" ^ path

type package = {
  name : Path.package;
  dependencies : Manifest.dependency list;
  modules : Path.module_ list;
  files : Path.file list;
}

type source_file = { path : string; directory : string; file : Path.file }

type layout = {
  packages : (string * Manifest.package) list;
  files : source_file list;
  problems : string list;
  time_limit_ms : int;
}

let files database root = Option.value (Query.find database tree root) ~default:[]

let manifest_problem problems directory format =
  Printf.ksprintf
    (fun message ->
      problems := Printf.sprintf "%s: %s" (manifest_file directory) message :: !problems)
    format

let layout =
  Query.query ~name:"project_layout" ~phase:Phases.project ~saved:true ~show:Fun.id
    (fun database root ->
      let files = files database root in
      let problems = ref [] in
      let problem directory = manifest_problem problems directory in
      let manifests =
        List.filter_map
          (fun path ->
            if Filename.basename path <> "truss.toml" then None
            else
              Option.map (fun text -> (parent path, text)) (Query.find database text (root, path)))
          files
      in
      let directories = Hashtbl.create 8 in
      List.iter (fun (directory, text) -> Hashtbl.replace directories directory text) manifests;
      let is_project directory =
        match Hashtbl.find_opt directories directory with
        | Some text -> Manifest.has_project_table text
        | None -> false
      in
      let root_is_project = is_project "" in
      let rec in_another_project directory =
        directory <> ""
        && ((Hashtbl.mem directories directory && ((not root_is_project) || is_project directory))
           || in_another_project (parent directory))
      in
      let parsed =
        List.filter_map
          (fun (directory, text) ->
            if in_another_project directory then None
            else
              match Manifest.parse text with
              | manifest -> Some (directory, manifest)
              | exception Manifest.Malformed { line; message } ->
                  problems :=
                    Printf.sprintf "%s:%d: %s" (manifest_file directory) line message :: !problems;
                  None)
          manifests
      in
      let time_limit_seconds =
        List.fold_left
          (fun limit (directory, (manifest : Manifest.t)) ->
            match manifest.time_limit_seconds with
            | Some seconds when directory = "" -> seconds
            | Some _ ->
                problem directory
                  "A test's time limit is its project's. Write `[test]` in the project's manifest, \
                   `truss.toml` at its root.";
                limit
            | None -> limit)
          Manifest.default_time_limit_seconds parsed
      in
      let seen = Hashtbl.create 8 in
      let packages =
        List.filter_map
          (fun (directory, (manifest : Manifest.t)) ->
            match manifest.package with
            | None -> None
            | Some package when root = project_root && package.name = Path.standard_package ->
                problem directory "The package name `standard` is the standard library's.";
                None
            | Some package -> (
                match Hashtbl.find_opt seen package.name with
                | Some other ->
                    problem directory "The package name `%s` is already used by %s."
                      (Path.show_package package.name) (manifest_file other);
                    None
                | None ->
                    Hashtbl.replace seen package.name directory;
                    Some (directory, package)))
          parsed
      in
      let files =
        List.filter_map
          (fun path ->
            if not (Filename.check_suffix path ".truss") then None
            else
              Option.bind
                (package_directory ~is_package:(Hashtbl.mem directories) (parent path))
                (fun directory ->
                  Option.map
                    (fun (package : Manifest.package) ->
                      { path; directory; file = file_of_path ~package:package.name ~directory path })
                    (List.assoc_opt directory packages)))
          files
      in
      { packages; files; problems = List.rev !problems; time_limit_ms = time_limit_seconds * 1000 })

type selection = {
  selected : Registry.Selection.package list;
  missing : (Path.package * Registry.Version.t * string) list;
  failed : string list;
  lock_problems : string list;
  lock_fix : string option;
}

let project_packages database = List.map snd (Query.demand database layout project_root).packages

let selection =
  Query.query ~name:"project_selection" ~phase:Phases.project ~saved:true
    ~show:(fun () -> "")
    (fun database () ->
      let packages = project_packages database in
      let named name =
        List.exists (fun (package : Manifest.package) -> package.name = name) packages
      in
      let problems = ref [] in
      let lock_problem format =
        Printf.ksprintf (fun message -> problems := ("truss.lock: " ^ message) :: !problems) format
      in
      let written_text = Query.find database text (project_root, lock_file) in
      let written =
        match Registry.Lock.parse (Option.value ~default:"" written_text) with
        | entries -> Some entries
        | exception Registry.Lock.Malformed { line; message } ->
            problems := Printf.sprintf "truss.lock:%d: %s" line message :: !problems;
            None
      in
      let missing = ref [] and failed = ref [] in
      let load name version ~hash =
        let root = registry_root hash in
        match Query.find database tree root with
        | None -> (
            match Query.find database unavailable hash with
            | Some reason ->
                failed := hash :: !failed;
                Error reason
            | None ->
                missing := (name, version, hash) :: !missing;
                Error "its files are not fetched yet")
        | Some _ ->
            Registry.Selection.manifest_and_record
              ~read:(fun file -> Query.find database text (root, file))
              name
      in
      let selected, selection_problems =
        Registry.Selection.choose
          ~lock:(Option.value ~default:[] written)
          ~roots:
            (List.concat_map
               (fun (package : Manifest.package) ->
                 List.filter_map
                   (fun (dependency : Manifest.dependency) ->
                     match dependency.package.owner with
                     | Some _ -> Some (package.name, dependency.package)
                     | None -> None)
                   package.dependencies)
               packages)
          ~local:named ~load
      in
      let missing = List.sort_uniq compare !missing in
      let is_build_fetched = missing = [] in
      let lock_fix = ref None in
      if is_build_fetched then begin
        List.iter
          (fun problem -> lock_problem "%s" (Registry.Selection.sentence problem))
          selection_problems;
        List.iter
          (fun (selected : Registry.Selection.package) ->
            match selected.manifest.truss with
            | Some version when not (Manifest.toolchain_builds version) ->
                lock_problem "`%s` %s is written for Truss %s, and this toolchain is Truss %s."
                  (Path.show_package selected.name)
                  (Registry.Version.show selected.version)
                  version Manifest.truss_version
            | _ -> ())
          selected;
        match written with
        | Some written when selection_problems = [] ->
            let current =
              Registry.Selection.lock
                ~project:
                  (List.concat_map
                     (fun (package : Manifest.package) -> package.dependencies)
                     packages)
                selected
            in
            let text = Registry.Lock.print current in
            if current = [] && written_text = None then ()
            else if written_text <> Some text then begin
              lock_fix := Some text;
              lock_problem
                "This is not the lock file the manifests give. %sRun `truss check --fix`."
                (String.concat ""
                   (List.map
                      (fun difference -> difference ^ " ")
                      (Registry.Selection.differences ~written ~current)))
            end
        | _ -> ()
      end;
      {
        selected;
        missing;
        failed = List.sort_uniq compare !failed;
        lock_problems = List.rev !problems;
        lock_fix = !lock_fix;
      })

type place = { root : string; directory : string; manifest : Manifest.package }

let places =
  Query.query ~name:"project_places" ~phase:Phases.project ~saved:true
    ~show:(fun () -> "")
    (fun database () ->
      let by_name = Hashtbl.create 16 in
      let add root =
        List.iter
          (fun (directory, (manifest : Manifest.package)) ->
            if not (Hashtbl.mem by_name manifest.name) then
              Hashtbl.replace by_name manifest.name { root; directory; manifest })
          (Query.demand database layout root).packages
      in
      let known_roots = Option.value (Query.find database roots ()) ~default:[] in
      if List.mem project_root known_roots then add project_root;
      List.iter (fun root -> if root <> project_root then add root) known_roots;
      if List.mem project_root known_roots then
        List.iter
          (fun (package : Registry.Selection.package) -> add (registry_root package.hash))
          (Query.demand database selection ()).selected;
      List.sort
        (fun (left, _) (right, _) -> Path.compare_package left right)
        (Hashtbl.fold (fun name place packages -> (name, place) :: packages) by_name []))

let place =
  Query.query ~name:"project_place" ~phase:Phases.project ~saved:true ~show:Path.show_package
    (fun database name ->
      if name = Path.standard_package then
        List.find_map
          (fun (directory, (manifest : Manifest.package)) ->
            if manifest.name = name then Some { root = standard_root; directory; manifest }
            else None)
          (Query.demand database layout standard_root).packages
      else List.assoc_opt name (Query.demand database places ()))

let package =
  Query.query ~name:"project_package" ~phase:Phases.project ~saved:true ~show:Path.show_package
    (fun database name ->
      Option.map
        (fun { root; directory; manifest } ->
          let files =
            List.filter_map
              (fun (source : source_file) ->
                if source.directory = directory then Some source.file else None)
              (Query.demand database layout root).files
          in
          {
            name;
            dependencies = manifest.dependencies;
            modules =
              List.sort_uniq compare (List.map (fun (file : Path.file) -> file.module_) files);
            files;
          })
        (Query.demand database place name))

let file_place =
  Query.query ~name:"project_file_place" ~phase:Phases.project ~show:Path.show_file
    (fun database (file : Path.file) ->
      Option.bind (Query.demand database place file.module_.package) (fun { root; directory; _ } ->
          let path = file_path ~directory file in
          if
            List.exists
              (fun (source : source_file) -> source.path = path)
              (Query.demand database layout root).files
          then Some (root, path)
          else None))

let file_text =
  Query.query ~name:"project_file_text" ~phase:Phases.project ~show:Path.show_file
    (fun database file ->
      Option.bind (Query.demand database file_place file) (Query.find database text))

let dependency_cycle (packages : (string * Manifest.package) list) =
  let dependencies name =
    match List.find_opt (fun (_, (package : Manifest.package)) -> package.name = name) packages with
    | Some (_, package) ->
        List.map (fun (dependency : Manifest.dependency) -> dependency.package) package.dependencies
    | None -> []
  in
  let visited = Hashtbl.create 8 in
  let rec reaches target name =
    if Hashtbl.mem visited name then None
    else begin
      Hashtbl.replace visited name ();
      List.find_map
        (fun next ->
          if next = target then Some [ name; target ]
          else Option.map (fun rest -> name :: rest) (reaches target next))
        (dependencies name)
    end
  in
  List.find_map
    (fun (directory, (package : Manifest.package)) ->
      Hashtbl.reset visited;
      Option.map (fun cycle -> (directory, cycle)) (reaches package.name package.name))
    packages

let problems =
  Query.query ~name:"project_problems" ~phase:Phases.project ~saved:true
    ~show:(fun () -> "")
    (fun database () ->
      let own = Query.demand database layout project_root in
      let chosen = Query.demand database selection () in
      let packages = own.packages in
      let problems = ref [] in
      let problem directory = manifest_problem problems directory in
      let named name =
        List.find_opt (fun (_, (package : Manifest.package)) -> package.name = name) packages
      in
      List.iter
        (fun (directory, (package : Manifest.package)) ->
          (match package.truss with
          | None ->
              problem directory
                "`[package]` needs `truss = \"%s\"`, the version of Truss the package is written \
                 for."
                Manifest.truss_version
          | Some version when not (Manifest.toolchain_builds version) ->
              problem directory "`%s` is written for Truss %s, and this toolchain is Truss %s."
                (Path.show_package package.name) version Manifest.truss_version
          | Some _ -> ());
          (match package.name with
          | { owner = None; name } ->
              List.iter
                (fun (other : Path.package) ->
                  if other.owner = Some name then
                    problem directory
                      "The package name `%s` is the owner in `%s`, so a path that starts with it \
                       could be read two ways. Give one of them another name."
                      name (Path.show_package other))
                (List.sort_uniq Path.compare_package
                   (List.map (fun (_, (package : Manifest.package)) -> package.name) packages
                   @ List.concat_map
                       (fun (_, (package : Manifest.package)) ->
                         List.map
                           (fun (dependency : Manifest.dependency) -> dependency.package)
                           package.dependencies)
                       packages))
          | { owner = Some _; _ } -> ());
          List.iter
            (fun (dependency : Manifest.dependency) ->
              if dependency.package = package.name then
                problem directory "`%s` cannot depend on itself." (Path.show_package package.name)
              else if dependency.package.owner = None && named dependency.package = None then
                problem directory "`%s` is not a package of this project."
                  (Path.show_package dependency.package))
            package.dependencies)
        packages;
      (match dependency_cycle packages with
      | Some (directory, cycle) ->
          problem directory "Packages cannot depend on each other in a cycle: %s."
            (String.concat " -> "
               (List.map (fun package -> Printf.sprintf "`%s`" (Path.show_package package)) cycle))
      | None -> ());
      own.problems @ chosen.lock_problems @ List.rev !problems)

let registry =
  Query.query ~name:"project_registry" ~phase:Phases.project ~saved:true
    ~show:(fun () -> "")
    (fun database () ->
      List.map
        (fun (selected : Registry.Selection.package) ->
          (selected.name, selected.version, selected.hash))
        (Query.demand database selection ()).selected)
