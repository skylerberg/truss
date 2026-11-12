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
let package_root name = "package " ^ name
let lock_file = "truss.lock"
let manifest_file directory = if directory = "" then "truss.toml" else directory ^ "/truss.toml"

(* Paths *)

let parent path = match String.rindex_opt path '/' with Some i -> String.sub path 0 i | None -> ""
let segments path = if path = "" then [] else String.split_on_char '/' path

(* A module file's path under its package's directory, as module names. *)
let module_names ~directory path =
  let inside =
    if directory = "" then path
    else
      String.sub path
        (String.length directory + 1)
        (String.length path - String.length directory - 1)
  in
  segments (Filename.chop_suffix inside ".truss")

let module_path ~directory (module_ : Path.module_) =
  let file = String.concat "/" module_.modules ^ ".truss" in
  if directory = "" then file else directory ^ "/" ^ file

type package = {
  name : string;
  dependencies : Manifest.dependency list;
  modules : Path.module_ list;
  usize_bits : int;
}

type layout = {
  packages : (string * Manifest.package) list;
  modules : (string * string * Path.module_) list;
  problems : string list;
  time_limit : int;
}

let files database root = Option.value (Query.find database tree root) ~default:[]

let layout =
  Query.query ~name:"project_layout" ~phase:Phases.project ~saved:true ~show:Fun.id
    (fun database root ->
      let files = files database root in
      let problems = ref [] in
      let problem directory format =
        Printf.ksprintf
          (fun message ->
            problems := Printf.sprintf "%s: %s" (manifest_file directory) message :: !problems)
          format
      in
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
              | exception Manifest.Malformed (line, message) ->
                  problems :=
                    Printf.sprintf "%s:%d: %s" (manifest_file directory) line message :: !problems;
                  None)
          manifests
      in
      let time_limit =
        List.fold_left
          (fun limit (directory, (manifest : Manifest.t)) ->
            match manifest.time_limit with
            | Some seconds when directory = "" -> seconds
            | Some _ ->
                problem directory
                  "A test's time limit is its project's. Write `[test]` in the project's manifest, \
                   `truss.toml` at its root.";
                limit
            | None -> limit)
          Manifest.default_time_limit parsed
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
                    problem directory "The package name `%s` is already used by %s." package.name
                      (manifest_file other);
                    None
                | None ->
                    Hashtbl.replace seen package.name directory;
                    Some (directory, package)))
          parsed
      in
      (* A module file belongs to the nearest directory above it with a
         manifest, if that manifest has a package. *)
      let rec owner directory =
        if Hashtbl.mem directories directory then Some directory
        else if directory = "" then None
        else owner (parent directory)
      in
      let modules =
        List.filter_map
          (fun path ->
            if not (Filename.check_suffix path ".truss") then None
            else
              Option.bind
                (owner (parent path))
                (fun directory ->
                  Option.map
                    (fun (package : Manifest.package) ->
                      ( path,
                        directory,
                        ({ package = package.name; modules = module_names ~directory path }
                          : Path.module_) ))
                    (List.assoc_opt directory packages)))
          files
      in
      { packages; modules; problems = List.rev !problems; time_limit })

type selection = {
  selected : Registry.Selection.package list;
  missing : (string * Registry.Version.t * string) list;
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
        | exception Registry.Lock.Malformed (line, message) ->
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
        | Some _ -> (
            let read file = Query.find database text (root, file) in
            match
              ( Option.map Manifest.parse (read "truss.toml"),
                Registry.Lock.parse (Option.value ~default:"" (read lock_file)) )
            with
            | exception Manifest.Malformed (line, message) ->
                Error (Printf.sprintf "its manifest cannot be read: line %d: %s" line message)
            | exception Registry.Lock.Malformed (line, message) ->
                Error (Printf.sprintf "its lock file cannot be read: line %d: %s" line message)
            | Some { package = Some manifest; _ }, record when manifest.name = name ->
                Ok (manifest, record)
            | _ -> Error (Printf.sprintf "its manifest does not name the package `%s`" name))
      in
      let selected, selection_problems =
        Registry.Selection.choose
          ~lock:(Option.value ~default:[] written)
          ~roots:
            (List.concat_map
               (fun (package : Manifest.package) ->
                 List.filter_map
                   (fun (dependency : Manifest.dependency) ->
                     match Path.package_parts dependency.package with
                     | [ _; _ ] -> Some (package.name, dependency.package)
                     | _ -> None)
                   package.dependencies)
               packages)
          ~local:named ~load
      in
      let missing = List.sort_uniq compare !missing in
      (* While a package is still to be fetched, what is wrong with the
         build is not known yet. *)
      let lock_fix = ref None in
      if missing = [] then begin
        List.iter
          (fun found -> lock_problem "%s" (Registry.Selection.sentence found))
          selection_problems;
        List.iter
          (fun (found : Registry.Selection.package) ->
            match found.manifest.truss with
            | Some version when not (Manifest.toolchain_builds version) ->
                lock_problem "`%s` %s is written for Truss %s, and this toolchain is Truss %s."
                  found.name
                  (Registry.Version.show found.version)
                  version Manifest.truss_version
            | _ -> ())
          selected;
        (* The lock file is written one way: what the manifests and the
           versions in it give. Another is a problem whose fix is to write
           that one. *)
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

(* Where each package of the build is, by name. *)
let build =
  Query.query ~name:"project_build" ~phase:Phases.project ~saved:true
    ~show:(fun () -> "")
    (fun database () ->
      let found = Hashtbl.create 16 in
      let add root =
        List.iter
          (fun (directory, (manifest : Manifest.package)) ->
            if not (Hashtbl.mem found manifest.name) then
              Hashtbl.replace found manifest.name { root; directory; manifest })
          (Query.demand database layout root).packages
      in
      let given = Option.value (Query.find database roots ()) ~default:[] in
      if List.mem project_root given then add project_root;
      List.iter (fun root -> if root <> project_root then add root) given;
      if List.mem project_root given then
        List.iter
          (fun (package : Registry.Selection.package) -> add (registry_root package.hash))
          (Query.demand database selection ()).selected;
      List.sort compare (Hashtbl.fold (fun name place found -> (name, place) :: found) found []))

let place =
  Query.query ~name:"project_place" ~phase:Phases.project ~saved:true ~show:Fun.id
    (fun database name -> List.assoc_opt name (Query.demand database build ()))

let package =
  Query.query ~name:"project_package" ~phase:Phases.project ~saved:true ~show:Fun.id
    (fun database name ->
      Option.map
        (fun { root; directory; manifest } ->
          {
            name;
            dependencies = manifest.dependencies;
            modules =
              List.filter_map
                (fun (_, owner, module_) -> if owner = directory then Some module_ else None)
                (Query.demand database layout root).modules;
            usize_bits = manifest.usize_bits;
          })
        (Query.demand database place name))

(* A module's root and its file's path in it. *)
let module_place =
  Query.query ~name:"project_module_place" ~phase:Phases.project ~show:Path.show_module
    (fun database (module_ : Path.module_) ->
      Option.bind (Query.demand database place module_.package) (fun { root; directory; _ } ->
          let path = module_path ~directory module_ in
          if
            List.exists
              (fun (file, _, _) -> file = path)
              (Query.demand database layout root).modules
          then Some (root, path)
          else None))

let module_text =
  Query.query ~name:"project_module_text" ~phase:Phases.project ~show:Path.show_module
    (fun database module_ ->
      Option.bind (Query.demand database module_place module_) (Query.find database text))

(* A package that is in a cycle of packages that depend on each other, with
   the cycle. *)
let dependency_cycle (packages : (string * Manifest.package) list) =
  let dependencies name =
    match List.find_opt (fun (_, (p : Manifest.package)) -> p.name = name) packages with
    | Some (_, package) ->
        List.map (fun (dependency : Manifest.dependency) -> dependency.package) package.dependencies
    | None -> []
  in
  (* A package that reaches no cycle is not walked again. *)
  let clear = Hashtbl.create 8 in
  let rec reaches target path name =
    if List.mem name path || Hashtbl.mem clear name then None
    else
      let found =
        List.find_map
          (fun next ->
            if next = target then Some [ name; target ]
            else Option.map (fun way -> name :: way) (reaches target (name :: path) next))
          (dependencies name)
      in
      if found = None then Hashtbl.replace clear name ();
      found
  in
  List.find_map
    (fun (directory, (package : Manifest.package)) ->
      Hashtbl.reset clear;
      Option.map (fun way -> (directory, way)) (reaches package.name [] package.name))
    packages

let problems =
  Query.query ~name:"project_problems" ~phase:Phases.project ~saved:true
    ~show:(fun () -> "")
    (fun database () ->
      let own = Query.demand database layout project_root in
      let chosen = Query.demand database selection () in
      let packages = own.packages in
      let problems = ref [] in
      let problem directory format =
        Printf.ksprintf
          (fun message ->
            problems := Printf.sprintf "%s: %s" (manifest_file directory) message :: !problems)
          format
      in
      let named name = List.find_opt (fun (_, (p : Manifest.package)) -> p.name = name) packages in
      let selected_named name =
        List.find_opt
          (fun (found : Registry.Selection.package) -> found.name = name)
          chosen.selected
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
                package.name version Manifest.truss_version
          | Some _ -> ());
          (* Every path must read one way: [acme::geometry::vector] cannot be
             both a module of [acme::geometry] and one of a package [acme]. *)
          (match Path.package_parts package.name with
          | [ name ] ->
              List.iter
                (fun other ->
                  match Path.package_parts other with
                  | [ owner; _ ] when owner = name ->
                      problem directory
                        "The package name `%s` is the owner in `%s`, so a path that starts with it \
                         could be read two ways. Give one of them another name."
                        name other
                  | _ -> ())
                (List.sort_uniq compare
                   (List.map (fun (_, (p : Manifest.package)) -> p.name) packages
                   @ List.concat_map
                       (fun (_, (p : Manifest.package)) ->
                         List.map (fun (d : Manifest.dependency) -> d.package) p.dependencies)
                       packages))
          | _ -> ());
          List.iter
            (fun (dependency : Manifest.dependency) ->
              if dependency.package = package.name then
                problem directory "`%s` cannot depend on itself." package.name
              else
                let found =
                  match (named dependency.package, selected_named dependency.package) with
                  | Some (_, other), _ -> Some other
                  | None, Some other -> Some other.manifest
                  | None, None ->
                      (* A dependency the registry would have, with no version
                         known, is reported with the lock file. *)
                      if List.length (Path.package_parts dependency.package) = 1 then
                        problem directory "`%s` is not a package of this project."
                          dependency.package;
                      None
                in
                match found with
                | Some other when package.usize_bits = 32 && other.usize_bits = 64 ->
                    (* A package that claims to run on every target cannot
                       rely on one that runs only on 64-bit targets. *)
                    problem directory
                      "`%s` runs only on 64-bit targets, so `%s` must say `usize_bits = 64` to \
                       depend on it."
                      other.name package.name
                | _ -> ())
            package.dependencies)
        packages;
      (match dependency_cycle packages with
      | Some (directory, way) ->
          problem directory "Packages cannot depend on each other in a cycle: %s."
            (String.concat " -> " (List.map (Printf.sprintf "`%s`") way))
      | None -> ());
      own.problems @ chosen.lock_problems @ List.rev !problems)

let registry =
  Query.query ~name:"project_registry" ~phase:Phases.project ~saved:true
    ~show:(fun () -> "")
    (fun database () ->
      List.map
        (fun (found : Registry.Selection.package) -> (found.name, found.version, found.hash))
        (Query.demand database selection ()).selected)
