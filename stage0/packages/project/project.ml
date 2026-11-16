type root = Project | Registry of string

module Root_table = Hashtbl.Make (Structural_key.Make (struct
  type t = root
end))

module Package_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.package
end))

type files = {
  tree : root -> string list option;
  text : root -> string -> string option;
  unavailable : string -> string option;
}

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
  files : (Path.file * string) list;
}

type source_file = { path : string; directory : string; file : Path.file }
type problem = { file : string; line : int option; message : string }

let show_problem { file; line; message } =
  match line with
  | Some line -> Printf.sprintf "%s:%d: %s" file line message
  | None -> Printf.sprintf "%s: %s" file message

type layout = {
  packages : (string * Manifest.package) list;
  files : source_file list;
  problems : problem list;
  time_limit_ms : int;
}

let files_of (files : files) root = Option.value (files.tree root) ~default:[]

let manifest_problem problems directory format =
  Printf.ksprintf
    (fun message ->
      problems := { file = manifest_file directory; line = None; message } :: !problems)
    format

let layout (files_in : files) root =
  let files = files_of files_in root in
  let problems = ref [] in
  let problem directory = manifest_problem problems directory in
  let manifests =
    List.filter_map
      (fun path ->
        if Filename.basename path <> "truss.toml" then None
        else Option.map (fun text -> (parent path, text)) (files_in.text root path))
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
              problems := { file = manifest_file directory; line = Some line; message } :: !problems;
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
  let seen = Package_table.create 8 in
  let packages =
    List.filter_map
      (fun (directory, (manifest : Manifest.t)) ->
        match manifest.package with
        | None -> None
        | Some package when root = Project && package.name = Path.standard_package ->
            problem directory "The package name `standard` is the standard library's.";
            None
        | Some package -> (
            match Package_table.find_opt seen package.name with
            | Some other ->
                problem directory "The package name `%s` is already used by %s."
                  (Path.show_package package.name) (manifest_file other);
                None
            | None ->
                Package_table.replace seen package.name directory;
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
  { packages; files; problems = List.rev !problems; time_limit_ms = time_limit_seconds * 1000 }

type selection = {
  selected : Registry.Selection.package list;
  missing : (Path.package * Registry.Version.t * string) list;
  failed : string list;
  lock_problems : problem list;
  lock_fix : string option;
}

let selection (files : files) (own : layout) =
  let packages = List.map snd own.packages in
  let named name = List.exists (fun (package : Manifest.package) -> package.name = name) packages in
  let problems = ref [] in
  let lock_problem format =
    Printf.ksprintf
      (fun message -> problems := { file = lock_file; line = None; message } :: !problems)
      format
  in
  let written_text = files.text Project lock_file in
  let written =
    match Registry.Lock.parse (Option.value ~default:"" written_text) with
    | entries -> Some entries
    | exception Registry.Lock.Malformed { line; message } ->
        problems := { file = lock_file; line = Some line; message } :: !problems;
        None
  in
  let missing = ref [] and failed = ref [] in
  let load name version ~hash =
    let root = Registry hash in
    match files.tree root with
    | None -> (
        match files.unavailable hash with
        | Some reason ->
            failed := hash :: !failed;
            Error reason
        | None ->
            missing := (name, version, hash) :: !missing;
            Error "its files are not fetched yet")
    | Some _ -> Registry.Selection.manifest_and_record ~read:(files.text root) name
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
              (List.concat_map (fun (package : Manifest.package) -> package.dependencies) packages)
            selected
        in
        let text = Registry.Lock.print current in
        if current = [] && written_text = None then ()
        else if written_text <> Some text then begin
          lock_fix := Some text;
          lock_problem "This is not the lock file the manifests give. %sRun `truss check --fix`."
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
  }

type place = { root : root; directory : string; manifest : Manifest.package }

let places ~layout ~(selection : selection) =
  let by_name = Package_table.create 16 in
  let add root =
    List.iter
      (fun (directory, (manifest : Manifest.package)) ->
        if not (Package_table.mem by_name manifest.name) then
          Package_table.replace by_name manifest.name { root; directory; manifest })
      (layout root).packages
  in
  add Project;
  List.iter
    (fun (package : Registry.Selection.package) -> add (Registry package.hash))
    selection.selected;
  List.sort
    (fun (left, _) (right, _) -> Path.compare_package left right)
    (Package_table.fold (fun name place packages -> (name, place) :: packages) by_name [])

let package (files : files) ~(layout : root -> layout) { root; directory; manifest } =
  {
    name = manifest.name;
    dependencies = manifest.dependencies;
    files =
      List.filter_map
        (fun (source : source_file) ->
          if source.directory = directory then
            Option.map (fun text -> (source.file, text)) (files.text root source.path)
          else None)
        (layout root).files;
  }

let dependency_cycle (places : (Path.package * place) list) =
  let dependencies name =
    match List.assoc_opt name places with
    | Some place ->
        List.map
          (fun (dependency : Manifest.dependency) -> dependency.package)
          place.manifest.dependencies
    | None -> []
  in
  let visited = Package_table.create 8 in
  let rec reaches target name =
    if Package_table.mem visited name then None
    else begin
      Package_table.replace visited name ();
      List.find_map
        (fun next ->
          if next = target then Some [ name; target ]
          else Option.map (fun rest -> name :: rest) (reaches target next))
        (dependencies name)
    end
  in
  let own, registry = List.partition (fun (_, place) -> place.root = Project) places in
  List.find_map
    (fun (name, place) ->
      Package_table.reset visited;
      Option.map (fun cycle -> (place, cycle)) (reaches name name))
    (own @ registry)

let cycle_problem ((place : place), cycle) =
  {
    file =
      (match place.root with Project -> manifest_file place.directory | Registry _ -> lock_file);
    line = None;
    message =
      (match cycle with
      | [ package; _ ] -> Printf.sprintf "`%s` cannot depend on itself." (Path.show_package package)
      | cycle ->
          Printf.sprintf "Packages cannot depend on each other in a cycle: %s."
            (String.concat " -> "
               (List.map (fun package -> Printf.sprintf "`%s`" (Path.show_package package)) cycle)));
  }

let problems (own : layout) (chosen : selection) =
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
            "`[package]` needs `truss = \"%s\"`, the version of Truss the package is written for."
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
                  "The package name `%s` is the owner in `%s`, so a path that starts with it could \
                   be read two ways. Give one of them another name."
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
          if dependency.package.owner = None && named dependency.package = None then
            problem directory "`%s` is not a package of this project."
              (Path.show_package dependency.package))
        package.dependencies)
    packages;
  own.problems @ chosen.lock_problems @ List.rev !problems

type t = {
  own : layout;
  selection : selection;
  places : (Path.package * place) list;
  packages : package list;
  problems : problem list;
}

let of_files files =
  let layouts = Root_table.create 4 in
  let layout root =
    match Root_table.find_opt layouts root with
    | Some layout -> layout
    | None ->
        let computed = layout files root in
        Root_table.replace layouts root computed;
        computed
  in
  let own = layout Project in
  let selection = selection files own in
  let places = places ~layout ~selection in
  let cycle = Option.map cycle_problem (dependency_cycle places) in
  let places = if Option.is_some cycle then [] else places in
  {
    own;
    selection;
    places;
    packages = List.map (fun (_, place) -> package files ~layout place) places;
    problems = problems own selection @ Option.to_list cycle;
  }
