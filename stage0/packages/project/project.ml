type root = Project | Registry of string

module Root_table = Hashtbl.Make (Structural_key.Make (struct
  type t = root
end))

module Package_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.package
end))

type files = {
  find_tree : root -> string list option;
  find_text : root -> string -> string option;
  find_unavailable_reason : string -> string option;
}

let lock_file = "truss.lock"
let raise_bug format = Compiler_bug.raise_bug ~stage:"Project" format
let make_manifest_path directory = File_system.join_path directory "truss.toml"

let read_parent path =
  match File_system.find_parent path with
  | Some parent -> parent
  | None -> raise_bug "the file %S has no parent directory" path

let rec find_package_directory ~is_package directory =
  if is_package directory then Some directory
  else Option.bind (File_system.find_parent directory) (find_package_directory ~is_package)

let make_file ~package ~directory path : Path.file =
  match File_system.find_relative_path ~root:directory path with
  | Some inside ->
      let modules =
        match read_parent inside with "" -> [] | parent -> String.split_on_char '/' parent
      in
      {
        module_ = { package; modules };
        name = Filename.chop_suffix (Filename.basename inside) ".truss";
      }
  | None -> raise_bug "%s is not in its package's directory %s" path directory

let make_file_path ~directory (file : Path.file) =
  File_system.join_path directory (String.concat "/" (Path.list_file_names file))

type package = {
  name : Path.package;
  dependencies : Manifest.dependency list;
  files : (Path.file * string) list;
}

type source_file = { path : string; directory : string; file : Path.file }
type problem = { file : string; line : int option; problem : Project_catalog.Problem.t }

let show_problem { file; line; problem } =
  let message = Project_catalog.describe problem in
  match line with
  | Some line -> Printf.sprintf "%s:%d: %s" file line message
  | None -> Printf.sprintf "%s: %s" file message

type layout = {
  packages : (string * Manifest.package) list;
  files : source_file list;
  problems : problem list;
  time_limit_ms : int;
}

let list_files (files : files) root = Option.value (files.find_tree root) ~default:[]

let report_manifest_problem problems directory problem =
  problems := { file = make_manifest_path directory; line = None; problem } :: !problems

let lay_out (files_in : files) root =
  let files = list_files files_in root in
  let problems = ref [] in
  let report_problem directory = report_manifest_problem problems directory in
  let manifests =
    List.filter_map
      (fun path ->
        if Filename.basename path <> "truss.toml" then None
        else Option.map (fun text -> (read_parent path, text)) (files_in.find_text root path))
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
  let rec is_in_another_project directory =
    match File_system.find_parent directory with
    | None -> false
    | Some parent ->
        (Hashtbl.mem directories directory && ((not root_is_project) || is_project directory))
        || is_in_another_project parent
  in
  let parsed =
    List.filter_map
      (fun (directory, text) ->
        if is_in_another_project directory then None
        else
          match Manifest.parse text with
          | manifest -> Some (directory, manifest)
          | exception Manifest.Malformed { line; problem } ->
              problems :=
                {
                  file = make_manifest_path directory;
                  line = Some line;
                  problem = Manifest problem;
                }
                :: !problems;
              None)
      manifests
  in
  let time_limit_seconds =
    List.fold_left
      (fun limit (directory, (manifest : Manifest.t)) ->
        match manifest.time_limit_seconds with
        | Some seconds when directory = "" -> seconds
        | Some _ ->
            report_problem directory Nested_time_limit;
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
            report_problem directory Standard_name;
            None
        | Some package -> (
            match Package_table.find_opt seen package.name with
            | Some other ->
                report_problem directory
                  (Name_in_use { name = package.name; manifest = make_manifest_path other });
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
            (find_package_directory ~is_package:(Hashtbl.mem directories) (read_parent path))
            (fun directory ->
              Option.map
                (fun (package : Manifest.package) ->
                  { path; directory; file = make_file ~package:package.name ~directory path })
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

let select_packages (files : files) (project_layout : layout) =
  let packages = List.map snd project_layout.packages in
  let is_named name =
    List.exists (fun (package : Manifest.package) -> package.name = name) packages
  in
  let problems = ref [] in
  let lock_problem problem = problems := { file = lock_file; line = None; problem } :: !problems in
  let written_text = files.find_text Project lock_file in
  let written =
    match Registry.Lock.parse (Option.value ~default:"" written_text) with
    | entries -> Some entries
    | exception Registry.Lock.Malformed { line; problem } ->
        problems := { file = lock_file; line = Some line; problem = Lock problem } :: !problems;
        None
  in
  let missing = ref [] and failed = ref [] in
  let load name version ~hash =
    let root = Registry hash in
    match files.find_tree root with
    | None -> (
        match files.find_unavailable_reason hash with
        | Some reason ->
            failed := hash :: !failed;
            Error (Project_catalog.Problem.Unavailable reason)
        | None ->
            missing := (name, version, hash) :: !missing;
            Error Project_catalog.Problem.Unfetched)
    | Some _ -> Registry.Selection.read_manifest_and_record ~read:(files.find_text root) name
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
      ~is_local:is_named ~load
  in
  let missing = List.sort_uniq compare !missing in
  let is_build_fetched = missing = [] in
  let lock_fix = ref None in
  if is_build_fetched then begin
    List.iter (fun problem -> lock_problem (Selection problem)) selection_problems;
    List.iter
      (fun (selected : Registry.Selection.package) ->
        match selected.manifest.truss with
        | Some version when not (Manifest.toolchain_builds version) ->
            lock_problem
              (Registry_toolchain
                 {
                   name = selected.name;
                   version = selected.version;
                   truss = version;
                   toolchain = Manifest.truss_version;
                 })
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
          lock_problem (Stale_lock (Registry.Selection.list_differences ~written ~current))
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

let place_packages ~lay_out_root ~(selection : selection) =
  let by_name = Package_table.create 16 in
  let add root =
    List.iter
      (fun (directory, (manifest : Manifest.package)) ->
        if not (Package_table.mem by_name manifest.name) then
          Package_table.replace by_name manifest.name { root; directory; manifest })
      (lay_out_root root).packages
  in
  add Project;
  List.iter
    (fun (package : Registry.Selection.package) -> add (Registry package.hash))
    selection.selected;
  List.sort
    (fun (left, _) (right, _) -> Path.compare_package left right)
    (Package_table.fold (fun name place packages -> (name, place) :: packages) by_name [])

let make_package (files : files) ~(lay_out_root : root -> layout) { root; directory; manifest } =
  {
    name = manifest.name;
    dependencies = manifest.dependencies;
    files =
      List.filter_map
        (fun (source : source_file) ->
          if source.directory = directory then
            Option.map (fun text -> (source.file, text)) (files.find_text root source.path)
          else None)
        (lay_out_root root).files;
  }

let find_dependency_cycle (places : (Path.package * place) list) =
  let list_dependencies name =
    match List.assoc_opt name places with
    | Some place ->
        List.map
          (fun (dependency : Manifest.dependency) -> dependency.package)
          place.manifest.dependencies
    | None -> []
  in
  let visited = Package_table.create 8 in
  let rec find_reach_path target name =
    if Package_table.mem visited name then None
    else begin
      Package_table.replace visited name ();
      List.find_map
        (fun next ->
          if next = target then Some [ name; target ]
          else Option.map (fun rest -> name :: rest) (find_reach_path target next))
        (list_dependencies name)
    end
  in
  let project_places, registry = List.partition (fun (_, place) -> place.root = Project) places in
  List.find_map
    (fun (name, place) ->
      Package_table.reset visited;
      Option.map (fun cycle -> (place, cycle)) (find_reach_path name name))
    (project_places @ registry)

let make_cycle_problem ((place : place), cycle) =
  {
    file =
      (match place.root with
      | Project -> make_manifest_path place.directory
      | Registry _ -> lock_file);
    line = None;
    problem =
      (match cycle with
      | [ package; _ ] -> Self_dependency package
      | cycle -> Dependency_cycle cycle);
  }

let list_problems (project_layout : layout) (chosen : selection) =
  let packages = project_layout.packages in
  let problems = ref [] in
  let report_problem directory = report_manifest_problem problems directory in
  let find_named name =
    List.find_opt (fun (_, (package : Manifest.package)) -> package.name = name) packages
  in
  List.iter
    (fun (directory, (package : Manifest.package)) ->
      (match package.truss with
      | None ->
          report_problem directory (Missing_truss_version { toolchain = Manifest.truss_version })
      | Some version when not (Manifest.toolchain_builds version) ->
          report_problem directory
            (Project_toolchain
               { name = package.name; truss = version; toolchain = Manifest.truss_version })
      | Some _ -> ());
      (match package.name with
      | { owner = None; name } ->
          List.iter
            (fun (other : Path.package) ->
              if other.owner = Some name then
                report_problem directory (Owner_named_like { name; other }))
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
          if dependency.package.owner = None && find_named dependency.package = None then
            report_problem directory (Not_a_project_package dependency.package))
        package.dependencies)
    packages;
  project_layout.problems @ chosen.lock_problems @ List.rev !problems

type t = {
  project_layout : layout;
  selection : selection;
  places : (Path.package * place) list;
  packages : package list;
  problems : problem list;
}

let lay_out_project files =
  let layouts = Root_table.create 4 in
  let lay_out_root root =
    match Root_table.find_opt layouts root with
    | Some layout -> layout
    | None ->
        let computed = lay_out files root in
        Root_table.replace layouts root computed;
        computed
  in
  let project_layout = lay_out_root Project in
  let selection = select_packages files project_layout in
  let places = place_packages ~lay_out_root ~selection in
  let cycle = Option.map make_cycle_problem (find_dependency_cycle places) in
  let places = if Option.is_some cycle then [] else places in
  {
    project_layout;
    selection;
    places;
    packages = List.map (fun (_, place) -> make_package files ~lay_out_root place) places;
    problems = list_problems project_layout selection @ Option.to_list cycle;
  }
