module Package_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.package
end))

let manifest_name = "truss.toml"
let write_file = File_system.write_atomically

let load directory =
  let directory = Shown_path.resolve_real_path directory in
  match Workspace.take_snapshot directory with
  | Error message -> raise (Outcome.Cannot_run message)
  | Ok (snapshot, selected) ->
      let packages = List.map snd selected in
      if packages = [] && Workspace.problems snapshot = [] then
        Outcome.raise_cannot_run "No package in %s or any directory below it."
          (Shown_path.show_path directory);
      (snapshot, packages)

let load_current () = load "."

let retake snapshot =
  match Workspace.retake snapshot with
  | Ok snapshot -> snapshot
  | Error message -> raise (Outcome.Cannot_run message)

let load_worktree () = load (Workspace.locate_root (fst (load_current ())))

let require_one = function
  | [ package ] -> package
  | [] -> Outcome.raise_cannot_run "No package here."
  | several ->
      Outcome.raise_cannot_run
        "This directory contains %d packages: %s. Run the command in one package's directory."
        (List.length several)
        (String.concat ", " (List.map Path.show_package several))

let locate_directory snapshot name =
  let root = Workspace.locate_root snapshot in
  match List.find_opt (fun (_, other) -> other = name) (Workspace.list_packages snapshot) with
  | Some ("", _) -> root
  | Some (relative, _) -> Filename.concat root relative
  | None ->
      Compiler_bug.raise_bug ~stage:"Command" "%s is not a package of the project"
        (Path.show_package name)

let locate_file snapshot file =
  Filename.concat (Workspace.locate_root snapshot) (Workspace.locate_file snapshot file)

let list_files snapshot packages = List.concat_map (Workspace.list_package_files snapshot) packages

let list_modules snapshot packages =
  List.sort_uniq compare
    (List.map (fun (file : Path.file) -> file.module_) (list_files snapshot packages))

let project_dependencies snapshot packages =
  let project_packages = List.map snd (Workspace.list_packages snapshot) in
  let seen = Package_table.create 8 in
  let rec visit name =
    List.iter
      (fun dependency ->
        if List.mem dependency project_packages && not (Package_table.mem seen dependency) then begin
          Package_table.replace seen dependency ();
          visit dependency
        end)
      (Workspace.list_dependency_names snapshot name)
  in
  List.iter visit packages;
  List.filter
    (fun name -> Package_table.mem seen name && not (List.mem name packages))
    project_packages

let list_program_packages snapshot packages = packages @ project_dependencies snapshot packages

let list_manifest_problems snapshot database packages =
  List.concat_map
    (fun (directory, name) ->
      if List.mem name packages then
        List.map
          (fun problem -> (Project.make_manifest_path directory, name, problem))
          (Database.list_manifest_problems database name)
      else [])
    (Workspace.list_packages snapshot)

let select_files snapshot packages paths =
  match paths with
  | [] -> list_files snapshot packages
  | paths ->
      let wanted =
        List.map
          (fun path ->
            if not (Sys.file_exists (Shown_path.normalize path)) then
              Outcome.raise_cannot_run "%s does not exist." (Shown_path.show_path path);
            Shown_path.resolve_real_path path)
          paths
      in
      List.filter
        (fun file ->
          let written = locate_file snapshot file in
          List.exists
            (fun path -> written = path || String.starts_with ~prefix:(path ^ "/") written)
            wanted)
        (list_files snapshot packages)

let read_source snapshot packages (file : Path.file) =
  let source = Workspace.read_source snapshot file in
  if List.mem file.module_.package packages then
    Source.create ~path:(Shown_path.show_path (locate_file snapshot file)) (Source.text source)
  else source

let show_workspace_path snapshot packages workspace_path =
  match
    List.find_opt (fun file -> Path.show_file file = workspace_path) (list_files snapshot packages)
  with
  | Some file -> Shown_path.show_path (locate_file snapshot file)
  | None -> workspace_path
