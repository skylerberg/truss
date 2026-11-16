let manifest_name = "truss.toml"
let write_file = File_system.write_atomically ~durable:false

let load directory =
  let directory = Shown_path.real directory in
  match Workspace.take_snapshot directory with
  | Error message -> raise (Outcome.Cannot_run message)
  | Ok (snapshot, selected) ->
      let packages = List.map snd selected in
      if packages = [] && Workspace.problems snapshot = [] then
        Outcome.cannot_run "No package in %s or any directory below it."
          (Shown_path.shown directory);
      (snapshot, packages)

let current () = load "."

let retake snapshot =
  match Workspace.retake snapshot with
  | Ok snapshot -> snapshot
  | Error message -> raise (Outcome.Cannot_run message)

let worktree () = load (Workspace.root (fst (current ())))

let one = function
  | [ package ] -> package
  | [] -> Outcome.cannot_run "No package here."
  | several ->
      Outcome.cannot_run
        "This directory contains %d packages: %s. Run the command in one package's directory."
        (List.length several)
        (String.concat ", " (List.map Path.show_package several))

let directory snapshot name =
  let root = Workspace.root snapshot in
  match List.find_opt (fun (_, other) -> other = name) (Workspace.packages snapshot) with
  | Some ("", _) -> root
  | Some (relative, _) -> Filename.concat root relative
  | None ->
      Compiler_bug.bug ~stage:"Command" "%s is not a package of the project"
        (Path.show_package name)

let path snapshot file =
  Filename.concat (Workspace.root snapshot) (Workspace.file_path snapshot file)

let files snapshot packages = List.concat_map (Workspace.package_files snapshot) packages

let modules snapshot packages =
  List.sort_uniq compare
    (List.map (fun (file : Path.file) -> file.module_) (files snapshot packages))

let project_dependencies snapshot packages =
  let project_packages = List.map snd (Workspace.packages snapshot) in
  let seen = Hashtbl.create 8 in
  let rec visit name =
    List.iter
      (fun dependency ->
        if List.mem dependency project_packages && not (Hashtbl.mem seen dependency) then begin
          Hashtbl.replace seen dependency ();
          visit dependency
        end)
      (Workspace.dependency_names snapshot name)
  in
  List.iter visit packages;
  List.filter (fun name -> Hashtbl.mem seen name && not (List.mem name packages)) project_packages

let program_packages snapshot packages = packages @ project_dependencies snapshot packages

let manifest_problems snapshot database packages =
  List.concat_map
    (fun (directory, name) ->
      if List.mem name packages then
        List.map
          (fun problem -> (Project.manifest_file directory, name, problem))
          (Database.list_manifest_problems database name)
      else [])
    (Workspace.packages snapshot)

let selected snapshot packages paths =
  match paths with
  | [] -> files snapshot packages
  | paths ->
      let wanted =
        List.map
          (fun path ->
            if not (Sys.file_exists (Shown_path.normalize path)) then
              Outcome.cannot_run "%s does not exist." (Shown_path.shown path);
            Shown_path.real path)
          paths
      in
      List.filter
        (fun file ->
          let written = path snapshot file in
          List.exists
            (fun path -> written = path || String.starts_with ~prefix:(path ^ "/") written)
            wanted)
        (files snapshot packages)

let source snapshot packages (file : Path.file) =
  let source = Workspace.source snapshot file in
  if List.mem file.module_.package packages then
    Source.create ~path:(Shown_path.shown (path snapshot file)) (Source.text source)
  else source

let shown_workspace_path snapshot packages workspace_path =
  match
    List.find_opt (fun file -> Path.show_file file = workspace_path) (files snapshot packages)
  with
  | Some file -> Shown_path.shown (path snapshot file)
  | None -> workspace_path
