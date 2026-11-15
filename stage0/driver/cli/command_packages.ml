let manifest_name = "truss.toml"
let write_file = File_system.write_atomically ~durable:false

let load directory =
  let directory = Shown_path.real directory in
  match Database.open_session directory with
  | Error message -> raise (Outcome.Cannot_run message)
  | Ok (session, selected) ->
      let packages = List.map snd selected in
      if packages = [] && Database.problems session = [] then
        Outcome.cannot_run "No package in %s or any directory below it."
          (Shown_path.shown directory);
      (session, packages)

let current () = load "."
let worktree () = load (Database.root (fst (current ())))

let one = function
  | [ package ] -> package
  | [] -> Outcome.cannot_run "No package here."
  | several ->
      Outcome.cannot_run
        "This directory contains %d packages: %s. Run the command in one package's directory."
        (List.length several)
        (String.concat ", " (List.map Path.show_package several))

let directory session name =
  let root = Database.root session in
  match List.find_opt (fun (_, other) -> other = name) (Database.packages session) with
  | Some ("", _) -> root
  | Some (relative, _) -> Filename.concat root relative
  | None ->
      Compiler_bug.bug ~stage:"Command" "%s is not a package of the project"
        (Path.show_package name)

let path session file = Filename.concat (Database.root session) (Database.file_path session file)
let files session packages = List.concat_map (Database.package_files session) packages

let modules session packages =
  List.sort_uniq compare
    (List.map (fun (file : Path.file) -> file.module_) (files session packages))

let project_dependencies session packages =
  let project_packages = List.map snd (Database.packages session) in
  let seen = Hashtbl.create 8 in
  let rec visit name =
    List.iter
      (fun dependency ->
        if List.mem dependency project_packages && not (Hashtbl.mem seen dependency) then begin
          Hashtbl.replace seen dependency ();
          visit dependency
        end)
      (Query.demand (Database.context session) Packages.dependency_names name)
  in
  List.iter visit packages;
  List.filter (fun name -> Hashtbl.mem seen name && not (List.mem name packages)) project_packages

let program_files session packages =
  files session packages
  @ List.concat_map (Database.package_files session) (project_dependencies session packages)

let selected session packages paths =
  match paths with
  | [] -> files session packages
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
          let written = path session file in
          List.exists
            (fun path -> written = path || String.starts_with ~prefix:(path ^ "/") written)
            wanted)
        (files session packages)

let source session packages (file : Path.file) =
  let source = Query.demand (Database.context session) Packages.source file in
  if List.mem file.module_.package packages then
    Source.create ~path:(Shown_path.shown (path session file)) (Source.text source)
  else source

let shown_workspace_path session packages workspace_path =
  match
    List.find_opt (fun file -> Path.show_file file = workspace_path) (files session packages)
  with
  | Some file -> Shown_path.shown (path session file)
  | None -> workspace_path
