(* The packages a command acts on, with the code database's session for
   their project.

   A command acts on the packages at or below its directory, or else on the
   package that contains its directory. A package's files are those below
   its directory, except in directories with their own [truss.toml], which
   are other packages, and in directories whose names start with [.]. The
   session caches results about the project's files, so a command after a
   small edit does little work. *)

let manifest_name = "truss.toml"
let write_file = File_system.write_atomically ~durable:false

(* The session of the project that [directory] is in, and the packages at or
   below [directory]. *)
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

(* The current directory's packages. *)
let current () = load "."

(* Every package of the current directory's worktree. *)
let worktree () = load (Database.root (fst (current ())))

(* The package of a command that acts on exactly one. *)
let one = function
  | [ package ] -> package
  | [] -> Outcome.cannot_run "No package here."
  | several ->
      Outcome.cannot_run
        "This directory contains %d packages: %s. Run the command in one package's directory."
        (List.length several)
        (String.concat ", " (List.map Path.show_package several))

(* The absolute directory of a package of the project. *)
let directory session name =
  let root = Database.root session in
  match List.find_opt (fun (_, other) -> other = name) (Database.packages session) with
  | Some ("", _) -> root
  | Some (relative, _) -> Filename.concat root relative
  | None ->
      Compiler_bug.bug ~stage:"Command" "%s is not a package of the project"
        (Path.show_package name)

(* A file's absolute path. *)
let path session file = Filename.concat (Database.root session) (Database.file_path session file)
let files session packages = List.concat_map (Database.package_files session) packages

let modules session packages =
  List.sort_uniq compare
    (List.map (fun (file : Path.file) -> file.module_) (files session packages))

(* The project's packages that [packages] depend on, transitively, in the
   project's order. A registry package and the standard library are checked
   and proven when they are published, so they are not checked again; a
   registry package's tests can also use dependencies that are not in this
   build. *)
let project_dependencies session packages =
  let project_packages = List.map snd (Database.packages session) in
  let seen = Hashtbl.create 8 in
  let rec visit name =
    List.iter
      (fun (dependency : Manifest.dependency) ->
        if List.mem dependency.package project_packages && not (Hashtbl.mem seen dependency.package)
        then begin
          Hashtbl.replace seen dependency.package ();
          visit dependency.package
        end)
      (Query.demand (Database.context session) Packages.dependencies name)
  in
  List.iter visit packages;
  List.filter (fun name -> Hashtbl.mem seen name && not (List.mem name packages)) project_packages

(* The files that a command checks for a program built from [packages]:
   their own, and those of the project's packages they depend on. *)
let program_files session packages =
  files session packages
  @ List.concat_map (Database.package_files session) (project_dependencies session packages)

(* The files of [packages] in [paths], each a file or a directory, or every
   file when [paths] is empty. *)
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

(* A file that the compiled program names in a position, such as
   [weather/forecast.truss], as a path relative to the current directory
   when the file belongs to one of [packages], and unchanged otherwise. *)
let shown_workspace_path session packages workspace_path =
  match
    List.find_opt (fun file -> Path.show_file file = workspace_path) (files session packages)
  with
  | Some file -> Shown_path.shown (path session file)
  | None -> workspace_path
