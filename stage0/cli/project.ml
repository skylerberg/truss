(* The packages a command acts on, from the code database's session for
   the command's project.

   A command acts on the packages at or below its directory, or else on the
   package that contains its directory. A package's files are those below
   its directory, except in directories with their own [truss.toml], which
   are other packages, and in directories whose names start with [.]. The
   session caches results about the project's files, so a command after a
   small edit does little work. *)

exception Cannot_run of string
(** The command cannot run: no manifest, a session that another process holds, or an unreadable
    file. It exits with status 2. *)

let cannot_run format = Printf.ksprintf (fun message -> raise (Cannot_run message)) format
let manifest_name = "truss.toml"
let absolute path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path

(* The path with [.] and [..] segments resolved and no trailing
   separator. *)
let normalize path =
  let parts = String.split_on_char '/' (absolute path) in
  let segments =
    List.fold_left
      (fun segments part ->
        match part with
        | "" | "." -> segments
        | ".." -> ( match segments with _ :: rest -> rest | [] -> [])
        | part -> part :: segments)
      [] parts
  in
  "/" ^ String.concat "/" (List.rev segments)

(* [path] relative to [from], both normalized, such as [forecast.truss] or
   [../weather/forecast.truss]. *)
let relative ~from path =
  let split path = List.filter (( <> ) "") (String.split_on_char '/' path) in
  let rec drop from path =
    match (from, path) with
    | from_part :: from', path_part :: path' when from_part = path_part -> drop from' path'
    | _ -> (from, path)
  in
  let up, down = drop (split from) (split path) in
  match List.map (fun _ -> "..") up @ down with [] -> "." | parts -> String.concat "/" parts

let real path = try Unix.realpath path with Unix.Unix_error _ -> normalize path
let shown path = relative ~from:(real (Sys.getcwd ())) (normalize path)

type package = { name : Path.package; directory : string  (** Absolute *) }

type t = {
  session : Database.session;
  context : Query.context;
  packages : package list;  (** The packages the command acts on *)
  mutable files : (Path.file * string) list;
      (** Each of their files with its absolute path, in order *)
}

let file_paths session packages =
  let root = Database.root session in
  List.concat_map
    (fun package ->
      List.map
        (fun file -> (file, Filename.concat root (Database.file_path session file)))
        (Database.package_files session package.name))
    packages

let load directory =
  let directory = real directory in
  match Database.open_session directory with
  | Error message -> raise (Cannot_run message)
  | Ok (session, targets) ->
      let root = Database.root session in
      let packages =
        List.map
          (fun (relative, name) ->
            { name; directory = (if relative = "" then root else Filename.concat root relative) })
          targets
      in
      if packages = [] && Database.problems session = [] then
        cannot_run "No package in %s or any directory below it." (shown directory);
      { session; context = Database.context session; packages; files = file_paths session packages }

(* The project of the current directory's packages. *)
let current () = load "."

(* The project of every package of the current directory's worktree. *)
let worktree () = load (Database.root (current ()).session)

(* The package of a command that acts on exactly one. *)
let package project =
  match project.packages with
  | [ package ] -> package
  | [] -> cannot_run "No package here."
  | several ->
      cannot_run
        "This directory contains %d packages: %s. Run the command in one package's directory."
        (List.length several)
        (String.concat ", " (List.map (fun part -> Path.show_package part.name) several))

let is_own project (module_ : Path.module_) =
  List.exists (fun part -> part.name = module_.package) project.packages

(* The manifest problems that only the code of the command's packages
   reveals. *)
let manifest_problems project =
  Database.manifest_problems project.session
    (List.map (fun (package : package) -> package.name) project.packages)

(* Rereads the files after a command edited some, so only the edited files
   are checked again. *)
let reload project =
  Database.refresh project.session;
  project.files <- file_paths project.session project.packages

let files project = List.map fst project.files

let modules project =
  List.sort_uniq compare (List.map (fun (file : Path.file) -> file.module_) (files project))

(* The project's packages that the command's packages depend on,
   transitively, in the project's order. A registry package and the
   standard library are checked and proven when they are published, so
   they are not checked again; a registry package's tests can also use
   dependencies that are not in this build. *)
let project_dependencies project =
  let project_packages = List.map snd (Database.packages project.session) in
  let seen = Hashtbl.create 8 in
  let rec visit name =
    List.iter
      (fun (dependency : Manifest.dependency) ->
        if List.mem dependency.package project_packages && not (Hashtbl.mem seen dependency.package)
        then begin
          Hashtbl.replace seen dependency.package ();
          visit dependency.package
        end)
      (Query.demand project.context Workspace.dependencies name)
  in
  List.iter (fun (package : package) -> visit package.name) project.packages;
  List.filter
    (fun name ->
      Hashtbl.mem seen name
      && not (List.exists (fun (package : package) -> package.name = name) project.packages))
    project_packages

(* The files that a command checks for a program built from its packages:
   the packages' own, and those of the project's packages they depend on. *)
let program_files project =
  files project
  @ List.concat_map
      (fun name -> Database.package_files project.session name)
      (project_dependencies project)

let path project file =
  match List.assoc_opt file project.files with
  | Some path -> path
  | None ->
      Filename.concat (Database.root project.session) (Database.file_path project.session file)

(* The files in [paths], each a file or a directory, or every file when
   [paths] is empty. *)
let selected project paths =
  match paths with
  | [] -> files project
  | paths ->
      let wanted =
        List.map
          (fun path ->
            if not (Sys.file_exists (normalize path)) then
              cannot_run "%s does not exist." (shown path);
            real path)
          paths
      in
      List.filter_map
        (fun (file, written) ->
          if
            List.exists
              (fun path -> written = path || String.starts_with ~prefix:(path ^ "/") written)
              wanted
          then Some file
          else None)
        project.files

let parsed project file = Query.demand project.context Workspace.file file

(* A file's text as a source named by its path relative to the current
   directory, which every command uses for positions. Offsets match the
   database's source. A file of a package outside the project, such as
   the standard library, keeps its database name. *)
let source project (file : Path.file) =
  let text = Source.text (parsed project file).source in
  if is_own project file.module_ || List.mem_assoc file project.files then
    Source.create ~path:(shown (path project file)) text
  else (parsed project file).source

(* A file that the compiled program names in a position, such as
   [weather/forecast.truss], as a path relative to the current directory
   when the file belongs to one of the command's packages, and unchanged
   otherwise. *)
let shown_workspace_path project workspace_path =
  match List.find_opt (fun (file, _) -> Path.show_file file = workspace_path) project.files with
  | Some (_, file) -> shown file
  | None -> workspace_path

let write_file = File_system.write_atomically ~durable:false
