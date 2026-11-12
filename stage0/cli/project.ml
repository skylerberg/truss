(* The packages a command acts on, from the code database's session for the
   project it is run in.

   A command is about the packages at or under the directory it is run
   from, or else the one that directory is in: a package's directory and
   everything below it, apart from directories that hold their own
   [truss.toml], which are other packages, and those whose names start with
   [.]. The session reads the project's files and keeps the results computed
   from them, so a command after a small edit does little work. *)

exception Cannot_run of string
(** The command cannot do its job: no manifest, a session another process holds, a file that cannot
    be read. It exits with status 2. *)

let cannot_run format = Printf.ksprintf (fun message -> raise (Cannot_run message)) format
let manifest_name = "truss.toml"
let absolute path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path

(* A path with [.] and [..] parts resolved, and no trailing separator. *)
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

(* [path] as written from [from], both normalized: [forecast.truss], or
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
  packages : package list;  (** The packages the command is about *)
  mutable files : (Path.module_ * string) list;
      (** Each of their modules, with its file, absolute, in order *)
}

(* The sessions commands opened, which the command line saves once the
   command is done. *)
let opened : Database.session list ref = ref []

let module_files session packages =
  let root = Database.root session in
  List.concat_map
    (fun package ->
      List.map
        (fun module_ -> (module_, Filename.concat root (Database.module_file session module_)))
        (Database.package_modules session package.name))
    packages

let load directory =
  let directory = real directory in
  match Database.open_session directory with
  | Error message -> raise (Cannot_run message)
  | Ok (session, targets) ->
      if not (List.memq session !opened) then opened := session :: !opened;
      let root = Database.root session in
      let packages =
        List.map
          (fun (relative, name) ->
            { name; directory = (if relative = "" then root else Filename.concat root relative) })
          targets
      in
      if packages = [] && Database.problems session = [] then
        cannot_run "No package in %s or any directory below it." (shown directory);
      {
        session;
        context = Database.context session;
        packages;
        files = module_files session packages;
      }

(* The one package a command that needs one is about. *)
let package project =
  match project.packages with
  | [ package ] -> package
  | [] -> cannot_run "No package here."
  | several ->
      cannot_run "This is about %d packages: %s. Run the command in one's directory."
        (List.length several)
        (String.concat ", " (List.map (fun part -> Path.show_package part.name) several))

let is_own project (module_ : Path.module_) =
  List.exists (fun part -> part.name = module_.package) project.packages

(* The errors in the command's packages' manifests that only their code
   shows. *)
let manifest_problems project =
  Database.manifest_problems project.session
    (List.map (fun (package : package) -> package.name) project.packages)

(* Reads the files again after a command changed some, so only the
   changes are checked again. *)
let reload project =
  Database.refresh project.session;
  project.files <- module_files project.session project.packages

let modules project = List.map fst project.files

(* The packages the command's packages depend on, directly or not, but
   the standard library, whose proofs are checked where it is released. *)
let dependency_packages project =
  let seen = Hashtbl.create 8 in
  let rec visit name =
    List.iter
      (fun (dependency : Manifest.dependency) ->
        if dependency.package <> Path.standard_package && not (Hashtbl.mem seen dependency.package)
        then begin
          Hashtbl.replace seen dependency.package ();
          visit dependency.package
        end)
      (Query.demand project.context Workspace.dependencies name)
  in
  List.iter (fun (package : package) -> visit package.name) project.packages;
  List.filter
    (fun name ->
      not (List.exists (fun (package : package) -> package.name = name) project.packages))
    (Hashtbl.fold (fun name () names -> name :: names) seen [])

(* The modules a program built from the command's packages is made of,
   which its proofs are about: theirs, and their dependencies'. *)
let program_modules project =
  modules project
  @ List.concat_map
      (fun name -> Database.package_modules project.session name)
      (dependency_packages project)

let file project module_ =
  match List.assoc_opt module_ project.files with
  | Some path -> path
  | None ->
      Filename.concat (Database.root project.session) (Database.module_file project.session module_)

(* The modules in each of [paths], files or directories, or every module
   when there are none. *)
let selected project paths =
  match paths with
  | [] -> modules project
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
        (fun (module_, file) ->
          if
            List.exists
              (fun path -> file = path || String.starts_with ~prefix:(path ^ "/") file)
              wanted
          then Some module_
          else None)
        project.files

let parsed project module_ = Query.demand project.context Workspace.file module_

(* A module's text as a source named by its file as the current directory
   reaches it, which is how every command shows positions. Offsets are the
   same as in the database's own source. A module of another package, such
   as the standard library's, keeps its own name. *)
let source project module_ =
  let text = Source.text (parsed project module_).source in
  if is_own project module_ || List.mem_assoc module_ project.files then
    Source.create ~path:(shown (file project module_)) text
  else (parsed project module_).source

(* The file a position the compiled program reports names, such as
   [weather/forecast.truss], as the current directory reaches it, if it is
   one of these packages'. *)
let shown_workspace_path project workspace_path =
  match
    List.find_opt (fun (module_, _) -> Workspace.file_path module_ = workspace_path) project.files
  with
  | Some (_, file) -> shown file
  | None -> workspace_path

let write_file = File_system.write_atomically ~durable:false

(* Every definition [start] reads, directly or not. *)
let reachable dependencies start =
  let seen = Hashtbl.create 64 in
  let rec walk path =
    if not (Hashtbl.mem seen path) then begin
      Hashtbl.replace seen path ();
      List.iter (fun (read, _, _) -> walk read) (Database.reads dependencies path)
    end
  in
  walk start;
  seen
