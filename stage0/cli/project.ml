(* The packages a command acts on, from the code database's session for the
   worktree it is run in.

   A command is about the packages at or under the directory it is run
   from, or else the one that directory is in: a package's directory and
   everything below it, apart from directories that hold their own
   [truss.toml], which are other packages, and those whose names start with
   [.]. The session reads the worktree's files and keeps what was computed
   about them, so a command after a small edit does little work. *)

exception Cannot_run of string
(** The command cannot do its job: no manifest, a session another process holds, a file that cannot
    be read. It exits with status 2. *)

let cannot_run format = Printf.ksprintf (fun message -> raise (Cannot_run message)) format
let manifest_name = "truss.toml"
let absolute path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path

(* A path with [.] and [..] parts worked out, and no trailing separator. *)
let normalize path =
  let parts = String.split_on_char '/' (absolute path) in
  let kept =
    List.fold_left
      (fun kept part ->
        match part with
        | "" | "." -> kept
        | ".." -> ( match kept with _ :: rest -> rest | [] -> [])
        | part -> part :: kept)
      [] parts
  in
  "/" ^ String.concat "/" (List.rev kept)

(* [path] as written from [from], both normalized: [forecast.truss], or
   [../weather/forecast.truss]. *)
let relative ~from path =
  let split path = List.filter (( <> ) "") (String.split_on_char '/' path) in
  let rec drop from path =
    match (from, path) with
    | f :: from', p :: path' when f = p -> drop from' path'
    | _ -> (from, path)
  in
  let up, down = drop (split from) (split path) in
  match List.map (fun _ -> "..") up @ down with [] -> "." | parts -> String.concat "/" parts

let real path = try Unix.realpath path with Unix.Unix_error _ -> normalize path
let shown path = relative ~from:(real (Sys.getcwd ())) (normalize path)

type package = {
  name : string;
  directory : string;  (** Absolute *)
  manifest : Type_checker.Manifest.t;
}

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

let read_text path =
  try In_channel.with_open_bin path In_channel.input_all
  with Sys_error message -> cannot_run "Cannot read %s: %s" (shown path) message

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
            let directory = if relative = "" then root else Filename.concat root relative in
            let manifest =
              try Type_checker.Manifest.parse (read_text (Filename.concat directory manifest_name))
              with Type_checker.Manifest.Malformed (line, message) ->
                cannot_run "%s:%d: %s"
                  (shown (Filename.concat directory manifest_name))
                  line message
            in
            { name; directory; manifest })
          targets
      in
      if packages = [] && Database.problems session = [] then
        cannot_run "No %s in %s or any directory above it, within its worktree." manifest_name
          (shown directory);
      {
        session;
        context = Database.context session;
        packages;
        files = module_files session packages;
      }

(* The one package a command that needs one is about. *)
let package t =
  match t.packages with
  | [ package ] -> package
  | [] -> cannot_run "No package here."
  | several ->
      cannot_run "This is about %d packages: %s. Run the command in one's directory."
        (List.length several)
        (String.concat ", " (List.map (fun p -> p.name) several))

let is_own t (module_ : Path.module_) = List.exists (fun p -> p.name = module_.package) t.packages

(* Reads the files again after a command changed some, so only what
   changed is checked again. *)
let reload t =
  Database.refresh t.session;
  t.files <- module_files t.session t.packages

let modules t = List.map fst t.files

let file t module_ =
  match List.assoc_opt module_ t.files with
  | Some path -> path
  | None -> Filename.concat (Database.root t.session) (Database.module_file t.session module_)

(* The modules in each of [paths], files or directories, or every module
   when there are none. *)
let selected t paths =
  match paths with
  | [] -> modules t
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
        t.files

(* A module's parsed file. *)
let parsed t module_ = Query.demand t.context Workspace.file module_

(* A module's text as a source named by its file as the current directory
   reaches it, which is how every command shows positions. Offsets are the
   same as in the database's own source. A module of another package, such
   as the standard library's, keeps its own name. *)
let source t module_ =
  let text = Source.text (parsed t module_).source in
  if is_own t module_ || List.mem_assoc module_ t.files then
    Source.create ~path:(shown (file t module_)) text
  else (parsed t module_).source

(* The file a position the compiled program reports names, such as
   [weather/forecast.truss], as the current directory reaches it, if it is
   one of these packages'. *)
let shown_workspace_path t workspace_path =
  match
    List.find_opt (fun (module_, _) -> Workspace.file_path module_ = workspace_path) t.files
  with
  | Some (_, file) -> shown file
  | None -> workspace_path

let write_file path text =
  let temporary = Printf.sprintf "%s.%d.tmp" path (Unix.getpid ()) in
  Out_channel.with_open_bin temporary (fun channel -> output_string channel text);
  Sys.rename temporary path

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
