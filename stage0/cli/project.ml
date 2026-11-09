(* Finding and loading the package a command acts on. See CLI.md, "Finding
   the package".

   A command looks for [truss.toml] in the current directory and each
   directory above it. The package's modules are the [.truss] files under
   its directory, except in directories that hold their own [truss.toml],
   which are other packages, and in directories whose names start with
   [.]. *)

exception Cannot_run of string
(** The command cannot do its job: no manifest, a malformed one, a file that cannot be read. It
    exits with status 2. *)

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

let shown path = relative ~from:(Sys.getcwd ()) (normalize path)

(* The nearest directory holding a manifest, from [start] up. *)
let find start =
  let rec up directory =
    if Sys.file_exists (Filename.concat directory manifest_name) then directory
    else
      let parent = Filename.dirname directory in
      if parent = directory then
        cannot_run "No %s here or in any directory above %s." manifest_name (shown start)
      else up parent
  in
  up (normalize start)

(* Each module of the package in [root], with its file, in order. *)
let module_files ~package root =
  let rec walk relative =
    let directory =
      if relative = [] then root else Filename.concat root (String.concat "/" relative)
    in
    let entries =
      try Array.to_list (Sys.readdir directory)
      with Sys_error message -> cannot_run "Cannot read %s: %s" (shown directory) message
    in
    List.sort compare entries
    |> List.concat_map (fun entry ->
        let path = Filename.concat directory entry in
        if String.starts_with ~prefix:"." entry then []
        else if Sys.is_directory path then
          if Sys.file_exists (Filename.concat path manifest_name) then []
          else walk (relative @ [ entry ])
        else if Filename.check_suffix entry ".truss" then
          [
            ( ({ package; modules = relative @ [ Filename.chop_suffix entry ".truss" ] }
                : Path.module_),
              path );
          ]
        else [])
  in
  walk []

type t = {
  root : string;  (** The package's directory, absolute *)
  manifest : Type_checker.Manifest.t;
  database : Query.database;
  mutable files : (Path.module_ * string) list;
      (** Each module, with its file, absolute, in order *)
}

let read_text path =
  try In_channel.with_open_bin path In_channel.input_all
  with Sys_error message -> cannot_run "Cannot read %s: %s" (shown path) message

let read_manifest root =
  let path = Filename.concat root manifest_name in
  try Type_checker.Manifest.parse (read_text path)
  with Type_checker.Manifest.Malformed (line, expected) ->
    cannot_run "%s:%d: expected %s." (shown path) line expected

(* Sets the package's modules and their text as the database's inputs. *)
let set_inputs t =
  Type_checker.load_package t.database ~name:t.manifest.name ~dependencies:t.manifest.dependencies
    (List.map (fun (module_, path) -> (module_, read_text path)) t.files)

let load_root root =
  let manifest = read_manifest root in
  let t =
    { root; manifest; database = Query.create (); files = module_files ~package:manifest.name root }
  in
  Type_checker.load_standard t.database;
  set_inputs t;
  t

let load directory = load_root (find directory)

(* Reads the package's files again, after a command changed some, so only
   what changed is checked again. *)
let reload t =
  t.files <- module_files ~package:t.manifest.name t.root;
  set_inputs t

let modules t = List.map fst t.files

let file t module_ =
  match List.assoc_opt module_ t.files with
  | Some path -> path
  | None -> invalid_arg ("Project.file: no module " ^ Path.show_module module_)

let module_of_file t path =
  let path = normalize path in
  List.find_map (fun (module_, file) -> if file = path then Some module_ else None) t.files

(* The modules in each of [paths], files or directories, or every module
   when there are none. *)
let selected t paths =
  match paths with
  | [] -> modules t
  | paths ->
      let wanted =
        List.map
          (fun path ->
            let path = normalize path in
            if not (Sys.file_exists path) then cannot_run "%s does not exist." (shown path);
            path)
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
let parsed t module_ = Query.demand t.database Workspace.file module_

(* A module's text as a source named by its file as the current directory
   reaches it, which is how every command shows positions. Offsets are the
   same as in the database's own source. *)
let source t module_ =
  Source.create ~path:(shown (file t module_)) (Source.text (parsed t module_).source)

(* The file a position the compiled program reports names, such as
   [weather/forecast.truss], as the current directory reaches it, if it is
   one of this package's. *)
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
