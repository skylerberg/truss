(* Loading packages *)

let load_package ?(usize_bits = 32) engine ~name ~dependencies
    (modules : (Path.module_ * string) list) =
  List.iter (fun (module_, text) -> Engine.set engine Workspace.file_text module_ text) modules;
  Engine.set engine Workspace.packages name
    { Workspace.name; dependencies; modules = List.map fst modules; usize_bits }

(* The standard library holds the code for each platform, and its bounds of
   [USize] are its target's, so it is checked with the target's width. *)
let load_standard engine =
  load_package ~usize_bits:64 engine ~name:Path.standard_package ~dependencies:[]
    Standard_library.modules

(* The standard library, checked whole in an engine of its own. Its sources
   never change, so the engine is frozen as a fixed base, which every state
   reads. *)
let check_standard engine =
  load_standard engine;
  List.iter
    (fun (module_, _) -> ignore (Engine.get engine Type_checker.file_diagnostics module_))
    Standard_library.modules

let standard_base () =
  let engine = Engine.create () in
  check_standard engine;
  Engine.freeze ~fixed:true engine;
  engine

(* The database's own inputs: how a project's files map to packages, and
   each file's stamp, so that a restart reads only the files that changed. *)

type layout = {
  packages : (string * string) list;
      (** Each package's directory, relative to the root, and name *)
  files : string list;
      (** Each manifest, lock file, and module file under the root, relative to it *)
  modules : (string * Path.module_) list;  (** Each module's file *)
  time_limit : int;  (** Each test's, in seconds *)
  registry : (string * Registry.Version.t * string) list;
      (** Each registry package of the build: its name, its version, and the hash of its files *)
}

let no_layout =
  {
    packages = [];
    files = [];
    modules = [];
    time_limit = Manifest.default_time_limit;
    registry = [];
  }

let layout : (unit, layout) Query.input =
  Query.input ~name:"worktree_layout" ~show:(fun () -> "") ()

(* Each file's stamp, by its path: what says, without reading the file,
   that it has not changed. *)
let stamps : (string, string) Query.input = Query.input ~name:"worktree_stamp" ~show:Fun.id ()

(* Each manifest's text, by its package's directory, so that an unchanged
   manifest need not be read again. *)
let manifest_texts : (string, string) Query.input =
  Query.input ~name:"worktree_manifest" ~show:Fun.id ()

(* The project's lock file's text, for the same reason. *)
let lock_text : (unit, string) Query.input =
  Query.input ~name:"worktree_lock" ~show:(fun () -> "") ()

(* Sessions *)

(* What a session's files are, for what is asked of git. *)
type kind =
  | Worktree of string  (** A project's root *)
  | Commit of { repository : string; commit : string }
  | Library  (** The standard library as a state of its own *)
  | Published  (** A published package with the packages it was published with *)

(* What the database keeps with a session of the session layer. *)
type project = {
  kind : kind;
  update : Session.t -> unit;  (** Brings the inputs in line with the session's files *)
  files : Files.t;
  mutable problems : string list;  (** Manifests that could not be read, and duplicate names *)
  mutable lock_fix : string option;
      (** The lock file the manifests give, when the one written is another *)
  mutable applied : bool;  (** Whether this process has brought the inputs in line with the files *)
}

type Session.attachment += Project of project
type session = Session.t

let project session =
  match Session.attachment session with
  | Project project -> project
  | _ -> invalid_arg "Database: a session with no project"

(* A package whose sources never change is checked once, written whole, and
   found from then on by the key of its sources: for the standard library,
   which is built into the compiler, the compiler's identity. *)
let standard_key identity = identity ^ " standard"

let stored_standard () =
  let store = Session.store () and identity = Session.identity () in
  let found =
    Option.bind
      (Store.find_result store ~kind:"package" ~key:(standard_key identity))
      (Engine.open_base store ~version:identity ~bases:[])
  in
  match found with
  | Some base when Engine.inputs_stored base -> base
  | Some _ | None ->
      let engine = Engine.create () in
      Engine.attach engine store ~version:identity;
      check_standard engine;
      Store.add_result store ~kind:"package" ~key:(standard_key identity)
        (Engine.write ~full:true engine);
      Engine.freeze ~fixed:true engine;
      engine

(* The standard library, a fixed base under every project's state. *)
let standard : Engine.t Lazy.t ref = ref (lazy (stored_standard ()))
let () = Session.on_close (fun () -> standard := lazy (stored_standard ()))
let prepare_store () = ignore (Lazy.force !standard)

let session_name root =
  Printf.sprintf "session-%s-%s"
    (Session.Identity.short (Session.identity ()))
    (String.sub (Blake3.to_hex (Blake3.hash root)) 0 16)

let read context input key = Query.find context input key
let current_layout engine = Option.value (read (Engine.context engine) layout ()) ~default:no_layout
let layout_of session = current_layout (Session.engine session)

(* Setting a worktree's files as inputs *)

type file_contents = Text of string | Unchanged

let manifest_file directory = if directory = "" then "truss.toml" else directory ^ "/truss.toml"

(* Registry packages *)

type published = {
  manifest : Manifest.package;
  record : Registry.Lock.t;
  sources : (string list * string) list;  (** Each module's names under its package, and its text *)
}

(* A published package never changes, so what was read of one is kept by its
   hash for as long as the process lives. *)
let published : (string, published) Hashtbl.t = Hashtbl.create 16

(* A published package's files, from the store, fetched into it from the
   registry when they are not there yet. *)
let load_published ~packages name version ~hash =
  match Hashtbl.find_opt published hash with
  | Some found -> Ok found
  | None -> (
      let fetched =
        let directory = Filename.concat packages hash in
        if Sys.file_exists directory then Ok directory
        else
          match Registry.Index.current () with
          | Some registry -> Registry.Index.fetch registry ~into:packages name version ~hash
          | None ->
              Error
                (Printf.sprintf "no registry is set: `%s` names its directory"
                   Registry.Index.variable)
      in
      match fetched with
      | Error reason -> Error reason
      | Ok directory -> (
          let files = Registry.Content.files ~all:true directory in
          let text file = List.assoc_opt file files in
          match
            ( Option.map Manifest.parse (text "truss.toml"),
              Registry.Lock.parse (Option.value ~default:"" (text "truss.lock")) )
          with
          | exception Manifest.Malformed (line, message) ->
              Error (Printf.sprintf "its manifest cannot be read: line %d: %s" line message)
          | exception Registry.Lock.Malformed (line, message) ->
              Error (Printf.sprintf "its lock file cannot be read: line %d: %s" line message)
          | Some { package = Some manifest; _ }, record when manifest.name = name ->
              let found =
                {
                  manifest;
                  record;
                  sources =
                    List.filter_map
                      (fun (path, text) ->
                        if Filename.check_suffix path ".truss" then
                          Some (Worktree.segments (Filename.chop_suffix path ".truss"), text)
                        else None)
                      files;
                }
              in
              Hashtbl.replace published hash found;
              Ok found
          | _ -> Error (Printf.sprintf "its manifest does not name the package `%s`" name)))

(* A package that is in a cycle of the project's packages that depend on
   each other, with the cycle. *)
let dependency_cycle (packages : (string * Manifest.package) list) =
  let dependencies name =
    match List.find_opt (fun (_, (p : Manifest.package)) -> p.name = name) packages with
    | Some (_, package) ->
        List.map
          (fun (dependency : Workspace.dependency) -> dependency.package)
          package.dependencies
    | None -> []
  in
  let rec reaches target seen name =
    if List.mem name seen then None
    else
      List.find_map
        (fun next ->
          if next = target then Some [ name; target ]
          else Option.map (fun way -> name :: way) (reaches target (name :: seen) next))
        (dependencies name)
  in
  List.find_map
    (fun (directory, (package : Manifest.package)) ->
      Option.map (fun way -> (directory, way)) (reaches package.name [] package.name))
    packages

(* Sets a published package's manifest and modules as an engine's inputs. *)
let set_published engine (found : published) =
  let name = found.manifest.name in
  let sources =
    List.map
      (fun (modules, text) -> (({ package = name; modules } : Path.module_), text))
      found.sources
  in
  List.iter (fun (module_, text) -> Engine.set engine Workspace.file_text module_ text) sources;
  Engine.set engine Workspace.packages name
    {
      Workspace.name;
      dependencies = found.manifest.dependencies;
      modules = List.map fst sources;
      usize_bits = found.manifest.usize_bits;
    }

(* Brings the inputs in line with a set of files, each with its contents, or
   [Unchanged] when its stamp shows it is the same as before. The files are
   every manifest and module file under the project's root. Those of another
   project are left out: under a root with a [[project]] table, a directory
   whose manifest has one of its own and everything below it, and under a
   root without one, which is a project of one package, every other
   directory with a manifest. *)
let apply ?(text = fun _ -> None) session (files : (string * file_contents) list) =
  let module Manifest = Manifest in
  let engine = Session.engine session in
  let project = project session in
  let old = current_layout engine in
  let problems = ref [] in
  let problem directory format =
    Printf.ksprintf
      (fun message ->
        problems := Printf.sprintf "%s: %s" (manifest_file directory) message :: !problems)
      format
  in
  let manifests =
    List.filter_map
      (fun (path, contents) ->
        if Filename.basename path <> "truss.toml" then None
        else
          let directory = Worktree.parent path in
          let text =
            match contents with
            | Text text -> Some text
            | Unchanged -> read (Engine.context engine) manifest_texts directory
          in
          Option.map (fun text -> (directory, text)) text)
      files
  in
  List.iter (fun (directory, text) -> Engine.set engine manifest_texts directory text) manifests;
  let directories = List.map fst manifests in
  let is_project directory =
    match List.assoc_opt directory manifests with
    | Some text -> Manifest.has_project_table text
    | None -> false
  in
  let root_is_project = is_project "" in
  let rec in_another_project directory =
    directory <> ""
    && ((List.mem directory directories && ((not root_is_project) || is_project directory))
       || in_another_project (Worktree.parent directory))
  in
  let parsed =
    List.filter_map
      (fun (directory, text) ->
        if in_another_project directory then None
        else
          match Manifest.parse text with
          | manifest -> Some (directory, manifest)
          | exception Manifest.Malformed (line, message) ->
              problems :=
                Printf.sprintf "%s:%d: %s" (manifest_file directory) line message :: !problems;
              None)
      manifests
  in
  let time_limit =
    List.fold_left
      (fun limit (directory, (manifest : Manifest.t)) ->
        match manifest.time_limit with
        | Some seconds when directory = "" -> seconds
        | Some _ ->
            problem directory
              "A test's time limit is its project's. Write `[test]` in the project's manifest, \
               `truss.toml` at its root.";
            limit
        | None -> limit)
      Manifest.default_time_limit parsed
  in
  let seen = Hashtbl.create 8 in
  let packages =
    List.filter_map
      (fun (directory, (manifest : Manifest.t)) ->
        match manifest.package with
        | None -> None
        | Some package when package.name = Path.standard_package ->
            problem directory "The package name `standard` is the standard library's.";
            None
        | Some package -> (
            match Hashtbl.find_opt seen package.name with
            | Some other ->
                problem directory "The package name `%s` is already used by %s." package.name
                  (manifest_file other);
                None
            | None ->
                Hashtbl.replace seen package.name directory;
                Some (directory, package)))
      parsed
  in
  let named name = List.find_opt (fun (_, (p : Manifest.package)) -> p.name = name) packages in
  let lock_problem format =
    Printf.ksprintf (fun message -> problems := ("truss.lock: " ^ message) :: !problems) format
  in
  let written_text =
    match List.assoc_opt "truss.lock" files with
    | Some (Text text) ->
        Engine.set engine lock_text () text;
        Some text
    | Some Unchanged -> read (Engine.context engine) lock_text ()
    | None ->
        Engine.remove engine lock_text ();
        None
  in
  let written =
    match Registry.Lock.parse (Option.value ~default:"" written_text) with
    | entries -> Some entries
    | exception Registry.Lock.Malformed (line, message) ->
        problems := Printf.sprintf "truss.lock:%d: %s" line message :: !problems;
        None
  in
  (* The registry packages of the build: what the project's packages depend
     on that is no package of the project, at the versions the lock file and
     their own records give. *)
  let store_packages = Session.directory "packages" in
  let selected, selection_problems =
    Registry.Selection.choose
      ~lock:(Option.value ~default:[] written)
      ~roots:
        (List.concat_map
           (fun (_, (package : Manifest.package)) ->
             List.filter_map
               (fun (dependency : Workspace.dependency) ->
                 match Path.package_parts dependency.package with
                 | [ _; _ ] -> Some (package.name, dependency.package)
                 | _ -> None)
               package.dependencies)
           packages)
      ~local:(fun name -> named name <> None)
      ~load:(fun name version ~hash ->
        Result.map
          (fun found -> (found.manifest, found.record))
          (load_published ~packages:store_packages name version ~hash))
  in
  List.iter (fun found -> lock_problem "%s" (Registry.Selection.sentence found)) selection_problems;
  let selected_named name =
    List.find_opt (fun (found : Registry.Selection.package) -> found.name = name) selected
  in
  List.iter
    (fun (found : Registry.Selection.package) ->
      match found.manifest.truss with
      | Some version when not (Manifest.toolchain_builds version) ->
          lock_problem "`%s` %s is written for Truss %s, and this toolchain is Truss %s." found.name
            (Registry.Version.show found.version)
            version Manifest.truss_version
      | _ -> ())
    selected;
  (* The lock file is written one way: what the manifests and the versions
     in it give. Another is a problem whose fix is to write that one. *)
  project.lock_fix <- None;
  (match written with
  | Some written when selection_problems = [] ->
      let current =
        Registry.Selection.lock
          ~project:
            (List.concat_map
               (fun (_, (package : Manifest.package)) -> package.dependencies)
               packages)
          selected
      in
      let text = Registry.Lock.print current in
      if current = [] && written_text = None then ()
      else if written_text <> Some text then begin
        project.lock_fix <- Some text;
        lock_problem "This is not the lock file the manifests give. %sRun `truss check --fix`."
          (String.concat ""
             (List.map
                (fun difference -> difference ^ " ")
                (Registry.Selection.differences ~written ~current)))
      end
  | _ -> ());
  List.iter
    (fun (directory, (package : Manifest.package)) ->
      (match package.truss with
      | None ->
          problem directory
            "`[package]` needs `truss = \"%s\"`, the version of Truss the package is written for."
            Manifest.truss_version
      | Some version when not (Manifest.toolchain_builds version) ->
          problem directory "`%s` is written for Truss %s, and this toolchain is Truss %s."
            package.name version Manifest.truss_version
      | Some _ -> ());
      (* Every path must read one way: [acme::geometry::vector] cannot be
         both a module of [acme::geometry] and one of a package [acme]. *)
      (match Path.package_parts package.name with
      | [ name ] ->
          List.iter
            (fun other ->
              match Path.package_parts other with
              | [ owner; _ ] when owner = name ->
                  problem directory
                    "The package name `%s` is the owner in `%s`, so a path that starts with it \
                     could be read two ways. Give one of them another name."
                    name other
              | _ -> ())
            (List.sort_uniq compare
               (List.map (fun (_, (p : Manifest.package)) -> p.name) packages
               @ List.concat_map
                   (fun (_, (p : Manifest.package)) ->
                     List.map (fun (d : Workspace.dependency) -> d.package) p.dependencies)
                   packages))
      | _ -> ());
      List.iter
        (fun (dependency : Workspace.dependency) ->
          if dependency.package = package.name then
            problem directory "`%s` cannot depend on itself." package.name
          else
            let found =
              match (named dependency.package, selected_named dependency.package) with
              | Some (_, other), _ -> Some other
              | None, Some other -> Some other.manifest
              | None, None ->
                  (* A dependency the registry would have, with no version
                     known, is reported with the lock file. *)
                  if List.length (Path.package_parts dependency.package) = 1 then
                    problem directory "`%s` is not a package of this project." dependency.package;
                  None
            in
            match found with
            | Some other when package.usize_bits = 32 && other.usize_bits = 64 ->
                (* A package that claims to run on every target cannot rely
                   on one that runs only on 64-bit targets. *)
                problem directory
                  "`%s` runs only on 64-bit targets, so `%s` must say `usize_bits = 64` to depend \
                   on it."
                  other.name package.name
            | _ -> ())
        package.dependencies)
    packages;
  (match dependency_cycle packages with
  | Some (directory, way) ->
      problem directory "Packages cannot depend on each other in a cycle: %s."
        (String.concat " -> " (List.map (Printf.sprintf "`%s`") way))
  | None -> ());
  let package_at directory = List.assoc_opt directory packages in
  let modules =
    List.filter_map
      (fun (path, contents) ->
        if not (Filename.check_suffix path ".truss") then None
        else
          match
            Option.bind (Worktree.owner directories path) (fun directory ->
                Option.map (fun package -> (directory, package)) (package_at directory))
          with
          | Some (directory, (package : Manifest.package)) ->
              Some
                ( path,
                  ({
                     package = package.name;
                     modules = Worktree.module_names ~package_directory:directory path;
                   }
                    : Path.module_),
                  contents )
          | None -> None)
      files
  in
  (* A file that is unchanged is a module whose text is not set when a
     manifest gave it another package, and so another path. *)
  List.iter
    (fun (path, module_, contents) ->
      match contents with
      | Text text -> Engine.set engine Workspace.file_text module_ text
      | Unchanged ->
          if read (Engine.context engine) Workspace.file_text module_ = None then
            Option.iter (Engine.set engine Workspace.file_text module_) (text path))
    modules;
  List.iter
    (fun (path, contents) ->
      match contents with
      | Text text -> Session.note_file session path (Some (Session.fingerprint text))
      | Unchanged -> ())
    files;
  let listed = Hashtbl.create (List.length files) in
  List.iter (fun (path, _) -> Hashtbl.replace listed path ()) files;
  List.iter
    (fun path -> if not (Hashtbl.mem listed path) then Session.note_file session path None)
    old.files;
  let present = Hashtbl.create (List.length modules) in
  List.iter (fun (_, module_, _) -> Hashtbl.replace present module_ ()) modules;
  List.iter
    (fun (_, module_) ->
      if not (Hashtbl.mem present module_) then Engine.remove engine Workspace.file_text module_)
    old.modules;
  List.iter
    (fun (_, name) -> if named name = None then Engine.remove engine Workspace.packages name)
    old.packages;
  List.iter
    (fun (directory, (package : Manifest.package)) ->
      let own =
        List.filter_map
          (fun (path, module_, _) ->
            if Worktree.owner directories path = Some directory then Some module_ else None)
          modules
      in
      Engine.set engine Workspace.packages package.name
        {
          Workspace.name = package.name;
          dependencies = package.dependencies;
          modules = own;
          usize_bits = package.usize_bits;
        })
    packages;
  (* A registry package's files never change, so its inputs are set when it
     enters the build, or its version changes, and taken away when it
     leaves. *)
  let registry =
    List.map
      (fun (found : Registry.Selection.package) -> (found.name, found.version, found.hash))
      selected
  in
  List.iter
    (fun ((name, _, _) as was) ->
      if not (List.mem was registry) then begin
        (match read (Engine.context engine) Workspace.packages name with
        | Some package when named name = None ->
            List.iter
              (fun module_ -> Engine.remove engine Workspace.file_text module_)
              package.modules
        | _ -> ());
        if named name = None && selected_named name = None then
          Engine.remove engine Workspace.packages name
      end)
    old.registry;
  List.iter
    (fun (found : Registry.Selection.package) ->
      if not (List.mem (found.name, found.version, found.hash) old.registry) then
        Option.iter (set_published engine) (Hashtbl.find_opt published found.hash))
    selected;
  Engine.set engine layout ()
    {
      packages = List.map (fun (d, (p : Manifest.package)) -> (d, p.name)) packages;
      files = List.map fst files;
      modules = List.map (fun (path, module_, _) -> (path, module_)) modules;
      time_limit;
      registry;
    };
  project.problems <- List.rev !problems

(* Reads the files whose stamps changed, and sets them. A file that cannot
   be read, such as one deleted since its directory was listed, is not
   there. A stamp is set only once its file's text is, so that a scan that
   fails leaves the file to be read by the next. *)
let scan (files : Files.t) session =
  let engine = Session.engine session in
  let project = project session in
  let context = Engine.context engine in
  let found =
    List.filter_map
      (fun (path, stamp) ->
        match read context stamps path with
        | Some old when old = stamp -> Some (path, stamp, Unchanged)
        | _ -> Option.map (fun text -> (path, stamp, Text text)) (files.read path))
      (files.list ())
  in
  let old = current_layout engine in
  (* A scan that finds every file as it was has nothing to bring in line.
     With a problem outstanding it looks again, since a problem can be one
     that the files do not show, such as a package that could not be
     fetched. *)
  let unchanged =
    project.applied && project.problems = []
    && List.for_all (fun (_, _, contents) -> contents = Unchanged) found
    && List.length found = List.length old.files
  in
  if not unchanged then begin
    apply ~text:files.read session (List.map (fun (path, _, contents) -> (path, contents)) found);
    project.applied <- true
  end;
  let present = Hashtbl.create (List.length found) in
  List.iter
    (fun (path, stamp, contents) ->
      Hashtbl.replace present path ();
      match contents with Text _ -> Engine.set engine stamps path stamp | Unchanged -> ())
    found;
  List.iter
    (fun path -> if not (Hashtbl.mem present path) then Engine.remove engine stamps path)
    old.files

(* Each file's fingerprint, by which the saved state nearest to a set of
   files is found. *)
let fingerprints (files : Files.t) () =
  List.filter_map
    (fun (path, _) -> Option.map (fun text -> (path, Session.fingerprint text)) (files.read path))
    (files.list ())

let attach_project session ~kind (files : Files.t) =
  Session.attach session
    (Project { kind; update = scan files; files; problems = []; lock_fix = None; applied = false })

(* The session for a set of files: its own state if it has one, else the
   nearest saved state, else a new one over the standard library. This is
   the one way a project's session is opened, whatever its files are. *)
let open_files ~key ?pointer ?home ~kind (files : Files.t) =
  match Session.find key with
  | Some session -> Ok session
  | None -> (
      match
        Session.open_ ~key ?pointer ?home ~version:(Session.identity ())
          ~bases:(fun () -> [ Lazy.force !standard ])
          ~fingerprints:(fingerprints files) ()
      with
      | Error () -> Error ()
      | Ok (session, start) ->
          attach_project session ~kind files;
          if start = Session.Near then
            (* The stamps it carries are another set of files'. *)
            List.iter (fun path -> Session.remove session stamps path) (layout_of session).files;
          Ok session)

let update session = (project session).update session

let open_directory root =
  Result.map_error
    (fun () ->
      Printf.sprintf
        "%s is open in another process of this compiler, such as its background process; leave out \
         --no-server, or stop that process with `truss stop`."
        root)
    (open_files ~key:root ~pointer:(session_name root) ~home:root ~kind:(Worktree root)
       (Files.of_directory root))

let open_commit ~repository commit =
  let key = Printf.sprintf "commit:%s:%s" repository commit in
  match Session.find key with
  | Some session -> Ok session
  | None -> (
      match Files.of_commit ~directory:repository commit with
      | None -> Error (Printf.sprintf "cannot read commit %s." commit)
      | Some files -> (
          match open_files ~key ~kind:(Commit { repository; commit }) files with
          | Ok session ->
              update session;
              ignore (Engine.stabilize (Session.engine session));
              Ok session
          | Error () -> Error (Printf.sprintf "cannot open commit %s." commit)))

(* The root of the project a directory is in: the nearest directory at or
   above it whose manifest has a [[project]] table, or with none, the
   nearest with a manifest, which is a package that is a project by
   itself. *)
let root_of directory =
  let directory = try Unix.realpath directory with Unix.Unix_error _ -> directory in
  let has_project_table manifest =
    try Manifest.has_project_table (In_channel.with_open_bin manifest In_channel.input_all)
    with Sys_error _ -> false
  in
  let rec up path nearest =
    let manifest = Filename.concat path "truss.toml" in
    let here = Sys.file_exists manifest in
    if here && has_project_table manifest then Some path
    else
      let nearest = if here && nearest = None then Some path else nearest in
      let parent = Filename.dirname path in
      if parent = path then nearest else up parent nearest
  in
  up directory None

let relative_to root directory =
  let directory = try Unix.realpath directory with Unix.Unix_error _ -> directory in
  if directory = root then ""
  else
    let prefix = root ^ "/" in
    if
      String.length directory > String.length prefix
      && String.sub directory 0 (String.length prefix) = prefix
    then String.sub directory (String.length prefix) (String.length directory - String.length prefix)
    else ""

(* The packages a request in a directory is about: those at or under it, or
   the one it is in. *)
let target_packages session within =
  let lay = layout_of session in
  let under (directory, _) =
    within = "" || directory = within
    || String.length directory > String.length within
       && String.sub directory 0 (String.length within + 1) = within ^ "/"
  in
  match List.filter under lay.packages with
  | [] -> (
      match Worktree.owner (List.map fst lay.packages) (within ^ "/x.truss") with
      | Some directory -> List.filter (fun (d, _) -> d = directory) lay.packages
      | None -> [])
  | found -> found

let package_modules session name =
  match read (Engine.context (Session.engine session)) Workspace.packages name with
  | Some package -> package.modules
  | None -> []

(* Sessions as the command line sees them *)

let root session =
  match (project session).kind with
  | Worktree root -> root
  | Commit commit -> commit.repository
  | Library | Published -> ""

let context session = Session.context session
let set = Session.set
let problems session = (project session).problems

(* What only a package's code shows to be wrong with its manifest, which
   checks the package. *)
let manifest_problems session names =
  List.concat_map
    (fun (directory, name) ->
      if not (List.mem name names) then []
      else
        List.map
          (fun problem -> (manifest_file directory, name, problem))
          (try Engine.get (Session.engine session) Type_checker.manifest_problems name
           with Not_found -> []))
    (layout_of session).packages

let packages session = (layout_of session).packages

let module_file session (module_ : Path.module_) =
  let lay = layout_of session in
  match List.find_opt (fun (_, name) -> name = module_.package) lay.packages with
  | Some (directory, _) -> Worktree.module_file ~package_directory:directory module_
  | None -> Workspace.file_path module_

let time_limit session = (layout_of session).time_limit
let registry_packages session = (layout_of session).registry
let lock_fix session = (project session).lock_fix

let diagnostics session module_ =
  try Engine.get (Session.engine session) Type_checker.file_diagnostics module_
  with Not_found -> []

let diagnostics_of session packages =
  List.concat_map
    (fun (_, name) ->
      List.filter_map
        (fun module_ ->
          match diagnostics session module_ with [] -> None | found -> Some (module_, found))
        (package_modules session name))
    packages

let open_session directory =
  if not (Sys.file_exists directory) then Error (directory ^ ": no such directory.")
  else
    match root_of directory with
    | None ->
        Error
          (Printf.sprintf "No `truss.toml` in %s or any directory above it, so it is in no project."
             directory)
    | Some root -> (
        match open_directory root with
        | Error message -> Error message
        | Ok session ->
            Session.touch session;
            (* Before any command holds the session's engine. *)
            Session.fold ~waited_for:true session;
            update session;
            (* The state is written when the command is done, with what the
               command computed, so that a first write holds a whole state. *)
            ignore (Engine.stabilize (Session.engine session));
            Ok (session, target_packages session (relative_to root directory)))

let refresh session =
  match (project session).kind with
  | Worktree _ ->
      update session;
      ignore (Engine.stabilize (Session.engine session))
  | Commit _ | Library | Published -> ()

let save_session = Session.save
let objects_directory () = Session.directory "objects"
let programs_directory () = Session.directory "programs"
let results = Session.results
let flush_store = Session.flush
let sessions = Session.sessions

(* Graph questions. The worktree is checked first, so that every
   definition's results are there to read and to compare; kept results make
   this cheap. *)

let check_all session = ignore (diagnostics_of session (layout_of session).packages)

type dependencies = Session.Graph.dependencies

let dependencies session =
  check_all session;
  Session.Graph.dependencies (Session.engine session)

let reads = Session.Graph.reads
let readers = Session.Graph.readers

let all_declarations session =
  let lay = layout_of session in
  List.concat_map
    (fun (_, name) ->
      List.concat_map
        (fun module_ ->
          try Engine.get (Session.engine session) Resolve.Names.declarations module_ with _ -> [])
        (package_modules session name))
    lay.packages

let matches name path =
  let shown = Path.show path in
  shown = name
  ||
  let n = String.length name and l = String.length shown in
  l > n && String.sub shown (l - n) n = name && (shown.[l - n - 1] = ':' || shown.[l - n - 1] = '.')

let find_definitions session name =
  List.sort_uniq Path.compare
    (List.filter_map
       (fun (d : Resolve.Names.declaration) -> if matches name d.path then Some d.path else None)
       (all_declarations session))

(* Comparing a session with another, such as its base commit's *)

type difference = Session.Graph.difference = Changed | Added | Same

let changes mine theirs =
  check_all mine;
  Session.Graph.changes (Session.engine mine) (Session.engine theirs)

let base_commit session base =
  let root = root session in
  match base with
  | Some revision -> Git.resolve ~directory:root revision
  | None -> (
      match (Git.head ~directory:root, Git.default_branch ~directory:root) with
      | Some head, Some branch -> Git.merge_base ~directory:root head branch
      | Some head, None -> Some head
      | None, _ -> None)

let open_commit_of session commit = open_commit ~repository:(root session) commit

(* Parallel work *)

type place = Session.Graph.place = { path : Path.t option; part : string option; label : string }

type overlap = Session.Graph.overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }

(* A commit of a worktree's files as they are, for merging. *)
let commit_of_worktree root = Git.snapshot ~directory:root

(* The same project in another worktree is at the same place under its
   worktree's top. *)
let other_worktrees session =
  let root = root session in
  let common = Git.common_directory root and prefix = Git.prefix root in
  List.filter
    (fun other ->
      match Session.attachment other with
      | Project { kind = Worktree other_root; _ } ->
          other_root <> root && common <> None
          && Git.common_directory other_root = common
          && Git.prefix other_root = prefix
      | _ -> false)
    (Session.all ())

let commit_of session =
  match (project session).kind with
  | Worktree root -> Git.head ~directory:root
  | Commit commit -> Some commit.commit
  | Library | Published -> None

let overlap_with session other =
  check_all session;
  check_all other;
  let root = root session in
  match (commit_of session, commit_of other) with
  | Some a, Some b -> (
      match Git.merge_base ~directory:root a b with
      | None -> Error "no common commit."
      | Some base -> (
          match open_commit ~repository:root base with
          | Error message -> Error message
          | Ok base_session ->
              Ok
                (Session.Graph.overlaps ~base:(Session.engine base_session) (Session.engine session)
                   (Session.engine other))))
  | _ -> Error "not a git worktree."

(* A session that starts from another's state, with other files: some of
   its files replaced, added, or, with [None], removed. It shares with the
   session everything but what the change reaches, and is never saved, so a
   change, such as a rename or another lock file, is tried before any file
   is written. *)
let trial_over session (files : Files.t) =
  let trial = Session.trial session in
  attach_project trial ~kind:(project session).kind files;
  update trial;
  ignore (Engine.stabilize (Session.engine trial));
  trial

let trial session changes = trial_over session (Files.with_changes (project session).files changes)

(* The standard library as a state of its own *)

let library_prefix = Printf.sprintf "library-%s-" (String.sub Compiler_version.digest 0 16)
let () = Session.trust Compiler_version.digest

(* The inputs of the [standard] package, set from sources: each module's
   text, and the package with its modules. The text of a module that the
   state holds and the sources do not is removed. *)
let set_library (modules : (Path.module_ * string) list) session =
  let engine = Session.engine session in
  (match read (Engine.context engine) Workspace.packages Path.standard_package with
  | Some (package : Workspace.package) ->
      List.iter
        (fun module_ ->
          if not (List.mem_assoc module_ modules) then
            Engine.remove engine Workspace.file_text module_)
        package.modules
  | None -> ());
  load_package ~usize_bits:64 engine ~name:Path.standard_package ~dependencies:[] modules

let open_library ?(modules = Standard_library.modules) name =
  match
    Session.open_ ~key:("library:" ^ name) ~pointer:(library_prefix ^ name)
      ~version:Compiler_version.digest
      ~bases:(fun () -> [])
      ~fingerprints:(fun () -> [])
      ()
  with
  | Error () -> Error (Printf.sprintf "The library state `%s` is open in another process." name)
  | Ok (session, _) ->
      Session.attach session
        (Project
           {
             kind = Library;
             update = set_library modules;
             files = Files.of_texts [];
             problems = [];
             lock_fix = None;
             applied = true;
           });
      (* A process that opens the state pays its size already, so this is
         when its differences are folded into one whole state. *)
      Session.fold session;
      update session;
      Ok session

(* Choosing versions *)

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

let project_manifests session =
  List.filter_map
    (fun (_, name) -> read (Engine.context (Session.engine session)) Workspace.packages name)
    (layout_of session).packages

(* The lock file a project would have with some packages at other versions:
   each of [set] at the version given, or at its newest, and with [all],
   every registry package of the build at its newest. The other versions
   follow as a build's do. *)
let plan_lock session ~set ~all =
  match Registry.Index.current () with
  | None ->
      Error (Printf.sprintf "No registry is set: `%s` names its directory." Registry.Index.variable)
  | Some registry -> (
      let before =
        try
          Registry.Lock.parse
            (Option.value ~default:"" (read (Engine.context (Session.engine session)) lock_text ()))
        with Registry.Lock.Malformed _ -> []
      in
      let set =
        set
        @
        if all then
          List.filter_map
            (fun (name, _, _) -> if List.mem_assoc name set then None else Some (name, None))
            (layout_of session).registry
        else []
      in
      let wanted =
        List.map
          (fun (name, version) ->
            match version with
            | None -> (
                match Registry.Index.newest registry name with
                | Some (version, hash) -> Ok (name, version, hash)
                | None -> Error (Printf.sprintf "The registry has no package `%s`." name))
            | Some version -> (
                match Registry.Index.hash_of registry name version with
                | Some hash -> Ok (name, version, hash)
                | None ->
                    Error
                      (Printf.sprintf "The registry has no `%s` %s." name
                         (Registry.Version.show version))))
          set
      in
      match List.find_map (function Error message -> Some message | Ok _ -> None) wanted with
      | Some message -> Error message
      | None ->
          let wanted = List.filter_map Result.to_option wanted in
          let lock =
            List.map
              (fun (name, version, hash) -> { Registry.Lock.name; version; hash; holds = [] })
              wanted
            @ List.filter
                (fun (entry : Registry.Lock.entry) ->
                  not (List.exists (fun (name, _, _) -> name = entry.name) wanted))
                before
          in
          let manifests = project_manifests session in
          let local name =
            List.exists (fun (package : Workspace.package) -> package.name = name) manifests
          in
          let packages = Session.directory "packages" in
          let selected, problems =
            Registry.Selection.choose ~lock
              ~roots:
                (List.concat_map
                   (fun (package : Workspace.package) ->
                     List.filter_map
                       (fun (dependency : Workspace.dependency) ->
                         match Path.package_parts dependency.package with
                         | [ _; _ ] -> Some (package.name, dependency.package)
                         | _ -> None)
                       package.dependencies)
                   manifests)
              ~local
              ~load:(fun name version ~hash ->
                Result.map
                  (fun found -> (found.manifest, found.record))
                  (load_published ~packages name version ~hash))
          in
          if problems <> [] then
            Error (String.concat " " (List.map Registry.Selection.sentence problems))
          else
            let after =
              Registry.Selection.lock
                ~project:
                  (List.concat_map
                     (fun (package : Workspace.package) -> package.dependencies)
                     manifests)
                selected
            in
            Ok { text = Registry.Lock.print after; before; after })

(* A published package at a version, as a session of its own with the
   packages it was published with, for comparing a release with it. Its
   files in the store are a project of one package, whose lock file names
   those packages. *)
let published name version =
  match
    Option.bind (Registry.Index.current ()) (fun registry ->
        Registry.Index.hash_of registry name version)
  with
  | None ->
      Error (Printf.sprintf "The registry has no `%s` %s." name (Registry.Version.show version))
  | Some hash -> (
      let cannot reason =
        Error
          (Printf.sprintf "`%s` %s cannot be read: %s." name (Registry.Version.show version) reason)
      in
      match load_published ~packages:(Session.directory "packages") name version ~hash with
      | Error reason -> cannot reason
      | Ok _ -> (
          let directory = Filename.concat (Session.directory "packages") hash in
          let key = Printf.sprintf "published:%s:%s" name hash in
          match open_files ~key ~kind:Published (Files.of_directory directory) with
          | Error () -> cannot "its state is open in another process"
          | Ok session -> (
              update session;
              ignore (Engine.stabilize (Session.engine session));
              match problems session with [] -> Ok session | problem :: _ -> cannot problem)))

let code_packages session name =
  try Engine.get (Session.engine session) Type_checker.code_packages name with Not_found -> []

(* The diagnostics of a merge of two commits that neither has. *)
let merge_preview session other =
  let root = root session in
  let snapshot session =
    match (project session).kind with
    | Worktree root -> commit_of_worktree root
    | Commit commit -> Some commit.commit
    | Library | Published -> None
  in
  match (snapshot session, snapshot other) with
  | None, _ | _, None -> Error "cannot make commits to merge."
  | Some mine, Some theirs -> (
      match Git.merged_files ~directory:root mine theirs with
      | None -> Error "the two do not merge without a textual conflict."
      | Some texts ->
          let merged = trial_over session (Files.of_texts texts) in
          let keys s =
            List.concat_map
              (fun (m, ds) ->
                List.map (fun (d : Diagnostic.t) -> (m, Diagnostic.Code.name d.code, d.message)) ds)
              (diagnostics_of s (layout_of s).packages)
          in
          let sides =
            List.concat_map
              (fun commit ->
                match open_commit ~repository:root commit with
                | Ok side -> keys side
                | Error _ -> [])
              [ mine; theirs ]
          in
          Ok
            (List.filter_map
               (fun ((m, code, message) as key) ->
                 if List.mem key sides then None else Some (module_file merged m, code, message))
               (List.sort_uniq compare (keys merged))))

let recovering = Session.recovering
let reset = Session.reset

(* The background process *)

(* Watching: each open worktree's file stamps are checked every second while
   no request is waiting, so that results are current before they are asked
   for. A request scans again before it is answered, so it always sees every
   change made before it. *)
let watch () =
  List.iter
    (fun session ->
      match Session.attachment session with
      | Project { kind = Worktree _; _ } -> (
          try
            update session;
            ignore (Session.stabilize session)
          with _ -> ())
      | _ -> ())
    (Session.all ())

(* The standard library's state is kept when the store is collected. *)
let kept () =
  let identity = Session.identity () in
  Option.to_list
    (Option.map
       (fun artifact -> (identity, artifact))
       (Session.find_result ~kind:"package" ~key:(standard_key identity)))

let serve ~handle = Session.Server.serve ~idle:watch ~keep:kept ~handle
let call = Session.Server.call
let stop = Session.Server.stop
let store_directory = Session.Server.store_directory

(* For tests *)

module Testing = struct
  let engine = Session.engine
  let logging = Session.logging
  let standard_base = standard_base

  let session_engine directory =
    Option.bind (root_of directory) (fun root -> Option.map Session.engine (Session.find root))
end
