(* Setting a root's files as inputs *)

(* Replaces a root's files: each one's path and text. *)
let set_root engine root (files : (string * string) list) =
  let old = Option.value (Query.find (Engine.observer engine) Project.tree root) ~default:[] in
  List.iter
    (fun path ->
      if not (List.mem_assoc path files) then Engine.remove engine Project.text (root, path))
    old;
  List.iter (fun (path, text) -> Engine.set engine Project.text (root, path) text) files;
  Engine.set engine Project.tree root (List.sort compare (List.map fst files))

let add_root engine root =
  let roots = Option.value (Query.find (Engine.observer engine) Project.roots ()) ~default:[] in
  if not (List.mem root roots) then Engine.set engine Project.roots () (roots @ [ root ])

(* A manifest of one package, as [Manifest.parse] reads it. *)
let manifest_text ~usize_bits ~name ~(dependencies : Manifest.dependency list) =
  String.concat ""
    ([
       Printf.sprintf "[package]\nname = %S\ntruss = %S\n" (Path.show_package name)
         Manifest.truss_version;
       (if usize_bits = 64 then "usize_bits = 64\n" else "");
       (if dependencies = [] then "" else "\n[dependencies]\n");
     ]
    @ List.map
        (fun (dependency : Manifest.dependency) ->
          Printf.sprintf "%S = [%s]\n"
            (Path.show_package dependency.package)
            (String.concat ", " (List.map (Printf.sprintf "%S") dependency.capabilities)))
        dependencies)

(* A package given by itself, as a root of its own: its manifest and its
   modules' files. *)
let set_package engine ~root ~usize_bits ~name ~dependencies
    (modules : (Path.module_ * string) list) =
  set_root engine root
    (("truss.toml", manifest_text ~usize_bits ~name ~dependencies)
    :: List.map (fun (module_, text) -> (Project.module_path ~directory:"" module_, text)) modules);
  add_root engine root

let load_package ?(usize_bits = 32) engine ~name ~dependencies modules =
  set_package engine ~root:(Project.package_root name) ~usize_bits ~name ~dependencies modules

(* The standard library holds the code for each platform, and its bounds of
   [USize] are its target's, so it is checked with the target's width. *)
let set_standard engine modules =
  set_package engine ~root:Project.standard_root ~usize_bits:64 ~name:Path.standard_package
    ~dependencies:[] modules

let load_standard engine = set_standard engine Standard_library.modules

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

(* Each file's stamp, by its path: what says, without reading the file,
   that it has not changed. A restart reads only the files whose stamps
   changed. *)
let stamps : (string, string) Query.input = Query.input ~name:"worktree_stamp" ~show:Fun.id ()

(* What a session's files are, for what is asked of git. *)
type kind =
  | Worktree of string  (** A project's root *)
  | Commit of { repository : string; commit : string }
  | Library  (** The standard library as a state of its own *)
  | Published  (** A published package with the packages it was published with *)

(* The database's state for a session of the session layer. *)
type project = {
  kind : kind;
  update : Session.t -> unit;  (** Brings the inputs in line with the session's files *)
  files : Files.t;
  mutable retried : bool;
      (** Whether this process has tried again to fetch the packages that could not be had *)
}

type Session.attachment += Project of project
type session = Session.t

let project session =
  match Session.attachment session with
  | Project project -> project
  | _ -> Compiler_bug.bug ~stage:"Database" "a session with no project"

(* A package whose sources never change is checked once, written whole, and
   found from then on by the key of its sources: for the standard library,
   which is built into the compiler, the compiler's identity. *)
let standard_key identity = Cbor.encode (Cbor.Array [ Cbor.Text identity; Cbor.Text "standard" ])

let stored_standard () =
  let store = Session.store () and identity = Session.identity () in
  let stored =
    Option.bind
      (Store.find_result store ~kind:"package" ~key:(standard_key identity))
      (Engine.open_base store ~version:identity ~bases:[])
  in
  match stored with
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
    (Blake3.hex_digest ~digits:16 root)

let demand session query key = Query.demand (Session.context session) query key
let own_layout session = demand session Project.layout Project.project_root

(* The project's files that are inputs now. *)
let held_files session =
  Option.value (Query.find (Session.observer session) Project.tree Project.project_root) ~default:[]

(* A published package's directory in the store, fetched into it from the
   registry if it is not there yet. *)
let fetch name version ~hash =
  let packages = Session.directory "packages" in
  let directory = Filename.concat packages hash in
  if Sys.file_exists directory then Ok directory
  else
    match Registry.Index.current () with
    | Some registry -> Registry.Index.fetch registry ~into:packages name version ~hash
    | None ->
        Error
          (Printf.sprintf "no registry is set: `%s` names its directory" Registry.Index.variable)

(* A published package's manifest and record, for planning a lock file. *)
let load_published name version ~hash =
  match fetch name version ~hash with
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
          Ok (manifest, record)
      | _ ->
          Error
            (Printf.sprintf "its manifest does not name the package `%s`" (Path.show_package name)))

(* Gives the build the files of the registry packages it selects. Which
   those are is a query, which names each package whose files are not
   inputs yet; this fetches them and sets them, which reaches the query, and
   asks again, since a package's record can name more. A package's files
   never change, so they are set once, and removed when the build no longer
   selects the package. *)
let resolve_registry session ~before =
  let engine = Session.engine session in
  let project = project session in
  let selection () = demand session Project.selection () in
  if not project.retried then begin
    List.iter (fun hash -> Engine.remove engine Project.unavailable hash) (selection ()).failed;
    project.retried <- true
  end;
  let rec fetch_missing rounds =
    match (selection ()).missing with
    | [] -> ()
    | missing when rounds > 0 ->
        List.iter
          (fun (name, version, hash) ->
            match fetch name version ~hash with
            | Ok directory ->
                set_root engine (Project.registry_root hash)
                  (Registry.Content.files ~all:true directory)
            | Error reason -> Engine.set engine Project.unavailable hash reason)
          missing;
        fetch_missing (rounds - 1)
    | _ -> ()
  in
  fetch_missing 64;
  let selected = demand session Project.registry () in
  List.iter
    (fun ((_, _, hash) as was) ->
      if not (List.mem was selected) then begin
        let root = Project.registry_root hash in
        let files =
          Option.value (Query.find (Session.observer session) Project.tree root) ~default:[]
        in
        List.iter (fun path -> Engine.remove engine Project.text (root, path)) files;
        Engine.remove engine Project.tree root
      end)
    before

(* Brings a session's inputs in line with its files: reads the files whose
   stamps changed, and sets each one's text, by its path. Everything else
   about the project follows from those as queries. A file that cannot be
   read, such as one deleted since its directory was listed, is not there.
   A stamp is set with its file's text, so a scan that fails leaves the
   file to be read by the next. *)
let scan (files : Files.t) session =
  let engine = Session.engine session in
  let observer = Session.observer session in
  let before = demand session Project.registry () in
  let was = held_files session in
  let was_modules = (own_layout session).modules in
  let present = Hashtbl.create 64 in
  List.iter
    (fun (path, stamp) ->
      match Query.find observer stamps path with
      | Some old when old = stamp -> Hashtbl.replace present path ()
      | _ -> (
          match files.read path with
          | Some text ->
              Hashtbl.replace present path ();
              Engine.set engine Project.text (Project.project_root, path) text;
              Engine.set engine stamps path stamp;
              Session.note_file session path (Some (Session.fingerprint text))
          | None -> ()))
    (files.list ());
  List.iter
    (fun path ->
      if not (Hashtbl.mem present path) then begin
        Engine.remove engine Project.text (Project.project_root, path);
        Engine.remove engine stamps path;
        Session.note_file session path None;
        (* A module that is gone has no diagnostics to maintain, so they
           are no longer a root. *)
        match List.find_opt (fun (file, _, _) -> file = path) was_modules with
        | Some (_, _, module_) -> Engine.unroot engine Type_checker.file_diagnostics module_
        | None -> ()
      end)
    was;
  Engine.set engine Project.tree Project.project_root
    (List.sort compare (Hashtbl.fold (fun path () paths -> path :: paths) present []));
  Engine.set engine Project.roots () [ Project.standard_root; Project.project_root ];
  resolve_registry session ~before

(* Each file's fingerprint, by which the saved state nearest to a set of
   files is found. *)
let fingerprints (files : Files.t) () =
  List.filter_map
    (fun (path, _) -> Option.map (fun text -> (path, Session.fingerprint text)) (files.read path))
    (files.list ())

let attach_project session ~kind (files : Files.t) =
  Session.attach session (Project { kind; update = scan files; files; retried = false })

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
            List.iter (fun path -> Session.remove session stamps path) (held_files session);
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
    if String.starts_with ~prefix directory then
      String.sub directory (String.length prefix) (String.length directory - String.length prefix)
    else ""

(* Every package of the project: its directory and its name. *)
let packages session =
  List.map
    (fun (directory, (package : Manifest.package)) -> (directory, package.name))
    (own_layout session).packages

(* The packages a request in a directory is about: those at or under it, or
   the one it is in. *)
let target_packages session requested =
  let packages = packages session in
  let under (directory, _) =
    requested = "" || directory = requested
    || String.starts_with ~prefix:(requested ^ "/") directory
  in
  match List.filter under packages with
  | [] -> (
      match
        Project.package_directory
          ~is_package:(fun candidate -> List.mem_assoc candidate packages)
          requested
      with
      | Some directory -> List.filter (fun (candidate, _) -> candidate = directory) packages
      | None -> [])
  | under_requested -> under_requested

let package_modules session name =
  match Query.demand (Session.context session) Project.package name with
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
let problems session = demand session Project.problems ()

(* What only a package's code shows to be wrong with its manifest, which
   checks the package. *)
let manifest_problems session names =
  List.concat_map
    (fun (directory, name) ->
      if not (List.mem name names) then []
      else
        List.map
          (fun problem -> (Project.manifest_file directory, name, problem))
          (try Engine.get (Session.engine session) Type_checker.manifest_problems name
           with Not_found -> []))
    (packages session)

(* A module's file, from the project's root: where it is, or for a module
   the project does not have, where it would be. *)
let module_file session (module_ : Path.module_) =
  match demand session Project.place module_.package with
  | Some { root; directory; _ } when root = Project.project_root ->
      Project.module_path ~directory module_
  | _ -> Workspace.file_path module_

let time_limit session = (own_layout session).time_limit
let registry_packages session = demand session Project.registry ()
let lock_fix session = (demand session Project.selection ()).lock_fix

let diagnostics session module_ =
  try Engine.get (Session.engine session) Type_checker.file_diagnostics module_
  with Not_found -> []

let diagnostics_of session packages =
  List.concat_map
    (fun (_, name) ->
      List.filter_map
        (fun module_ ->
          match diagnostics session module_ with
          | [] -> None
          | module_diagnostics -> Some (module_, module_diagnostics))
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
            Session.compact ~waited_for:true session;
            update session;
            (* The state is written when the command is done, with the
               command's results, so that a first write holds a whole state. *)
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
   definition's results are there to read and to compare. Each file's
   diagnostics are a root, so this is cheap after the first time. *)

let check_all session = ignore (diagnostics_of session (packages session))

type dependencies = Session.Graph.dependencies

let dependencies session =
  check_all session;
  Session.Graph.dependencies (Session.engine session)

let reads = Session.Graph.reads
let readers = Session.Graph.readers

let all_declarations session =
  List.concat_map
    (fun (_, name) ->
      List.concat_map
        (fun module_ ->
          try Query.demand (Session.observer session) Resolve.Names.declarations module_
          with _ -> [])
        (package_modules session name))
    (packages session)

let matches name path =
  let shown = Path.show path in
  shown = name
  ||
  let name_length = String.length name and shown_length = String.length shown in
  shown_length > name_length
  && String.sub shown (shown_length - name_length) name_length = name
  && (shown.[shown_length - name_length - 1] = ':' || shown.[shown_length - name_length - 1] = '.')

let find_definitions session name =
  List.sort_uniq Path.compare
    (List.filter_map
       (fun (candidate : Resolve.Names.declaration) ->
         if matches name candidate.path then Some candidate.path else None)
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

type place = Session.Graph.place = { path : Path.t option; part : string option; label : string }

type overlap = Session.Graph.overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }

(* A commit of a worktree's files as they are, for merging. *)
let commit_of_worktree root = Git.snapshot ~directory:root

(* Where a root is in git: its repository's common directory, and its
   place under its worktree's top. Neither changes while a process runs. *)
let git_places : (string, string option * string option) Hashtbl.t = Hashtbl.create 8

let git_place root =
  match Hashtbl.find_opt git_places root with
  | Some place -> place
  | None ->
      let place = (Git.common_directory root, Git.prefix root) in
      Hashtbl.replace git_places root place;
      place

(* A snapshot is of the state the background process saves, brought up to
   date with the worktree's files. The same project in another worktree is
   at the same place under its worktree's top. *)
let other_worktrees session =
  let root = root session in
  let common, prefix = git_place root in
  let same_project other_root =
    other_root <> root && common <> None && git_place other_root = (common, prefix)
  in
  let open_here =
    List.filter
      (fun other ->
        match Session.attachment other with
        | Project { kind = Worktree other_root; _ } ->
            Session.key other = other_root && same_project other_root
        | _ -> false)
      (Session.all ())
  in
  let held = List.map Session.key open_here in
  let served =
    List.filter_map
      (fun (other_root, name) ->
        if
          List.mem other_root held
          || (not (same_project other_root))
          || (not (String.equal name (session_name other_root)))
          || (not (Sys.file_exists other_root))
          || not (Session.Server.running other_root)
        then None
        else
          Option.map
            (fun snapshot ->
              attach_project snapshot ~kind:(Worktree other_root) (Files.of_directory other_root);
              update snapshot;
              ignore (Engine.stabilize (Session.engine snapshot));
              snapshot)
            (Session.snapshot ~key:("snapshot:" ^ other_root) ~pointer:name
               ~version:(Session.identity ()) ~bases:(fun () -> [ Lazy.force !standard ])))
      (List.sort_uniq compare (Session.homes ()))
  in
  open_here @ served

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
  | Some left, Some right -> (
      match Git.merge_base ~directory:root left right with
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
   session everything but the change's dependents, and is never saved, so a
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
let () = Session.allow_reading Compiler_version.digest

(* The inputs of the [standard] package, set from sources: its modules'
   files. The file of a module that the sources no longer have is removed. *)
let set_library (modules : (Path.module_ * string) list) session =
  set_standard (Session.engine session) modules

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
             retried = true;
           });
      (* A process that opens the state pays its size already, so this is
         when its differences are folded into one whole state. *)
      Session.compact session;
      update session;
      Ok session

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

let project_manifests session =
  List.filter_map
    (fun (_, name) -> Query.demand (Session.context session) Project.package name)
    (packages session)

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
            (Option.value ~default:""
               (Query.find (Session.observer session) Project.text
                  (Project.project_root, Project.lock_file)))
        with Registry.Lock.Malformed _ -> []
      in
      let set =
        set
        @
        if all then
          List.filter_map
            (fun (name, _, _) -> if List.mem_assoc name set then None else Some (name, None))
            (registry_packages session)
        else []
      in
      let wanted =
        List.map
          (fun (name, version) ->
            match version with
            | None -> (
                match Registry.Index.newest registry name with
                | Some (version, hash) -> Ok (name, version, hash)
                | None ->
                    Error
                      (Printf.sprintf "The registry has no package `%s`." (Path.show_package name)))
            | Some version -> (
                match Registry.Index.hash_of registry name version with
                | Some hash -> Ok (name, version, hash)
                | None ->
                    Error
                      (Printf.sprintf "The registry has no `%s` %s." (Path.show_package name)
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
            List.exists (fun (package : Project.package) -> package.name = name) manifests
          in
          let selected, problems =
            Registry.Selection.choose ~lock
              ~roots:
                (List.concat_map
                   (fun (package : Project.package) ->
                     List.filter_map
                       (fun (dependency : Manifest.dependency) ->
                         match Path.package_parts dependency.package with
                         | [ _; _ ] -> Some (package.name, dependency.package)
                         | _ -> None)
                       package.dependencies)
                   manifests)
              ~local ~load:load_published
          in
          if problems <> [] then
            Error (String.concat " " (List.map Registry.Selection.sentence problems))
          else
            let after =
              Registry.Selection.lock
                ~project:
                  (List.concat_map
                     (fun (package : Project.package) -> package.dependencies)
                     manifests)
                selected
            in
            Ok { text = Registry.Lock.print after; before; after })

(* The package's files in the store are a project of one package, whose
   lock file names the packages it was published with. *)
let published name version =
  match
    Option.bind (Registry.Index.current ()) (fun registry ->
        Registry.Index.hash_of registry name version)
  with
  | None ->
      Error
        (Printf.sprintf "The registry has no `%s` %s." (Path.show_package name)
           (Registry.Version.show version))
  | Some hash -> (
      let cannot reason =
        Error
          (Printf.sprintf "`%s` %s cannot be read: %s." (Path.show_package name)
             (Registry.Version.show version) reason)
      in
      match load_published name version ~hash with
      | Error reason -> cannot reason
      | Ok _ -> (
          let directory = Filename.concat (Session.directory "packages") hash in
          let key = Printf.sprintf "published:%s:%s" (Path.show_package name) hash in
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
          let keys session =
            List.concat_map
              (fun (module_, diagnostics) ->
                List.map
                  (fun (candidate : Diagnostic.t) ->
                    (module_, Diagnostic.Code.name candidate.code, candidate.message))
                  diagnostics)
              (diagnostics_of session (packages session))
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
               (fun ((module_, code, message) as key) ->
                 if List.mem key sides then None
                 else Some (module_file merged module_, code, message))
               (List.sort_uniq compare (keys merged))))

let recovering = Session.recovering
let reset = Session.reset

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
let standard_artifacts () =
  let identity = Session.identity () in
  Option.to_list
    (Option.map
       (fun artifact -> (identity, artifact))
       (Session.find_result ~kind:"package" ~key:(standard_key identity)))

(* What names the background process for a directory: its project's root.
   A directory in no project is served by a process of its own. *)
let server_key directory = Option.value (root_of directory) ~default:""

(* A process serves one project, and ends when the project's directory is
   gone. *)
let serve ~key ~handle =
  Session.Server.serve ~key
    ~alive:(fun () -> key = "" || Sys.file_exists key)
    ~idle:watch ~keep:standard_artifacts ~handle

let call ?program ?start_server ?key ~progress request =
  let key = match key with Some key -> key | None -> server_key (Sys.getcwd ()) in
  Session.Server.call ?program ?start_server ~key ~progress request

let servers = Session.Server.serving
let stop = Session.Server.stop
let store_directory = Session.Server.store_directory

module Testing = struct
  (* Gives one module of a package given by itself another text. *)
  let set_text engine (module_ : Path.module_) text =
    let root = Project.package_root module_.package in
    let path = Project.module_path ~directory:"" module_ in
    Engine.set engine Project.text (root, path) text;
    let files = Option.value (Query.find (Engine.observer engine) Project.tree root) ~default:[] in
    if not (List.mem path files) then
      Engine.set engine Project.tree root (List.sort compare (path :: files))

  (* Gives a package given by itself another manifest, and leaves its
     modules as they are. *)
  let set_manifest ?(usize_bits = 32) engine ~name ~dependencies =
    let root = Project.package_root name in
    Engine.set engine Project.text (root, "truss.toml")
      (manifest_text ~usize_bits ~name ~dependencies);
    let files = Option.value (Query.find (Engine.observer engine) Project.tree root) ~default:[] in
    if not (List.mem "truss.toml" files) then
      Engine.set engine Project.tree root (List.sort compare ("truss.toml" :: files));
    add_root engine root

  let engine = Session.engine
  let logging = Session.logging
  let standard_base = standard_base

  let session_engine directory =
    Option.bind (root_of directory) (fun root -> Option.map Session.engine (Session.find root))
end
