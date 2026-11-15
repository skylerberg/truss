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

let manifest_text ~name ~(dependencies : Manifest.dependency list) =
  String.concat ""
    ([
       Printf.sprintf "[package]\nname = %S\ntruss = %S\n" (Path.show_package name)
         Manifest.truss_version;
       (if dependencies = [] then "" else "\n[dependencies]\n");
     ]
    @ List.map
        (fun (dependency : Manifest.dependency) ->
          Printf.sprintf "%S = [%s]\n"
            (Path.show_package dependency.package)
            (String.concat ", " (List.map (Printf.sprintf "%S") dependency.capabilities)))
        dependencies)

let set_package engine ~root ~name ~dependencies (files : (Path.file * string) list) =
  set_root engine root
    (("truss.toml", manifest_text ~name ~dependencies)
    :: List.map (fun (file, text) -> (Project.file_path ~directory:"" file, text)) files);
  add_root engine root

let load_package engine ~name ~dependencies files =
  set_package engine ~root:(Project.package_root name) ~name ~dependencies files

let set_standard engine files =
  set_package engine
    ~root:(Project.package_root Path.standard_package)
    ~name:Path.standard_package ~dependencies:[] files

let standard_files = ref Standard_library.files
let load_standard engine = set_standard engine !standard_files

let check_standard engine =
  load_standard engine;
  let rendered =
    List.concat_map
      (fun (file, _) ->
        match Engine.get engine Checks.file_diagnostics file with
        | [] -> []
        | diagnostics ->
            let source = Engine.get engine Packages.source file in
            List.map (Diagnostic.render source) diagnostics)
      !standard_files
  in
  if rendered <> [] then
    Compiler_bug.bug ~stage:"Database" "the standard library has diagnostics:\n%s"
      (String.concat "" rendered)

let standard_base () =
  let engine = Engine.create () in
  check_standard engine;
  Engine.freeze ~fixed:true engine;
  engine

let stamps : (string, string) Query.input = Query.input ~name:"worktree_stamp" ~show:Fun.id ()

type kind = Worktree of string | Commit of string | Library | Published
type project = { kind : kind; update : Session.t -> unit; files : Files.t; mutable retried : bool }
type Session.attachment += Project of project
type session = Session.t

let project session =
  match Session.attachment session with
  | Project project -> project
  | _ -> Compiler_bug.bug ~stage:"Database" "a session with no project"

let standard_key identity =
  let sources =
    Registry.Content.hash
      (List.map (fun (file, text) -> (Project.file_path ~directory:"" file, text)) !standard_files)
  in
  Cbor.encode (Cbor.Array [ Cbor.Text identity; Cbor.Text "standard"; Cbor.Text sources ])

let stored_standard () =
  let store = Session.store () and identity = Session.identity () in
  let stored =
    Option.bind
      (Store.find_result store ~kind:Store.Package_state ~key:(standard_key identity))
      (Engine.open_base store ~version:identity ~bases:[])
  in
  match stored with
  | Some base when Engine.inputs_stored base -> base
  | Some _ | None ->
      let engine = Engine.create () in
      Engine.attach engine store ~version:identity;
      check_standard engine;
      Store.add_result store ~kind:Store.Package_state ~key:(standard_key identity)
        (Engine.write ~full:true ~stores_every_value:true engine);
      Engine.freeze ~fixed:true engine;
      engine

let standard : Engine.t Lazy.t ref = ref (lazy (stored_standard ()))
let () = Session.on_close (fun () -> standard := lazy (stored_standard ()))
let prepare_store () = ignore (Lazy.force !standard)

let session_name root =
  Printf.sprintf "session-%s-%s"
    (Session.Identity.short (Session.identity ()))
    (Blake3.hex_digest ~digits:16 root)

let demand session query key = Query.demand (Session.context session) query key
let own_layout session = demand session Project.layout Project.Project

let held_files session =
  Option.value (Query.find (Session.observer session) Project.tree Project.Project) ~default:[]

let fetch name version ~hash =
  let packages = Session.directory "packages" in
  let directory = Filename.concat packages hash in
  if Sys.file_exists directory then Ok directory
  else
    match Registry.Index.current () with
    | Some registry -> Registry.Index.fetch registry ~into:packages name version ~hash
    | None ->
        Error
          (Printf.sprintf "no registry is set; set `%s` to the registry's directory"
             Registry.Index.variable)

let load_published name version ~hash =
  match fetch name version ~hash with
  | Error reason -> Error reason
  | Ok directory ->
      let files = Registry.Content.all_files directory in
      Registry.Selection.manifest_and_record ~read:(fun file -> List.assoc_opt file files) name

let resolve_registry session ~before =
  let engine = Session.engine session in
  let project = project session in
  let selection () = demand session Project.selection () in
  if not project.retried then begin
    List.iter (fun hash -> Engine.remove engine Project.unavailable hash) (selection ()).failed;
    project.retried <- true
  end;
  let rec fetch_missing () =
    match (selection ()).missing with
    | [] -> ()
    | missing ->
        List.iter
          (fun (name, version, hash) ->
            match fetch name version ~hash with
            | Ok directory ->
                set_root engine (Project.Registry hash) (Registry.Content.all_files directory)
            | Error reason -> Engine.set engine Project.unavailable hash reason)
          missing;
        fetch_missing ()
  in
  fetch_missing ();
  let selected = demand session Project.registry () in
  List.iter
    (fun ((_, _, hash) as was) ->
      if not (List.mem was selected) then begin
        let root = Project.Registry hash in
        let files =
          Option.value (Query.find (Session.observer session) Project.tree root) ~default:[]
        in
        List.iter (fun path -> Engine.remove engine Project.text (root, path)) files;
        Engine.remove engine Project.tree root
      end)
    before

let scan (files : Files.t) session =
  let engine = Session.engine session in
  let observer = Session.observer session in
  let before = demand session Project.registry () in
  let was = held_files session in
  let was_files = (own_layout session).files in
  let present = Hashtbl.create 64 in
  List.iter
    (fun (path, stamp) ->
      match Query.find observer stamps path with
      | Some old when old = stamp -> Hashtbl.replace present path ()
      | _ -> (
          match files.read path with
          | Some text ->
              Hashtbl.replace present path ();
              Engine.set engine Project.text (Project.Project, path) text;
              Engine.set engine stamps path stamp;
              Session.note_file session path (Some (Session.fingerprint text))
          | None -> ()))
    (files.list ());
  List.iter
    (fun path ->
      if not (Hashtbl.mem present path) then begin
        Engine.remove engine Project.text (Project.Project, path);
        Engine.remove engine stamps path;
        Session.note_file session path None;
        match
          List.find_opt (fun (source : Project.source_file) -> source.path = path) was_files
        with
        | Some source -> Engine.unroot engine Checks.file_diagnostics source.file
        | None -> ()
      end)
    was;
  Engine.set engine Project.tree Project.Project
    (List.sort compare (Hashtbl.fold (fun path () paths -> path :: paths) present []));
  Engine.set engine Project.roots () [ Project.Standard; Project.Project ];
  resolve_registry session ~before

let fingerprints (files : Files.t) () =
  List.filter_map
    (fun (path, _) -> Option.map (fun text -> (path, Session.fingerprint text)) (files.read path))
    (files.list ())

let attach_project session ~kind (files : Files.t) =
  Session.attach session (Project { kind; update = scan files; files; retried = false })

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
    (open_files ~key:(Session.Worktree root) ~pointer:(session_name root) ~home:root
       ~kind:(Worktree root) (Files.of_directory root))

let open_commit ~repository commit =
  let key = Session.Commit { repository; commit } in
  match Session.find key with
  | Some session -> Ok session
  | None -> (
      match Files.of_commit ~directory:repository commit with
      | None -> Error (Printf.sprintf "cannot read commit %s." commit)
      | Some files -> (
          match open_files ~key ~kind:(Commit commit) files with
          | Ok session ->
              update session;
              ignore (Engine.stabilize (Session.engine session));
              Ok session
          | Error () -> Error (Printf.sprintf "cannot open commit %s." commit)))

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

let packages session =
  List.map
    (fun (directory, (package : Manifest.package)) -> (directory, package.name))
    (own_layout session).packages

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

let package_files session name =
  match Query.demand (Session.context session) Project.package name with
  | Some package -> package.files
  | None -> []

let root session =
  match (project session).kind with
  | Worktree root -> root
  | Commit _ | Library | Published ->
      Compiler_bug.bug ~stage:"Database" "only a worktree's session has a root"

let context session = Session.context session
let set = Session.set
let problems session = demand session Project.problems ()

let manifest_problems session names =
  List.concat_map
    (fun (directory, name) ->
      if not (List.mem name names) then []
      else
        List.map
          (fun problem -> (Project.manifest_file directory, name, problem))
          (try Engine.get (Session.engine session) Checks.manifest_problems name
           with Not_found -> []))
    (packages session)

let file_path session (file : Path.file) =
  match demand session Project.place file.module_.package with
  | Some { root; directory; _ } when root = Project.Project -> Project.file_path ~directory file
  | _ -> Path.show_file file

let time_limit_ms session = (own_layout session).time_limit_ms
let registry_packages session = demand session Project.registry ()
let lock_fix session = (demand session Project.selection ()).lock_fix

let diagnostics session file =
  try Engine.get (Session.engine session) Checks.file_diagnostics file with Not_found -> []

let diagnostics_of session packages =
  List.concat_map
    (fun (_, name) ->
      List.filter_map
        (fun file ->
          match diagnostics session file with
          | [] -> None
          | file_diagnostics -> Some (file, file_diagnostics))
        (package_files session name))
    packages

let opened = ref []

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
            Session.compact ~waited_for:true session;
            update session;
            ignore (Engine.stabilize (Session.engine session));
            if not (List.memq session !opened) then opened := session :: !opened;
            Ok (session, target_packages session (relative_to root directory)))

let refresh session =
  match (project session).kind with
  | Worktree _ ->
      update session;
      ignore (Engine.stabilize (Session.engine session))
  | Commit _ | Library | Published -> ()

let save_session = Session.save
let objects_directory () = Session.cache_directory "objects"
let programs_directory () = Session.directory "programs"
let results = Session.results
let flush_store = Session.flush

let save_opened () =
  List.iter Session.save !opened;
  opened := [];
  Session.flush ()

let sessions () =
  List.map (fun (key, results) -> (Session.show_key key, results)) (Session.sessions ())

let check_all session = ignore (diagnostics_of session (packages session))

let after_checking question session paths =
  check_all session;
  question (Session.engine session) paths

let dependencies = after_checking Session.Graph.dependencies
let dependents = after_checking Session.Graph.dependents
let reachable = after_checking Session.Graph.reachable

let all_declarations session =
  List.concat_map
    (fun (_, name) ->
      List.concat_map
        (fun module_ ->
          try Query.demand (Session.observer session) Resolve.Names.declarations module_
          with _ -> [])
        (package_modules session name))
    (packages session)

let ends_path name shown =
  shown = name
  ||
  let name_length = String.length name and shown_length = String.length shown in
  shown_length > name_length
  && String.sub shown (shown_length - name_length) name_length = name
  && (shown.[shown_length - name_length - 1] = ':' || shown.[shown_length - name_length - 1] = '.')

let matches name (path : Path.t) =
  ends_path name (Path.show path)
  ||
  match path with
  | Method method_ -> ends_path name (Path.show (Method { method_ with receiver = Read }))
  | _ -> false

let find_definitions session name =
  List.sort_uniq Path.compare
    (List.filter_map
       (fun (candidate : Resolve.Names.declaration) ->
         if matches name candidate.path then Some candidate.path else None)
       (all_declarations session))

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
let commit_of_worktree root = Git.snapshot ~directory:root
let git_places : (string, string option * string option) Hashtbl.t = Hashtbl.create 8

let git_place root =
  match Hashtbl.find_opt git_places root with
  | Some place -> place
  | None ->
      let place = (Git.common_directory root, Git.prefix root) in
      Hashtbl.replace git_places root place;
      place

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
            Session.key other = Session.Worktree other_root && same_project other_root
        | _ -> false)
      (Session.all ())
  in
  let held = List.map Session.key open_here in
  let served =
    List.filter_map
      (fun (other_root, name) ->
        if
          List.mem (Session.Worktree other_root) held
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
            (Session.snapshot ~key:(Session.Snapshot other_root) ~pointer:name
               ~version:(Session.identity ()) ~bases:(fun () -> [ Lazy.force !standard ])))
      (List.sort_uniq compare (Session.homes ()))
  in
  open_here @ served

let commit_of session =
  match (project session).kind with
  | Worktree root -> Git.head ~directory:root
  | Commit commit -> Some commit
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

let trial_over session (files : Files.t) =
  let trial = Session.trial session in
  attach_project trial ~kind:(project session).kind files;
  update trial;
  ignore (Engine.stabilize (Session.engine trial));
  trial

let trial session changes = trial_over session (Files.with_changes (project session).files changes)
let library_prefix = Printf.sprintf "library-%s-" (String.sub Compiler_version.digest 0 16)
let () = Session.allow_reading Compiler_version.digest

let set_library (files : (Path.file * string) list) session =
  set_standard (Session.engine session) files

let open_library ?(files = !standard_files) name =
  match
    Session.open_ ~key:(Session.Library name) ~pointer:(library_prefix ^ name)
      ~version:Compiler_version.digest
      ~bases:(fun () -> [])
      ~fingerprints:(fun () -> [])
      ()
  with
  | Error () -> Error (Printf.sprintf "The library state `%s` is open in another process." name)
  | Ok (session, _) ->
      Session.attach session
        (Project
           { kind = Library; update = set_library files; files = Files.of_texts []; retried = true });
      Session.compact session;
      update session;
      Ok session

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

let project_manifests session =
  List.filter_map
    (fun (_, name) -> Query.demand (Session.context session) Project.package name)
    (packages session)

let plan_lock session ~set ~all =
  match Registry.Index.current () with
  | None ->
      Error
        (Printf.sprintf "No registry is set. Set `%s` to the registry's directory."
           Registry.Index.variable)
  | Some registry -> (
      let before =
        try
          Registry.Lock.parse
            (Option.value ~default:""
               (Query.find (Session.observer session) Project.text
                  (Project.Project, Project.lock_file)))
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
          let key = Session.Published { package = name; hash } in
          match open_files ~key ~kind:Published (Files.of_directory directory) with
          | Error () -> cannot "its state is open in another process"
          | Ok session -> (
              update session;
              ignore (Engine.stabilize (Session.engine session));
              match problems session with
              | [] -> Ok session
              | problem :: _ -> cannot (Project.show_problem problem))))

let code_packages session name =
  try Engine.get (Session.engine session) Checks.code_packages name with Not_found -> []

type merge_diagnostic = { path : string; diagnostic : Diagnostic.t }

let merge_preview session other =
  let root = root session in
  let snapshot session =
    match (project session).kind with
    | Worktree root -> commit_of_worktree root
    | Commit commit -> Some commit
    | Library | Published -> None
  in
  match (snapshot session, snapshot other) with
  | None, _ | _, None -> Error "cannot make commits to merge."
  | Some mine, Some theirs -> (
      match Git.merged_files ~directory:root mine theirs with
      | None -> Error "the two do not merge without a textual conflict."
      | Some texts ->
          let merged = trial_over session (Files.of_texts texts) in
          let keyed_diagnostics session =
            List.concat_map
              (fun (file, diagnostics) ->
                List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    ((file, Diagnostic.Code.name diagnostic.code, diagnostic.message), diagnostic))
                  diagnostics)
              (diagnostics_of session (packages session))
          in
          let sides =
            List.concat_map
              (fun commit ->
                match open_commit ~repository:root commit with
                | Ok side -> List.map fst (keyed_diagnostics side)
                | Error _ -> [])
              [ mine; theirs ]
          in
          Ok
            (List.filter_map
               (fun (((file, _, _) as key), diagnostic) ->
                 if List.mem key sides then None
                 else Some { path = file_path merged file; diagnostic })
               (List.sort_uniq
                  (fun (left, _) (right, _) -> compare left right)
                  (keyed_diagnostics merged))))

let recovering = Session.recovering
let reset = Session.reset

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

let standard_artifacts () =
  let identity = Session.identity () in
  Option.to_list
    (Option.map
       (fun artifact -> (identity, artifact))
       (Session.find_result ~kind:Store.Package_state ~key:(standard_key identity)))

let server_key directory = Option.value (root_of directory) ~default:""

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

module For_testing = struct
  let prepare_store = prepare_store
  let open_library = open_library

  let set_text engine (file : Path.file) text =
    let root = Project.package_root file.module_.package in
    let path = Project.file_path ~directory:"" file in
    Engine.set engine Project.text (root, path) text;
    let files = Option.value (Query.find (Engine.observer engine) Project.tree root) ~default:[] in
    if not (List.mem path files) then
      Engine.set engine Project.tree root (List.sort compare (path :: files))

  let set_manifest engine ~name ~dependencies =
    let root = Project.package_root name in
    Engine.set engine Project.text (root, "truss.toml") (manifest_text ~name ~dependencies);
    let files = Option.value (Query.find (Engine.observer engine) Project.tree root) ~default:[] in
    if not (List.mem "truss.toml" files) then
      Engine.set engine Project.tree root (List.sort compare ("truss.toml" :: files));
    add_root engine root

  let engine = Session.engine
  let logging = Session.logging
  let standard_base = standard_base

  let use_standard files =
    standard_files := files;
    standard := lazy (stored_standard ())

  let session_base () = Lazy.force !standard
  let collect_store () = Session.collect ~keep:(fun () -> [])

  let session_engine directory =
    Option.bind (root_of directory) (fun root ->
        Option.map Session.engine (Session.find (Session.Worktree root)))
end
