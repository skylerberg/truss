let opened : Store.t option ref = ref None

let store () =
  match !opened with
  | Some store -> store
  | None ->
      let store = Store.open_ (Store.default_directory ()) in
      Store.compact store;
      opened := Some store;
      store

let flush_store () = Option.iter Store.flush !opened

let reset () =
  Option.iter Store.close !opened;
  opened := None

let objects_directory () = Store.cache_files (store ()) "objects"
let programs_directory () = Store.files (store ()) "programs"
let packages_directory () = Store.files (store ()) "packages"
let store_directory = Store.default_directory

let results ~kind =
  let store = store () in
  ( (fun key -> Store.find_result store ~kind ~key),
    fun key value -> Store.add_result store ~kind ~key value )

let budget () =
  match Option.bind (Sys.getenv_opt "TRUSS_CACHE_SIZE") int_of_string_opt with
  | Some bytes -> bytes
  | None -> 20 * 1024 * 1024 * 1024

let collect () =
  let store = store () in
  Store.compact store;
  let lock =
    Unix.openfile
      (Filename.concat (Store.directory store) "collect.lock")
      [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644
  in
  Fun.protect
    ~finally:(fun () -> Unix.close lock)
    (fun () ->
      match Unix.lockf lock F_TLOCK 0 with
      | () -> Store.collect store ~budget:(budget ())
      | exception Unix.Unix_error _ -> ())

type loaded = { package : Path.package; hash : string; key : string; state : Pipeline.state }

let loaded_states : (string, loaded) Hashtbl.t = Hashtbl.create 8

let state_key ~hash ~visible =
  Cbor.encode
    (Cbor.Array
       [
         Cbor.Text Compiler_version.digest;
         Cbor.Text hash;
         Cbor.Array
           (List.map
              (fun { package; hash; _ } ->
                Cbor.Array [ Cbor.Text (Path.show_package package); Cbor.Text hash ])
              visible);
       ])

let exclusively name work =
  let lock =
    Unix.openfile
      (Filename.concat (Store.directory (store ())) name)
      [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644
  in
  Fun.protect
    ~finally:(fun () -> Unix.close lock)
    (fun () ->
      Unix.lockf lock F_LOCK 0;
      work ())

let package_state (package : Project.package) ~hash ~visible =
  let key = state_key ~hash ~visible in
  match Hashtbl.find_opt loaded_states key with
  | Some loaded -> loaded
  | None ->
      let stored () =
        Option.map
          (fun bytes -> (Marshal.from_string bytes 0 : Pipeline.state))
          (Store.find_result (store ()) ~kind:Package_state ~key)
      in
      let state =
        match stored () with
        | Some state -> state
        | None ->
            exclusively "package-states.lock" (fun () ->
                match stored () with
                | Some state -> state
                | None ->
                    let state =
                      Pipeline.state
                        (Pipeline.create
                           ~loaded:(List.map (fun visible -> visible.state) visible)
                           [ package ])
                        package.name
                    in
                    Store.add_result (store ()) ~kind:Package_state ~key
                      (Marshal.to_string state []);
                    Store.flush (store ());
                    state)
      in
      let loaded = { package = package.name; hash; key; state } in
      Hashtbl.replace loaded_states key loaded;
      loaded

let standard_package : Project.package =
  { name = Path.standard_package; dependencies = []; files = Standard_library.files }

let standard_state =
  lazy
    (let standard =
       package_state standard_package ~visible:[]
         ~hash:
           (Registry.Content.hash
              (List.map
                 (fun (file, text) -> (Project.file_path ~directory:"" file, text))
                 Standard_library.files))
     in
     let pipeline = Pipeline.create ~loaded:[ standard.state ] [] in
     let rendered =
       List.concat_map
         (fun ((file : Path.file), text) ->
           match Pipeline.file_diagnostics pipeline file with
           | [] -> []
           | diagnostics ->
               let source = Source.create ~path:(Path.show_file file) text in
               List.map (Diagnostic.render source) diagnostics)
         Standard_library.files
     in
     if rendered <> [] then
       Compiler_bug.bug ~stage:"Database" "the standard library has diagnostics:\n%s"
         (String.concat "" rendered);
     standard)

let states () =
  List.sort compare
    (Hashtbl.fold
       (fun _ { package; hash; _ } lines ->
         Printf.sprintf "%s %s" (Path.show_package package) (String.sub hash 0 16) :: lines)
       loaded_states [])

type kind =
  | Worktree of string
  | Trial of { root : string; pipeline : Pipeline.t Lazy.t }
  | Published

type snapshot = { kind : kind; files : (string * string) list; project : Project.t }

let fetch name version ~hash =
  let packages = packages_directory () in
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

let indexed files =
  let table = Hashtbl.create (List.length files) in
  List.iter (fun (path, text) -> Hashtbl.replace table path text) files;
  (List.sort compare (List.map fst files), table)

let project_of files =
  let own = indexed files in
  let registry = Hashtbl.create 4 and unavailable = Hashtbl.create 4 in
  let root = function
    | Project.Project -> Some own
    | Registry hash -> Hashtbl.find_opt registry hash
  in
  let rec settle () =
    let project =
      Project.of_files
        {
          tree = (fun name -> Option.map fst (root name));
          text =
            (fun name path ->
              Option.bind (root name) (fun (_, texts) -> Hashtbl.find_opt texts path));
          unavailable = Hashtbl.find_opt unavailable;
        }
    in
    match project.selection.missing with
    | [] -> project
    | missing ->
        List.iter
          (fun (name, version, hash) ->
            match fetch name version ~hash with
            | Ok directory ->
                Hashtbl.replace registry hash (indexed (Registry.Content.all_files directory))
            | Error reason -> Hashtbl.replace unavailable hash reason)
          missing;
        settle ()
  in
  settle ()

let snapshot_of_files kind files = { kind; files; project = project_of files }
let with_files (snapshot : snapshot) files = { snapshot with files; project = project_of files }

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

let packages snapshot =
  List.map
    (fun (directory, (package : Manifest.package)) -> (directory, package.name))
    snapshot.project.own.packages

let target_packages snapshot requested =
  let packages = packages snapshot in
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

let package snapshot name =
  List.find_opt (fun (package : Project.package) -> package.name = name) snapshot.project.packages

let package_files snapshot name =
  match package snapshot name with Some package -> List.map fst package.files | None -> []

let dependency_names snapshot name =
  match package snapshot name with
  | Some package ->
      List.map (fun (dependency : Manifest.dependency) -> dependency.package) package.dependencies
  | None -> []

let source snapshot (file : Path.file) =
  match
    Option.bind (package snapshot file.module_.package) (fun package ->
        List.assoc_opt file package.files)
  with
  | Some text -> Source.create ~path:(Path.show_file file) text
  | None -> Compiler_bug.bug ~stage:"Database" "%s is not a file" (Path.show_file file)

let root snapshot =
  match snapshot.kind with
  | Worktree root | Trial { root; _ } -> root
  | Published -> Compiler_bug.bug ~stage:"Database" "only a worktree's snapshot has a root"

let registry_packages snapshot =
  List.map
    (fun (selected : Registry.Selection.package) ->
      (selected.name, selected.version, selected.hash))
    snapshot.project.selection.selected

let package_states snapshot =
  let standard = Lazy.force standard_state in
  let hashes =
    List.filter_map
      (fun (name, (place : Project.place)) ->
        match place.root with Registry hash -> Some (name, hash) | Project -> None)
      snapshot.project.places
  in
  let states = Hashtbl.create 8 in
  let rec visible name =
    List.concat_map
      (fun dependency ->
        if List.mem_assoc dependency hashes then dependency :: visible dependency else [])
      (dependency_names snapshot name)
  in
  let rec state_of name =
    match Hashtbl.find_opt states name with
    | Some loaded -> loaded
    | None ->
        let loaded =
          match package snapshot name with
          | Some package ->
              package_state package ~hash:(List.assoc name hashes)
                ~visible:
                  (standard
                  :: List.map state_of (List.sort_uniq Path.compare_package (visible name)))
          | None -> Compiler_bug.bug ~stage:"Database" "%s has no files" (Path.show_package name)
        in
        Hashtbl.replace states name loaded;
        loaded
  in
  standard :: List.map (fun (name, _) -> state_of name) hashes

let layout snapshot =
  let loaded = package_states snapshot in
  ( loaded,
    List.filter
      (fun (package : Project.package) ->
        not (List.exists (fun (state : loaded) -> state.package = package.name) loaded))
      snapshot.project.packages )

let pipeline_states loaded = List.map (fun (loaded : loaded) -> loaded.state) loaded

let cold_pipeline ~checks snapshot =
  let loaded, packages = layout snapshot in
  Pipeline.create ~checks ~loaded:(pipeline_states loaded) packages

let database_directory = ".truss"
let compiler_line = "compiler " ^ Compiler_version.digest

let header loaded =
  compiler_line :: List.map (fun (loaded : loaded) -> "loaded " ^ Blake3.to_hex loaded.key) loaded

let of_hex hex =
  let digit character =
    match character with
    | '0' .. '9' -> Some (Char.code character - Char.code '0')
    | 'a' .. 'f' -> Some (Char.code character - Char.code 'a' + 10)
    | _ -> None
  in
  if String.length hex mod 2 <> 0 then None
  else
    let bytes = Bytes.create (String.length hex / 2) in
    let rec fill index =
      if index = Bytes.length bytes then Some (Bytes.to_string bytes)
      else
        match (digit hex.[2 * index], digit hex.[(2 * index) + 1]) with
        | Some high, Some low ->
            Bytes.set bytes index (Char.chr ((high * 16) + low));
            fill (index + 1)
        | None, _ | _, None -> None
    in
    fill 0

let saved_state ~(current : loaded list) key =
  match List.find_opt (fun (loaded : loaded) -> loaded.key = key) current with
  | Some loaded -> Some loaded.state
  | None -> (
      match Hashtbl.find_opt loaded_states key with
      | Some loaded -> Some loaded.state
      | None ->
          Option.map
            (fun bytes -> (Marshal.from_string bytes 0 : Pipeline.state))
            (Store.find_result (store ()) ~kind:Package_state ~key))

let saved_states segments ~current =
  match Segments.header segments with
  | Some (line :: loaded_lines) when line = compiler_line ->
      List.fold_right
        (fun line states ->
          Option.bind states (fun states ->
              match String.split_on_char ' ' line with
              | [ "loaded"; hex ] ->
                  Option.map
                    (fun state -> state :: states)
                    (Option.bind (of_hex hex) (saved_state ~current))
              | _ -> None))
        loaded_lines (Some [])
  | Some _ | None -> None

let project_texts snapshot =
  let texts = Hashtbl.create 256 in
  List.iter
    (fun (package : Project.package) ->
      List.iter (fun (file, text) -> Hashtbl.replace texts file text) package.files)
    snapshot.project.packages;
  Hashtbl.find_opt texts

let opened segments snapshot =
  let loaded, packages = layout snapshot in
  let cold () =
    Segments.discard segments;
    Pipeline.create ~loaded:(pipeline_states loaded) packages
  in
  let pipeline =
    match saved_states segments ~current:loaded with
    | None -> cold ()
    | Some saved -> (
        match Segments.entries segments with
        | None -> cold ()
        | Some entries -> (
            match Pipeline.restore ~loaded:saved ~texts:(project_texts snapshot) entries with
            | pipeline ->
                Pipeline.relayout pipeline ~loaded:(pipeline_states loaded) packages;
                pipeline
            | exception (Failure _ | Invalid_argument _ | End_of_file) -> cold ()))
  in
  (pipeline, loaded)

type database = {
  root : string;
  watcher : Watcher.t option;
  segments : Segments.t;
  mutable snapshot : snapshot;
  pipeline : Pipeline.t;
  mutable loaded : loaded list;
}

let databases : (string, database) Hashtbl.t = Hashtbl.create 4
let is_serving = ref false
let log_bug bug = prerr_endline (Compiler_bug.to_string bug)

let commit database =
  match Pipeline.unsaved database.pipeline with
  | entries -> (
      match Segments.commit database.segments ~header:(header database.loaded) entries with
      | () -> Pipeline.mark_saved database.pipeline
      | exception ((Unix.Unix_error _ | Sys_error _) as failure) ->
          prerr_endline
            (Printf.sprintf "Cannot save the database in %s: %s."
               (Filename.concat database.root database_directory)
               (match failure with
               | Unix.Unix_error (error, _, _) -> Unix.error_message error
               | failure -> Printexc.to_string failure)))
  | exception Compiler_bug.Bug bug -> log_bug bug

let close database =
  Option.iter Watcher.stop database.watcher;
  Segments.close database.segments;
  Hashtbl.remove databases database.root

let is_layout path =
  path = Project.lock_file || Filename.basename path = Filename.basename (Project.manifest_file "")

let file_changes (before : snapshot) (after : snapshot) =
  let layout snapshot = List.filter (fun (path, _) -> is_layout path) snapshot.files in
  if layout before <> layout after then None
  else
    let texts (snapshot : snapshot) =
      let table = Hashtbl.create 256 in
      List.iter
        (fun (package : Project.package) ->
          List.iter (fun (file, text) -> Hashtbl.replace table file text) package.files)
        snapshot.project.packages;
      table
    in
    let previous = texts before and current = texts after in
    Some
      (Hashtbl.fold
         (fun file text changes ->
           match Hashtbl.find_opt previous file with
           | Some old when String.equal old text -> changes
           | Some _ | None -> (file, Some text) :: changes)
         current
         (Hashtbl.fold
            (fun file _ changes ->
              if Hashtbl.mem current file then changes else (file, None) :: changes)
            previous []))

let apply_changes pipeline (after : snapshot) = function
  | Some changes ->
      Pipeline.update pipeline changes;
      None
  | None ->
      let loaded, packages = layout after in
      Pipeline.relayout pipeline ~loaded:(pipeline_states loaded) packages;
      Some loaded

let copied_database root (trial : snapshot) =
  match Hashtbl.find_opt databases root with
  | Some database ->
      let pipeline = Pipeline.copy database.pipeline in
      ignore (apply_changes pipeline trial (file_changes database.snapshot trial));
      pipeline
  | None -> cold_pipeline ~checks:true trial

let over (snapshot : snapshot) files =
  let root = root snapshot in
  let trial = with_files snapshot files in
  { trial with kind = Trial { root; pipeline = lazy (copied_database root trial) } }

let trial snapshot changes =
  over snapshot
    (List.filter (fun (path, _) -> not (List.mem_assoc path changes)) snapshot.files
    @ List.filter_map (fun (path, text) -> Option.map (fun text -> (path, text)) text) changes)

let base_commit snapshot base =
  let directory = root snapshot in
  match base with
  | Some revision -> Git.resolve ~directory revision
  | None -> (
      match (Git.head ~directory, Git.default_branch ~directory) with
      | Some head, Some branch -> Git.merge_base ~directory head branch
      | Some head, None -> Some head
      | None, _ -> None)

let of_commit snapshot commit =
  match Git.files ~directory:(root snapshot) commit with
  | Some files -> Ok (over snapshot files)
  | None -> Error (Printf.sprintf "The files of commit %s cannot be read." commit)

type side = { base : snapshot; other : snapshot; merged : unit -> (snapshot, string) result }

let side snapshot ~head ~other ~mergeable =
  let directory = root snapshot in
  match Option.map (fun mine -> Git.merge_base ~directory mine head) (Git.head ~directory) with
  | None -> Error "This worktree has no commit."
  | Some None -> Error "The two have no commit in common."
  | Some (Some merge_base) ->
      Result.map
        (fun base ->
          {
            base;
            other;
            merged =
              (fun () ->
                match (Git.snapshot ~directory, mergeable ()) with
                | Some mine, Some theirs -> (
                    match Git.merged_files ~directory mine theirs with
                    | Some files -> Ok (over snapshot files)
                    | None -> Error "The two do not merge without a textual conflict.")
                | None, _ | _, None ->
                    Error "The files of the two cannot be committed to merge them.");
          })
        (of_commit snapshot merge_base)

let branch snapshot name =
  match Git.resolve ~directory:(root snapshot) name with
  | None -> Error (Printf.sprintf "No commit is named %s." name)
  | Some commit ->
      Result.bind (of_commit snapshot commit) (fun other ->
          side snapshot ~head:commit ~other ~mergeable:(fun () -> Some commit))

let other_worktree snapshot other =
  match Git.head ~directory:other with
  | None -> Error "The other worktree has no commit."
  | Some head ->
      side snapshot ~head
        ~other:(over snapshot (Registry.Content.input_files other))
        ~mergeable:(fun () -> Git.snapshot ~directory:other)

let other_worktrees snapshot =
  let root = root snapshot in
  match
    List.filter
      (fun other -> other <> root && other <> "" && Sys.file_exists other)
      (List.sort_uniq compare
         (Server.serving () @ Hashtbl.fold (fun root _ roots -> root :: roots) databases []))
  with
  | [] -> []
  | others -> (
      let place directory = (Git.common_directory directory, Git.prefix directory) in
      match place root with
      | (Some _, Some _) as here -> List.filter (fun other -> place other = here) others
      | _ -> [])

let pipeline ?(checks = true) snapshot =
  match snapshot.kind with
  | Worktree root when checks -> (
      match Hashtbl.find_opt databases root with
      | Some database when database.snapshot == snapshot -> database.pipeline
      | Some _ | None -> copied_database root snapshot)
  | Trial { pipeline; _ } when checks -> Lazy.force pipeline
  | Worktree _ | Trial _ | Published -> cold_pipeline ~checks snapshot

let is_watched relative =
  List.for_all (fun part -> not (Registry.Content.skipped part)) (String.split_on_char '/' relative)
  || relative = ""

let is_under prefix path =
  prefix = "" || path = prefix || String.starts_with ~prefix:(prefix ^ "/") path

let changed_files root files paths =
  let prefixes =
    List.filter
      (fun path -> not (List.exists (fun other -> other <> path && is_under other path) paths))
      (List.sort_uniq compare (List.filter is_watched paths))
  in
  let found prefix =
    let absolute = if prefix = "" then root else Filename.concat root prefix in
    match (Unix.lstat absolute).st_kind with
    | S_DIR ->
        List.map
          (fun (path, text) -> ((if prefix = "" then path else prefix ^ "/" ^ path), text))
          (Registry.Content.input_files absolute)
    | S_REG when Registry.Content.is_input (Filename.basename prefix) ->
        [ (prefix, File_system.read absolute) ]
    | _ -> []
    | exception Unix.Unix_error _ -> []
  in
  List.filter
    (fun (path, _) -> not (List.exists (fun prefix -> is_under prefix path) prefixes))
    files
  @ List.concat_map found prefixes

let refresh database =
  let root = database.root in
  let files =
    match Option.map Watcher.changes database.watcher with
    | Some Overflow | None -> Some (Registry.Content.input_files root)
    | Some (Changed []) -> None
    | Some (Changed paths) -> Some (changed_files root database.snapshot.files paths)
  in
  match files with
  | None -> false
  | Some files -> (
      let before = database.snapshot in
      let after = with_files before files in
      database.snapshot <- after;
      match file_changes before after with
      | Some [] -> false
      | changes ->
          Option.iter
            (fun loaded -> database.loaded <- loaded)
            (apply_changes database.pipeline after changes);
          true)

let open_database root =
  match Segments.open_ (Filename.concat root database_directory) with
  | Error `Open_elsewhere ->
      Error
        (Printf.sprintf
           "The database in %s is open in another process. Wait for that process, or stop the \
            background process with `truss stop`."
           (Filename.concat root database_directory))
  | Ok segments -> (
      let watcher =
        if !is_serving then
          Some
            (Watcher.start ~skipped:Registry.Content.skipped ~cookie_directory:database_directory
               root)
        else None
      in
      match
        let snapshot = snapshot_of_files (Worktree root) (Registry.Content.input_files root) in
        (snapshot, opened segments snapshot)
      with
      | snapshot, (pipeline, loaded) ->
          let database = { root; watcher; segments; snapshot; pipeline; loaded } in
          Hashtbl.replace databases root database;
          Ok database
      | exception failure ->
          Option.iter Watcher.stop watcher;
          Segments.close segments;
          raise failure)

let worktree_snapshot root =
  match Hashtbl.find_opt databases root with
  | Some database ->
      ignore (refresh database);
      Ok database.snapshot
  | None -> Result.map (fun database -> database.snapshot) (open_database root)

let take_snapshot directory =
  if not (Sys.file_exists directory) then Error (directory ^ ": no such directory.")
  else
    match root_of directory with
    | None ->
        Error
          (Printf.sprintf "No `truss.toml` in %s or any directory above it, so it is in no project."
             directory)
    | Some root ->
        Result.map
          (fun snapshot -> (snapshot, target_packages snapshot (relative_to root directory)))
          (worktree_snapshot root)

let retake snapshot =
  match snapshot.kind with
  | Worktree root -> worktree_snapshot root
  | Trial _ | Published -> Ok snapshot

let propagate_changes descriptor =
  Hashtbl.iter
    (fun _ database ->
      if Option.map Watcher.descriptor database.watcher = Some descriptor then
        match if refresh database then Pipeline.propagate ~on_bug:log_bug database.pipeline with
        | () -> commit database
        | exception Compiler_bug.Bug bug ->
            log_bug bug;
            close database)
    (Hashtbl.copy databases)

let problems snapshot = snapshot.project.problems

let file_path snapshot (file : Path.file) =
  match List.assoc_opt file.module_.package snapshot.project.places with
  | Some { root = Project.Project; directory; _ } -> Project.file_path ~directory file
  | _ -> Path.show_file file

let time_limit_ms snapshot = snapshot.project.own.time_limit_ms
let lock_fix snapshot = snapshot.project.selection.lock_fix

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

let plan_lock snapshot ~set ~all =
  match Registry.Index.current () with
  | None ->
      Error
        (Printf.sprintf "No registry is set. Set `%s` to the registry's directory."
           Registry.Index.variable)
  | Some registry -> (
      let before =
        try
          Registry.Lock.parse
            (Option.value ~default:"" (List.assoc_opt Project.lock_file snapshot.files))
        with Registry.Lock.Malformed _ -> []
      in
      let set =
        set
        @
        if all then
          List.filter_map
            (fun (name, _, _) -> if List.mem_assoc name set then None else Some (name, None))
            (registry_packages snapshot)
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
          let manifests = List.map snd snapshot.project.own.packages in
          let local name =
            List.exists (fun (package : Manifest.package) -> package.name = name) manifests
          in
          let selected, problems =
            Registry.Selection.choose ~lock
              ~roots:
                (List.concat_map
                   (fun (package : Manifest.package) ->
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
                     (fun (package : Manifest.package) -> package.dependencies)
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
          let snapshot =
            snapshot_of_files Published
              (Registry.Content.input_files (Filename.concat (packages_directory ()) hash))
          in
          match problems snapshot with
          | [] -> Ok snapshot
          | problem :: _ -> cannot (Project.show_problem problem)))

let server_key directory = Option.value (root_of directory) ~default:""

let close_all () =
  List.iter
    (fun database ->
      commit database;
      close database)
    (Hashtbl.fold (fun _ database databases -> database :: databases) databases [])

let flush () =
  if !is_serving then Hashtbl.iter (fun _ database -> commit database) databases else close_all ();
  flush_store ()

let serve ~key ~handle =
  is_serving := true;
  Server.serve ~key
    ~is_alive:(fun () -> key = "" || Sys.file_exists key)
    ~collect
    ~watcher_descriptors:(fun () ->
      Hashtbl.fold
        (fun _ database descriptors ->
          Option.fold ~none:descriptors
            ~some:(fun watcher -> Watcher.descriptor watcher :: descriptors)
            database.watcher)
        databases [])
    ~propagate:propagate_changes ~handle ~save:flush
    ~close:(fun () ->
      close_all ();
      reset ());
  is_serving := false

let call ?program ?start_server ?key ~progress request =
  let key = match key with Some key -> key | None -> server_key (Sys.getcwd ()) in
  Server.call ?program ?start_server ~key ~progress request

let servers = Server.serving
let stop = Server.stop
let wait_until_ended = Server.wait_until_ended

module For_testing = struct
  let standard_state () = (Lazy.force standard_state).state
  let cold_pipeline = cold_pipeline ~checks:true
  let collect_store = collect
  let listen = Server.listen

  let interrupt_commit root =
    match Hashtbl.find_opt databases root with
    | Some database ->
        Segments.For_testing.interrupted_commit database.segments ~header:(header database.loaded)
          (Pipeline.unsaved database.pipeline);
        close database
    | None -> Compiler_bug.bug ~stage:"Database" "%s has no open database" root
end
