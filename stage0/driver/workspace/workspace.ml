module File_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.file
end))

module Package_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.package
end))

let opened_cache : Cache.t option ref = ref None

exception Unusable_cache of string

let open_cache () =
  match !opened_cache with
  | Some cache -> cache
  | None -> (
      match Result.bind (Cache.locate_default_directory ()) Cache.open_ with
      | Ok cache ->
          Cache.compact cache;
          opened_cache := Some cache;
          cache
      | Error message -> raise (Unusable_cache message))

let flush_cache () = Option.iter Cache.flush !opened_cache

let reset () =
  Option.iter Cache.close !opened_cache;
  opened_cache := None

let read_cache_budget () =
  match Option.bind (Sys.getenv_opt "TRUSS_CACHE_SIZE") int_of_string_opt with
  | Some bytes -> bytes
  | None -> 20 * 1024 * 1024 * 1024

let collect () =
  let cache = open_cache () in
  Cache.compact cache;
  let lock =
    Unix.openfile
      (Filename.concat (Cache.directory cache) "collect.lock")
      [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644
  in
  Fun.protect
    ~finally:(fun () -> Unix.close lock)
    (fun () ->
      match Unix.lockf lock F_TLOCK 0 with
      | () -> Cache.collect cache ~budget:(read_cache_budget ())
      | exception Unix.Unix_error _ -> ())

type loaded = {
  package : Path.package;
  hash : string;
  key : string;
  package_database : Database.package_database;
}

let loaded_package_databases : (string, loaded) Hashtbl.t = Hashtbl.create 8

let make_package_database_key ~hash ~visible =
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
      (Filename.concat (Cache.directory (open_cache ())) name)
      [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644
  in
  Fun.protect
    ~finally:(fun () -> Unix.close lock)
    (fun () ->
      Unix.lockf lock F_LOCK 0;
      work ())

let load_package_database (package : Project.package) ~hash ~visible =
  let key = make_package_database_key ~hash ~visible in
  match Hashtbl.find_opt loaded_package_databases key with
  | Some loaded -> loaded
  | None ->
      let stored () =
        Option.map
          (fun bytes -> (Marshal.from_string bytes 0 : Database.package_database))
          (Cache.find_result (open_cache ()) ~kind:Package_database ~key)
      in
      let package_database =
        match stored () with
        | Some package_database -> package_database
        | None ->
            exclusively "package-states.lock" (fun () ->
                match stored () with
                | Some package_database -> package_database
                | None ->
                    let package_database =
                      Database.read_package_database
                        (Database.create
                           ~loaded:(List.map (fun visible -> visible.package_database) visible)
                           [ package ])
                        package.name
                    in
                    Cache.add_result (open_cache ()) ~kind:Package_database ~key
                      (Marshal.to_string package_database []);
                    Cache.flush (open_cache ());
                    package_database)
      in
      let loaded = { package = package.name; hash; key; package_database } in
      Hashtbl.replace loaded_package_databases key loaded;
      loaded

let standard_package : Project.package =
  { name = Path.standard_package; dependencies = []; files = Standard_library.files }

let checked_standard_package : loaded option ref = ref None

let load_standard_package () =
  match !checked_standard_package with
  | Some standard -> standard
  | None ->
      let standard =
        load_package_database standard_package ~visible:[]
          ~hash:
            (Registry.Content.hash
               (List.map
                  (fun (file, text) -> (Project.make_file_path ~directory:"" file, text))
                  Standard_library.files))
      in
      let database = Database.create ~loaded:[ standard.package_database ] [] in
      let rendered =
        List.concat_map
          (fun ((file : Path.file), text) ->
            match Database.list_file_diagnostics database file with
            | [] -> []
            | diagnostics ->
                let source = Source.create ~path:(Path.show_file file) text in
                List.map (Diagnostic.render source) diagnostics)
          Standard_library.files
      in
      if rendered <> [] then
        Compiler_bug.bug ~stage:"Workspace" "the standard library has diagnostics:\n%s"
          (String.concat "" rendered);
      checked_standard_package := Some standard;
      standard

let list_package_databases () =
  List.sort compare
    (Hashtbl.fold
       (fun _ { package; hash; _ } lines ->
         Printf.sprintf "%s %s" (Path.show_package package) (String.sub hash 0 16) :: lines)
       loaded_package_databases [])

type kind =
  | Worktree of string
  | Trial of { root : string; database : Database.t Lazy.t }
  | Published

type snapshot = { kind : kind; files : (string * string) list; project : Project.t }

let fetch name version ~hash =
  let packages = Cache.make_packages_directory (open_cache ()) in
  let directory = Filename.concat packages hash in
  if Sys.file_exists directory then Ok directory
  else
    match Registry.Index.find_current_registry () with
    | Some registry -> Registry.Index.fetch registry ~into:packages name version ~hash
    | None ->
        Error
          (Printf.sprintf "no registry is set; set `%s` to the registry's directory"
             Registry.Index.variable)

let load_published name version ~hash =
  match fetch name version ~hash with
  | Error reason -> Error reason
  | Ok directory ->
      let files = Registry.Content.list_all_files directory in
      Registry.Selection.read_manifest_and_record ~read:(fun file -> List.assoc_opt file files) name

let index_files (files : (string * string) list) =
  let table = Hashtbl.create (List.length files) in
  List.iter (fun (path, text) -> Hashtbl.replace table path text) files;
  (List.sort compare (List.map fst files), table)

let project_of files =
  let own = index_files files in
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
                Hashtbl.replace registry hash
                  (index_files (Registry.Content.list_all_files directory))
            | Error reason -> Hashtbl.replace unavailable hash reason)
          missing;
        settle ()
  in
  settle ()

let snapshot_of_files kind files = { kind; files; project = project_of files }
let replace_files (snapshot : snapshot) files = { snapshot with files; project = project_of files }

let find_root directory =
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

let make_relative_to root directory =
  let directory = try Unix.realpath directory with Unix.Unix_error _ -> directory in
  if directory = root then ""
  else
    let prefix = root ^ "/" in
    if String.starts_with ~prefix directory then String.drop_first (String.length prefix) directory
    else ""

let list_packages snapshot =
  List.map
    (fun (directory, (package : Manifest.package)) -> (directory, package.name))
    snapshot.project.own.packages

let list_target_packages snapshot requested =
  let packages = list_packages snapshot in
  let under (directory, _) =
    requested = "" || directory = requested
    || String.starts_with ~prefix:(requested ^ "/") directory
  in
  match List.filter under packages with
  | [] -> (
      match
        Project.find_package_directory
          ~is_package:(fun candidate -> List.mem_assoc candidate packages)
          requested
      with
      | Some directory -> List.filter (fun (candidate, _) -> candidate = directory) packages
      | None -> [])
  | under_requested -> under_requested

let find_package snapshot name =
  List.find_opt (fun (package : Project.package) -> package.name = name) snapshot.project.packages

let list_package_files snapshot name =
  match find_package snapshot name with Some package -> List.map fst package.files | None -> []

let list_dependency_names snapshot name =
  match find_package snapshot name with
  | Some package ->
      List.map (fun (dependency : Manifest.dependency) -> dependency.package) package.dependencies
  | None -> []

let read_source snapshot (file : Path.file) =
  match
    Option.bind (find_package snapshot file.module_.package) (fun package ->
        List.assoc_opt file package.files)
  with
  | Some text -> Source.create ~path:(Path.show_file file) text
  | None -> Compiler_bug.bug ~stage:"Workspace" "%s is not a file" (Path.show_file file)

let locate_root snapshot =
  match snapshot.kind with
  | Worktree root | Trial { root; _ } -> root
  | Published -> Compiler_bug.bug ~stage:"Workspace" "only a worktree's snapshot has a root"

let list_registry_packages snapshot =
  List.map
    (fun (selected : Registry.Selection.package) ->
      (selected.name, selected.version, selected.hash))
    snapshot.project.selection.selected

let load_package_databases snapshot =
  let standard = load_standard_package () in
  let hashes =
    List.filter_map
      (fun (name, (place : Project.place)) ->
        match place.root with Registry hash -> Some (name, hash) | Project -> None)
      snapshot.project.places
  in
  let loaded_by_name = Package_table.create 8 in
  let rec visible name =
    List.concat_map
      (fun dependency ->
        if List.mem_assoc dependency hashes then dependency :: visible dependency else [])
      (list_dependency_names snapshot name)
  in
  let rec load_named name =
    match Package_table.find_opt loaded_by_name name with
    | Some loaded -> loaded
    | None ->
        let loaded =
          match find_package snapshot name with
          | Some package ->
              load_package_database package ~hash:(List.assoc name hashes)
                ~visible:
                  (standard
                  :: List.map load_named (List.sort_uniq Path.compare_package (visible name)))
          | None -> Compiler_bug.bug ~stage:"Workspace" "%s has no files" (Path.show_package name)
        in
        Package_table.replace loaded_by_name name loaded;
        loaded
  in
  standard :: List.map (fun (name, _) -> load_named name) hashes

let load_layout snapshot =
  let loaded = load_package_databases snapshot in
  ( loaded,
    List.filter
      (fun (package : Project.package) ->
        not (List.exists (fun (candidate : loaded) -> candidate.package = package.name) loaded))
      snapshot.project.packages )

let extract_package_databases loaded =
  List.map (fun (loaded : loaded) -> loaded.package_database) loaded

let build_cold_database ~checks snapshot =
  let loaded, packages = load_layout snapshot in
  Database.create ~checks ~loaded:(extract_package_databases loaded) packages

let database_directory = ".truss"
let compiler_line = "compiler " ^ Compiler_version.digest

let make_header loaded =
  compiler_line :: List.map (fun (loaded : loaded) -> "loaded " ^ Blake3.to_hex loaded.key) loaded

let of_hex hex =
  if String.length hex mod 2 <> 0 || not (String.for_all Char.Ascii.is_hex_digit hex) then None
  else
    let byte_at index =
      Char.chr
        ((Char.Ascii.hex_digit_to_int hex.[2 * index] * 16)
        + Char.Ascii.hex_digit_to_int hex.[(2 * index) + 1])
    in
    Some (String.init (String.length hex / 2) byte_at)

let find_saved_package_database ~(current : loaded list) key =
  match List.find_opt (fun (loaded : loaded) -> loaded.key = key) current with
  | Some loaded -> Some loaded.package_database
  | None -> (
      match Hashtbl.find_opt loaded_package_databases key with
      | Some loaded -> Some loaded.package_database
      | None ->
          Option.map
            (fun bytes -> (Marshal.from_string bytes 0 : Database.package_database))
            (Cache.find_result (open_cache ()) ~kind:Package_database ~key))

let find_saved_package_databases segments ~current =
  match Segments.header segments with
  | Some (line :: loaded_lines) when line = compiler_line ->
      List.fold_right
        (fun line package_databases ->
          Option.bind package_databases (fun package_databases ->
              match String.split_on_char ' ' line with
              | [ "loaded"; hex ] ->
                  Option.map
                    (fun package_database -> package_database :: package_databases)
                    (Option.bind (of_hex hex) (find_saved_package_database ~current))
              | _ -> None))
        loaded_lines (Some [])
  | Some _ | None -> None

let project_texts snapshot =
  let texts = File_table.create 256 in
  List.iter
    (fun (package : Project.package) ->
      List.iter (fun (file, text) -> File_table.replace texts file text) package.files)
    snapshot.project.packages;
  File_table.find_opt texts

let restore_database segments snapshot =
  let loaded, packages = load_layout snapshot in
  let cold () =
    Segments.discard segments;
    Database.create ~loaded:(extract_package_databases loaded) packages
  in
  let database =
    match find_saved_package_databases segments ~current:loaded with
    | None -> cold ()
    | Some saved -> (
        match Segments.read_entries segments with
        | None -> cold ()
        | Some entries -> (
            match Database.restore ~loaded:saved ~texts:(project_texts snapshot) entries with
            | database ->
                Database.relayout database ~loaded:(extract_package_databases loaded) packages;
                database
            | exception (Failure _ | Invalid_argument _ | End_of_file) -> cold ()))
  in
  (database, loaded)

type worktree = {
  root : string;
  watcher : Watcher.t option;
  segments : Segments.t;
  mutable snapshot : snapshot;
  database : Database.t;
  mutable loaded : loaded list;
}

let worktrees : (string, worktree) Hashtbl.t = Hashtbl.create 4
let is_serving = ref false
let log_bug bug = prerr_endline (Compiler_bug.to_string bug)

let commit worktree =
  match Database.list_unsaved worktree.database with
  | entries -> (
      match Segments.commit worktree.segments ~header:(make_header worktree.loaded) entries with
      | () -> Database.mark_saved worktree.database
      | exception ((Unix.Unix_error _ | Sys_error _) as failure) ->
          prerr_endline
            (Printf.sprintf "Cannot save the database in %s: %s."
               (Filename.concat worktree.root database_directory)
               (match failure with
               | Unix.Unix_error (error, _, _) -> Unix.error_message error
               | failure -> Printexc.to_string failure)))
  | exception Compiler_bug.Bug bug -> log_bug bug

let close worktree =
  Option.iter Watcher.stop worktree.watcher;
  Segments.close worktree.segments;
  Hashtbl.remove worktrees worktree.root

let is_layout path =
  path = Project.lock_file
  || Filename.basename path = Filename.basename (Project.make_manifest_path "")

let find_file_changes (before : snapshot) (after : snapshot) =
  let layout snapshot = List.filter (fun (path, _) -> is_layout path) snapshot.files in
  if layout before <> layout after then None
  else
    let texts (snapshot : snapshot) =
      let table = File_table.create 256 in
      List.iter
        (fun (package : Project.package) ->
          List.iter (fun (file, text) -> File_table.replace table file text) package.files)
        snapshot.project.packages;
      table
    in
    let previous = texts before and current = texts after in
    Some
      (File_table.fold
         (fun file text changes ->
           match File_table.find_opt previous file with
           | Some old when String.equal old text -> changes
           | Some _ | None -> (file, Some text) :: changes)
         current
         (File_table.fold
            (fun file _ changes ->
              if File_table.mem current file then changes else (file, None) :: changes)
            previous []))

let apply_changes database (after : snapshot) = function
  | Some changes ->
      Database.update database changes;
      None
  | None ->
      let loaded, packages = load_layout after in
      Database.relayout database ~loaded:(extract_package_databases loaded) packages;
      Some loaded

let copy_database root (trial : snapshot) =
  match Hashtbl.find_opt worktrees root with
  | Some worktree ->
      let database = Database.copy worktree.database in
      ignore (apply_changes database trial (find_file_changes worktree.snapshot trial));
      database
  | None -> build_cold_database ~checks:true trial

let make_trial snapshot changes =
  let root = locate_root snapshot in
  let trial =
    replace_files snapshot
      (List.filter (fun (path, _) -> not (List.mem_assoc path changes)) snapshot.files
      @ List.filter_map (fun (path, text) -> Option.map (fun text -> (path, text)) text) changes)
  in
  { trial with kind = Trial { root; database = lazy (copy_database root trial) } }

let open_database ?(checks = true) snapshot =
  match snapshot.kind with
  | Worktree root when checks -> (
      match Hashtbl.find_opt worktrees root with
      | Some worktree when worktree.snapshot == snapshot -> worktree.database
      | Some _ | None -> copy_database root snapshot)
  | Trial { database; _ } when checks -> Lazy.force database
  | Worktree _ | Trial _ | Published -> build_cold_database ~checks snapshot

let is_watched relative =
  List.for_all
    (fun part -> not (Registry.Content.is_skipped part))
    (String.split_on_char '/' relative)
  || relative = ""

let is_under prefix path =
  prefix = "" || path = prefix || String.starts_with ~prefix:(prefix ^ "/") path

let list_changed_files root files paths =
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
          (Registry.Content.list_input_files absolute)
    | S_REG when Registry.Content.is_input (Filename.basename prefix) ->
        [ (prefix, File_system.read absolute) ]
    | _ -> []
    | exception Unix.Unix_error _ -> []
  in
  List.filter
    (fun (path, _) -> not (List.exists (fun prefix -> is_under prefix path) prefixes))
    files
  @ List.concat_map found prefixes

let refresh worktree =
  let root = worktree.root in
  let files =
    match Option.map Watcher.read_changes worktree.watcher with
    | Some Overflow | None -> Some (Registry.Content.list_input_files root)
    | Some (Changed []) -> None
    | Some (Changed paths) -> Some (list_changed_files root worktree.snapshot.files paths)
  in
  match files with
  | None -> false
  | Some files -> (
      let before = worktree.snapshot in
      let after = replace_files before files in
      worktree.snapshot <- after;
      match find_file_changes before after with
      | Some [] -> false
      | changes ->
          Option.iter
            (fun loaded -> worktree.loaded <- loaded)
            (apply_changes worktree.database after changes);
          true)

let open_worktree root =
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
            (Watcher.start ~skipped:Registry.Content.is_skipped ~cookie_directory:database_directory
               root)
        else None
      in
      match
        let snapshot = snapshot_of_files (Worktree root) (Registry.Content.list_input_files root) in
        (snapshot, restore_database segments snapshot)
      with
      | snapshot, (database, loaded) ->
          let worktree = { root; watcher; segments; snapshot; database; loaded } in
          Hashtbl.replace worktrees root worktree;
          Ok worktree
      | exception failure ->
          Option.iter Watcher.stop watcher;
          Segments.close segments;
          raise failure)

let load_worktree_snapshot root =
  match Hashtbl.find_opt worktrees root with
  | Some worktree ->
      ignore (refresh worktree);
      Ok worktree.snapshot
  | None -> Result.map (fun worktree -> worktree.snapshot) (open_worktree root)

let take_snapshot directory =
  if not (Sys.file_exists directory) then Error (directory ^ ": no such directory.")
  else
    match find_root directory with
    | None ->
        Error
          (Printf.sprintf "No `truss.toml` in %s or any directory above it, so it is in no project."
             directory)
    | Some root ->
        Result.map
          (fun snapshot ->
            (snapshot, list_target_packages snapshot (make_relative_to root directory)))
          (load_worktree_snapshot root)

let retake snapshot =
  match snapshot.kind with
  | Worktree root -> load_worktree_snapshot root
  | Trial _ | Published -> Ok snapshot

let propagate_changes descriptor =
  Hashtbl.iter
    (fun _ worktree ->
      if Option.map Watcher.extract_descriptor worktree.watcher = Some descriptor then
        match if refresh worktree then Database.propagate ~on_bug:log_bug worktree.database with
        | () -> commit worktree
        | exception Compiler_bug.Bug bug ->
            log_bug bug;
            close worktree)
    (Hashtbl.copy worktrees)

let problems snapshot = snapshot.project.problems

let locate_file snapshot (file : Path.file) =
  match List.assoc_opt file.module_.package snapshot.project.places with
  | Some { root = Project.Project; directory; _ } -> Project.make_file_path ~directory file
  | _ -> Path.show_file file

let time_limit_ms snapshot = snapshot.project.own.time_limit_ms
let lock_fix snapshot = snapshot.project.selection.lock_fix

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

let plan_lock snapshot ~set ~all =
  match Registry.Index.find_current_registry () with
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
            (list_registry_packages snapshot)
        else []
      in
      let wanted =
        List.map
          (fun (name, version) ->
            match version with
            | None -> (
                match Registry.Index.find_newest registry name with
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
                         match Path.list_package_parts dependency.package with
                         | [ _; _ ] -> Some (package.name, dependency.package)
                         | _ -> None)
                       package.dependencies)
                   manifests)
              ~local ~load:load_published
          in
          if problems <> [] then
            Error (String.concat " " (List.map Registry.Selection.describe_problem problems))
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

let fetch_published name version =
  match
    Option.bind (Registry.Index.find_current_registry ()) (fun registry ->
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
              (Registry.Content.list_input_files
                 (Filename.concat (Cache.make_packages_directory (open_cache ())) hash))
          in
          match problems snapshot with
          | [] -> Ok snapshot
          | problem :: _ -> cannot (Project.show_problem problem)))

let make_server_key directory = Option.value (find_root directory) ~default:""

let close_all () =
  List.iter
    (fun worktree ->
      commit worktree;
      close worktree)
    (Hashtbl.fold (fun _ worktree worktrees -> worktree :: worktrees) worktrees [])

let flush () =
  if !is_serving then Hashtbl.iter (fun _ worktree -> commit worktree) worktrees else close_all ();
  flush_cache ()

let serve ~key ~handle =
  is_serving := true;
  Server.serve ~key
    ~is_alive:(fun () -> key = "" || Sys.file_exists key)
    ~collect
    ~watcher_descriptors:(fun () ->
      Hashtbl.fold
        (fun _ worktree descriptors ->
          Option.fold ~none:descriptors
            ~some:(fun watcher -> Watcher.extract_descriptor watcher :: descriptors)
            worktree.watcher)
        worktrees [])
    ~propagate:propagate_changes ~handle ~save:flush
    ~close:(fun () ->
      close_all ();
      reset ());
  is_serving := false

let call = Server.call
let list_servers = Server.list_servers
let stop = Server.stop
let wait_until_ended = Server.wait_until_ended

module For_testing = struct
  let load_standard_package_database () = (load_standard_package ()).package_database
  let build_cold_database = build_cold_database ~checks:true
  let collect_cache = collect
  let listen = Server.listen
  let call = Server.For_testing.call

  let interrupt_commit root =
    match Hashtbl.find_opt worktrees root with
    | Some worktree ->
        Segments.For_testing.interrupted_commit worktree.segments
          ~header:(make_header worktree.loaded)
          (Database.list_unsaved worktree.database);
        close worktree
    | None -> Compiler_bug.bug ~stage:"Workspace" "%s has no open database" root
end
