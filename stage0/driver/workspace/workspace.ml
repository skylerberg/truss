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
  match Lock_file.acquire_if_free (Filename.concat (Cache.directory cache) "collect.lock") with
  | None -> ()
  | Some lock ->
      Fun.protect
        ~finally:(fun () -> Lock_file.release lock)
        (fun () -> Cache.collect cache ~budget:(read_cache_budget ()))

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

let run_exclusively name work =
  Lock_file.with_lock (Filename.concat (Cache.directory (open_cache ())) name) work

let load_package_database (package : Project.package) ~hash ~visible =
  let key = make_package_database_key ~hash ~visible in
  match Hashtbl.find_opt loaded_package_databases key with
  | Some loaded -> loaded
  | None ->
      let find_stored () =
        Option.map
          (fun bytes -> (Marshal.from_string bytes 0 : Database.package_database))
          (Cache.find_result (open_cache ()) ~kind:Package_database ~key)
      in
      let package_database =
        match find_stored () with
        | Some package_database -> package_database
        | None ->
            run_exclusively "package-states.lock" (fun () ->
                match find_stored () with
                | Some package_database -> package_database
                | None ->
                    let package_database =
                      Database.build_package_database
                        ~loaded:(List.map (fun visible -> visible.package_database) visible)
                        package
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

let standard_hash =
  lazy
    (Registry.Content.hash
       (List.map
          (fun (file, text) -> (Project.make_file_path ~directory:"" file, text))
          Standard_library.files))

let load_standard_package () =
  let standard =
    load_package_database standard_package ~visible:[] ~hash:(Lazy.force standard_hash)
  in
  match Database.list_package_diagnostics standard.package_database with
  | [] -> standard
  | failed ->
      Compiler_bug.raise_bug ~stage:"Workspace" "the standard library has diagnostics:\n%s"
        (String.concat ""
           (List.concat_map
              (fun (source, diagnostics) -> List.map (Diagnostic.render source) diagnostics)
              failed))

let list_package_databases () =
  List.sort compare
    (Hashtbl.fold
       (fun _ { package; hash; _ } lines ->
         Printf.sprintf "%s %s" (Path.show_package package) (String.sub hash 0 16) :: lines)
       loaded_package_databases [])

type kind = Worktree of string | Trial of { root : string; database : Database.t Lazy.t }
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

let load_project files =
  let project_files = index_files files in
  let registry = Hashtbl.create 4 and unavailable = Hashtbl.create 4 in
  let find_indexed_files = function
    | Project.Project -> Some project_files
    | Registry hash -> Hashtbl.find_opt registry hash
  in
  let rec settle () =
    let project =
      Project.lay_out_project
        {
          find_tree = (fun root -> Option.map fst (find_indexed_files root));
          find_text =
            (fun root path ->
              Option.bind (find_indexed_files root) (fun (_, texts) -> Hashtbl.find_opt texts path));
          find_unavailable_reason = Hashtbl.find_opt unavailable;
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

let make_snapshot kind files = { kind; files; project = load_project files }

let replace_files (snapshot : snapshot) files =
  { snapshot with files; project = load_project files }

let find_project_root directory =
  let directory = try Unix.realpath directory with Unix.Unix_error _ -> directory in
  let has_project_table manifest =
    try Manifest.has_project_table (In_channel.with_open_bin manifest In_channel.input_all)
    with Sys_error _ -> false
  in
  let rec find_upward path nearest =
    let manifest = Filename.concat path "truss.toml" in
    let here = Sys.file_exists manifest in
    if here && has_project_table manifest then Some path
    else
      let nearest = if here && nearest = None then Some path else nearest in
      let parent = Filename.dirname path in
      if parent = path then nearest else find_upward parent nearest
  in
  find_upward directory None

let list_packages snapshot =
  List.map
    (fun (directory, (package : Manifest.package)) -> (directory, package.name))
    snapshot.project.project_layout.packages

let list_target_packages snapshot requested =
  let packages = list_packages snapshot in
  match
    List.filter
      (fun (directory, _) -> File_system.is_inside ~directory:requested directory)
      packages
  with
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

let locate_root snapshot = match snapshot.kind with Worktree root | Trial { root; _ } -> root

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
  let rec list_visible name =
    List.concat_map
      (fun dependency ->
        if List.mem_assoc dependency hashes then dependency :: list_visible dependency else [])
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
                  :: List.map load_named (List.sort_uniq Path.compare_package (list_visible name)))
          | None ->
              Compiler_bug.raise_bug ~stage:"Workspace" "%s has no files" (Path.show_package name)
        in
        Package_table.replace loaded_by_name name loaded;
        loaded
  in
  let rec depends_on_project seen name =
    (not (List.mem name seen))
    && List.exists
         (fun dependency ->
           (not (List.mem_assoc dependency hashes)) || depends_on_project (name :: seen) dependency)
         (list_dependency_names snapshot name)
  in
  standard
  :: List.filter_map
       (fun (name, _) -> if depends_on_project [] name then None else Some (load_named name))
       hashes

let describe_failed_dependency name version ~is_loaded failed =
  match failed with
  | (source, (first : Diagnostic.t) :: _) :: _ ->
      let line, column = Source.compute_position source first.span.start in
      Printf.sprintf "`%s` %s does not check %s. It has %s; the first is at %s:%d:%d: %s"
        (Path.show_package name) (Registry.Version.show version)
        (if is_loaded then "with this toolchain" else "against this project's packages")
        (Diagnostic.show_count
           (List.fold_left (fun total (_, diagnostics) -> total + List.length diagnostics) 0 failed)
           "error" "errors")
        (Source.path source) line column first.message
  | _ -> Compiler_bug.raise_bug ~stage:"Workspace" "a failed package lists no diagnostic"

let list_dependency_problems snapshot database =
  let loaded =
    List.map (fun (loaded : loaded) -> loaded.package) (load_package_databases snapshot)
  in
  List.filter_map
    (fun (name, version, _) ->
      match Database.list_dependency_diagnostics database name with
      | [] -> None
      | failed ->
          Some
            {
              Project.file = Project.lock_file;
              line = None;
              message =
                describe_failed_dependency name version ~is_loaded:(List.mem name loaded) failed;
            })
    (List.filter
       (fun (name, _, _) -> Option.is_some (find_package snapshot name))
       (list_registry_packages snapshot))

let load_layout snapshot =
  let loaded = load_package_databases snapshot in
  ( loaded,
    List.filter
      (fun (package : Project.package) ->
        not (List.exists (fun (candidate : loaded) -> candidate.package = package.name) loaded))
      snapshot.project.packages )

let extract_package_databases loaded =
  List.map (fun (loaded : loaded) -> loaded.package_database) loaded

let build_cold_database snapshot =
  let loaded, packages = load_layout snapshot in
  Database.create ~loaded:(extract_package_databases loaded) packages

let database_directory = ".truss"

let encode_header loaded =
  Cbor.encode
    (Cbor.Array
       [
         Cbor.Text Compiler_version.digest;
         Cbor.Array (List.map (fun (loaded : loaded) -> Cbor.Bytes loaded.key) loaded);
       ])

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
  match Option.bind (Segments.header segments) Cbor.decode with
  | Some (Cbor.Array [ Cbor.Text compiler; keys ]) when compiler = Compiler_version.digest ->
      Cbor.find_list
        (function Cbor.Bytes key -> find_saved_package_database ~current key | _ -> None)
        keys
  | Some _ | None -> None

let make_text_lookup snapshot =
  let texts = File_table.create 256 in
  List.iter
    (fun (package : Project.package) ->
      List.iter (fun (file, text) -> File_table.replace texts file text) package.files)
    snapshot.project.packages;
  File_table.find_opt texts

let restore_database segments snapshot =
  let loaded, packages = load_layout snapshot in
  let start_cold () =
    Segments.discard segments;
    Database.create ~loaded:(extract_package_databases loaded) packages
  in
  let database =
    match find_saved_package_databases segments ~current:loaded with
    | None -> start_cold ()
    | Some saved -> (
        match Segments.read_entries segments with
        | None -> start_cold ()
        | Some entries -> (
            try
              Database.restore ~saved ~find_text:(make_text_lookup snapshot)
                ~loaded:(extract_package_databases loaded)
                packages entries
            with Failure _ | Invalid_argument _ | End_of_file -> start_cold ()))
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
      match Segments.commit worktree.segments ~header:(encode_header worktree.loaded) entries with
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
  let list_layout_files snapshot = List.filter (fun (path, _) -> is_layout path) snapshot.files in
  if list_layout_files before <> list_layout_files after then None
  else
    let index_texts (snapshot : snapshot) =
      let table = File_table.create 256 in
      List.iter
        (fun (package : Project.package) ->
          List.iter (fun (file, text) -> File_table.replace table file text) package.files)
        snapshot.project.packages;
      table
    in
    let previous = index_texts before and current = index_texts after in
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

let apply_changes ?on_bug database (after : snapshot) = function
  | Some changes ->
      Database.update ?on_bug database changes;
      None
  | None ->
      let loaded, packages = load_layout after in
      Database.relayout ?on_bug database ~loaded:(extract_package_databases loaded) packages;
      Some loaded

let copy_database root (trial : snapshot) =
  match Hashtbl.find_opt worktrees root with
  | Some worktree ->
      let database = Database.copy worktree.database in
      ignore (apply_changes database trial (find_file_changes worktree.snapshot trial));
      database
  | None -> build_cold_database trial

let make_trial snapshot changes =
  let root = locate_root snapshot in
  let trial =
    replace_files snapshot
      (List.filter (fun (path, _) -> not (List.mem_assoc path changes)) snapshot.files
      @ List.filter_map (fun (path, text) -> Option.map (fun text -> (path, text)) text) changes)
  in
  { trial with kind = Trial { root; database = lazy (copy_database root trial) } }

let open_database snapshot =
  match snapshot.kind with
  | Worktree root -> (
      match Hashtbl.find_opt worktrees root with
      | Some worktree when worktree.snapshot == snapshot -> worktree.database
      | Some _ | None -> copy_database root snapshot)
  | Trial { database; _ } -> Lazy.force database

let list_changed_files root files paths =
  let prefixes =
    List.filter
      (fun path ->
        not
          (List.exists
             (fun other -> other <> path && File_system.is_inside ~directory:other path)
             paths))
      (List.sort_uniq compare paths)
  in
  let list_with_prefix prefix =
    let absolute = File_system.join_path root prefix in
    match (Unix.lstat absolute).st_kind with
    | S_DIR ->
        List.map
          (fun (path, text) -> (File_system.join_path prefix path, text))
          (Registry.Content.list_input_files absolute)
    | S_REG when Registry.Content.is_input (Filename.basename prefix) ->
        [ (prefix, File_system.read absolute) ]
    | _ -> []
    | exception Unix.Unix_error _ -> []
  in
  List.filter
    (fun (path, _) ->
      not (List.exists (fun prefix -> File_system.is_inside ~directory:prefix path) prefixes))
    files
  @ List.concat_map list_with_prefix prefixes

let refresh ?on_bug ~(read : Watcher.t -> Watcher.changes) worktree =
  let root = worktree.root in
  let update files =
    let before = worktree.snapshot in
    let after = replace_files before files in
    worktree.snapshot <- after;
    match find_file_changes before after with
    | Some [] -> `Unchanged
    | changes ->
        Option.iter
          (fun loaded -> worktree.loaded <- loaded)
          (apply_changes ?on_bug worktree.database after changes);
        `Changed
  in
  match Option.map read worktree.watcher with
  | Some Removed -> `Removed
  | Some Rescan | None -> update (Registry.Content.list_input_files root)
  | Some (Changed []) -> `Unchanged
  | Some (Changed paths) -> update (list_changed_files root worktree.snapshot.files paths)

let open_worktree root =
  let directory = Filename.concat root database_directory in
  match
    Segments.open_ directory ~stop_holder:(fun () -> Server.stop_servers ~key:root ~wait:false ())
  with
  | exception Unix.Unix_error (ENOENT, _, _) -> Error (root ^ ": no such directory.")
  | Error `Open_elsewhere ->
      Error
        (Printf.sprintf
           "The database in %s is open in another process, such as a command run with --no-server. \
            Wait for that process to end."
           directory)
  | Ok segments -> (
      let watcher =
        if !is_serving then
          Some
            (Watcher.start ~is_skipped_name:Registry.Content.is_skipped
               ~cookie_directory:database_directory root)
        else None
      in
      match
        let snapshot = make_snapshot (Worktree root) (Registry.Content.list_input_files root) in
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

let rec load_worktree_snapshot root =
  match Hashtbl.find_opt worktrees root with
  | None -> Result.map (fun worktree -> worktree.snapshot) (open_worktree root)
  | Some worktree -> (
      match refresh ~read:Watcher.read_changes worktree with
      | `Removed ->
          close worktree;
          load_worktree_snapshot root
      | `Changed | `Unchanged -> Ok worktree.snapshot)

let take_snapshot directory =
  if not (Sys.file_exists directory) then Error (directory ^ ": no such directory.")
  else
    match Unix.realpath directory with
    | exception Unix.Unix_error (error, _, _) ->
        Error (Printf.sprintf "%s: %s." directory (Unix.error_message error))
    | resolved -> (
        match find_project_root resolved with
        | None ->
            Error
              (Printf.sprintf
                 "No `truss.toml` in %s or any directory above it, so it is in no project."
                 directory)
        | Some root -> (
            match File_system.find_relative_path ~root resolved with
            | Some requested ->
                Result.map
                  (fun snapshot -> (snapshot, list_target_packages snapshot requested))
                  (load_worktree_snapshot root)
            | None ->
                Compiler_bug.raise_bug ~stage:"Workspace" "the project root %s does not contain %s"
                  root resolved))

let retake snapshot =
  match snapshot.kind with Worktree root -> load_worktree_snapshot root | Trial _ -> Ok snapshot

let propagate_changes descriptor =
  Hashtbl.iter
    (fun _ worktree ->
      if Option.map Watcher.extract_descriptor worktree.watcher = Some descriptor then
        match refresh ~on_bug:log_bug ~read:Watcher.read_pending_changes worktree with
        | `Removed -> close worktree
        | `Unchanged -> ()
        | `Changed -> commit worktree
        | exception Compiler_bug.Bug bug ->
            log_bug bug;
            close worktree)
    (Hashtbl.copy worktrees)

let problems snapshot = snapshot.project.problems

let locate_file snapshot (file : Path.file) =
  match List.assoc_opt file.module_.package snapshot.project.places with
  | Some { root = Project.Project; directory; _ } -> Project.make_file_path ~directory file
  | _ -> Path.show_file file

let time_limit_ms snapshot = snapshot.project.project_layout.time_limit_ms
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
          let manifests = List.map snd snapshot.project.project_layout.packages in
          let is_local name =
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
              ~is_local ~load:load_published
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

let close_all () =
  List.iter
    (fun worktree ->
      commit worktree;
      close worktree)
    (Hashtbl.fold (fun _ worktree worktrees -> worktree :: worktrees) worktrees [])

let save () =
  Hashtbl.iter (fun _ worktree -> commit worktree) worktrees;
  flush_cache ()

let flush () =
  if !is_serving then save ()
  else begin
    close_all ();
    flush_cache ()
  end

let serve ~key ~handle =
  is_serving := true;
  Server.serve ~key
    ~is_alive:(fun () -> Sys.file_exists key)
    ~collect
    ~list_watcher_descriptors:(fun () ->
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
let stop_servers ?key () = Server.stop_servers ?key ~wait:true ()

module For_testing = struct
  let load_standard_package_database () = (load_standard_package ()).package_database

  let copy_standard_package_database ~into =
    let standard = load_standard_package () in
    match Cache.open_ into with
    | Error message -> raise (Unusable_cache message)
    | Ok cache ->
        Cache.add_result cache ~kind:Package_database ~key:standard.key
          (Marshal.to_string standard.package_database []);
        Cache.flush cache;
        Cache.close cache

  let build_cold_database = build_cold_database
  let collect_cache = collect
  let save = save
  let listen = Server.listen
  let call_starting = Server.For_testing.call_starting
  let remove_ended_servers = Server.For_testing.remove_ended_servers

  let interrupt_commit root =
    match Hashtbl.find_opt worktrees root with
    | Some worktree ->
        Segments.For_testing.interrupt_commit worktree.segments
          ~header:(encode_header worktree.loaded)
          (Database.list_unsaved worktree.database);
        close worktree
    | None -> Compiler_bug.raise_bug ~stage:"Workspace" "%s has no open database" root

  let compiler_digest = Compiler_version.digest
end
