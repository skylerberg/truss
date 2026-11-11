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
    time_limit = Type_checker.Manifest.default_time_limit;
    registry = [];
  }

let layout : (unit, layout) Query.input =
  Query.input ~name:"worktree_layout" ~show:(fun () -> "") ()

let stamps : (string, Worktree.stamp) Query.input =
  Query.input ~name:"worktree_stamp" ~show:Fun.id ()

(* Each manifest's text, by its package's directory, so that an unchanged
   manifest need not be read again. *)
let manifest_texts : (string, string) Query.input =
  Query.input ~name:"worktree_manifest" ~show:Fun.id ()

(* The project's lock file's text, for the same reason. *)
let lock_text : (unit, string) Query.input =
  Query.input ~name:"worktree_lock" ~show:(fun () -> "") ()

(* Sessions *)

type source = Directory of string | Commit of { repository : string; commit : string }

type session = {
  source : source;
  mutable engine : Engine.t;
  pointer : Store.pointer option;  (** Where a worktree's current state is named *)
  mutable problems : string list;  (** Manifests that could not be read, and duplicate names *)
  mutable lock_fix : string option;
      (** The lock file the manifests give, when the one written is another *)
  mutable used : float;
  texts : (string, string) Hashtbl.t;
      (** Each manifest and module file's fingerprint, by its path from the root *)
  mutable pointed : bool;  (** Whether the pointer names the state as it is *)
  mutable applied : bool;  (** Whether this process has brought the inputs in line with the files *)
}

(* The standard library as a state of its own, for working on the library. *)
type library = { library_engine : Engine.t; library_pointer : Store.pointer }

type state = {
  store : Store.t;
  identity : string;
  standard : Engine.t Lazy.t;  (** The standard library, a fixed base under every state *)
  sessions : (string, session) Hashtbl.t;
      (** By root, or for a commit, by the project's root and the commit *)
  libraries : (string, library) Hashtbl.t;  (** By name *)
}

let state : state option ref = ref None

let budget () =
  match Option.bind (Sys.getenv_opt "TRUSS_CACHE_SIZE") int_of_string_opt with
  | Some bytes -> bytes
  | None -> 20 * 1024 * 1024 * 1024

(* A package whose sources never change is checked once, written whole, and
   found from then on by the key of its sources: for the standard library,
   which is built into the compiler, the compiler's identity. *)
let standard_key identity = identity ^ " standard"

let stored_standard store identity =
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

let current () =
  match !state with
  | Some state -> state
  | None ->
      Engine.seal ();
      let store = Store.open_ (Store.default_directory ()) in
      let identity = Identity.compute (Store.directory store) in
      let fresh =
        {
          store;
          identity;
          standard = lazy (stored_standard store identity);
          sessions = Hashtbl.create 8;
          libraries = Hashtbl.create 1;
        }
      in
      state := Some fresh;
      fresh

let prepare_store () = ignore (Lazy.force (current ()).standard)
let session_prefix state = Printf.sprintf "session-%s-" (Identity.short state.identity)

let session_name state root =
  session_prefix state ^ String.sub (Blake3.to_hex (Blake3.hash root)) 0 16

(* The list of worktrees with states, so that collection can tell which
   still have a worktree. *)
let worktrees_file state = Filename.concat (Store.directory state.store) "worktrees"

let known_worktrees state =
  try
    In_channel.with_open_bin (worktrees_file state) In_channel.input_lines
    |> List.filter_map (fun line ->
        match String.index_opt line '\t' with
        | Some i -> Some (String.sub line 0 i, String.sub line (i + 1) (String.length line - i - 1))
        | None -> None)
  with Sys_error _ -> []

let remember_worktree state root name =
  if not (List.mem (root, name) (known_worktrees state)) then
    try
      Out_channel.with_open_gen [ Open_append; Open_creat; Open_binary ]
        0o644 (worktrees_file state) (fun out -> Printf.fprintf out "%s\t%s\n" root name)
    with Sys_error _ -> ()

let read context input key = Query.find context input key
let current_layout engine = Option.value (read (Engine.context engine) layout ()) ~default:no_layout

(* A file's fingerprint, for telling which saved state a set of files is
   nearest to. *)
let text_fingerprint text = Blake3.hash text

(* Setting a worktree's files as inputs *)

type file_contents = Text of string | Unchanged

let manifest_file directory = if directory = "" then "truss.toml" else directory ^ "/truss.toml"

(* Registry packages *)

type published = {
  manifest : Type_checker.Manifest.package;
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
            ( Option.map Type_checker.Manifest.parse (text "truss.toml"),
              Registry.Lock.parse (Option.value ~default:"" (text "truss.lock")) )
          with
          | exception Type_checker.Manifest.Malformed (line, message) ->
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
let dependency_cycle (packages : (string * Type_checker.Manifest.package) list) =
  let dependencies name =
    match
      List.find_opt (fun (_, (p : Type_checker.Manifest.package)) -> p.name = name) packages
    with
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
    (fun (directory, (package : Type_checker.Manifest.package)) ->
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
  let module Manifest = Type_checker.Manifest in
  let engine = session.engine in
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
  let store_packages = Store.files (current ()).store "packages" in
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
  session.lock_fix <- None;
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
        session.lock_fix <- Some text;
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
      | Text text ->
          let fingerprint = text_fingerprint text in
          if Hashtbl.find_opt session.texts path <> Some fingerprint then begin
            Hashtbl.replace session.texts path fingerprint;
            session.pointed <- false
          end
      | Unchanged -> ())
    files;
  let listed = Hashtbl.create (List.length files) in
  List.iter (fun (path, _) -> Hashtbl.replace listed path ()) files;
  List.iter
    (fun path ->
      if not (Hashtbl.mem listed path) then begin
        Hashtbl.remove session.texts path;
        session.pointed <- false
      end)
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
  session.problems <- List.rev !problems

(* Reads the files of a directory whose stamps changed, and sets them. A
   file that cannot be read, such as one deleted since the directory was
   listed, is not there. A stamp is set only once its file's text is, so
   that a scan that fails leaves the file to be read by the next. *)
let scan session root =
  let engine = session.engine in
  let context = Engine.context engine in
  let text path =
    try Some (In_channel.with_open_bin (Filename.concat root path) In_channel.input_all)
    with Sys_error _ -> None
  in
  let found =
    List.filter_map
      (fun (path, stamp) ->
        match read context stamps path with
        | Some old when old = stamp -> Some (path, stamp, Unchanged)
        | _ -> Option.map (fun text -> (path, stamp, Text text)) (text path))
      (Worktree.files root)
  in
  let old = current_layout engine in
  (* A scan that finds every file as it was has nothing to bring in line.
     With a problem outstanding it looks again, since a problem can be one
     that the files do not show, such as a package that could not be
     fetched. *)
  let unchanged =
    session.applied && session.problems = []
    && List.for_all (fun (_, _, contents) -> contents = Unchanged) found
    && List.length found = List.length old.files
  in
  if not unchanged then begin
    apply ~text session (List.map (fun (path, _, contents) -> (path, contents)) found);
    session.applied <- true
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

(* A worktree's pointer holds the name of its state's artifact, and each of
   its files' fingerprints, by which a new worktree finds the saved state
   nearest to it. *)
type record = { artifact : string; files : (string * string) list }

let read_record pointer : record option =
  match Store.read pointer with
  | Some bytes -> ( try Some (Marshal.from_string bytes 0) with _ -> None)
  | None -> None

let logging = ref false

let new_engine state =
  let engine = Engine.create ~log:!logging ~bases:[ Lazy.force state.standard ] () in
  Engine.attach engine state.store ~version:state.identity;
  engine

let open_state state artifact =
  Engine.open_ ~log:!logging state.store ~version:state.identity
    ~bases:[ Lazy.force state.standard ]
    artifact

(* Writes what changed in a session's state since it was last written, as a
   difference over the artifact it was opened from or last wrote, and points
   the worktree at it. *)
let save state session =
  match session.pointer with
  | Some pointer when Engine.unwritten session.engine || not session.pointed ->
      let artifact = Engine.write session.engine in
      let files =
        List.sort compare
          (Hashtbl.fold (fun path print found -> (path, print) :: found) session.texts [])
      in
      Store.point pointer (Marshal.to_string { artifact; files } []);
      session.pointed <- true
  | _ -> Engine.record session.engine

let stabilize state session =
  let change = Engine.stabilize session.engine in
  save state session;
  change

(* A chain of differences is folded into one whole state once the
   differences reach half its size, which costs the state's size. So the
   background process folds while no request is waiting, and makes a command
   wait for it only once the differences are several times that. A process
   that serves one command folds as it opens the state, which costs it the
   state's size already. *)
let serving = ref false

let fold ?(waited_for = false) state session =
  match session.pointer with
  | Some pointer ->
      let debt = Engine.debt session.engine in
      let limit = max (debt.whole / 2) 256 in
      if debt.differences > if waited_for && !serving then 4 * limit else limit then begin
        let artifact = Engine.write ~full:true session.engine in
        let files =
          List.sort compare
            (Hashtbl.fold (fun path print found -> (path, print) :: found) session.texts [])
        in
        Store.point pointer (Marshal.to_string { artifact; files } []);
        session.pointed <- true;
        Option.iter (fun engine -> session.engine <- engine) (open_state state artifact)
      end
  | None -> ()

(* The saved state nearest to a set of files: the one that differs from them
   in the fewest files, if it shares any. *)
let nearest state (texts : (string * string) list) =
  (* Another process may have written a state a moment ago. *)
  Store.refresh state.store;
  let prefix = session_prefix state in
  let wanted = Hashtbl.create (List.length texts) in
  List.iter (fun (path, print) -> Hashtbl.replace wanted path print) texts;
  let score (record : record) =
    let shared =
      List.fold_left
        (fun shared (path, print) ->
          if Hashtbl.find_opt wanted path = Some print then shared + 1 else shared)
        0 record.files
    in
    (shared, List.length record.files + List.length texts - (2 * shared))
  in
  List.fold_left
    (fun best name ->
      if not (String.starts_with ~prefix name) then best
      else
        match read_record (Store.pointer state.store name) with
        | None -> best
        | Some record -> (
            let shared, differing = score record in
            if shared = 0 then best
            else
              match best with
              | Some (_, least) when least <= differing -> best
              | _ -> Some (record, differing)))
    None (Store.pointers state.store)
  |> Option.map fst

(* An engine for a set of files that has no state of its own: the nearest
   saved state's, or a new one over the standard library. The second result
   says whether it came from another state. *)
let engine_near state texts =
  match Option.bind (nearest state texts) (fun record -> open_state state record.artifact) with
  | Some engine when Engine.inputs_stored engine -> (engine, true)
  | Some _ | None -> (new_engine state, false)

let fingerprints root =
  List.map
    (fun (path, _) ->
      ( path,
        text_fingerprint (In_channel.with_open_bin (Filename.concat root path) In_channel.input_all)
      ))
    (Worktree.files root)

let open_directory state root =
  match Hashtbl.find_opt state.sessions root with
  | Some session -> Ok session
  | None ->
      let name = session_name state root in
      let pointer = Store.pointer state.store name in
      if not (Store.lock pointer) then
        Error
          (Printf.sprintf
             "%s is open in another process of this compiler, such as its background process; \
              leave out --no-server, or stop that process with `truss stop`."
             root)
      else
        let own =
          (* Another process may have written the state a moment ago. *)
          Store.refresh state.store;
          Option.bind (read_record pointer) (fun record ->
              Option.map (fun engine -> (engine, record)) (open_state state record.artifact))
        in
        let engine, files, near =
          match own with
          | Some (engine, record) -> (engine, record.files, false)
          | None ->
              (* A new worktree starts from the nearest saved state. *)
              let engine, near = engine_near state (fingerprints root) in
              (engine, [], near)
        in
        let texts = Hashtbl.create (max 16 (List.length files)) in
        List.iter (fun (path, print) -> Hashtbl.replace texts path print) files;
        let session =
          {
            source = Directory root;
            engine;
            pointer = Some pointer;
            problems = [];
            lock_fix = None;
            used = Unix.time ();
            texts;
            pointed = own <> None;
            applied = false;
          }
        in
        if near then
          (* The stamps it carries are another worktree's. *)
          List.iter (fun path -> Engine.remove engine stamps path) (current_layout engine).files;
        Hashtbl.replace state.sessions root session;
        remember_worktree state root name;
        Ok session

let open_commit state ~repository commit =
  let name = Printf.sprintf "commit:%s:%s" repository commit in
  match Hashtbl.find_opt state.sessions name with
  | Some session -> Ok session
  | None -> (
      match Git.files ~directory:repository commit with
      | None -> Error (Printf.sprintf "cannot read commit %s." commit)
      | Some texts ->
          let engine, _ =
            engine_near state (List.map (fun (path, text) -> (path, text_fingerprint text)) texts)
          in
          let session =
            {
              source = Commit { repository; commit };
              engine;
              pointer = None;
              problems = [];
              lock_fix = None;
              used = Unix.time ();
              texts = Hashtbl.create 16;
              pointed = true;
              applied = false;
            }
          in
          apply session (List.map (fun (path, text) -> (path, Text text)) texts);
          ignore (Engine.stabilize engine);
          Hashtbl.replace state.sessions name session;
          Ok session)

(* The root of the project a directory is in: the nearest directory at or
   above it whose manifest has a [[project]] table, or with none, the
   nearest with a manifest, which is a package that is a project by
   itself. *)
let root_of directory =
  let directory = try Unix.realpath directory with Unix.Unix_error _ -> directory in
  let has_project_table manifest =
    try
      Type_checker.Manifest.has_project_table
        (In_channel.with_open_bin manifest In_channel.input_all)
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
  let lay = current_layout session.engine in
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
  match read (Engine.context session.engine) Workspace.packages name with
  | Some package -> package.modules
  | None -> []

(* Sessions as the command line sees them *)

let root_of_session session =
  match session.source with Directory root -> root | Commit c -> c.repository

let root = root_of_session
let engine session = session.engine
let context session = Engine.context session.engine
let problems session = session.problems

(* What only a package's code shows to be wrong with its manifest, which
   checks the package. *)
let manifest_problems session names =
  List.concat_map
    (fun (directory, name) ->
      if not (List.mem name names) then []
      else
        List.map
          (fun problem -> (manifest_file directory, name, problem))
          (try Engine.get session.engine Type_checker.manifest_problems name with Not_found -> []))
    (current_layout session.engine).packages

let packages session = (current_layout session.engine).packages

let module_file session (module_ : Path.module_) =
  let lay = current_layout session.engine in
  match List.find_opt (fun (_, name) -> name = module_.package) lay.packages with
  | Some (directory, _) -> Worktree.module_file ~package_directory:directory module_
  | None -> Workspace.file_path module_

let time_limit session = (current_layout session.engine).time_limit
let registry_packages session = (current_layout session.engine).registry
let lock_fix session = session.lock_fix

let diagnostics session module_ =
  try Engine.get session.engine Type_checker.file_diagnostics module_ with Not_found -> []

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
        let state = current () in
        match open_directory state root with
        | Error message -> Error message
        | Ok session ->
            session.used <- Unix.time ();
            (* Before any command holds the session's engine. *)
            fold ~waited_for:true state session;
            scan session root;
            (* The state is written when the command is done, with what the
               command computed, so that a first write holds a whole state. *)
            ignore (Engine.stabilize session.engine);
            Ok (session, target_packages session (relative_to root directory)))

let refresh session =
  match session.source with
  | Directory root ->
      scan session root;
      ignore (Engine.stabilize session.engine)
  | Commit _ -> ()

let save_session session = save (current ()) session
let objects_directory () = Store.files (current ()).store "objects"
let programs_directory () = Store.files (current ()).store "programs"

let test_results () : Compile.results =
  let store = (current ()).store in
  {
    find = (fun key -> Store.find_result store ~kind:"tests" ~key);
    add = (fun key value -> Store.add_result store ~kind:"tests" ~key value);
  }

let flush_store () = Store.flush (current ()).store

(* The roots code generation searches from are an input, which only the
   database sets. *)
let want_in engine lowering wanted =
  let old = Option.value (read (Engine.context engine) Compile.roots lowering) ~default:[] in
  let all = List.sort_uniq Instance.compare (wanted @ old) in
  if all <> old then Engine.set engine Compile.roots lowering all

let want session lowering wanted = want_in session.engine lowering wanted

let sessions () =
  match !state with
  | None -> []
  | Some state ->
      Hashtbl.fold
        (fun key session acc -> (key, List.length (Engine.nodes session.engine)) :: acc)
        state.sessions []
      |> List.sort compare

(* Graph questions. Every answer names definitions and parts; the engine's
   nodes stay inside. *)

let subject_of node = Engine.subject node

(* What a node's definition reads of other definitions: its reads, through
   nodes about no definition, to the definitions and parts they reach. *)
let definition_reads engine memo node =
  let own = Option.map (fun (s : Query.subject) -> s.path) (subject_of node) in
  let found = Hashtbl.create 8 in
  let seen = Hashtbl.create 16 in
  let rec walk n =
    List.iter
      (fun read ->
        let identity = Engine.identity read in
        if not (Hashtbl.mem seen identity) then begin
          Hashtbl.replace seen identity ();
          match subject_of read with
          | Some subject when Some subject.path <> own ->
              Hashtbl.replace found (subject.path, Option.value subject.part ~default:"") ()
          | Some _ | None -> (
              if
                (* The standard library's own lookups are not followed, so a
                 definition is not said to read everything they read. *)
                not (Engine.is_fixed read)
              then
                match Hashtbl.find_opt memo identity with
                | Some reached -> List.iter (fun r -> Hashtbl.replace found r ()) reached
                | None -> walk read)
        end)
      (Engine.reads engine n)
  in
  walk node;
  let reached = Hashtbl.fold (fun r () acc -> r :: acc) found [] in
  reached

(* For every definition in a session, what it reads of every other. The
   worktree is checked first, so that every definition's results are there
   to read. *)
let dependency_table session =
  ignore (diagnostics_of session (current_layout session.engine).packages);
  let memo = Hashtbl.create 1024 in
  let table : (Path.t, (Path.t * string * string) list) Hashtbl.t = Hashtbl.create 256 in
  List.iter
    (fun node ->
      match subject_of node with
      | Some subject ->
          let part = Option.value subject.part ~default:"" in
          let reads = definition_reads session.engine memo node in
          let previous = Option.value (Hashtbl.find_opt table subject.path) ~default:[] in
          Hashtbl.replace table subject.path
            (List.map (fun (path, read_part) -> (path, part, read_part)) reads @ previous)
      | None -> ())
    (Engine.nodes session.engine);
  table

let all_declarations session =
  let lay = current_layout session.engine in
  List.concat_map
    (fun (_, name) ->
      List.concat_map
        (fun module_ ->
          try Engine.get session.engine Resolve.Names.declarations module_ with _ -> [])
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

type dependencies = (Path.t, (Path.t * string * string) list) Hashtbl.t

let dependencies = dependency_table
let reads (table : dependencies) path = Option.value (Hashtbl.find_opt table path) ~default:[]

let readers (table : dependencies) target =
  Hashtbl.fold
    (fun reader reads acc ->
      List.filter_map
        (fun (path, reader_part, read_part) ->
          if Path.equal path target then Some (reader, reader_part, read_part) else None)
        reads
      @ acc)
    table []
  |> List.sort_uniq compare

(* Comparing a session with another, such as its base commit's *)

type difference = Changed | Added | Same

(* Every node of [mine] that may differ from the same node in [theirs],
   with how it compares. A state holds only what differs from its bases, or
   may, so where the two share a base these are the nodes either holds
   itself; a base that only one has is compared whole. *)
let compare_sessions mine theirs =
  let differs node =
    match Engine.current_in node theirs.engine with
    | None -> Added
    | Some other ->
        if Engine.same_outcome mine.engine node theirs.engine other then Same else Changed
  in
  let seen = Hashtbl.create 256 in
  let found = ref [] in
  let consider node =
    let identity = Engine.identity node in
    if not (Hashtbl.mem seen identity) then begin
      Hashtbl.replace seen identity ();
      found := node :: !found
    end
  in
  List.iter consider (Engine.unshared mine.engine theirs.engine);
  List.iter
    (fun other -> Option.iter consider (Engine.current_in other mine.engine))
    (Engine.unshared theirs.engine mine.engine);
  List.rev_map (fun node -> (node, differs node)) !found

(* Checks every package of a session, so that every definition's results
   are there to compare and to walk; kept results make this cheap. *)
let check_all session = ignore (diagnostics_of session (current_layout session.engine).packages)

let changes mine theirs =
  check_all mine;
  List.filter_map
    (fun (node, difference) ->
      match subject_of node with
      | Some (subject : Query.subject) -> Some (subject.path, subject.part, difference)
      | None -> None)
    (compare_sessions mine theirs)

let base_commit session base =
  let root = root_of_session session in
  match base with
  | Some revision -> Git.resolve ~directory:root revision
  | None -> (
      match (Git.head ~directory:root, Git.default_branch ~directory:root) with
      | Some head, Some branch -> Git.merge_base ~directory:root head branch
      | Some head, None -> Some head
      | None, _ -> None)

let open_commit_of session commit =
  open_commit (current ()) ~repository:(root_of_session session) commit

(* Parallel work *)

type place = { path : Path.t option; part : string option; label : string }

type overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }
      (** One worktree's change reads what the other changes *)

(* Where two sessions' changes from a common base meet: each node both
   changed, and each node one changed that reads what the other changed. *)
let overlaps ~base mine theirs =
  let changed session =
    List.filter_map
      (fun (node, difference) -> if difference = Same then None else Some node)
      (compare_sessions session base)
  in
  let mine_changed = changed mine and theirs_changed = changed theirs in
  let by_identity nodes =
    let table = Hashtbl.create 64 in
    List.iter (fun n -> Hashtbl.replace table (Engine.identity n) n) nodes;
    table
  in
  let mine_table = by_identity mine_changed and theirs_table = by_identity theirs_changed in
  let describe node =
    match subject_of node with
    | Some subject -> { path = Some subject.path; part = subject.part; label = Engine.label node }
    | None -> { path = None; part = None; label = Engine.label node }
  in
  let both =
    List.filter_map
      (fun node ->
        if Hashtbl.mem theirs_table (Engine.identity node) then Some (Both_change (describe node))
        else None)
      mine_changed
  in
  let reads_other session changed own_table other_table ~this_worktree =
    List.concat_map
      (fun node ->
        if subject_of node = None then []
        else
          List.filter_map
            (fun read ->
              let identity = Engine.identity read in
              match Hashtbl.find_opt other_table identity with
              | Some other when not (Hashtbl.mem own_table identity) ->
                  Some (Reads { this_worktree; change = describe node; reads = describe other })
              | _ -> None)
            (Engine.reads session.engine node))
      changed
  in
  List.sort_uniq compare
    (both
    @ reads_other mine mine_changed mine_table theirs_table ~this_worktree:true
    @ reads_other theirs theirs_changed theirs_table mine_table ~this_worktree:false)

(* A commit of a worktree's files as they are, for merging. *)
let commit_of_worktree root = Git.snapshot ~directory:root

(* The same project in another worktree is at the same place under its
   worktree's top. *)
let other_worktrees session =
  let state = current () in
  let root = root_of_session session in
  let common = Git.common_directory root and prefix = Git.prefix root in
  Hashtbl.fold
    (fun _ other acc ->
      match other.source with
      | Directory other_root
        when other_root <> root && common <> None
             && Git.common_directory other_root = common
             && Git.prefix other_root = prefix ->
          other :: acc
      | _ -> acc)
    state.sessions []

let overlap_with session other =
  let state = current () in
  check_all session;
  check_all other;
  let root = root_of_session session in
  let mine_commit = Git.head ~directory:root in
  let theirs_commit =
    match other.source with
    | Directory other_root -> Git.head ~directory:other_root
    | Commit c -> Some c.commit
  in
  match (mine_commit, theirs_commit) with
  | Some a, Some b -> (
      match Git.merge_base ~directory:root a b with
      | None -> Error "no common commit."
      | Some base -> (
          match open_commit state ~repository:root base with
          | Error message -> Error message
          | Ok base_session -> Ok (overlaps ~base:base_session session other)))
  | _ -> Error "not a git worktree."

(* An engine that starts from a session's state and changes on its own, for
   trying a change: the session's state is written, and opened again, so
   the two share everything but what the trial changes. *)
let trial_engine state session =
  save state session;
  let artifact =
    match Engine.artifact session.engine with
    | Some artifact when not (Engine.unwritten session.engine) -> artifact
    | _ -> Engine.write session.engine
  in
  match open_state state artifact with Some engine -> engine | None -> new_engine state

let trial session = trial_engine (current ()) session

(* The standard library as a state of its own *)

let library_prefix = Printf.sprintf "library-%s-" (String.sub Compiler_version.digest 0 16)

(* The inputs of the [standard] package, set from sources: each module's
   text, and the package with its modules. The text of a module that the
   state holds and the sources do not is removed. *)
let set_library engine (modules : (Path.module_ * string) list) =
  (match read (Engine.context engine) Workspace.packages Path.standard_package with
  | Some (package : Workspace.package) ->
      List.iter
        (fun module_ ->
          if not (List.mem_assoc module_ modules) then
            Engine.remove engine Workspace.file_text module_)
        package.modules
  | None -> ());
  load_package ~usize_bits:64 engine ~name:Path.standard_package ~dependencies:[] modules

let write_library ?full library =
  let artifact = Engine.write ?full library.library_engine in
  Store.point library.library_pointer (Marshal.to_string { artifact; files = [] } [])

let open_library ?(modules = Standard_library.modules) name =
  let state = current () in
  match Hashtbl.find_opt state.libraries name with
  | Some library ->
      set_library library.library_engine modules;
      Ok library
  | None ->
      let pointer = Store.pointer state.store (library_prefix ^ name) in
      if not (Store.lock pointer) then
        Error (Printf.sprintf "The library state `%s` is open in another process." name)
      else begin
        Store.refresh state.store;
        let version = Compiler_version.digest in
        let opened =
          Option.bind (read_record pointer) (fun record ->
              Engine.open_ ~log:!logging state.store ~version ~bases:[] record.artifact)
        in
        let engine =
          match opened with
          | Some engine -> engine
          | None ->
              let engine = Engine.create ~log:!logging () in
              Engine.attach engine state.store ~version;
              engine
        in
        let library = { library_engine = engine; library_pointer = pointer } in
        (* A process that opens the state pays its size already, so this is
           when its differences are folded into one whole state. *)
        let debt = Engine.debt engine in
        let library =
          if debt.differences > max (debt.whole / 2) 256 then begin
            write_library ~full:true library;
            match
              Option.bind (Engine.artifact engine)
                (Engine.open_ ~log:!logging state.store ~version ~bases:[])
            with
            | Some engine -> { library with library_engine = engine }
            | None -> library
          end
          else library
        in
        set_library library.library_engine modules;
        Hashtbl.replace state.libraries name library;
        Ok library
      end

let library_engine library = library.library_engine

let save_library library =
  if Engine.unwritten library.library_engine then write_library library
  else Engine.record library.library_engine

(* Choosing versions *)

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

let project_manifests session =
  List.filter_map
    (fun (_, name) -> read (Engine.context session.engine) Workspace.packages name)
    (current_layout session.engine).packages

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
            (Option.value ~default:"" (read (Engine.context session.engine) lock_text ()))
        with Registry.Lock.Malformed _ -> []
      in
      let set =
        set
        @
        if all then
          List.filter_map
            (fun (name, _, _) -> if List.mem_assoc name set then None else Some (name, None))
            (current_layout session.engine).registry
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
          let packages = Store.files (current ()).store "packages" in
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

(* A published package at a version, in an engine of its own with the
   packages it was published with, for comparing a release with it. *)
let published_engine name version =
  let state = current () in
  let packages = Store.files state.store "packages" in
  match
    Option.bind (Registry.Index.current ()) (fun registry ->
        Registry.Index.hash_of registry name version)
  with
  | None ->
      Error (Printf.sprintf "The registry has no `%s` %s." name (Registry.Version.show version))
  | Some hash ->
      let engine = new_engine state in
      let set name version ~hash =
        match load_published ~packages name version ~hash with
        | Ok found ->
            set_published engine found;
            Ok found
        | Error reason ->
            Error
              (Printf.sprintf "`%s` %s cannot be read: %s." name (Registry.Version.show version)
                 reason)
      in
      Result.bind (set name version ~hash) (fun found ->
          List.fold_left
            (fun result (entry : Registry.Lock.entry) ->
              Result.bind result (fun engine ->
                  Result.map (fun _ -> engine) (set entry.name entry.version ~hash:entry.hash)))
            (Ok engine) found.record)

let code_packages session name =
  try Engine.get session.engine Type_checker.code_packages name with Not_found -> []

(* A session that starts from another's state, with a lock file in place of
   its own, for seeing what other versions would change before the file is
   written. It is never saved. *)
let trial_with_lock session text =
  let state = current () in
  let trial =
    {
      source = session.source;
      engine = trial_engine state session;
      pointer = None;
      problems = [];
      lock_fix = None;
      used = Unix.time ();
      texts = Hashtbl.create 16;
      pointed = true;
      applied = false;
    }
  in
  let files = (current_layout session.engine).files in
  apply trial
    (("truss.lock", Text text)
    :: List.filter_map
         (fun path -> if path = "truss.lock" then None else Some (path, Unchanged))
         files);
  ignore (Engine.stabilize trial.engine);
  trial

(* The diagnostics of a merge of two commits that neither has. *)
let merge_preview session other =
  let state = current () in
  let root = root_of_session session in
  match
    ( commit_of_worktree root,
      match other.source with
      | Directory other_root -> commit_of_worktree other_root
      | Commit c -> Some c.commit )
  with
  | None, _ | _, None -> Error "cannot make commits to merge."
  | Some mine, Some theirs -> (
      match Git.merged_files ~directory:root mine theirs with
      | None -> Error "the two do not merge without a textual conflict."
      | Some texts ->
          let merged =
            {
              source = Commit { repository = root; commit = "merge" };
              engine = trial_engine state session;
              pointer = None;
              problems = [];
              lock_fix = None;
              used = Unix.time ();
              texts = Hashtbl.create 16;
              pointed = true;
              applied = false;
            }
          in
          apply merged (List.map (fun (path, text) -> (path, Text text)) texts);
          let keys s =
            List.concat_map
              (fun (m, ds) ->
                List.map (fun (d : Diagnostic.t) -> (m, Diagnostic.Code.name d.code, d.message)) ds)
              (diagnostics_of s (current_layout s.engine).packages)
          in
          let sides =
            List.concat_map
              (fun commit ->
                match open_commit state ~repository:root commit with
                | Ok side -> keys side
                | Error _ -> [])
              [ mine; theirs ]
          in
          Ok
            (List.filter_map
               (fun ((m, code, message) as key) ->
                 if List.mem key sides then None else Some (module_file merged m, code, message))
               (List.sort_uniq compare (keys merged))))

(* Runs a command. If a state it reads has lost an input's value, as after
   another process collected the store, every open state is discarded with
   its pointer, and the command is run once more, from the files. *)
let recovering run =
  try run ()
  with Engine.Lost _ ->
    (match !state with
    | Some s ->
        let discard pointer =
          Store.remove_pointer pointer;
          Store.unlock pointer
        in
        Hashtbl.iter (fun _ session -> Option.iter discard session.pointer) s.sessions;
        Hashtbl.iter (fun _ library -> discard library.library_pointer) s.libraries;
        Store.close s.store;
        Engine.forget_bases ();
        state := None
    | None -> ());
    run ()

let stopping = ref false
let stop () = stopping := true

let reset () =
  match !state with
  | None -> ()
  | Some s ->
      Hashtbl.iter (fun _ session -> save s session) s.sessions;
      Hashtbl.iter
        (fun _ library ->
          save_library library;
          Store.unlock library.library_pointer)
        s.libraries;
      Store.close s.store;
      Engine.forget_bases ();
      state := None

let session_engine directory =
  match !state with
  | None -> None
  | Some s ->
      Option.bind (root_of directory) (fun root ->
          Option.map (fun session -> session.engine) (Hashtbl.find_opt s.sessions root))

(* The background process *)

let rec make_directory path =
  if not (Sys.file_exists path) then begin
    make_directory (Filename.dirname path);
    try Unix.mkdir path 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* Only the user may reach the background process: what travels over its
   socket is marshaled, and reading marshaled bytes from another user would
   let that user run code as this one. *)
let servers_directory () =
  let directory = Filename.concat (Store.default_directory ()) "servers" in
  make_directory directory;
  (try Unix.chmod directory 0o700 with Unix.Unix_error _ -> ());
  directory

(* A directory in /tmp that is the user's alone. Another user could have
   made one of this name first, so it is used only if it is a directory,
   this user's, and closed to everyone else. *)
let private_temporary_directory () =
  let directory = Printf.sprintf "/tmp/truss-%d" (Unix.getuid ()) in
  (try Unix.mkdir directory 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  match Unix.lstat directory with
  | { st_kind = S_DIR; st_uid; st_perm; _ } when st_uid = Unix.getuid () && st_perm land 0o077 = 0
    ->
      directory
  | _ | (exception Unix.Unix_error _) ->
      failwith (directory ^ " is not a directory that only this user can use.")

(* The socket's address, and its lock beside it in the store. A socket's
   path has a short limit, about 100 bytes, so one under a long store path
   goes in a directory of the user's own in /tmp, named by a hash of where it
   would have been. *)
let server_path identity = Filename.concat (servers_directory ()) (Identity.short identity)

let socket_path identity =
  let path = server_path identity ^ ".socket" in
  if String.length path < 100 then path
  else
    Filename.concat (private_temporary_directory ())
      (String.sub (Blake3.to_hex (Blake3.hash path)) 0 16 ^ ".socket")

let idle_limit = 3. *. 3600.
let session_idle_limit = 3600.

let send channel value =
  Marshal.to_channel channel value [];
  flush channel

(* Drops sessions nobody has used for an hour, saving them first. *)
let drop_idle state now =
  let idle =
    Hashtbl.fold
      (fun key session acc ->
        if now -. session.used > session_idle_limit then (key, session) :: acc else acc)
      state.sessions []
  in
  List.iter
    (fun (key, session) ->
      save state session;
      Option.iter Store.unlock session.pointer;
      Hashtbl.remove state.sessions key)
    idle

(* Removes the pointer of each worktree whose directory is gone, of any
   compiler, and its line in the list of worktrees. A new worktree looks
   through every pointer for the state nearest to it, so those of worktrees
   that are gone must not gather. *)
let prune state =
  let known = known_worktrees state in
  let live, dead = List.partition (fun (root, _) -> Sys.file_exists root) known in
  if dead <> [] then begin
    List.iter (fun (_, name) -> Store.remove_pointer (Store.pointer state.store name)) dead;
    let file = worktrees_file state in
    let partial = file ^ ".partial" in
    try
      Out_channel.with_open_bin partial (fun out ->
          List.iter (fun (root, name) -> Printf.fprintf out "%s\t%s\n" root name) live);
      Sys.rename partial file
    with Sys_error _ -> ()
  end

(* Keeps the store within its budget. What the state of a worktree of this
   compiler refers to is kept, and so are the standard library's state and
   each named state of the library. A state another compiler wrote can be
   read only by that compiler, so its values are not kept; that compiler
   finds its state gone, and starts from its files. *)
let collect state =
  prune state;
  Store.compact state.store;
  if Store.size state.store > budget () then begin
    let live = Hashtbl.create 4096 in
    let keep ~version artifact =
      List.iter
        (fun name -> Hashtbl.replace live name ())
        (Engine.values_in state.store ~version artifact)
    in
    let keep_pointer ~version name =
      Option.iter
        (fun (record : record) -> keep ~version record.artifact)
        (read_record (Store.pointer state.store name))
    in
    let sessions = session_prefix state in
    List.iter
      (fun name ->
        if String.starts_with ~prefix:sessions name then keep_pointer ~version:state.identity name
        else if String.starts_with ~prefix:library_prefix name then
          keep_pointer ~version:Compiler_version.digest name)
      (Store.pointers state.store);
    Option.iter (keep ~version:state.identity)
      (Store.find_result state.store ~kind:"package" ~key:(standard_key state.identity));
    Store.collect state.store ~budget:(budget ()) ~live:(Hashtbl.mem live)
  end

(* Watching: each open worktree's file stamps are checked every second while
   no request is waiting, so that results are current before they are asked
   for. A request scans again before it is answered, so it always sees every
   change made before it. *)
let watch state =
  Hashtbl.iter
    (fun _ session ->
      match session.source with
      | Directory root -> (
          try
            scan session root;
            ignore (stabilize state session)
          with _ -> ())
      | Commit _ -> ())
    state.sessions

type 'response message = Progress of string | Final of 'response

let serve ~handle =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let state = current () in
  let path = socket_path state.identity in
  let lock =
    Unix.openfile (server_path state.identity ^ ".lock") [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644
  in
  match Unix.lockf lock F_TLOCK 0 with
  | exception Unix.Unix_error _ -> ()
  | () ->
      serving := true;
      (try Unix.unlink path with Unix.Unix_error _ -> ());
      let socket = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
      Unix.bind socket (ADDR_UNIX path);
      Unix.listen socket 16;
      let last = ref (Unix.time ()) in
      let last_collection = ref 0. in
      while (not !stopping) && Unix.time () -. !last < idle_limit do
        match Unix.select [ socket ] [] [] 1.0 with
        | exception Unix.Unix_error (EINTR, _, _) -> ()
        | [], _, _ ->
            let now = Unix.time () in
            drop_idle (current ()) now;
            (let state = current () in
             watch state;
             Hashtbl.iter (fun _ session -> fold state session) state.sessions);
            if now -. !last_collection > 60. then begin
              last_collection := now;
              (* A compiler that was built again has another identity, and
                 its clients start a process of their own, so this one would
                 only scan worktrees for no one. *)
              if Identity.compute (Store.default_directory ()) <> (current ()).identity then
                stopping := true;
              collect (current ())
            end
        | _ -> (
            match Unix.accept ~cloexec:true socket with
            | exception Unix.Unix_error _ -> ()
            | client, _ -> (
                last := Unix.time ();
                let input = Unix.in_channel_of_descr client in
                let output = Unix.out_channel_of_descr client in
                (try
                   let request = Marshal.from_channel input in
                   let progress text = send output (Progress text) in
                   send output (Final (recovering (fun () -> handle ~progress request)))
                 with _ -> ());
                try Unix.close client with Unix.Unix_error _ -> ()))
      done;
      (let state = current () in
       Hashtbl.iter (fun _ session -> save state session) state.sessions;
       Store.close state.store);
      (try Unix.unlink path with Unix.Unix_error _ -> ());
      Unix.close lock

(* Starts the background process, detached from the client's terminal. *)
let start program =
  let log = Filename.concat (servers_directory ()) "server.log" in
  match Unix.fork () with
  | 0 -> (
      ignore (Unix.setsid ());
      match Unix.fork () with
      | 0 ->
          let null = Unix.openfile "/dev/null" [ O_RDONLY ] 0 in
          let out = Unix.openfile log [ O_WRONLY; O_CREAT; O_APPEND ] 0o644 in
          Unix.dup2 null Unix.stdin;
          Unix.dup2 out Unix.stdout;
          Unix.dup2 out Unix.stderr;
          (try Unix.execv program [| program; "__serve" |] with _ -> ());
          Unix._exit 1
      | _ -> Unix._exit 0)
  | child -> ignore (Unix.waitpid [] child)

let connect path =
  let socket = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
  match Unix.connect socket (ADDR_UNIX path) with
  | () -> Some socket
  | exception Unix.Unix_error _ ->
      Unix.close socket;
      None

let store_directory () = Store.default_directory ()

let call ?program ?(start_server = true) ~progress request =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let identity = Identity.compute (Store.default_directory ()) in
  let path = socket_path identity in
  let program = Option.value program ~default:(Identity.executable ()) in
  let rec attempt tries =
    match connect path with
    | Some socket -> Some socket
    | None ->
        if tries = 0 || not start_server then None
        else begin
          if tries = 50 then start program;
          Unix.sleepf 0.1;
          attempt (tries - 1)
        end
  in
  match attempt 50 with
  | None when not start_server -> Error "No background process is running."
  | None -> Error "could not start or reach the background process; try --no-server."
  | Some socket -> (
      let input = Unix.in_channel_of_descr socket in
      let output = Unix.out_channel_of_descr socket in
      let rec receive () =
        match Marshal.from_channel input with
        | Progress text ->
            progress text;
            receive ()
        | Final response -> response
      in
      match
        send output request;
        receive ()
      with
      | response ->
          Unix.close socket;
          Ok response
      | exception _ ->
          (try Unix.close socket with Unix.Unix_error _ -> ());
          Error
            "the background process ended while answering; see its log in the store's \
             servers              directory.")

let set_answers session answers =
  List.iter (fun (key, told) -> Engine.set session.engine Prover.told key told) answers
