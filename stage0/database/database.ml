(* The code database's sessions and requests. See database.mli and
   DATABASE.md, "Sessions" and "Requests". *)

(* Loading packages *)

let load_package ?(usize_bits = 32) engine ~name ~dependencies
    (modules : (Path.module_ * string) list) =
  List.iter (fun (module_, text) -> Engine.set engine Workspace.file_text module_ text) modules;
  Engine.set engine Workspace.packages name
    { Workspace.name; dependencies; modules = List.map fst modules; usize_bits }

(* The standard library holds the code for each platform, and its bounds of
   [USize] are its target's, so it is checked with the target's width. *)
let load_standard engine =
  load_package ~usize_bits:64 engine ~name:Standard_library.package ~dependencies:[]
    Standard_library.modules

let standard_layer ?log () =
  let layer = Engine.frozen_layer ?log () in
  load_standard layer;
  layer

(* The database's own inputs: how a worktree's files map to packages, and
   each file's stamp, so that a restart reads only the files that changed. *)

type layout = {
  packages : (string * string) list;
      (** Each package's directory, relative to the root, and name *)
  files : string list;  (** Each manifest and module file, relative to the root *)
}

let layout : (unit, layout) Query.input =
  Query.input ~name:"worktree_layout" ~show:(fun () -> "") ()

let stamps : (string, Worktree.stamp) Query.input =
  Query.input ~name:"worktree_stamp" ~show:Fun.id ()

(* Each manifest's text, by its package's directory, so that an unchanged
   manifest need not be read again. *)
let manifest_texts : (string, string) Query.input =
  Query.input ~name:"worktree_manifest" ~show:Fun.id ()

(* Sessions *)

type source = Directory of string | Commit of { repository : string; commit : string }

type session = {
  source : source;
  engine : Engine.t;
  journal : Store.journal option;
  mutable problems : string list;  (** Manifests that could not be read, and duplicate names *)
  mutable used : float;
  base : (string * session) option ref;  (** The commit this session's changes are measured from *)
}

type state = {
  store : Store.t;
  identity : string;
  standard : Engine.t;
  standard_journal : Store.journal option;  (** When this process may write it *)
  sessions : (string, session) Hashtbl.t;  (** By root, or by ["commit:" ^ id] *)
}

let state : state option ref = ref None

let budget () =
  match Option.bind (Sys.getenv_opt "TRUSS_CACHE_SIZE") int_of_string_opt with
  | Some bytes -> bytes
  | None -> 20 * 1024 * 1024 * 1024

let current () =
  match !state with
  | Some state -> state
  | None ->
      let store = Store.open_ (Store.default_directory ()) in
      let identity = Identity.compute (Store.directory store) in
      let journal = Store.journal store ("standard-" ^ Identity.short identity) in
      let standard =
        match Engine.load ~frozen:true store journal with
        | Some layer -> layer
        | None -> Engine.frozen_layer ()
      in
      Engine.attach standard store;
      load_standard standard;
      let standard_journal = if Store.lock journal then Some journal else None in
      let fresh = { store; identity; standard; standard_journal; sessions = Hashtbl.create 8 } in
      state := Some fresh;
      fresh

let session_name state root =
  Printf.sprintf "session-%s-%s" (Identity.short state.identity)
    (String.sub (Blake3.to_hex (Blake3.hash root)) 0 16)

(* The list of worktrees with journals, so that collection can tell which
   journals still have a worktree. *)
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

let current_layout engine =
  Option.value (read (Engine.context engine) layout ()) ~default:{ packages = []; files = [] }

(* Setting a worktree's files as inputs *)

type file_contents = Text of string | Unchanged

(* Brings the inputs in line with a set of files, each with its contents, or
   [Unchanged] when its stamp shows it is the same as before. *)
let apply session (files : (string * file_contents) list) =
  let engine = session.engine in
  let old = current_layout engine in
  let manifests =
    List.filter_map
      (fun (path, contents) ->
        if Filename.basename path = "truss.toml" then Some (Worktree.parent path, contents)
        else None)
      files
  in
  let manifest_text directory contents =
    match contents with
    | Text text -> Some text
    | Unchanged ->
        (* An unchanged manifest's text is kept as the input it was set as. *)
        read (Engine.context engine) manifest_texts directory
  in
  let problems = ref [] in
  let parsed =
    List.filter_map
      (fun (directory, contents) ->
        match manifest_text directory contents with
        | None -> None
        | Some text -> (
            Engine.set engine manifest_texts directory text;
            let shown = if directory = "" then "truss.toml" else directory ^ "/truss.toml" in
            match Type_checker.Manifest.parse text with
            | manifest -> Some (directory, manifest)
            | exception Type_checker.Manifest.Malformed (line, expected) ->
                problems := Printf.sprintf "%s:%d: expected %s." shown line expected :: !problems;
                None))
      manifests
  in
  let seen = Hashtbl.create 8 in
  let packages =
    List.filter
      (fun (directory, (manifest : Type_checker.Manifest.t)) ->
        if manifest.name = Standard_library.package then begin
          problems :=
            Printf.sprintf "%s: the package name standard is the standard library's."
              (if directory = "" then "truss.toml" else directory ^ "/truss.toml")
            :: !problems;
          false
        end
        else
          match Hashtbl.find_opt seen manifest.name with
          | Some other ->
              problems :=
                Printf.sprintf
                  "%s/truss.toml: the package name %s is already used by %s/truss.toml." directory
                  manifest.name other
                :: !problems;
              false
          | None ->
              Hashtbl.replace seen manifest.name directory;
              true)
      parsed
  in
  (* A package that claims to run on every target cannot rely on one that
     runs only on 64-bit targets. *)
  List.iter
    (fun (directory, (manifest : Type_checker.Manifest.t)) ->
      if manifest.usize_bits = 32 then
        List.iter
          (fun (dependency : Workspace.dependency) ->
            match
              List.find_opt
                (fun (_, (other : Type_checker.Manifest.t)) -> other.name = dependency.package)
                packages
            with
            | Some (_, other) when other.usize_bits = 64 ->
                problems :=
                  Printf.sprintf
                    "%s: %s runs only on 64-bit targets, so %s must say usize_bits = 64 to depend \
                     on it."
                    (if directory = "" then "truss.toml" else directory ^ "/truss.toml")
                    other.name manifest.name
                  :: !problems
            | _ -> ())
          manifest.dependencies)
    packages;
  let directories = List.map fst packages in
  let modules =
    List.filter_map
      (fun (path, contents) ->
        if Filename.check_suffix path ".truss" then
          match Worktree.owner directories path with
          | Some directory ->
              let manifest = List.assoc directory packages in
              Some
                ( path,
                  ({
                     package = manifest.Type_checker.Manifest.name;
                     modules = Worktree.module_names ~package_directory:directory path;
                   }
                    : Path.module_),
                  contents )
          | None -> None
        else None)
      files
  in
  List.iter
    (fun (_, module_, contents) ->
      match contents with
      | Text text -> Engine.set engine Workspace.file_text module_ text
      | Unchanged -> ())
    modules;
  (* Modules and packages that are gone *)
  let module_of_old path =
    match Worktree.owner (List.map fst old.packages) path with
    | Some directory ->
        Some
          ({
             package = List.assoc directory old.packages;
             modules = Worktree.module_names ~package_directory:directory path;
           }
            : Path.module_)
    | None -> None
  in
  let present = List.map (fun (_, m, _) -> m) modules in
  List.iter
    (fun path ->
      if Filename.check_suffix path ".truss" then
        match module_of_old path with
        | Some module_ when not (List.mem module_ present) ->
            Engine.remove engine Workspace.file_text module_
        | _ -> ())
    old.files;
  List.iter
    (fun (_, name) ->
      if not (List.exists (fun (_, (m : Type_checker.Manifest.t)) -> m.name = name) packages) then
        Engine.remove engine Workspace.packages name)
    old.packages;
  List.iter
    (fun (directory, (manifest : Type_checker.Manifest.t)) ->
      let own =
        List.filter_map
          (fun (path, module_, _) ->
            if Worktree.owner directories path = Some directory then Some module_ else None)
          modules
      in
      Engine.set engine Workspace.packages manifest.name
        {
          Workspace.name = manifest.name;
          dependencies = manifest.dependencies;
          modules = own;
          usize_bits = manifest.usize_bits;
        })
    packages;
  Engine.set engine layout ()
    {
      packages = List.map (fun (d, (m : Type_checker.Manifest.t)) -> (d, m.name)) packages;
      files = List.map fst files;
    };
  session.problems <- List.rev !problems

(* Reads the files of a directory whose stamps changed, and sets them. *)
let scan session root =
  let engine = session.engine in
  let files = Worktree.files root in
  let context = Engine.context engine in
  let contents =
    List.map
      (fun (path, stamp) ->
        match read context stamps path with
        | Some old when old = stamp -> (path, Unchanged)
        | _ ->
            let text = In_channel.with_open_bin (Filename.concat root path) In_channel.input_all in
            Engine.set engine stamps path stamp;
            (path, Text text))
      files
  in
  let old = current_layout engine in
  List.iter
    (fun path -> if not (List.mem_assoc path files) then Engine.remove engine stamps path)
    old.files;
  apply session contents

let save state session =
  (match session.journal with Some journal -> Engine.save session.engine journal | None -> ());
  match state.standard_journal with
  | Some journal -> Engine.save state.standard journal
  | None -> ()

let stabilize state session =
  let change = Engine.stabilize session.engine in
  save state session;
  change

(* The open or saved session nearest to a set of files: the one whose
   modules differ from them in the fewest files. *)
let nearest state (texts : (string * string) list) =
  let differences (session : session) =
    let context = Engine.context session.engine in
    let lay = current_layout session.engine in
    let modules = List.filter (fun (path, _) -> Filename.check_suffix path ".truss") texts in
    let owner path = Worktree.owner (List.map fst lay.packages) path in
    List.fold_left
      (fun count (path, text) ->
        match owner path with
        | Some directory -> (
            let module_ : Path.module_ =
              {
                package = List.assoc directory lay.packages;
                modules = Worktree.module_names ~package_directory:directory path;
              }
            in
            match read context Workspace.file_text module_ with
            | Some known when known = text -> count
            | _ -> count + 1)
        | None -> count + 1)
      0 modules
  in
  Hashtbl.fold
    (fun _ session best ->
      let d = differences session in
      match best with Some (_, bd) when bd <= d -> best | _ -> Some (session, d))
    state.sessions None

let logging = ref false

let new_engine state =
  let engine = Engine.create ~log:!logging ~shared:state.standard () in
  Engine.attach engine state.store;
  engine

let open_directory state root =
  match Hashtbl.find_opt state.sessions root with
  | Some session -> Ok session
  | None ->
      let name = session_name state root in
      let journal = Store.journal state.store name in
      if not (Store.lock journal) then
        Error
          (Printf.sprintf
             "%s is open in another process of this compiler, such as its background process; \
              leave out --no-server, or stop that process with `truss stop`."
             root)
      else
        let engine =
          match Engine.load ~log:!logging ~shared:state.standard state.store journal with
          | Some engine -> Some engine
          | None -> None
        in
        let engine, started_near =
          match engine with
          | Some engine -> (engine, false)
          | None -> (
              (* A new worktree starts from the nearest session's state. *)
              let texts =
                List.filter_map
                  (fun (path, _) ->
                    if Filename.check_suffix path ".truss" then
                      Some
                        ( path,
                          In_channel.with_open_bin (Filename.concat root path) In_channel.input_all
                        )
                    else None)
                  (Worktree.files root)
              in
              match nearest state texts with
              | Some (near, _) -> (Engine.fork near.engine, true)
              | None -> (new_engine state, false))
        in
        Engine.attach engine state.store;
        let session =
          {
            source = Directory root;
            engine;
            journal = Some journal;
            problems = [];
            used = Unix.time ();
            base = ref None;
          }
        in
        if started_near then begin
          (* The stamps it carries are another worktree's. *)
          List.iter (fun path -> Engine.remove engine stamps path) (current_layout engine).files
        end;
        Hashtbl.replace state.sessions root session;
        remember_worktree state root name;
        scan session root;
        ignore (Engine.stabilize engine);
        Engine.save_all engine journal;
        Ok session

let open_commit state ~repository commit =
  let name = "commit:" ^ commit in
  match Hashtbl.find_opt state.sessions name with
  | Some session -> Ok session
  | None -> (
      match Git.files ~directory:repository commit with
      | None -> Error (Printf.sprintf "cannot read commit %s." commit)
      | Some texts ->
          let engine =
            match nearest state texts with
            | Some (near, _) -> Engine.fork near.engine
            | None -> new_engine state
          in
          let session =
            {
              source = Commit { repository; commit };
              engine;
              journal = None;
              problems = [];
              used = Unix.time ();
              base = ref None;
            }
          in
          apply session (List.map (fun (path, text) -> (path, Text text)) texts);
          ignore (Engine.stabilize engine);
          Hashtbl.replace state.sessions name session;
          Ok session)

(* The worktree a directory is in: the top of its git worktree, or outside
   git, the nearest directory holding a manifest, or the directory
   itself. *)
let root_of directory =
  let directory = try Unix.realpath directory with Unix.Unix_error _ -> directory in
  match Git.toplevel directory with
  | Some top -> ( try Unix.realpath top with Unix.Unix_error _ -> top)
  | None ->
      (* Outside git, the nearest directory at or above that holds a
         manifest, so a package's subdirectory is about the package. *)
      let rec up path =
        if Sys.file_exists (Filename.concat path "truss.toml") then Some path
        else
          let parent = Filename.dirname path in
          if parent = path then None else up parent
      in
      Option.value (up directory) ~default:directory

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
let packages session = (current_layout session.engine).packages

let module_file session (module_ : Path.module_) =
  let lay = current_layout session.engine in
  match List.find_opt (fun (_, name) -> name = module_.package) lay.packages with
  | Some (directory, _) -> Worktree.module_file ~package_directory:directory module_
  | None -> Workspace.file_path module_

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
  let state = current () in
  let root = root_of directory in
  if not (Sys.file_exists root) then Error (directory ^ ": no such directory.")
  else
    match open_directory state root with
    | Error message -> Error message
    | Ok session ->
        session.used <- Unix.time ();
        scan session root;
        ignore (stabilize state session);
        Ok (session, target_packages session (relative_to root directory))

let refresh session =
  match session.source with
  | Directory root ->
      scan session root;
      ignore (stabilize (current ()) session)
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
let definition_reads memo node =
  let own = Option.map (fun (s : Query.subject) -> s.path) (subject_of node) in
  let found = Hashtbl.create 8 in
  let seen = Hashtbl.create 16 in
  let rec walk n =
    List.iter
      (fun read ->
        let label = Engine.label read in
        if not (Hashtbl.mem seen label) then begin
          Hashtbl.replace seen label ();
          match subject_of read with
          | Some subject when Some subject.path <> own ->
              Hashtbl.replace found (subject.path, Option.value subject.part ~default:"") ()
          | Some _ | None -> (
              if
                (* The standard library's own lookups are not followed, so a
                 definition is not said to read everything they read. *)
                not (Engine.is_frozen read)
              then
                match Hashtbl.find_opt memo label with
                | Some reached -> List.iter (fun r -> Hashtbl.replace found r ()) reached
                | None -> walk read)
        end)
      (Engine.reads n)
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
          let reads = definition_reads memo node in
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

(* Every node a change between two sessions could reach, in [mine], with
   how it compares with the same node in [theirs]: the inputs that differ,
   and everything that reads them, directly or not. *)
let compare_sessions mine theirs =
  let differs node =
    match Engine.current_in node theirs.engine with
    | None -> Added
    | Some other -> if Engine.same_outcome node other then Same else Changed
  in
  let inputs = List.filter Engine.is_input (Engine.nodes mine.engine) in
  let changed_inputs = List.filter (fun node -> differs node <> Same) inputs in
  (* Inputs set in theirs and gone from mine *)
  let removed =
    List.filter
      (fun node -> Engine.is_input node && Engine.current_in node mine.engine = None)
      (Engine.nodes theirs.engine)
  in
  let seen = Hashtbl.create 256 in
  let cone = ref [] in
  let rec reach node =
    let label = Engine.label node in
    if not (Hashtbl.mem seen label) then begin
      Hashtbl.replace seen label ();
      cone := node :: !cone;
      List.iter reach (Engine.readers node)
    end
  in
  List.iter reach changed_inputs;
  List.iter
    (fun gone ->
      match Engine.counterpart gone mine.engine with
      | Some node -> reach node
      | None ->
          List.iter
            (fun reader -> Option.iter reach (Engine.counterpart reader mine.engine))
            (Engine.readers gone))
    removed;
  List.rev_map
    (fun node ->
      if not (Engine.is_input node) then Engine.bring_up_to_date node;
      (node, differs node))
    !cone

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
  let labels nodes =
    let table = Hashtbl.create 64 in
    List.iter (fun n -> Hashtbl.replace table (Engine.label n) n) nodes;
    table
  in
  let mine_labels = labels mine_changed and theirs_labels = labels theirs_changed in
  let describe node =
    match subject_of node with
    | Some subject -> { path = Some subject.path; part = subject.part; label = Engine.label node }
    | None -> { path = None; part = None; label = Engine.label node }
  in
  let both =
    List.filter_map
      (fun node ->
        if Hashtbl.mem theirs_labels (Engine.label node) then Some (Both_change (describe node))
        else None)
      mine_changed
  in
  let reads_other changed other_labels who =
    List.concat_map
      (fun node ->
        if subject_of node = None then []
        else
          List.filter_map
            (fun read ->
              match Hashtbl.find_opt other_labels (Engine.label read) with
              | Some other
                when not
                       (Hashtbl.mem
                          (if who = "this" then mine_labels else theirs_labels)
                          (Engine.label read)) ->
                  Some
                    (Reads
                       {
                         this_worktree = who = "this";
                         change = describe node;
                         reads = describe other;
                       })
              | _ -> None)
            (Engine.reads node))
      changed
  in
  List.sort_uniq compare
    (both
    @ reads_other mine_changed theirs_labels "this"
    @ reads_other theirs_changed mine_labels "the other")

(* A commit of a worktree's files as they are, for merging. *)
let commit_of_worktree root = Git.snapshot ~directory:root

let other_worktrees session =
  let state = current () in
  let root = root_of_session session in
  let common = Git.common_directory root in
  Hashtbl.fold
    (fun _ other acc ->
      match other.source with
      | Directory other_root
        when other_root <> root && common <> None && Git.common_directory other_root = common ->
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
          let engine = Engine.fork session.engine in
          let merged =
            {
              source = Commit { repository = root; commit = "merge" };
              engine;
              journal = None;
              problems = [];
              used = Unix.time ();
              base = ref None;
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

let stopping = ref false
let stop () = stopping := true

let reset () =
  match !state with
  | None -> ()
  | Some s ->
      Hashtbl.iter (fun _ session -> save s session) s.sessions;
      Store.close s.store;
      state := None

let session_engine directory =
  match !state with
  | None -> None
  | Some s ->
      Option.map (fun session -> session.engine) (Hashtbl.find_opt s.sessions (root_of directory))

(* The background process *)

let rec make_directory path =
  if not (Sys.file_exists path) then begin
    make_directory (Filename.dirname path);
    try Unix.mkdir path 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let servers_directory () =
  let directory = Filename.concat (Store.default_directory ()) "servers" in
  make_directory directory;
  directory

(* The socket's address, and its lock beside it in the store. A socket's
   path has a short limit, about 100 bytes, so one under a long store path
   goes in /tmp, named by a hash of where it would have been. *)
let server_path identity = Filename.concat (servers_directory ()) (Identity.short identity)

let socket_path identity =
  let path = server_path identity ^ ".socket" in
  if String.length path < 100 then path
  else
    Printf.sprintf "/tmp/truss-%d-%s.socket" (Unix.getuid ())
      (String.sub (Blake3.to_hex (Blake3.hash path)) 0 16)

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
      Option.iter Store.unlock session.journal;
      Hashtbl.remove state.sessions key)
    idle

(* Keeps the store within its budget: every value a live journal refers to
   is kept, and journals whose worktree is gone are removed. *)
let collect state =
  if Store.size state.store > budget () then begin
    let live = Hashtbl.create 4096 in
    let worktrees = known_worktrees state in
    let alive = List.filter (fun (root, _) -> Sys.file_exists root) worktrees in
    List.iter
      (fun (root, name) ->
        if not (List.mem (root, name) alive) then
          Store.remove_journal (Store.journal state.store name))
      worktrees;
    List.iter
      (fun name ->
        let journal = Store.journal state.store name in
        let alive_journal =
          List.exists (fun (_, n) -> n = name) alive
          || (String.length name > 9 && String.sub name 0 9 = "standard-")
        in
        if alive_journal then
          List.iter (fun v -> Hashtbl.replace live v ()) (Engine.values_in journal))
      (Store.journals state.store);
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
            drop_idle state now;
            watch state;
            if now -. !last_collection > 600. then begin
              last_collection := now;
              collect state
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
                   send output (Final (handle ~progress request))
                 with _ -> ());
                try Unix.close client with Unix.Unix_error _ -> ()))
      done;
      Hashtbl.iter (fun _ session -> save state session) state.sessions;
      Store.close state.store;
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
