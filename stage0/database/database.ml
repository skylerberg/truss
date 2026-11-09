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

let read_directory ~package directory =
  let rec walk relative =
    let absolute =
      if relative = [] then directory
      else Filename.concat directory (String.concat Filename.dir_sep relative)
    in
    Array.to_list (Sys.readdir absolute)
    |> List.sort compare
    |> List.concat_map (fun entry ->
        let path = Filename.concat absolute entry in
        if Sys.is_directory path then walk (relative @ [ entry ])
        else if Filename.check_suffix entry ".truss" then
          let text = Source.text (Source.read_file path) in
          [
            ( ({ package; modules = relative @ [ Filename.chop_suffix entry ".truss" ] }
                : Path.module_),
              text );
          ]
        else [])
  in
  walk []

(* Requests and answers *)

type command =
  | Check
  | Test of { sanitize : bool }
  | Build of { output : string; sanitize : bool }
  | Run of { sanitize : bool }
  | Impact of { base : string option }
  | Holes
  | References of { name : string }
  | Dependencies of { name : string }
  | Overlap of { other : string option; merge : bool }
  | Explain of { file : string; line : int; column : int }
  | Sync
  | Status
  | Stop

type request = { directory : string; command : command; json : bool }
type response = { output : string; errors : string; status : int; program : string option }

let answer ?(errors = "") ?(status = 0) ?program output = { output; errors; status; program }
let refuse message = answer ~errors:(message ^ "\n") ~status:2 ""

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

(* The worktree a request is about: the top of its git worktree, or the
   directory itself outside git. *)
let root_of directory =
  let directory = try Unix.realpath directory with Unix.Unix_error _ -> directory in
  match Git.toplevel directory with
  | Some top -> ( try Unix.realpath top with Unix.Unix_error _ -> top)
  | None -> directory

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

(* Rendering *)

let file_of session (module_ : Path.module_) =
  let lay = current_layout session.engine in
  match List.find_opt (fun (_, name) -> name = module_.package) lay.packages with
  | Some (directory, _) -> Worktree.module_file ~package_directory:directory module_
  | None -> Workspace.file_path module_

let source_of session module_ =
  let file = Engine.get session.engine Workspace.file module_ in
  Source.create ~path:(file_of session module_) (Source.text file.source)

let diagnostics_of session packages =
  List.concat_map
    (fun (_, name) ->
      List.filter_map
        (fun module_ ->
          match Engine.get session.engine Type_checker.file_diagnostics module_ with
          | [] -> None
          | found -> Some (module_, found)
          | exception Not_found -> None)
        (package_modules session name))
    packages

let render_diagnostics ~json session found =
  if json then
    "["
    ^ String.concat ",\n"
        (List.concat_map
           (fun (module_, diagnostics) ->
             let source = source_of session module_ in
             List.map (Diagnostic.to_json_object source) (Diagnostic.shown diagnostics))
           found)
    ^ "]\n"
  else
    String.concat ""
      (List.concat_map
         (fun (module_, diagnostics) ->
           let source = source_of session module_ in
           List.map (Diagnostic.render source) (Diagnostic.shown diagnostics))
         found)

(* Compiling *)

let sanitizers =
  [ "-fsanitize=address,undefined"; "-fno-sanitize-recover=undefined"; "-fno-omit-frame-pointer" ]

let compiler state session ~sanitize =
  match Toolchain.find () with
  | Error message -> Error message
  | Ok toolchain ->
      let cache = Build.cache (Store.files state.store "objects") in
      Ok
        (Compile.create (Engine.context session.engine) Memory_layout.target_64 toolchain cache
           { build = Development; optimization = O1; extra = (if sanitize then sanitizers else []) })

let declarations session packages kind =
  List.concat_map
    (fun (_, name) ->
      List.concat_map
        (fun module_ ->
          List.filter_map
            (fun (d : Resolve.Names.declaration) -> if kind d.path then Some d.path else None)
            (Engine.get session.engine Resolve.Names.declarations module_))
        (package_modules session name))
    packages

let test_results state : Compile.results =
  {
    find = (fun key -> Store.find_result state.store ~kind:"tests" ~key);
    add = (fun key value -> Store.add_result state.store ~kind:"tests" ~key value);
  }

let find_main session packages =
  match
    declarations session packages (function Path.Top { name = "main"; _ } -> true | _ -> false)
  with
  | main :: _ -> Some main
  | [] -> None

(* The requests that need a worktree's session *)

let with_session state request f =
  let root = root_of request.directory in
  if not (Sys.file_exists root) then refuse (request.directory ^ ": no such directory.")
  else
    match open_directory state root with
    | Error message -> refuse message
    | Ok session ->
        session.used <- Unix.time ();
        scan session root;
        ignore (stabilize state session);
        let within = relative_to root request.directory in
        let packages = target_packages session within in
        if packages = [] && session.problems = [] then
          refuse (request.directory ^ ": no truss.toml here or above, within the worktree.")
        else Fun.protect ~finally:(fun () -> save state session) (fun () -> f session packages)

let problems_text session = String.concat "" (List.map (fun p -> p ^ "\n") session.problems)

let checked_or_fail session packages k =
  let found = diagnostics_of session packages in
  if found <> [] || session.problems <> [] then
    answer
      ~errors:(problems_text session ^ render_diagnostics ~json:false session found)
      ~status:1 ""
  else k ()

let test state request ~sanitize =
  with_session state request (fun session packages ->
      checked_or_fail session packages (fun () ->
          let tests = declarations session packages (function Path.Test _ -> true | _ -> false) in
          match compiler state session ~sanitize with
          | Error message -> refuse message
          | Ok compile -> (
              let results = if sanitize then None else Some (test_results state) in
              match Compile.run_tests ?results compile ~time_limit:10_000 tests with
              | Error message -> answer ~errors:(message ^ "\n") ~status:1 ""
              | Ok (status, output) ->
                  let records = Compile.parse_report output in
                  let buffer = Buffer.create 256 in
                  let indented text =
                    String.split_on_char '\n' text
                    |> List.filter (( <> ) "")
                    |> List.iter (fun line -> Buffer.add_string buffer ("    " ^ line ^ "\n"))
                  in
                  List.iter2
                    (fun test (record : Compile.record) ->
                      Buffer.add_string buffer
                        (Printf.sprintf "%s: %s\n" (Path.show test) record.outcome);
                      Option.iter indented record.message;
                      Option.iter indented record.echo)
                    tests records;
                  let count outcome =
                    List.length
                      (List.filter (fun (r : Compile.record) -> r.outcome = outcome) records)
                  in
                  Buffer.add_string buffer
                    (Printf.sprintf "\n%d passed, %d did not pass\n" (count "passed")
                       (List.length records - count "passed"));
                  Store.flush state.store;
                  answer ~status (Buffer.contents buffer))))

let build state request ~output ~sanitize =
  with_session state request (fun session packages ->
      checked_or_fail session packages (fun () ->
          match find_main session packages with
          | None -> refuse (request.directory ^ ": the package has no main.")
          | Some main -> (
              match compiler state session ~sanitize with
              | Error message -> refuse message
              | Ok compile -> (
                  match Compile.build_program compile ~main ~output with
                  | Error message -> answer ~errors:(message ^ "\n") ~status:1 ""
                  | Ok () -> answer ~program:output ""))))

let run state request ~sanitize =
  let directory = Store.files state.store "programs" in
  let output =
    Filename.concat directory
      (Printf.sprintf "program-%d-%d" (Unix.getpid ())
         (int_of_float (Unix.gettimeofday () *. 1000.)))
  in
  build state request ~output ~sanitize

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

let unique_sorted pairs = List.sort_uniq compare pairs
let lines_of rows = String.concat "" (List.map (fun row -> row ^ "\n") rows)

let references state request name =
  ignore state;
  with_session state request (fun session _ ->
      match find_definitions session name with
      | [] -> refuse (Printf.sprintf "no definition named %s in this worktree." name)
      | targets ->
          let table = dependency_table session in
          let rows =
            List.concat_map
              (fun target ->
                Hashtbl.fold
                  (fun reader reads acc ->
                    List.filter_map
                      (fun (path, reader_part, read_part) ->
                        if Path.equal path target then
                          Some
                            (Printf.sprintf "%s: its %s reads the %s of %s" (Path.show reader)
                               reader_part read_part (Path.show target))
                        else None)
                      reads
                    @ acc)
                  table [])
              targets
          in
          answer (lines_of (List.sort_uniq compare rows)))

let dependencies state request name =
  with_session state request (fun session _ ->
      match find_definitions session name with
      | [] -> refuse (Printf.sprintf "no definition named %s in this worktree." name)
      | targets ->
          let table = dependency_table session in
          let rows =
            List.concat_map
              (fun target ->
                List.map
                  (fun (path, part, read_part) ->
                    Printf.sprintf "%s: its %s reads the %s of %s" (Path.show target) part read_part
                      (Path.show path))
                  (Option.value (Hashtbl.find_opt table target) ~default:[]))
              targets
          in
          answer (lines_of (unique_sorted rows)))

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

let header_of session (path : Path.t) =
  match
    List.find_opt
      (fun (d : Resolve.Names.declaration) -> Path.equal d.path path)
      (all_declarations session)
  with
  | None -> None
  | Some declaration -> (
      match Engine.get session.engine Resolve.Names.text (Resolve.Names.key_of declaration) with
      | Some text ->
          let lines = String.split_on_char '\n' text in
          let rec until = function
            | [] -> []
            | line :: rest ->
                let trimmed = String.trim line in
                if trimmed = "{" then []
                else if String.length trimmed > 0 && trimmed.[String.length trimmed - 1] = '{' then
                  [ String.trim (String.sub trimmed 0 (String.length trimmed - 1)) ]
                else line :: until rest
          in
          Some (String.concat "\n" (until lines))
      | None -> None
      | exception _ -> None)

let base_commit ~root base =
  match base with
  | Some revision -> Git.resolve ~directory:root revision
  | None -> (
      match (Git.head ~directory:root, Git.default_branch ~directory:root) with
      | Some head, Some branch -> Git.merge_base ~directory:root head branch
      | Some head, None -> Some head
      | None, _ -> None)

let root_of_session session =
  match session.source with Directory root -> root | Commit c -> c.repository

let group rows =
  let table = Hashtbl.create 16 in
  List.iter
    (fun (path, part) ->
      let parts = Option.value (Hashtbl.find_opt table path) ~default:[] in
      if not (List.mem part parts) then Hashtbl.replace table path (part :: parts))
    rows;
  Hashtbl.fold (fun path parts acc -> (path, List.sort compare parts) :: acc) table []
  |> List.sort (fun (a, _) (b, _) -> Path.compare a b)

let show_grouped rows =
  lines_of
    (List.map
       (fun (path, parts) -> Printf.sprintf "  %s: %s" (Path.show path) (String.concat ", " parts))
       (group rows))

let impact state request base =
  with_session state request (fun session _ ->
      ignore (diagnostics_of session (current_layout session.engine).packages);
      let root = root_of_session session in
      match base_commit ~root base with
      | None -> refuse "no base commit: name one with --base, or work in a git worktree."
      | Some commit -> (
          match open_commit state ~repository:root commit with
          | Error message -> refuse message
          | Ok base_session ->
              let compared = compare_sessions session base_session in
              let with_subject status =
                List.filter_map
                  (fun (node, difference) ->
                    match subject_of node with
                    | Some subject when difference = status ->
                        Some (subject.path, Option.value subject.part ~default:"")
                    | _ -> None)
                  compared
              in
              let changed = with_subject Changed @ with_subject Added in
              let same = with_subject Same in
              let changed_paths = List.sort_uniq Path.compare (List.map fst changed) in
              let same =
                List.filter
                  (fun (path, _) -> not (List.exists (Path.equal path) changed_paths))
                  same
              in
              let interface_changed =
                List.sort_uniq Path.compare
                  (List.filter_map
                     (fun (path, part) ->
                       if List.mem part [ "interface"; "signature"; "shape" ] then Some path
                       else None)
                     changed)
              in
              let table = dependency_table session in
              let readers_of target =
                Hashtbl.fold
                  (fun reader reads acc ->
                    if List.exists (fun (path, _, _) -> Path.equal path target) reads then
                      reader :: acc
                    else acc)
                  table []
              in
              let review =
                List.sort_uniq Path.compare
                  (interface_changed @ List.concat_map readers_of interface_changed)
              in
              let signatures =
                List.filter_map
                  (fun path ->
                    Option.map
                      (fun header ->
                        Printf.sprintf "  %s\n    %s" (Path.show path)
                          (String.concat "\n    " (String.split_on_char '\n' header)))
                      (header_of session path))
                  review
              in
              let tests =
                match
                  ( compiler state session ~sanitize:false,
                    compiler state base_session ~sanitize:false )
                with
                | Ok mine, Ok theirs ->
                    let packages = current_layout session.engine in
                    let tests =
                      declarations session packages.packages (function
                        | Path.Test _ -> true
                        | _ -> false)
                    in
                    let base_tests =
                      declarations base_session (current_layout base_session.engine).packages
                        (function
                        | Path.Test _ -> true
                        | _ -> false)
                    in
                    let mine = Compile.test_keys mine tests in
                    let theirs = Compile.test_keys theirs base_tests in
                    Some
                      (List.filter_map
                         (fun (path, key) ->
                           match List.find_opt (fun (p, _) -> Path.equal p path) theirs with
                           | Some (_, base_key) when base_key = key -> None
                           | _ -> Some ("  " ^ Path.show path))
                         mine)
                | _ -> None
              in
              let section title body = if body = "" then "" else title ^ ":\n" ^ body in
              answer
                (String.concat ""
                   [
                     Printf.sprintf "Compared with %s.\n"
                       (String.sub commit 0 (min 12 (String.length commit)));
                     section "Changed" (show_grouped changed);
                     section "Checked again, unchanged" (show_grouped same);
                     section "Signatures to review" (lines_of signatures);
                     (match tests with
                     | Some tests -> section "Tests whose code changed" (lines_of tests)
                     | None -> "");
                   ])))

(* Holes *)

let reachable table start =
  let seen = Hashtbl.create 64 in
  let rec walk path =
    if not (Hashtbl.mem seen path) then begin
      Hashtbl.replace seen path ();
      List.iter
        (fun (read, _, _) -> walk read)
        (Option.value (Hashtbl.find_opt table path) ~default:[])
    end
  in
  walk start;
  seen

let holes state request =
  with_session state request (fun session packages ->
      let table = dependency_table session in
      let roots =
        declarations session packages (function
          | Path.Test _ | Path.Top { name = "main"; _ } -> true
          | _ -> false)
      in
      let reach = List.map (fun root -> (root, reachable table root)) roots in
      let rows =
        List.concat_map
          (fun (_, name) ->
            List.concat_map
              (fun module_ ->
                let source = lazy (source_of session module_) in
                List.concat_map
                  (fun (d : Resolve.Names.declaration) ->
                    let key = Resolve.Names.key_of d in
                    match
                      ( Engine.get session.engine Resolve.Names.definition key,
                        Engine.get session.engine Resolve.resolved key,
                        Engine.get session.engine Infer.checked key,
                        Engine.get session.engine Resolve.Names.base key )
                    with
                    | Some definition, Some resolved, Some checked, Some (_, base) ->
                        List.map
                          (fun (hole : Inspect.hole) ->
                            let line, column =
                              Source.position (Lazy.force source) (base + hole.offset)
                            in
                            let blocks =
                              List.filter_map
                                (fun (root, seen) ->
                                  if Hashtbl.mem seen d.path then Some (Path.show root) else None)
                                reach
                            in
                            Printf.sprintf
                              "%s:%d:%d: a hole of type %s in %s\n  in scope: %s\n  blocks: %s"
                              (file_of session module_) line column hole.expected (Path.show d.path)
                              (if hole.scope = [] then "nothing"
                               else
                                 String.concat ", "
                                   (List.map (fun (n, t) -> n ^ ": " ^ t) hole.scope))
                              (if blocks = [] then "nothing" else String.concat ", " blocks))
                          (Inspect.holes definition resolved checked.checked)
                    | _ -> []
                    | exception _ -> [])
                  (Engine.get session.engine Resolve.Names.declarations module_))
              (package_modules session name))
          packages
      in
      answer (lines_of rows))

(* What is at a position *)

(* The byte offset of a line and column, both counting from 1, where a
   column counts Unicode scalar values, as diagnostics do. *)
let offset_of text ~line ~column =
  let length = String.length text in
  let rec start_of current offset =
    if current >= line || offset >= length then offset
    else
      match String.index_from_opt text offset '\n' with
      | Some newline -> start_of (current + 1) (newline + 1)
      | None -> length
  in
  let rec advance offset remaining =
    if remaining <= 0 || offset >= length || text.[offset] = '\n' then offset
    else
      let width = Uchar.utf_decode_length (String.get_utf_8_uchar text offset) in
      advance (offset + max 1 width) (remaining - 1)
  in
  advance (start_of 1 0) (column - 1)

let explain state request ~file ~line ~column =
  with_session state request (fun session _ ->
      let root = root_of_session session in
      let relative = relative_to root (Filename.dirname file) in
      let relative = (if relative = "" then "" else relative ^ "/") ^ Filename.basename file in
      let lay = current_layout session.engine in
      match Worktree.owner (List.map fst lay.packages) relative with
      | None -> refuse (file ^ ": not a module of a package in this worktree.")
      | Some directory -> (
          let module_ : Path.module_ =
            {
              package = List.assoc directory lay.packages;
              modules = Worktree.module_names ~package_directory:directory relative;
            }
          in
          let source = source_of session module_ in
          let offset = offset_of (Source.text source) ~line ~column in
          let declarations = Engine.get session.engine Resolve.Names.declarations module_ in
          let found =
            List.find_map
              (fun (d : Resolve.Names.declaration) ->
                let key = Resolve.Names.key_of d in
                match
                  ( Engine.get session.engine Resolve.Names.base key,
                    Engine.get session.engine Resolve.Names.text key )
                with
                | Some (_, base), Some text
                  when base <= offset && offset <= base + String.length text -> (
                    match
                      ( Engine.get session.engine Resolve.Names.definition key,
                        Engine.get session.engine Resolve.resolved key )
                    with
                    | Some definition, Some resolved ->
                        let checked =
                          Option.map
                            (fun (r : Infer.result) -> r.checked)
                            (try Engine.get session.engine Infer.checked key with _ -> None)
                        in
                        Inspect.at definition resolved checked ~text (offset - base)
                    | _ -> None)
                | _ -> None
                | exception _ -> None)
              declarations
          in
          match found with
          | None -> answer "nothing there.\n"
          | Some explanation ->
              let signature =
                match explanation.refers_to with
                | Some path -> (
                    match header_of session path with Some header -> Some header | None -> None)
                | None -> None
              in
              answer
                (lines_of
                   (List.filter_map Fun.id
                      [
                        Some ("`" ^ explanation.text ^ "`");
                        Option.map (fun m -> "means " ^ m) explanation.meaning;
                        Option.map (fun t -> "has type " ^ t) explanation.type_;
                        Option.map
                          (fun s ->
                            "signature:\n  " ^ String.concat "\n  " (String.split_on_char '\n' s))
                          signature;
                      ]))))

(* Parallel work *)

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
    | Some subject ->
        Printf.sprintf "the %s of %s"
          (Option.value subject.part ~default:"definition")
          (Path.show subject.path)
    | None -> Engine.label node
  in
  let both =
    List.filter_map
      (fun node ->
        if Hashtbl.mem theirs_labels (Engine.label node) then Some ("both change " ^ describe node)
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
                    (Printf.sprintf "%s worktree's change to %s reads %s, which the other changes"
                       who (describe node) (describe other))
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

let other_worktrees state session =
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

let overlap_with state session other ~other_name =
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
          | Ok base_session ->
              Ok
                (List.map
                   (fun line -> other_name ^ ": " ^ line)
                   (overlaps ~base:base_session session other))))
  | _ -> Error "not a git worktree."

(* The diagnostics of a merge of two commits that neither has. *)
let merge_preview state session ~root ~mine ~theirs =
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
             if List.mem key sides then None
             else Some (Printf.sprintf "%s: %s: %s" (file_of merged m) code message))
           (List.sort_uniq compare (keys merged)))

let overlap state request ~other ~merge =
  with_session state request (fun session _ ->
      let root = root_of_session session in
      let others =
        match other with
        | Some branch -> (
            match Git.resolve ~directory:root branch with
            | Some commit -> (
                match open_commit state ~repository:root commit with
                | Ok s -> [ (branch, s) ]
                | Error _ -> [])
            | None -> [])
        | None -> List.map (fun s -> (root_of_session s, s)) (other_worktrees state session)
      in
      if others = [] then
        answer "No other worktree of this repository is open, and no branch was named.\n"
      else
        let rows =
          List.concat_map
            (fun (name, other_session) ->
              let found =
                match overlap_with state session other_session ~other_name:name with
                | Ok rows -> rows
                | Error message -> [ name ^ ": " ^ message ]
              in
              let merged =
                if not merge then []
                else
                  let theirs =
                    match other_session.source with
                    | Directory other_root -> commit_of_worktree other_root
                    | Commit c -> Some c.commit
                  in
                  match (commit_of_worktree root, theirs) with
                  | Some mine, Some theirs -> (
                      match merge_preview state session ~root ~mine ~theirs with
                      | Ok [] -> [ name ^ ": merging the two gives no new error." ]
                      | Ok errors -> List.map (fun e -> name ^ ": merged: " ^ e) errors
                      | Error message -> [ name ^ ": " ^ message ])
                  | _ -> [ name ^ ": cannot make commits to merge." ]
              in
              found @ merged)
            others
        in
        answer (if rows = [] then "No overlap.\n" else lines_of rows))

(* A check also lists where this worktree's changes meet those of other open
   worktrees of the repository. Overlaps are not diagnostics: nothing is
   wrong with either worktree's code. *)
let check state request =
  with_session state request (fun session packages ->
      let found = diagnostics_of session packages in
      let errors = problems_text session in
      let output = render_diagnostics ~json:request.json session found in
      let status = if found = [] && session.problems = [] then 0 else 1 in
      let overlaps =
        if request.json then ""
        else
          match other_worktrees state session with
          | [] -> ""
          | others ->
              let rows =
                List.concat_map
                  (fun other ->
                    match overlap_with state session other ~other_name:(root_of_session other) with
                    | Ok rows -> rows
                    | Error _ -> [])
                  others
              in
              if rows = [] then "" else "Overlaps with other worktrees:\n" ^ lines_of rows
      in
      if request.json then answer ~errors ~status output
      else answer ~errors:(errors ^ output) ~status overlaps)

let status state =
  let lines =
    Hashtbl.fold
      (fun key session acc ->
        Printf.sprintf "%s: %d nodes\n" key (List.length (Engine.nodes session.engine)) :: acc)
      state.sessions []
  in
  answer (String.concat "" (List.sort compare lines))

let stopping = ref false

let handle_with state request =
  match request.command with
  | Check -> check state request
  | Test { sanitize } -> test state request ~sanitize
  | Build { output; sanitize } -> build state request ~output ~sanitize
  | Run { sanitize } -> run state request ~sanitize
  | Sync -> with_session state request (fun _ _ -> answer "")
  | Status -> status state
  | Stop ->
      stopping := true;
      answer ""
  | Impact { base } -> impact state request base
  | Holes -> holes state request
  | References { name } -> references state request name
  | Dependencies { name } -> dependencies state request name
  | Overlap { other; merge } -> overlap state request ~other ~merge
  | Explain { file; line; column } -> explain state request ~file ~line ~column

let handle request =
  let state = current () in
  match handle_with state request with
  | response -> response
  | exception exception_ -> refuse ("the compiler failed: " ^ Printexc.to_string exception_)

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

let serve () =
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
                   let request : request = Marshal.from_channel input in
                   send output (handle request)
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

let call ?program request =
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let identity = Identity.compute (Store.default_directory ()) in
  let path = socket_path identity in
  let program = Option.value program ~default:(Identity.executable ()) in
  let rec attempt tries =
    match connect path with
    | Some socket -> Some socket
    | None ->
        if tries = 0 then None
        else begin
          if tries = 50 then start program;
          Unix.sleepf 0.1;
          attempt (tries - 1)
        end
  in
  match attempt 50 with
  | None -> refuse "could not start or reach the background process; try --no-server."
  | Some socket -> (
      let input = Unix.in_channel_of_descr socket in
      let output = Unix.out_channel_of_descr socket in
      match
        send output request;
        (Marshal.from_channel input : response)
      with
      | response ->
          Unix.close socket;
          response
      | exception _ ->
          (try Unix.close socket with Unix.Unix_error _ -> ());
          refuse
            "the background process ended while answering; see its log in the store's servers \
             directory.")
