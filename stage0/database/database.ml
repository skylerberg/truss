(* The code database's sessions and requests. See database.mli and
   DATABASE.md, "Sessions" and "Requests". *)

(* Loading packages *)

let load_package engine ~name ~dependencies (modules : (Path.module_ * string) list) =
  List.iter (fun (module_, text) -> Engine.set engine Workspace.file_text module_ text) modules;
  Engine.set engine Workspace.packages name
    { Workspace.name; dependencies; modules = List.map fst modules }

let load_standard engine =
  load_package engine ~name:Standard_library.package ~dependencies:[] Standard_library.modules

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
        { Workspace.name = manifest.name; dependencies = manifest.dependencies; modules = own })
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

let new_engine state =
  let engine = Engine.create ~shared:state.standard () in
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
          match Engine.load ~shared:state.standard state.store journal with
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
        else f session packages

let problems_text session = String.concat "" (List.map (fun p -> p ^ "\n") session.problems)

let check state request =
  with_session state request (fun session packages ->
      let found = diagnostics_of session packages in
      let errors = problems_text session in
      let output = render_diagnostics ~json:request.json session found in
      let status = if found = [] && session.problems = [] then 0 else 1 in
      if request.json then answer ~errors ~status output
      else answer ~errors:(errors ^ output) ~status "")

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
  | Impact _ | Holes | References _ | Dependencies _ | Overlap _ | Explain _ ->
      refuse "not built yet"

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
