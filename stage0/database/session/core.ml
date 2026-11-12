(* What a client keeps with a session, such as the problems of a project's
   manifests. The session layer does not look inside. *)
type attachment = ..
type attachment += Nothing

type t = {
  key : string;
  mutable engine : Engine.t;
  pointer : Store.pointer option;  (** Where the state is named in the store, if it is saved *)
  version : string;  (** What names the code that computed the state's results *)
  bases : Engine.t list;  (** The fixed bases the state is over *)
  mutable used : float;
  fingerprints : (string, string) Hashtbl.t;
      (** Each file's fingerprint, by its path, by which another set of files finds this state *)
  mutable pointed : bool;  (** Whether the pointer names the state as it is *)
  mutable attachment : attachment;
  snapshot_of : string option;
      (** For a snapshot of a state another process saves: the artifact it was opened from *)
}

type state = { store : Store.t; identity : string; sessions : (string, t) Hashtbl.t }

let state : state option ref = ref None
let logging = ref false

(* Run when every state is closed or discarded, so that a client lets go of
   what it built on them. *)
let closing : (unit -> unit) list ref = ref []
let on_close hook = closing := hook :: !closing

let current () =
  match !state with
  | Some state -> state
  | None ->
      (* A state leaves out the results of a query that is not declared, so
         none may be declared from here on. *)
      Engine.seal ();
      let store = Store.open_ (Store.default_directory ()) in
      (* Every process leaves a segment, so one that opens the store gathers
         the small ones once there are many, whether or not a background
         process ever runs. *)
      Store.compact store;
      let fresh =
        { store; identity = Identity.compute (Store.directory store); sessions = Hashtbl.create 8 }
      in
      state := Some fresh;
      fresh

let store () = (current ()).store
let identity () = (current ()).identity
let engine session = session.engine
let context session = Engine.context session.engine
let observer session = Engine.observer session.engine
let key session = session.key
let attachment session = session.attachment
let attach session attachment = session.attachment <- attachment
let touch session = session.used <- Unix.time ()
let set session input key value = Engine.set session.engine input key value
let remove session input key = Engine.remove session.engine input key
let find key = Hashtbl.find_opt (current ()).sessions key

let budget () =
  match Option.bind (Sys.getenv_opt "TRUSS_CACHE_SIZE") int_of_string_opt with
  | Some bytes -> bytes
  | None -> 20 * 1024 * 1024 * 1024

(* The versions whose states this program can read: its own identity, and
   each a client names. An artifact is marshaled, so a state of any other
   version is never read. *)
let readable_versions : string list ref = ref []

let allow_reading version =
  if not (List.mem version !readable_versions) then
    readable_versions := version :: !readable_versions

(* A pointer's record: the version that wrote the state, its artifact's
   name, and each file's fingerprint. It is text, not a marshaled value, so
   that any compiler can read any pointer of the store. *)
type record = { version : string; artifact : string; files : (string * string) list }

let record_header = "truss state 1"

let of_hex text =
  if String.length text mod 2 <> 0 then None
  else
    try
      Some
        (String.init
           (String.length text / 2)
           (fun index -> Char.chr (int_of_string ("0x" ^ String.sub text (2 * index) 2))))
    with Failure _ -> None

let print_record { version; artifact; files } =
  String.concat "\n"
    (record_header :: version :: Blake3.to_hex artifact
    :: List.map (fun (path, fingerprint) -> Blake3.to_hex fingerprint ^ " " ^ path) files)

let parse_record text =
  match String.split_on_char '\n' text with
  | header :: version :: artifact :: files when header = record_header -> (
      let file line =
        match String.index_opt line ' ' with
        | Some space ->
            Option.map
              (fun fingerprint ->
                (String.sub line (space + 1) (String.length line - space - 1), fingerprint))
              (of_hex (String.sub line 0 space))
        | None -> None
      in
      let files = List.map file files in
      match of_hex artifact with
      | Some artifact when List.for_all Option.is_some files ->
          Some { version; artifact; files = List.filter_map Fun.id files }
      | _ -> None)
  | _ -> None

let read_record pointer = Option.bind (Store.read pointer) parse_record

let new_engine state ~version ~bases =
  let engine = Engine.create ~log:!logging ~bases () in
  Engine.attach engine state.store ~version;
  engine

let open_state state ~version ~bases artifact =
  Engine.open_ ~log:!logging state.store ~version ~bases artifact

let point session pointer artifact =
  let files =
    List.sort compare
      (Hashtbl.fold (fun path print files -> (path, print) :: files) session.fingerprints [])
  in
  Store.write_pointer pointer (print_record { version = session.version; artifact; files });
  session.pointed <- true

(* Writes what changed in a session's state since it was last written, as a
   difference over the artifact it was opened from or last wrote, and points
   its name at it. *)
let save session =
  match session.pointer with
  | Some pointer when Engine.unwritten session.engine || not session.pointed ->
      point session pointer (Engine.write session.engine)
  | _ -> Engine.record_facts session.engine

let stabilize session =
  let change = Engine.stabilize session.engine in
  save session;
  change

(* A chain of differences is folded into one whole state once the
   differences reach half its size, which costs the state's size. So the
   background process folds while no request is waiting, and makes a command
   wait for it only once the differences are several times that. A process
   that serves one command folds as it opens the state, which costs it the
   state's size already. *)
let serving = ref false

let compact ?(waited_for = false) session =
  match session.pointer with
  | Some pointer ->
      let chain_size = Engine.chain_size session.engine in
      let limit = max (chain_size.whole / 2) 256 in
      if chain_size.differences > if waited_for && !serving then 4 * limit else limit then begin
        let artifact = Engine.write ~full:true session.engine in
        point session pointer artifact;
        Option.iter
          (fun engine -> session.engine <- engine)
          (open_state (current ()) ~version:session.version ~bases:session.bases artifact)
      end
  | None -> ()

(* A file's fingerprint, for telling which saved state a set of files is
   nearest to. *)
let fingerprint text = Blake3.hash text

let note_file session path = function
  | Some print ->
      if Hashtbl.find_opt session.fingerprints path <> Some print then begin
        Hashtbl.replace session.fingerprints path print;
        session.pointed <- false
      end
  | None ->
      if Hashtbl.mem session.fingerprints path then begin
        Hashtbl.remove session.fingerprints path;
        session.pointed <- false
      end

(* The saved state of a version nearest to a set of files: the one that
   differs from them in the fewest files, if it shares any. *)
let nearest state ~version (files : (string * string) list) =
  (* Another process may have written a state a moment ago. *)
  Store.refresh state.store;
  let wanted = Hashtbl.create (List.length files) in
  List.iter (fun (path, print) -> Hashtbl.replace wanted path print) files;
  let score (record : record) =
    let shared =
      List.fold_left
        (fun shared (path, print) ->
          if Hashtbl.find_opt wanted path = Some print then shared + 1 else shared)
        0 record.files
    in
    (shared, List.length record.files + List.length files - (2 * shared))
  in
  List.fold_left
    (fun best name ->
      match read_record (Store.pointer state.store name) with
      | Some record when record.version = version -> (
          let shared, differing = score record in
          if shared = 0 then best
          else
            match best with
            | Some (_, least) when least <= differing -> best
            | _ -> Some (record, differing))
      | Some _ | None -> best)
    None (Store.pointers state.store)
  |> Option.map fst

(* The list of the directories that have states, so that the pointer of one
   that is gone can be removed. *)
let homes_file state = Filename.concat (Store.directory state.store) "worktrees"

let known_homes state =
  try
    In_channel.with_open_bin (homes_file state) In_channel.input_lines
    |> List.filter_map (fun line ->
        match String.index_opt line '\t' with
        | Some i -> Some (String.sub line 0 i, String.sub line (i + 1) (String.length line - i - 1))
        | None -> None)
  with Sys_error _ -> []

let remember_home state home name =
  if not (List.mem (home, name) (known_homes state)) then
    try
      Out_channel.with_open_gen [ Open_append; Open_creat; Open_binary ] 0o644 (homes_file state)
        (fun out -> Printf.fprintf out "%s\t%s\n" home name)
    with Sys_error _ -> ()

type start = Own | Near | New

let open_ ~key ?pointer:name ?home ~version ~bases ~fingerprints () =
  let state = current () in
  match Hashtbl.find_opt state.sessions key with
  | Some session -> Ok (session, Own)
  | None -> (
      let pointer = Option.map (Store.pointer state.store) name in
      match pointer with
      | Some held when not (Store.lock held) -> Error ()
      | _ ->
          let bases = bases () in
          let own =
            (* Another process may have written the state a moment ago. *)
            Store.refresh state.store;
            Option.bind (Option.bind pointer read_record) (fun record ->
                if record.version <> version then None
                else
                  Option.map
                    (fun engine -> (engine, record))
                    (open_state state ~version ~bases record.artifact))
          in
          let engine, files, start =
            match own with
            | Some (engine, record) -> (engine, record.files, Own)
            | None -> (
                (* A new set of files starts from the nearest saved state,
                   if the store still has every input's value of it. *)
                match
                  Option.bind
                    (nearest state ~version (fingerprints ()))
                    (fun record -> open_state state ~version ~bases record.artifact)
                with
                | Some engine when Engine.inputs_stored engine -> (engine, [], Near)
                | Some _ | None -> (new_engine state ~version ~bases, [], New))
          in
          let table = Hashtbl.create (max 16 (List.length files)) in
          List.iter (fun (path, print) -> Hashtbl.replace table path print) files;
          let session =
            {
              key;
              engine;
              pointer;
              version;
              bases;
              used = Unix.time ();
              fingerprints = table;
              pointed = own <> None;
              attachment = Nothing;
              snapshot_of = None;
            }
          in
          Hashtbl.replace state.sessions key session;
          (match (home, name) with
          | Some home, Some name -> remember_home state home name
          | _ -> ());
          Ok (session, start))

(* A session that starts from another's state and changes on its own, for
   trying a change: the state is written, and opened again, so the two share
   everything but the trial's changes. It is never saved. *)
let trial session =
  let state = current () in
  save session;
  let artifact =
    match Engine.artifact session.engine with
    | Some artifact when not (Engine.unwritten session.engine) -> artifact
    | _ -> Engine.write session.engine
  in
  let engine =
    match open_state state ~version:session.version ~bases:session.bases artifact with
    | Some engine -> engine
    | None -> new_engine state ~version:session.version ~bases:session.bases
  in
  {
    key = session.key ^ " (trial)";
    engine;
    pointer = None;
    version = session.version;
    bases = session.bases;
    used = Unix.time ();
    fingerprints = Hashtbl.create 16;
    pointed = true;
    attachment = Nothing;
    snapshot_of = None;
  }

(* A session of the state that a name points at, which another process
   saves: opened without the name's lock, never saved, and changing on its
   own. It is opened again when the name points at another state. *)
let snapshot ~key ~pointer:name ~version ~bases =
  let state = current () in
  Store.refresh state.store;
  match read_record (Store.pointer state.store name) with
  | Some record when record.version = version -> (
      match Hashtbl.find_opt state.sessions key with
      | Some session when session.snapshot_of = Some record.artifact -> Some session
      | _ ->
          let bases = bases () in
          Option.map
            (fun engine ->
              let session =
                {
                  key;
                  engine;
                  pointer = None;
                  version;
                  bases;
                  used = Unix.time ();
                  fingerprints = Hashtbl.create 16;
                  pointed = true;
                  attachment = Nothing;
                  snapshot_of = Some record.artifact;
                }
              in
              Hashtbl.replace state.sessions key session;
              session)
            (open_state state ~version ~bases record.artifact))
  | Some _ | None -> None

(* Each directory that has a saved state, with the name its state is saved
   under. *)
let homes () = known_homes (current ())

let sessions () =
  match !state with
  | None -> []
  | Some state ->
      Hashtbl.fold
        (fun key session acc -> (key, List.length (Engine.nodes session.engine)) :: acc)
        state.sessions []
      |> List.sort compare

let all () =
  match !state with
  | None -> []
  | Some state -> Hashtbl.fold (fun _ session sessions -> session :: sessions) state.sessions []

let directory name = Store.files (store ()) name

let results ~kind =
  let store = store () in
  ( (fun key -> Store.find_result store ~kind ~key),
    fun key value -> Store.add_result store ~kind ~key value )

let find_result ~kind ~key = Store.find_result (store ()) ~kind ~key
let flush () = Store.flush (store ())

let close_all state =
  Store.close state.store;
  Engine.forget_bases ();
  List.iter (fun hook -> hook ()) !closing

let reset () =
  match !state with
  | None -> ()
  | Some s ->
      Hashtbl.iter
        (fun _ session ->
          save session;
          Option.iter Store.unlock session.pointer)
        s.sessions;
      close_all s;
      state := None

(* Runs a command. If a state it reads has lost an input's value, as after
   another process collected the store, every open state is discarded with
   its pointer, and the command is run once more, from the files. *)
let recovering run =
  try run ()
  with Engine.Lost _ ->
    (match !state with
    | Some s ->
        Hashtbl.iter
          (fun _ session ->
            Option.iter
              (fun pointer ->
                Store.remove_pointer pointer;
                Store.unlock pointer)
              session.pointer)
          s.sessions;
        close_all s;
        state := None
    | None -> ());
    run ()

let idle_limit = 3600.

(* Drops sessions unused for [idle_limit], saving them first. *)
let drop_idle () =
  let state = current () in
  let now = Unix.time () in
  let idle =
    Hashtbl.fold
      (fun key session acc ->
        if now -. session.used > idle_limit then (key, session) :: acc else acc)
      state.sessions []
  in
  List.iter
    (fun (key, session) ->
      save session;
      Option.iter Store.unlock session.pointer;
      Hashtbl.remove state.sessions key)
    idle

(* Removes the pointer of each directory that is gone, of any compiler, and
   its line in the list. A new set of files looks through every pointer for
   the state nearest to it, so those of directories that are gone must not
   gather. *)
let prune state =
  let known = known_homes state in
  let live, dead = List.partition (fun (home, _) -> Sys.file_exists home) known in
  if dead <> [] then begin
    List.iter (fun (_, name) -> Store.remove_pointer (Store.pointer state.store name)) dead;
    try
      File_system.write_atomically (homes_file state)
        (String.concat "" (List.map (fun (home, name) -> Printf.sprintf "%s\t%s\n" home name) live))
    with Sys_error _ -> ()
  end

(* Keeps the store within its budget. What a state of a version this
   program can read refers to is kept, and so is what [keep] names. A state
   another version wrote can be read only by that version, so its values
   are not kept; that version finds its state gone, and starts again. *)
let collect ~keep =
  let state = current () in
  prune state;
  Store.compact state.store;
  (* One process collects at a time: every background process comes here. *)
  let lock =
    Unix.openfile
      (Filename.concat (Store.directory state.store) "collect.lock")
      [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644
  in
  let held =
    match Unix.lockf lock F_TLOCK 0 with () -> true | exception Unix.Unix_error _ -> false
  in
  Fun.protect
    ~finally:(fun () -> Unix.close lock)
    (fun () ->
      if held && Store.size state.store > budget () then begin
        let live = Hashtbl.create 4096 in
        let keep_artifact ~version artifact =
          List.iter
            (fun name -> Hashtbl.replace live name ())
            (Engine.values_in state.store ~version artifact)
        in
        List.iter
          (fun name ->
            match read_record (Store.pointer state.store name) with
            | Some record
              when record.version = state.identity || List.mem record.version !readable_versions ->
                keep_artifact ~version:record.version record.artifact
            | Some _ | None -> ())
          (Store.pointers state.store);
        List.iter (fun (version, artifact) -> keep_artifact ~version artifact) (keep ());
        Store.collect state.store ~budget:(budget ()) ~live:(Hashtbl.mem live)
      end)
