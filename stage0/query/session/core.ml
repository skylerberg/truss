type attachment = ..
type attachment += Nothing

type key =
  | Worktree of string
  | Commit of { repository : string; commit : string }
  | Library of string
  | Published of { package : Path.package; hash : string }
  | Snapshot of string
  | Trial of key

type t = {
  key : key;
  mutable engine : Engine.t;
  pointer : Store.pointer option;
  version : string;
  bases : Engine.t list;
  mutable used : float;
  fingerprints : (string, string) Hashtbl.t;
  mutable pointed : bool;
  mutable attachment : attachment;
  snapshot_of : string option;
}

type state = { store : Store.t; identity : string; sessions : (key, t) Hashtbl.t }

let state : state option ref = ref None
let logging = ref false
let closing : (unit -> unit) list ref = ref []
let on_close hook = closing := hook :: !closing

let current () =
  match !state with
  | Some state -> state
  | None ->
      Engine.seal ();
      let store = Store.open_ (Store.default_directory ()) in
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

let rec show_key = function
  | Worktree root -> root
  | Commit { repository; commit } -> Printf.sprintf "commit %s of %s" commit repository
  | Library name -> "library " ^ name
  | Published { package; hash } -> Printf.sprintf "%s %s" (Path.show_package package) hash
  | Snapshot root -> "snapshot of " ^ root
  | Trial key -> show_key key ^ " (trial)"

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

let readable_versions : string list ref = ref []

let allow_reading version =
  if not (List.mem version !readable_versions) then
    readable_versions := version :: !readable_versions

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

let save session =
  match session.pointer with
  | Some pointer when Engine.unwritten session.engine || not session.pointed ->
      point session pointer (Engine.write session.engine)
  | _ -> Engine.record_facts session.engine

let stabilize session =
  let change = Engine.stabilize session.engine in
  save session;
  change

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

let nearest state ~version (files : (string * string) list) =
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

let homes_file state = Filename.concat (Store.directory state.store) "worktrees"

let known_homes state =
  try
    In_channel.with_open_bin (homes_file state) In_channel.input_lines
    |> List.filter_map (fun line ->
        match String.index_opt line '\t' with
        | Some separator ->
            Some
              ( String.sub line 0 separator,
                String.sub line (separator + 1) (String.length line - separator - 1) )
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
    key = Trial session.key;
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
let cache_directory name = Store.cache_files (store ()) name

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
  | Some current ->
      Hashtbl.iter
        (fun _ session ->
          save session;
          Option.iter Store.unlock session.pointer)
        current.sessions;
      close_all current;
      state := None

let recovering run =
  try run ()
  with Engine.Lost _ ->
    (match !state with
    | Some current ->
        Hashtbl.iter
          (fun _ session ->
            Option.iter
              (fun pointer ->
                Store.remove_pointer pointer;
                Store.unlock pointer)
              session.pointer)
          current.sessions;
        close_all current;
        state := None
    | None -> ());
    run ()

let idle_limit = 3600.

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

let collect ~keep =
  let state = current () in
  prune state;
  Store.compact state.store;
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
