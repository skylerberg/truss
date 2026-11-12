(* A segment is a header followed by records. A record is a kind byte, a
   32-byte key, the value's length in 4 bytes, the value, and an 8-byte
   checksum of everything before it in the record. A value's key is the hash
   of its bytes, and a result's is the hash of its kind and key, so every key
   has the same width, and a sealed segment's index is a sorted run of
   fixed-width entries: the key, the record's offset in 8 bytes, and its
   value's length in 4. *)

let header = "TRUSS-SEGMENT-1\n"
let key_width = 32
let entry_width = key_width + 8 + 4
let seal_size = 64 * 1024 * 1024

(* FNV-1a, 64 bits: a checksum against torn and damaged records, which need
   no cryptographic strength. *)
let fnv hash bytes =
  let hash = ref hash in
  for index = 0 to String.length bytes - 1 do
    hash :=
      Int64.mul
        (Int64.logxor !hash (Int64.of_int (Char.code (String.unsafe_get bytes index))))
        0x100000001b3L
  done;
  !hash

let checksum parts =
  let buffer = Bytes.create 8 in
  Bytes.set_int64_le buffer 0 (List.fold_left fnv 0xcbf29ce484222325L parts);
  Bytes.to_string buffer

type location = { offset : int; length : int }

type segment = {
  path : string;
  mutable index : string option;  (** A sealed segment's sorted entries *)
  table : (string, location) Hashtbl.t;  (** An active segment's entries, as scanned *)
  mutable scanned : int;  (** How far an active segment has been read *)
  mutable channel : in_channel option;
}

type writer = {
  segment : segment;
  descriptor : Unix.file_descr;
  mutable size : int;  (** The segment's length once [pending] is written *)
  pending : Buffer.t;  (** Records not yet written to the file *)
}

type t = {
  root : string;
  mutable segments : segment list;  (** Others', newest first *)
  mutable refreshed : float;  (** When other processes' segments were last looked for *)
  mutable writer : writer option;
  used : (string, unit) Hashtbl.t;  (** Results this process read or added *)
}

let segments_directory store = Filename.concat store.root "segments"
let directory store = store.root

let default_directory () =
  match Sys.getenv_opt "TRUSS_CACHE" with
  | Some directory when directory <> "" -> directory
  | _ -> (
      match Sys.getenv_opt "XDG_CACHE_HOME" with
      | Some cache when cache <> "" -> Filename.concat cache "truss"
      | _ ->
          let home =
            Option.value (Sys.getenv_opt "HOME") ~default:(Filename.get_temp_dir_name ())
          in
          Filename.concat (Filename.concat home ".cache") "truss")

let close_channel segment =
  Option.iter close_in_noerr segment.channel;
  segment.channel <- None

(* The segments with an open channel. A process reads from many segments,
   and may hold only so many files open, so past a limit the channels are
   closed, and each is opened again when next read. *)
let open_segments : segment list ref = ref []
let open_limit = 64

let channel segment =
  match segment.channel with
  | Some channel -> channel
  | None ->
      if List.length !open_segments >= open_limit then begin
        List.iter close_channel !open_segments;
        open_segments := []
      end;
      let channel = open_in_bin segment.path in
      segment.channel <- Some channel;
      open_segments := segment :: !open_segments;
      channel

(* The record at an offset, checked; [None] if it is cut short or damaged. *)
let read_record channel ~offset =
  try
    seek_in channel offset;
    let head = really_input_string channel (1 + key_width + 4) in
    let length = Int32.to_int (String.get_int32_le head (1 + key_width)) in
    if length < 0 then None
    else
      let value = really_input_string channel length in
      let check = really_input_string channel 8 in
      if checksum [ head; value ] = check then Some (head.[0], String.sub head 1 key_width, value)
      else None
  with End_of_file | Sys_error _ -> None

let record_size length = 1 + key_width + 4 + length + 8

(* Reads an active segment's records from where the last scan stopped. *)
let scan segment =
  match open_in_bin segment.path with
  | exception Sys_error _ -> ()
  | channel ->
      Fun.protect
        ~finally:(fun () -> close_in_noerr channel)
        (fun () ->
          let size = in_channel_length channel in
          if segment.scanned = 0 then
            segment.scanned <-
              (match really_input_string channel (String.length header) with
              | read when read = header -> String.length header
              | _ -> size
              | exception End_of_file -> size);
          let rec loop offset =
            if offset < size then
              match read_record channel ~offset with
              | Some (_, key, value) ->
                  Hashtbl.replace segment.table key { offset; length = String.length value };
                  loop (offset + record_size (String.length value))
              | None -> offset
            else offset
          in
          segment.scanned <- loop segment.scanned)

let index_path segment_path = Filename.remove_extension segment_path ^ ".index"

let compare_key index position key =
  let rec loop offset =
    if offset = key_width then 0
    else
      let order = Char.compare index.[position + offset] key.[offset] in
      if order <> 0 then order else loop (offset + 1)
  in
  loop 0

let search index key =
  let rec halve low high =
    if low >= high then None
    else
      let middle = (low + high) / 2 in
      let position = middle * entry_width in
      let order = compare_key index position key in
      if order = 0 then
        Some
          {
            offset = Int64.to_int (String.get_int64_le index (position + key_width));
            length = Int32.to_int (String.get_int32_le index (position + key_width + 8));
          }
      else if order < 0 then halve (middle + 1) high
      else halve low middle
  in
  halve 0 (String.length index / entry_width)

let find_in segment key =
  match segment.index with
  | Some index -> search index key
  | None -> Hashtbl.find_opt segment.table key

let load_segment path =
  let segment = { path; index = None; table = Hashtbl.create 64; scanned = 0; channel = None } in
  (match File_system.read (index_path path) with
  | index when String.length index mod entry_width = 0 -> segment.index <- Some index
  | _ | (exception Sys_error _) -> scan segment);
  segment

(* Finds segments other processes made or grew since the last look. *)
let refresh store =
  let directory = segments_directory store in
  let own = Option.map (fun writer -> writer.segment.path) store.writer in
  let present =
    match Sys.readdir directory with
    | entries ->
        Array.to_list entries
        |> List.filter (fun entry -> Filename.check_suffix entry ".segment")
        |> List.map (Filename.concat directory)
        |> List.filter (fun path -> Some path <> own)
    | exception Sys_error _ -> []
  in
  let there = Hashtbl.create (List.length present) in
  List.iter (fun path -> Hashtbl.replace there path ()) present;
  let known = List.filter (fun segment -> Hashtbl.mem there segment.path) store.segments in
  List.iter
    (fun segment -> if not (Hashtbl.mem there segment.path) then close_channel segment)
    store.segments;
  let had = Hashtbl.create (List.length known) in
  List.iter (fun segment -> Hashtbl.replace had segment.path ()) known;
  let fresh =
    List.filter_map
      (fun path -> if Hashtbl.mem had path then None else Some (load_segment path))
      present
  in
  List.iter
    (fun segment ->
      if segment.index = None then
        if Sys.file_exists (index_path segment.path) then
          begin match File_system.read (index_path segment.path) with
          | index when String.length index mod entry_width = 0 -> segment.index <- Some index
          | _ | (exception Sys_error _) -> scan segment
          end
        else scan segment)
    known;
  store.segments <- fresh @ known;
  store.refreshed <- Unix.gettimeofday ()

let writer_name () =
  Random.self_init ();
  Printf.sprintf "%d-%d-%06x" (Unix.getpid ()) (int_of_float (Unix.time ())) (Random.bits ())

let new_writer store =
  File_system.make_directory (segments_directory store);
  let path = Filename.concat (segments_directory store) (writer_name () ^ ".segment") in
  let descriptor = Unix.openfile path [ O_WRONLY; O_CREAT; O_EXCL; O_CLOEXEC ] 0o644 in
  Unix.lockf descriptor F_LOCK 0;
  File_system.write_all descriptor header;
  let segment =
    {
      path;
      index = None;
      table = Hashtbl.create 1024;
      scanned = String.length header;
      channel = None;
    }
  in
  { segment; descriptor; size = String.length header; pending = Buffer.create 4096 }

(* Records are gathered and written to the file together, so that adding one
   is not a system call. *)
let pending_limit = 1024 * 1024

let drain writer =
  if Buffer.length writer.pending > 0 then begin
    File_system.write_all writer.descriptor (Buffer.contents writer.pending);
    Buffer.clear writer.pending
  end

(* Writes a sealed segment's index beside it, from its entries. *)
let write_index segment =
  let entries =
    List.sort
      (fun (left, _) (right, _) -> String.compare left right)
      (Hashtbl.fold (fun key location acc -> (key, location) :: acc) segment.table [])
  in
  let buffer = Buffer.create (List.length entries * entry_width) in
  List.iter
    (fun (key, { offset; length }) ->
      Buffer.add_string buffer key;
      Buffer.add_int64_le buffer (Int64.of_int offset);
      Buffer.add_int32_le buffer (Int32.of_int length))
    entries;
  File_system.write_atomically (index_path segment.path) (Buffer.contents buffer);
  segment.index <- Some (Buffer.contents buffer)

let writing : t list ref = ref []

let seal store =
  match store.writer with
  | None -> ()
  | Some writer ->
      drain writer;
      (try Unix.fsync writer.descriptor with Unix.Unix_error _ -> ());
      write_index writer.segment;
      Unix.close writer.descriptor;
      store.writer <- None;
      store.segments <- writer.segment :: store.segments;
      writing := List.filter (fun other -> other != store) !writing

(* A process that ends seals what it added, so that the next reads an index
   and not every record. *)
let () =
  at_exit (fun () ->
      List.iter (fun store -> try seal store with Sys_error _ | Unix.Unix_error _ -> ()) !writing)

let writer store =
  match store.writer with
  | Some writer when writer.size < seal_size -> writer
  | full_writer ->
      if Option.is_some full_writer then seal store;
      let writer = new_writer store in
      store.writer <- Some writer;
      writing := store :: !writing;
      writer

let append_record store kind key value =
  let writer = writer store in
  let head = Bytes.create (1 + key_width + 4) in
  Bytes.set head 0 kind;
  Bytes.blit_string key 0 head 1 key_width;
  Bytes.set_int32_le head (1 + key_width) (Int32.of_int (String.length value));
  let head = Bytes.unsafe_to_string head in
  Hashtbl.replace writer.segment.table key { offset = writer.size; length = String.length value };
  Buffer.add_string writer.pending head;
  Buffer.add_string writer.pending value;
  Buffer.add_string writer.pending (checksum [ head; value ]);
  writer.size <- writer.size + record_size (String.length value);
  if Buffer.length writer.pending >= pending_limit then drain writer

let open_ root =
  File_system.make_directory root;
  let store = { root; segments = []; refreshed = 0.; writer = None; used = Hashtbl.create 64 } in
  refresh store;
  store

let close store =
  seal store;
  List.iter close_channel store.segments

let flush store =
  Option.iter
    (fun writer ->
      drain writer;
      Unix.fsync writer.descriptor)
    store.writer

(* The record must be the key's own: an index that is damaged can name
   another record's offset. *)
let read_from segment key location =
  match read_record (channel segment) ~offset:location.offset with
  | Some (_, record_key, value) when record_key = key -> Some value
  | Some _ | None -> None
  | exception Sys_error _ -> None

(* A record this process added, which is in memory until it is written. *)
let read_own writer key location =
  let written = writer.size - Buffer.length writer.pending in
  if location.offset >= written then
    Some (Buffer.sub writer.pending (location.offset - written + 1 + key_width + 4) location.length)
  else read_from writer.segment key location

let lookup_once store key =
  let own =
    Option.bind store.writer (fun writer ->
        Option.bind (Hashtbl.find_opt writer.segment.table key) (read_own writer key))
  in
  match own with
  | Some value -> Some value
  | None ->
      List.find_map
        (fun segment -> Option.bind (find_in segment key) (read_from segment key))
        store.segments

let refresh_interval = 0.02

(* A miss looks again for what other processes added, but not more often
   than every [refresh_interval]: a build that computes everything misses
   on every result, and a result another process added a moment ago is only
   computed again. *)
let lookup store key =
  match lookup_once store key with
  | Some value -> Some value
  | None ->
      if Unix.gettimeofday () -. store.refreshed > refresh_interval then begin
        refresh store;
        lookup_once store key
      end
      else None

let present store key =
  (match store.writer with Some writer -> Hashtbl.mem writer.segment.table key | None -> false)
  || List.exists (fun segment -> find_in segment key <> None) store.segments

let put store bytes =
  let key = Blake3.hash bytes in
  if not (present store key) then append_record store 'v' key bytes;
  key

let get store key = if String.length key <> key_width then None else lookup store key

(* A result's name. Values share the segments with results, and the
   derive-key mode keeps every result's name apart from every value's. *)
let derive_result_key = Blake3.derive_key ~context:"truss 2026-11-12 store result"

let result_key ~kind ~key =
  derive_result_key (Cbor.encode (Cbor.Array [ Cbor.Text kind; Cbor.Bytes key ]))

let find_result store ~kind ~key =
  let name = result_key ~kind ~key in
  match lookup store name with
  | Some value ->
      Hashtbl.replace store.used name ();
      Some value
  | None -> None

let add_result store ~kind ~key value =
  let name = result_key ~kind ~key in
  Hashtbl.replace store.used name ();
  if not (present store name) then append_record store 'r' name value

let files store name =
  let path = Filename.concat store.root name in
  File_system.make_directory path;
  path

type pointer = {
  store : t;
  pointer_path : string;
  mutable lock_descriptor : Unix.file_descr option;
}

let pointers_directory store = Filename.concat store.root "pointers"

let file_name name =
  String.map
    (fun order ->
      match order with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '-' | '_' | '.' -> order | _ -> '_')
    name

let pointer store name =
  File_system.make_directory (pointers_directory store);
  {
    store;
    pointer_path = Filename.concat (pointers_directory store) (file_name name ^ ".pointer");
    lock_descriptor = None;
  }

let pointers store =
  match Sys.readdir (pointers_directory store) with
  | entries ->
      Array.to_list entries
      |> List.filter (fun entry -> Filename.check_suffix entry ".pointer")
      |> List.map Filename.remove_extension
      |> List.sort compare
  | exception Sys_error _ -> []

let lock pointer =
  match pointer.lock_descriptor with
  | Some _ -> true
  | None -> (
      let descriptor =
        Unix.openfile (pointer.pointer_path ^ ".lock") [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644
      in
      match Unix.lockf descriptor F_TLOCK 0 with
      | () ->
          pointer.lock_descriptor <- Some descriptor;
          true
      | exception Unix.Unix_error ((Unix.EAGAIN | Unix.EACCES), _, _) ->
          Unix.close descriptor;
          false)

let unlock pointer =
  match pointer.lock_descriptor with
  | Some descriptor ->
      Unix.close descriptor;
      pointer.lock_descriptor <- None
  | None -> ()

(* What a pointer holds is framed with its length and a checksum, so that
   one cut short or damaged reads as nothing. *)
let framed bytes =
  let length = Bytes.create 4 in
  Bytes.set_int32_le length 0 (Int32.of_int (String.length bytes));
  let head = Bytes.to_string length in
  head ^ checksum [ head; bytes ] ^ bytes

let read pointer =
  match File_system.read pointer.pointer_path with
  | exception Sys_error _ -> None
  | contents ->
      let total = String.length contents in
      if total < 12 then None
      else
        let length = Int32.to_int (String.get_int32_le contents 0) in
        if length < 0 || 12 + length <> total then None
        else
          let head = String.sub contents 0 4 in
          let check = String.sub contents 4 8 in
          let bytes = String.sub contents 12 length in
          if checksum [ head; bytes ] = check then Some bytes else None

(* Written beside the pointer and renamed over it, after the values it may
   name are durable, so a pointer never names a value a crash lost. *)
let write_pointer pointer bytes =
  flush pointer.store;
  File_system.write_atomically ~durable:true pointer.pointer_path (framed bytes)

let remove_pointer pointer =
  List.iter
    (fun path -> try Sys.remove path with Sys_error _ -> ())
    [ pointer.pointer_path; pointer.pointer_path ^ ".lock" ]

let file_size path = try (Unix.stat path).st_size with Unix.Unix_error _ -> 0

let size store =
  refresh store;
  List.fold_left (fun total segment -> total + file_size segment.path) 0 store.segments
  + match store.writer with Some writer -> writer.size | None -> 0

(* Whether a segment's writer has gone: its lock can be taken. *)
let abandoned segment =
  segment.index <> None
  ||
  match Unix.openfile segment.path [ O_RDWR; O_CLOEXEC ] 0 with
  | exception Unix.Unix_error _ -> false
  | descriptor ->
      Fun.protect
        ~finally:(fun () -> Unix.close descriptor)
        (fun () ->
          match Unix.lockf descriptor F_TEST 0 with
          | () -> true
          | exception Unix.Unix_error _ -> false)

let week = 7. *. 24. *. 3600.

let entries segment =
  match segment.index with
  | Some index ->
      List.init
        (String.length index / entry_width)
        (fun offset ->
          let position = offset * entry_width in
          ( String.sub index position key_width,
            {
              offset = Int64.to_int (String.get_int64_le index (position + key_width));
              length = Int32.to_int (String.get_int32_le index (position + key_width + 8));
            } ))
  | None -> Hashtbl.fold (fun key location acc -> (key, location) :: acc) segment.table []

(* Copies the records of segments that [keep] chooses into this process's
   segment, and deletes those segments. *)
let rewrite store candidates ~keep =
  List.iter
    (fun segment ->
      List.iter
        (fun (key, location) ->
          match read_record (channel segment) ~offset:location.offset with
          | Some (kind, record_key, value) when record_key = key ->
              if
                keep segment kind key
                && not
                     (match store.writer with
                     | Some writer -> Hashtbl.mem writer.segment.table key
                     | None -> false)
              then append_record store kind key value
          | Some _ | None | (exception Sys_error _) -> ())
        (entries segment))
    candidates;
  flush store;
  List.iter
    (fun segment ->
      close_channel segment;
      List.iter
        (fun path -> try Sys.remove path with Sys_error _ -> ())
        [ segment.path; index_path segment.path ])
    candidates;
  store.segments <- List.filter (fun segment -> not (List.memq segment candidates)) store.segments

let collect store ~budget ~live =
  if size store > budget then begin
    let recent path =
      match Unix.stat path with
      | stat -> Unix.time () -. stat.st_mtime < week
      | exception Unix.Unix_error _ -> false
    in
    let young = Hashtbl.create 64 in
    let candidates = List.filter abandoned store.segments in
    List.iter (fun segment -> Hashtbl.replace young segment.path (recent segment.path)) candidates;
    rewrite store candidates ~keep:(fun segment kind key ->
        match kind with
        | 'v' -> live key
        | _ -> Hashtbl.find young segment.path || Hashtbl.mem store.used key)
  end

(* Every process that writes leaves a segment, and a lookup searches each
   segment's index, so small segments are gathered into one once there are
   many. Every record is kept. *)
let small = 8 * 1024 * 1024
let many = 32

let compact store =
  refresh store;
  let candidates =
    List.filter (fun segment -> file_size segment.path < small && abandoned segment) store.segments
  in
  if List.length candidates >= many then rewrite store candidates ~keep:(fun _ _ _ -> true)
