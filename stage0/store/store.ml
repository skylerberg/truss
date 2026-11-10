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

let rec make_directory path =
  if not (Sys.file_exists path) then begin
    make_directory (Filename.dirname path);
    try Unix.mkdir path 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let segments_directory t = Filename.concat t.root "segments"
let directory t = t.root

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

let read_file path = In_channel.with_open_bin path In_channel.input_all

(* Reading records *)

let channel segment =
  match segment.channel with
  | Some channel -> channel
  | None ->
      let channel = open_in_bin segment.path in
      segment.channel <- Some channel;
      channel

let close_channel segment =
  Option.iter close_in_noerr segment.channel;
  segment.channel <- None

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
  let rec loop i =
    if i = key_width then 0
    else
      let c = Char.compare index.[position + i] key.[i] in
      if c <> 0 then c else loop (i + 1)
  in
  loop 0

let search index key =
  let rec halve low high =
    if low >= high then None
    else
      let middle = (low + high) / 2 in
      let position = middle * entry_width in
      let c = compare_key index position key in
      if c = 0 then
        Some
          {
            offset = Int64.to_int (String.get_int64_le index (position + key_width));
            length = Int32.to_int (String.get_int32_le index (position + key_width + 8));
          }
      else if c < 0 then halve (middle + 1) high
      else halve low middle
  in
  halve 0 (String.length index / entry_width)

let find_in segment key =
  match segment.index with
  | Some index -> search index key
  | None -> Hashtbl.find_opt segment.table key

let load_segment path =
  let segment = { path; index = None; table = Hashtbl.create 64; scanned = 0; channel = None } in
  (match read_file (index_path path) with
  | index when String.length index mod entry_width = 0 -> segment.index <- Some index
  | _ | (exception Sys_error _) -> scan segment);
  segment

(* Finds segments other processes made or grew since the last look. *)
let refresh t =
  let directory = segments_directory t in
  let own = Option.map (fun w -> w.segment.path) t.writer in
  let present =
    match Sys.readdir directory with
    | entries ->
        Array.to_list entries
        |> List.filter (fun entry -> Filename.check_suffix entry ".segment")
        |> List.map (Filename.concat directory)
        |> List.filter (fun path -> Some path <> own)
    | exception Sys_error _ -> []
  in
  let known = List.filter (fun s -> List.mem s.path present) t.segments in
  List.iter (fun s -> if not (List.mem s.path present) then close_channel s) t.segments;
  let fresh =
    List.filter_map
      (fun path ->
        if List.exists (fun s -> s.path = path) known then None else Some (load_segment path))
      present
  in
  List.iter
    (fun s ->
      if s.index = None then
        if Sys.file_exists (index_path s.path) then
          begin match read_file (index_path s.path) with
          | index when String.length index mod entry_width = 0 -> s.index <- Some index
          | _ | (exception Sys_error _) -> scan s
          end
        else scan s)
    known;
  t.segments <- fresh @ known;
  t.refreshed <- Unix.gettimeofday ()

(* Writing *)

let writer_name () =
  Random.self_init ();
  Printf.sprintf "%d-%d-%06x" (Unix.getpid ()) (int_of_float (Unix.time ())) (Random.bits ())

let rec write_all descriptor bytes offset =
  if offset < String.length bytes then
    let written = Unix.write_substring descriptor bytes offset (String.length bytes - offset) in
    write_all descriptor bytes (offset + written)

let new_writer t =
  make_directory (segments_directory t);
  let path = Filename.concat (segments_directory t) (writer_name () ^ ".segment") in
  let descriptor = Unix.openfile path [ O_WRONLY; O_CREAT; O_EXCL; O_CLOEXEC ] 0o644 in
  Unix.lockf descriptor F_LOCK 0;
  write_all descriptor header 0;
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
    write_all writer.descriptor (Buffer.contents writer.pending) 0;
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
  let path = index_path segment.path in
  let temporary = path ^ ".partial" in
  Out_channel.with_open_bin temporary (fun out -> Buffer.output_buffer out buffer);
  Sys.rename temporary path;
  segment.index <- Some (Buffer.contents buffer)

let writing : t list ref = ref []

let seal t =
  match t.writer with
  | None -> ()
  | Some writer ->
      drain writer;
      (try Unix.fsync writer.descriptor with Unix.Unix_error _ -> ());
      write_index writer.segment;
      Unix.close writer.descriptor;
      t.writer <- None;
      t.segments <- writer.segment :: t.segments;
      writing := List.filter (fun other -> other != t) !writing

(* A process that ends seals what it added, so that the next reads an index
   and not every record. *)
let () =
  at_exit (fun () ->
      List.iter (fun t -> try seal t with Sys_error _ | Unix.Unix_error _ -> ()) !writing)

let writer t =
  match t.writer with
  | Some writer when writer.size < seal_size -> writer
  | found ->
      if Option.is_some found then seal t;
      let writer = new_writer t in
      t.writer <- Some writer;
      writing := t :: !writing;
      writer

let append_record t kind key value =
  let writer = writer t in
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
  make_directory root;
  let t = { root; segments = []; refreshed = 0.; writer = None; used = Hashtbl.create 64 } in
  refresh t;
  t

let close t =
  seal t;
  List.iter close_channel t.segments

let flush t =
  Option.iter
    (fun writer ->
      drain writer;
      Unix.fsync writer.descriptor)
    t.writer

(* Looking up *)

let read_from segment location =
  match read_record (channel segment) ~offset:location.offset with
  | Some (_, _, value) -> Some value
  | None -> None
  | exception Sys_error _ -> None

(* A record this process added, which is in memory until it is written. *)
let read_own writer location =
  let written = writer.size - Buffer.length writer.pending in
  if location.offset >= written then
    Some (Buffer.sub writer.pending (location.offset - written + 1 + key_width + 4) location.length)
  else read_from writer.segment location

let lookup_once t key =
  let own =
    Option.bind t.writer (fun writer ->
        Option.bind (Hashtbl.find_opt writer.segment.table key) (read_own writer))
  in
  match own with
  | Some value -> Some value
  | None ->
      List.find_map
        (fun segment -> Option.bind (find_in segment key) (read_from segment))
        t.segments

(* A miss looks again for what other processes added, but not more often
   than every twenty milliseconds: a build that computes everything misses
   on every result, and a result another process added a moment ago is only
   computed again. *)
let lookup t key =
  match lookup_once t key with
  | Some value -> Some value
  | None ->
      if Unix.gettimeofday () -. t.refreshed > 0.02 then begin
        refresh t;
        lookup_once t key
      end
      else None

let present t key =
  (match t.writer with Some w -> Hashtbl.mem w.segment.table key | None -> false)
  || List.exists (fun segment -> find_in segment key <> None) t.segments

let put t bytes =
  let key = Blake3.hash bytes in
  if not (present t key) then append_record t 'v' key bytes;
  key

let get t key = if String.length key <> key_width then None else lookup t key
let result_key ~kind ~key = Blake3.hash ("result\000" ^ kind ^ "\000" ^ key)

let find_result t ~kind ~key =
  let name = result_key ~kind ~key in
  match lookup t name with
  | Some value ->
      Hashtbl.replace t.used name ();
      Some value
  | None -> None

let add_result t ~kind ~key value =
  let name = result_key ~kind ~key in
  Hashtbl.replace t.used name ();
  if not (present t name) then append_record t 'r' name value

let files t name =
  let path = Filename.concat t.root name in
  make_directory path;
  path

(* Pointers *)

type pointer = {
  store : t;
  pointer_path : string;
  mutable lock_descriptor : Unix.file_descr option;
}

let pointers_directory t = Filename.concat t.root "pointers"

let file_name name =
  String.map
    (fun c -> match c with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '-' | '_' | '.' -> c | _ -> '_')
    name

let pointer t name =
  make_directory (pointers_directory t);
  {
    store = t;
    pointer_path = Filename.concat (pointers_directory t) (file_name name ^ ".pointer");
    lock_descriptor = None;
  }

let pointers t =
  match Sys.readdir (pointers_directory t) with
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
  match read_file pointer.pointer_path with
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
let point pointer bytes =
  flush pointer.store;
  let temporary = pointer.pointer_path ^ ".partial" in
  let descriptor = Unix.openfile temporary [ O_WRONLY; O_CLOEXEC; O_CREAT; O_TRUNC ] 0o644 in
  Fun.protect
    ~finally:(fun () -> Unix.close descriptor)
    (fun () ->
      write_all descriptor (framed bytes) 0;
      Unix.fsync descriptor);
  Sys.rename temporary pointer.pointer_path

let remove_pointer pointer =
  List.iter
    (fun path -> try Sys.remove path with Sys_error _ -> ())
    [ pointer.pointer_path; pointer.pointer_path ^ ".lock" ]

(* Collection *)

let file_size path = try (Unix.stat path).st_size with Unix.Unix_error _ -> 0

let size t =
  refresh t;
  List.fold_left (fun total s -> total + file_size s.path) 0 t.segments
  + match t.writer with Some w -> w.size | None -> 0

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
        (fun i ->
          let position = i * entry_width in
          ( String.sub index position key_width,
            {
              offset = Int64.to_int (String.get_int64_le index (position + key_width));
              length = Int32.to_int (String.get_int32_le index (position + key_width + 8));
            } ))
  | None -> Hashtbl.fold (fun key location acc -> (key, location) :: acc) segment.table []

let collect t ~budget ~live =
  if size t > budget then begin
    let candidates = List.filter abandoned t.segments in
    let recent path =
      match Unix.stat path with
      | stat -> Unix.time () -. stat.st_mtime < week
      | exception Unix.Unix_error _ -> false
    in
    List.iter
      (fun segment ->
        let young = recent segment.path in
        List.iter
          (fun (key, location) ->
            match read_record (channel segment) ~offset:location.offset with
            | Some (kind, _, value) ->
                let keep =
                  match kind with 'v' -> live key | _ -> young || Hashtbl.mem t.used key
                in
                if
                  keep
                  && not
                       (match t.writer with
                       | Some w -> Hashtbl.mem w.segment.table key
                       | None -> false)
                then append_record t kind key value
            | None -> ())
          (entries segment))
      candidates;
    flush t;
    List.iter
      (fun segment ->
        close_channel segment;
        List.iter
          (fun path -> try Sys.remove path with Sys_error _ -> ())
          [ segment.path; index_path segment.path ])
      candidates;
    t.segments <- List.filter (fun s -> not (List.memq s candidates)) t.segments
  end
