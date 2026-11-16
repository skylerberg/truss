let header = "TRUSS-SEGMENT-1\n"
let kind_width = 1
let key_width = 32
let length_width = 4
let offset_width = 8
let checksum_width = 8
let length_position = kind_width + key_width
let record_head_width = length_position + length_width
let entry_width = key_width + offset_width + length_width
let seal_size = 64 * 1024 * 1024

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
  let buffer = Bytes.create checksum_width in
  Bytes.set_int64_le buffer 0 (List.fold_left fnv 0xcbf29ce484222325L parts);
  Bytes.to_string buffer

type location = { offset : int; length : int }

type segment = {
  path : string;
  mutable index : string option;
  table : (string, location) Hashtbl.t;
  mutable scanned : int;
  mutable channel : in_channel option;
}

type writer = {
  segment : segment;
  descriptor : Unix.file_descr;
  mutable size : int;
  pending : Buffer.t;
}

type t = {
  root : string;
  mutable segments : segment list;
  mutable refreshed : float;
  mutable writer : writer option;
  used : (string, unit) Hashtbl.t;
}

let segments_directory cache = Filename.concat cache.root "segments"
let directory cache = cache.root

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

let read_record channel ~offset =
  try
    seek_in channel offset;
    let head = really_input_string channel record_head_width in
    let length = Int32.to_int (String.get_int32_le head length_position) in
    if length < 0 then None
    else
      let value = really_input_string channel length in
      let check = really_input_string channel checksum_width in
      if checksum [ head; value ] = check then
        Some (head.[0], String.sub head kind_width key_width, value)
      else None
  with End_of_file | Sys_error _ -> None

let record_size length = record_head_width + length + checksum_width

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

let entry_location index position =
  {
    offset = Int64.to_int (String.get_int64_le index (position + key_width));
    length = Int32.to_int (String.get_int32_le index (position + key_width + offset_width));
  }

let search index key =
  let rec halve low high =
    if low >= high then None
    else
      let middle = (low + high) / 2 in
      let position = middle * entry_width in
      let order = compare_key index position key in
      if order = 0 then Some (entry_location index position)
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

let refresh cache =
  let directory = segments_directory cache in
  let own = Option.map (fun writer -> writer.segment.path) cache.writer in
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
  let known = List.filter (fun segment -> Hashtbl.mem there segment.path) cache.segments in
  List.iter
    (fun segment -> if not (Hashtbl.mem there segment.path) then close_channel segment)
    cache.segments;
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
  cache.segments <- fresh @ known;
  cache.refreshed <- Unix.gettimeofday ()

let writer_name () =
  Random.self_init ();
  Printf.sprintf "%d-%d-%06x" (Unix.getpid ()) (int_of_float (Unix.time ())) (Random.bits ())

let new_writer cache =
  File_system.make_directory (segments_directory cache);
  let path = Filename.concat (segments_directory cache) (writer_name () ^ ".segment") in
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

let pending_limit = 1024 * 1024

let drain writer =
  if Buffer.length writer.pending > 0 then begin
    File_system.write_all writer.descriptor (Buffer.contents writer.pending);
    Buffer.clear writer.pending
  end

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

let seal cache =
  match cache.writer with
  | None -> ()
  | Some writer ->
      drain writer;
      (try Unix.fsync writer.descriptor with Unix.Unix_error _ -> ());
      write_index writer.segment;
      Unix.close writer.descriptor;
      cache.writer <- None;
      cache.segments <- writer.segment :: cache.segments;
      writing := List.filter (fun other -> other != cache) !writing

let () =
  at_exit (fun () ->
      List.iter (fun cache -> try seal cache with Sys_error _ | Unix.Unix_error _ -> ()) !writing)

let writer cache =
  match cache.writer with
  | Some writer when writer.size < seal_size -> writer
  | full_writer ->
      if Option.is_some full_writer then seal cache;
      let writer = new_writer cache in
      cache.writer <- Some writer;
      writing := cache :: !writing;
      writer

let append_record cache kind key value =
  let writer = writer cache in
  let head = Bytes.create record_head_width in
  Bytes.set head 0 kind;
  Bytes.blit_string key 0 head kind_width key_width;
  Bytes.set_int32_le head length_position (Int32.of_int (String.length value));
  let head = Bytes.unsafe_to_string head in
  Hashtbl.replace writer.segment.table key { offset = writer.size; length = String.length value };
  Buffer.add_string writer.pending head;
  Buffer.add_string writer.pending value;
  Buffer.add_string writer.pending (checksum [ head; value ]);
  writer.size <- writer.size + record_size (String.length value);
  if Buffer.length writer.pending >= pending_limit then drain writer

let open_ root =
  File_system.make_directory root;
  let cache = { root; segments = []; refreshed = 0.; writer = None; used = Hashtbl.create 64 } in
  refresh cache;
  cache

let close cache =
  seal cache;
  List.iter close_channel cache.segments

let flush cache =
  Option.iter
    (fun writer ->
      drain writer;
      Unix.fsync writer.descriptor)
    cache.writer

let read_from segment key location =
  match read_record (channel segment) ~offset:location.offset with
  | Some (_, record_key, value) when record_key = key -> Some value
  | Some _ | None -> None
  | exception Sys_error _ -> None

let read_own writer key location =
  let written = writer.size - Buffer.length writer.pending in
  if location.offset >= written then
    Some (Buffer.sub writer.pending (location.offset - written + record_head_width) location.length)
  else read_from writer.segment key location

let lookup_once cache key =
  let own =
    Option.bind cache.writer (fun writer ->
        Option.bind (Hashtbl.find_opt writer.segment.table key) (read_own writer key))
  in
  match own with
  | Some value -> Some value
  | None ->
      List.find_map
        (fun segment -> Option.bind (find_in segment key) (read_from segment key))
        cache.segments

let refresh_interval = 0.02

let lookup cache key =
  match lookup_once cache key with
  | Some value -> Some value
  | None ->
      if Unix.gettimeofday () -. cache.refreshed > refresh_interval then begin
        refresh cache;
        lookup_once cache key
      end
      else None

let present cache key =
  (match cache.writer with Some writer -> Hashtbl.mem writer.segment.table key | None -> false)
  || List.exists (fun segment -> find_in segment key <> None) cache.segments

let derive_result_key = Blake3.derive_key ~context:"truss 2026-11-12 store result"

type result_kind = Package_database | Test_result | Solver_answer

let result_tag = function
  | Package_database -> "package"
  | Test_result -> "tests"
  | Solver_answer -> "solver"

let result_key ~kind ~key =
  derive_result_key (Cbor.encode (Cbor.Array [ Cbor.Text (result_tag kind); Cbor.Bytes key ]))

let find_result cache ~kind ~key =
  let name = result_key ~kind ~key in
  match lookup cache name with
  | Some value ->
      Hashtbl.replace cache.used name ();
      Some value
  | None -> None

let add_result cache ~kind ~key value =
  let name = result_key ~kind ~key in
  Hashtbl.replace cache.used name ();
  if not (present cache name) then append_record cache 'r' name value

let files cache name =
  let path = Filename.concat cache.root name in
  File_system.make_directory path;
  path

let caches_directory cache = Filename.concat cache.root "caches"

let cache_files cache name =
  let path = Filename.concat (caches_directory cache) name in
  File_system.make_directory path;
  path

let files_in_caches cache =
  let rec walk directory files =
    match Sys.readdir directory with
    | exception Sys_error _ -> files
    | names ->
        Array.fold_left
          (fun files name ->
            let path = Filename.concat directory name in
            match Unix.lstat path with
            | { st_kind = S_DIR; _ } -> walk path files
            | { st_kind = S_REG; st_size; st_mtime; _ } -> (path, st_size, st_mtime) :: files
            | _ -> files
            | exception Unix.Unix_error _ -> files)
          files names
  in
  walk (caches_directory cache) []

let file_size path = try (Unix.stat path).st_size with Unix.Unix_error _ -> 0

let size cache =
  refresh cache;
  List.fold_left (fun total segment -> total + file_size segment.path) 0 cache.segments
  + List.fold_left (fun total (_, size, _) -> total + size) 0 (files_in_caches cache)
  + match cache.writer with Some writer -> writer.size | None -> 0

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

let entries segment =
  match segment.index with
  | Some index ->
      List.init
        (String.length index / entry_width)
        (fun entry ->
          let position = entry * entry_width in
          (String.sub index position key_width, entry_location index position))
  | None -> Hashtbl.fold (fun key location acc -> (key, location) :: acc) segment.table []

let rewrite cache candidates ~keep =
  List.iter
    (fun segment ->
      List.iter
        (fun (key, location) ->
          match read_record (channel segment) ~offset:location.offset with
          | Some (kind, record_key, value) when record_key = key ->
              if
                keep key
                && not
                     (match cache.writer with
                     | Some writer -> Hashtbl.mem writer.segment.table key
                     | None -> false)
              then append_record cache kind key value
          | Some _ | None | (exception Sys_error _) -> ())
        (entries segment))
    candidates;
  flush cache;
  List.iter
    (fun segment ->
      close_channel segment;
      List.iter
        (fun path -> try Sys.remove path with Sys_error _ -> ())
        [ segment.path; index_path segment.path ])
    candidates;
  cache.segments <- List.filter (fun segment -> not (List.memq segment candidates)) cache.segments

let modified path =
  match Unix.stat path with stat -> stat.st_mtime | exception Unix.Unix_error _ -> 0.

type evictable = Segment of segment | Cache_file of string

let collect cache ~budget =
  let excess = size cache - budget in
  if excess > 0 then begin
    let entries =
      List.map
        (fun segment -> (modified segment.path, file_size segment.path, Segment segment))
        (List.filter abandoned cache.segments)
      @ List.map
          (fun (path, size, modified) -> (modified, size, Cache_file path))
          (files_in_caches cache)
    in
    let rec least_recent freed = function
      | (_, size, entry) :: rest when freed < excess -> entry :: least_recent (freed + size) rest
      | _ -> []
    in
    let evicted =
      least_recent 0
        (List.sort (fun (left, _, _) (right, _, _) -> Float.compare left right) entries)
    in
    rewrite cache
      (List.filter_map (function Segment segment -> Some segment | Cache_file _ -> None) evicted)
      ~keep:(Hashtbl.mem cache.used);
    List.iter
      (function
        | Cache_file path -> ( try Sys.remove path with Sys_error _ -> ()) | Segment _ -> ())
      evicted
  end

let small = 8 * 1024 * 1024
let many = 32

let compact cache =
  refresh cache;
  let candidates =
    List.filter (fun segment -> file_size segment.path < small && abandoned segment) cache.segments
  in
  if List.length candidates >= many then rewrite cache candidates ~keep:(fun _ -> true)
