type segment = { number : int; size : int; digest : string }

type t = {
  directory : string;
  lock : Unix.file_descr;
  mutable header : string list option;
  mutable segments : segment list;
}

let list_magic = "truss database"
let segment_magic = "truss segment\n"
let make_list_path t = Filename.concat t.directory "list"
let make_next_list_path t = Filename.concat t.directory "list.new"
let make_segments_directory t = Filename.concat t.directory "segments"

let make_segment_path t number =
  Filename.concat (make_segments_directory t) (Printf.sprintf "%08d.segment" number)

let digest text = Digest.BLAKE128.to_hex (Digest.BLAKE128.string text)

let write_durably path text =
  let descriptor = Unix.openfile path [ O_WRONLY; O_CREAT; O_TRUNC; O_CLOEXEC ] 0o644 in
  Fun.protect
    ~finally:(fun () -> Unix.close descriptor)
    (fun () ->
      File_system.write_all descriptor text;
      Unix.fsync descriptor)

let header_prefix = "header "

let parse_list text =
  let parse_line parsed line =
    Option.bind parsed (fun (header, segments) ->
        if String.starts_with ~prefix:header_prefix line then
          let length = String.length header_prefix in
          Some (String.drop_first length line :: header, segments)
        else
          match String.split_on_char ' ' line with
          | [ "segment"; number; size; digest ] -> (
              match (int_of_string_opt number, int_of_string_opt size) with
              | Some number, Some size -> Some (header, { number; size; digest } :: segments)
              | None, _ | _, None -> None)
          | [ "" ] -> Some (header, segments)
          | _ -> None)
  in
  match String.split_on_char '\n' text with
  | magic :: lines when magic = list_magic ->
      Option.map
        (fun (header, segments) -> (List.rev header, List.rev segments))
        (List.fold_left parse_line (Some ([], [])) lines)
  | _ -> None

let open_ directory =
  File_system.make_directory directory;
  let ignored = Filename.concat directory ".gitignore" in
  if not (Sys.file_exists ignored) then File_system.write ignored "*\n";
  let lock =
    Unix.openfile (Filename.concat directory "lock") [ O_RDWR; O_CREAT; O_CLOEXEC ] 0o644
  in
  match Unix.lockf lock F_TLOCK 0 with
  | exception Unix.Unix_error ((EAGAIN | EACCES), _, _) ->
      Unix.close lock;
      Error `Open_elsewhere
  | () ->
      let t = { directory; lock; header = None; segments = [] } in
      (match parse_list (File_system.read (make_list_path t)) with
      | Some (header, segments) ->
          t.header <- Some header;
          t.segments <- segments
      | None -> ()
      | exception Sys_error _ -> ());
      Ok t

let header t = t.header

exception Damaged

let parse_records text =
  let length = String.length text in
  let read_length_at position =
    if position + 4 > length then raise Damaged
    else Int32.to_int (String.get_int32_le text position)
  in
  let read_bytes_at position size =
    if size < 0 || position + size > length then raise Damaged else String.sub text position size
  in
  let rec read position records =
    if position = length then List.rev records
    else
      let key_length = read_length_at position in
      let key = read_bytes_at (position + 4) key_length in
      let kind = read_bytes_at (position + 4 + key_length) 1 in
      let value_length = read_length_at (position + 5 + key_length) in
      let value = read_bytes_at (position + 9 + key_length) value_length in
      let next = position + 9 + key_length + value_length in
      match kind with
      | "v" -> read next ((key, Some value) :: records)
      | "r" -> read next ((key, None) :: records)
      | _ -> raise Damaged
  in
  if String.starts_with ~prefix:segment_magic text then read (String.length segment_magic) []
  else raise Damaged

let read_segment t segment =
  match File_system.read (make_segment_path t segment.number) with
  | text when String.length text = segment.size && digest text = segment.digest ->
      parse_records text
  | _ -> raise Damaged
  | exception Sys_error _ -> raise Damaged

let list_live t =
  let table = Hashtbl.create 4096 in
  List.iter
    (fun segment ->
      List.iter
        (fun (key, value) ->
          match value with
          | Some value -> Hashtbl.replace table key value
          | None -> Hashtbl.remove table key)
        (read_segment t segment))
    t.segments;
  Hashtbl.fold (fun key value entries -> (key, value) :: entries) table []

let read_entries t = match list_live t with entries -> Some entries | exception Damaged -> None

let list_segment_numbers t =
  match Sys.readdir (make_segments_directory t) with
  | names ->
      List.filter_map
        (fun name ->
          if Filename.check_suffix name ".segment" then
            int_of_string_opt (Filename.chop_suffix name ".segment")
          else None)
        (Array.to_list names)
  | exception Sys_error _ -> []

let write_segment t entries =
  let buffer = Buffer.create 65536 in
  Buffer.add_string buffer segment_magic;
  List.iter
    (fun (key, value) ->
      Buffer.add_int32_le buffer (Int32.of_int (String.length key));
      Buffer.add_string buffer key;
      match value with
      | Some value ->
          Buffer.add_char buffer 'v';
          Buffer.add_int32_le buffer (Int32.of_int (String.length value));
          Buffer.add_string buffer value
      | None ->
          Buffer.add_char buffer 'r';
          Buffer.add_int32_le buffer 0l)
    entries;
  let text = Buffer.contents buffer in
  let number =
    1
    + List.fold_left max 0
        (list_segment_numbers t @ List.map (fun segment -> segment.number) t.segments)
  in
  File_system.make_directory (make_segments_directory t);
  write_durably (make_segment_path t number) text;
  { number; size = String.length text; digest = digest text }

let make_list_text ~header segments =
  String.concat "\n"
    ((list_magic :: List.map (fun line -> header_prefix ^ line) header)
    @ List.map
        (fun segment ->
          Printf.sprintf "segment %d %d %s" segment.number segment.size segment.digest)
        segments)
  ^ "\n"

let prepare_commit t ~header entries =
  let segments = if entries = [] then t.segments else t.segments @ [ write_segment t entries ] in
  write_durably (make_next_list_path t) (make_list_text ~header segments);
  segments

let remove_unlisted t =
  List.iter
    (fun number ->
      if not (List.exists (fun segment -> segment.number = number) t.segments) then
        try Sys.remove (make_segment_path t number) with Sys_error _ -> ())
    (list_segment_numbers t)

let rename_list t ~header segments =
  Unix.rename (make_next_list_path t) (make_list_path t);
  t.header <- Some header;
  t.segments <- segments;
  remove_unlisted t

let is_compaction_due t =
  match t.segments with
  | first :: rest ->
      List.length t.segments > 32
      || List.fold_left (fun total segment -> total + segment.size) 0 rest > first.size
  | [] -> false

let compact t ~header =
  match list_live t with
  | entries ->
      let compacted = write_segment t (List.map (fun (key, value) -> (key, Some value)) entries) in
      write_durably (make_next_list_path t) (make_list_text ~header [ compacted ]);
      rename_list t ~header [ compacted ]
  | exception Damaged -> ()

let commit t ~header entries =
  if entries <> [] || t.header <> Some header then begin
    rename_list t ~header (prepare_commit t ~header entries);
    if is_compaction_due t then compact t ~header
  end

let discard t =
  t.header <- None;
  t.segments <- []

let close t = Unix.close t.lock

module For_testing = struct
  let interrupt_commit t ~header entries = ignore (prepare_commit t ~header entries)
end
