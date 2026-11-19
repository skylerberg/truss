type outcome = Passed | Failed | Panicked | Incomplete | Timed_out | Crashed

let show_outcome = function
  | Passed -> "passed"
  | Failed -> "failed"
  | Panicked -> "panicked"
  | Incomplete -> "incomplete"
  | Timed_out -> "timed_out"
  | Crashed -> "crashed"

type record = {
  outcome : outcome;
  message : string option;
  echo : string option;
  output : string option;
  microseconds : int;
  cached : bool;
}

exception Malformed of string

let raise_malformed text = raise (Malformed ("A test report cannot be read: " ^ text))
let started_kind = 0
let ended_kind = 1
let record_head_width = 5

type reader = {
  tests : int;
  pending : Buffer.t;
  mutable unread_from : int;
  on_start : int -> unit;
  on_record : int -> record -> unit;
}

let make_reader ~tests ?(on_start = ignore) on_record =
  { tests; pending = Buffer.create 1024; unread_from = 0; on_start; on_record }

let get_unsigned_32 bytes position =
  Int32.to_int (String.get_int32_le bytes position) land 0xffff_ffff

let handle_record reader ~kind payload =
  let length = String.length payload in
  let position = ref 0 in
  let take count =
    if count > length - !position then raise_malformed "a record ends before its last field";
    let field = String.sub payload !position count in
    position := !position + count;
    field
  in
  let take_test_number () =
    match get_unsigned_32 (take 4) 0 with
    | number when number < reader.tests -> number
    | number -> raise_malformed (Printf.sprintf "a test numbered %d" number)
  in
  let take_outcome () =
    match Char.code (take 1).[0] with
    | 0 -> Passed
    | 1 -> Failed
    | 2 -> Panicked
    | 3 -> Incomplete
    | 5 -> Timed_out
    | 6 -> Crashed
    | code -> raise_malformed (Printf.sprintf "an outcome numbered %d" code)
  in
  let take_text () =
    match take (get_unsigned_32 (take 4) 0) with "" -> None | text -> Some text
  in
  let expect_end () =
    if !position <> length then raise_malformed "a record has bytes after its last field"
  in
  if kind = started_kind then begin
    let number = take_test_number () in
    expect_end ();
    reader.on_start number
  end
  else if kind = ended_kind then begin
    let number = take_test_number () in
    let outcome = take_outcome () in
    let microseconds = Int64.to_int (String.get_int64_le (take 8) 0) in
    let message = take_text () in
    let echo = take_text () in
    let output = take_text () in
    expect_end ();
    reader.on_record number { outcome; message; echo; output; microseconds; cached = false }
  end
  else raise_malformed (Printf.sprintf "a record of kind %d" kind)

let rec drain reader =
  let available = Buffer.length reader.pending - reader.unread_from in
  if available >= record_head_width then begin
    let head = Buffer.sub reader.pending reader.unread_from record_head_width in
    let length = get_unsigned_32 head 1 in
    if available - record_head_width >= length then begin
      let payload = Buffer.sub reader.pending (reader.unread_from + record_head_width) length in
      reader.unread_from <- reader.unread_from + record_head_width + length;
      handle_record reader ~kind:(Char.code head.[0]) payload;
      drain reader
    end
  end

let feed reader text =
  Buffer.add_string reader.pending text;
  drain reader;
  if reader.unread_from > 0 then begin
    let unread =
      Buffer.sub reader.pending reader.unread_from
        (Buffer.length reader.pending - reader.unread_from)
    in
    Buffer.clear reader.pending;
    Buffer.add_string reader.pending unread;
    reader.unread_from <- 0
  end

module For_testing = struct
  let parse ~tests text =
    let records = ref [] in
    let reader =
      make_reader ~tests (fun number record -> records := (number, record) :: !records)
    in
    match
      feed reader text;
      if Buffer.length reader.pending > 0 then raise_malformed "it ends partway through a record"
    with
    | () -> Ok (List.map snd (List.sort (fun (left, _) (right, _) -> compare left right) !records))
    | exception Malformed message -> Error message

  let list_records_by_piece ~tests pieces =
    let records = ref [] and pieces_fed = ref 0 in
    let reader =
      make_reader ~tests (fun _ record -> records := (!pieces_fed, record) :: !records)
    in
    List.iter
      (fun piece ->
        incr pieces_fed;
        feed reader piece)
      pieces;
    List.rev !records
end
