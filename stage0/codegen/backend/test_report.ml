type outcome = Passed | Failed | Panicked | Incomplete | Timed_out | Crashed

let outcomes =
  [
    ("passed", Passed);
    ("failed", Failed);
    ("panicked", Panicked);
    ("incomplete", Incomplete);
    ("timed_out", Timed_out);
    ("crashed", Crashed);
  ]

let show_outcome outcome = fst (List.find (fun (_, shown) -> shown = outcome) outcomes)

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

type reader = {
  tests : int;
  pending : Buffer.t;
  mutable unread_from : int;
  mutable message : string option;
  mutable echo : string option;
  mutable output : string option;
  on_start : int -> unit;
  on_record : int -> record -> unit;
}

let make_reader ~tests ?(on_start = ignore) on_record =
  {
    tests;
    pending = Buffer.create 1024;
    unread_from = 0;
    message = None;
    echo = None;
    output = None;
    on_start;
    on_record;
  }

let read_test_number reader line text =
  match int_of_string_opt text with
  | Some number when number >= 0 && number < reader.tests -> number
  | Some number -> raise_malformed (Printf.sprintf "a test numbered %d" number)
  | None -> raise_malformed line

let find_line_end reader =
  let rec scan index =
    if index >= Buffer.length reader.pending then None
    else if Buffer.nth reader.pending index = '\n' then Some index
    else scan (index + 1)
  in
  scan reader.unread_from

let rec drain reader =
  match find_line_end reader with
  | None -> ()
  | Some stop -> (
      let line = Buffer.sub reader.pending reader.unread_from (stop - reader.unread_from) in
      let consume_through last = reader.unread_from <- last + 1 in
      match String.split_on_char ' ' line with
      | [ (("message" | "echo" | "output") as label); count ] ->
          let count =
            match int_of_string_opt count with
            | Some parsed_count -> parsed_count
            | None -> raise_malformed line
          in
          if Buffer.length reader.pending >= stop + 1 + count + 1 then begin
            let content = Buffer.sub reader.pending (stop + 1) count in
            (match label with
            | "message" -> reader.message <- Some content
            | "echo" -> reader.echo <- Some content
            | _ -> reader.output <- Some content);
            consume_through (stop + 1 + count);
            drain reader
          end
      | [ "start"; number ] ->
          let number = read_test_number reader line number in
          consume_through stop;
          reader.on_start number;
          drain reader
      | [ "test"; number; outcome; microseconds ] -> (
          let number = read_test_number reader line number in
          match (List.assoc_opt outcome outcomes, int_of_string_opt microseconds) with
          | Some outcome, Some microseconds ->
              let record =
                {
                  outcome;
                  message = reader.message;
                  echo = reader.echo;
                  output = reader.output;
                  microseconds;
                  cached = false;
                }
              in
              reader.message <- None;
              reader.echo <- None;
              reader.output <- None;
              consume_through stop;
              reader.on_record number record;
              drain reader
          | _ -> raise_malformed line)
      | _ -> raise_malformed line)

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
      if
        Buffer.length reader.pending > 0
        || reader.message <> None || reader.echo <> None || reader.output <> None
      then raise_malformed "it ends partway through a record"
    with
    | () -> Ok (List.map snd (List.sort (fun (left, _) (right, _) -> compare left right) !records))
    | exception Malformed message -> Error message
end
