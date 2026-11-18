type encoding = Utf_8 | Utf_16

let show_encoding = function Utf_8 -> "utf-8" | Utf_16 -> "utf-16"
let classify_units = function Utf_8 -> Source.Bytes | Utf_16 -> Source.Utf_16_code_units

let locate_position encoding source offset =
  Source.compute_location (classify_units encoding) source offset

let locate_offset encoding source ~line ~column =
  Source.compute_offset (classify_units encoding) source ~line ~column

let encode_range encoding source (span : Source.span) =
  let encode_point offset =
    let line, character = locate_position encoding source offset in
    Json.Object [ ("line", Json.Int line); ("character", Json.Int character) ]
  in
  Json.Object [ ("start", encode_point span.start); ("end", encode_point span.stop) ]

let decode_file_uri uri =
  let prefix = "file://" in
  if not (String.starts_with ~prefix uri) then None
  else
    let encoded = String.drop_first (String.length prefix) uri in
    let buffer = Buffer.create (String.length encoded) in
    let rec decode at =
      if at < String.length encoded then
        match encoded.[at] with
        | '%'
          when at + 2 < String.length encoded
               && Char.Ascii.is_hex_digit encoded.[at + 1]
               && Char.Ascii.is_hex_digit encoded.[at + 2] ->
            let high = Char.Ascii.hex_digit_to_int encoded.[at + 1]
            and low = Char.Ascii.hex_digit_to_int encoded.[at + 2] in
            Buffer.add_char buffer (Char.chr ((high * 16) + low));
            decode (at + 3)
        | character ->
            Buffer.add_char buffer character;
            decode (at + 1)
    in
    decode 0;
    Some (Buffer.contents buffer)

let encode_diagnostic encoding ~uri source (diagnostic : Diagnostic.t) =
  Json.Object
    [
      ("range", encode_range encoding source diagnostic.span);
      ("severity", Json.Int 1);
      ("code", Json.String (Diagnostic.Code.name diagnostic.code));
      ("source", Json.String "truss");
      ("message", Json.String diagnostic.message);
      ( "relatedInformation",
        Json.List
          (List.map
             (fun (span, message) ->
               Json.Object
                 [
                   ( "location",
                     Json.Object
                       [ ("uri", Json.String uri); ("range", encode_range encoding source span) ] );
                   ("message", Json.String message);
                 ])
             diagnostic.notes) );
    ]

let encode_state encoding source (state : Source.span Prover.state) =
  Json.Object
    [
      ("range", encode_range encoding source state.span);
      ("code", Json.String (Diagnostic.Code.name (Prover state.code)));
      ("shows", Json.String state.shows);
      ("proven", Json.Bool (state.failure = None));
      ("trustsCompiledCode", Json.Bool state.trusts_compiled_code);
    ]

let check ~root encoding (buffers : (string * string) list) =
  let buffers =
    List.filter_map
      (fun (uri, text) -> Option.map (fun path -> (uri, path, text)) (decode_file_uri uri))
      buffers
  in
  let snapshot, _ = Command_packages.load root in
  let base = Workspace.locate_root snapshot in
  let trial =
    Workspace.make_trial snapshot
      (List.map
         (fun (_, path, text) -> (Shown_path.make_relative ~from:base path, Some text))
         buffers)
  in
  let packages = List.map snd (Workspace.list_packages trial) in
  let find_file path =
    List.find_opt
      (fun file -> Shown_path.normalize (Command_packages.locate_file trial file) = path)
      (Command_packages.list_files trial packages)
  in
  let opened =
    List.map
      (fun (uri, path, text) ->
        (uri, Source.create ~path text, find_file (Shown_path.normalize path)))
      buffers
  in
  let database = Workspace.open_database trial in
  let proofs =
    Proofs.check database trial packages (List.filter_map (fun (_, _, file) -> file) opened)
  in
  Json.Object
    [
      ( "files",
        Json.List
          (List.map
             (fun (uri, source, file) ->
               let diagnostics, states =
                 match file with
                 | Some file ->
                     ( Diagnostic.select_shown
                         (Database.list_file_diagnostics database file
                         @ Proofs.list_diagnostics proofs file),
                       Proofs.list_states proofs file )
                 | None -> ([], [])
               in
               Json.Object
                 [
                   ("uri", Json.String uri);
                   ( "diagnostics",
                     Json.List (List.map (encode_diagnostic encoding ~uri source) diagnostics) );
                   ("states", Json.List (List.map (encode_state encoding source) states));
                 ])
             opened) );
    ]

let read_message input =
  let rec read_headers length =
    match In_channel.input_line input with
    | None -> None
    | Some line -> (
        let line = String.trim line in
        if line = "" then length
        else
          match String.split_first ~sep:":" line with
          | Some (name, value) when String.lowercase_ascii name = "content-length" ->
              read_headers (int_of_string_opt (String.trim value))
          | _ -> read_headers length)
  in
  match read_headers None with
  | None -> None
  | Some length -> really_input_string input length |> Option.some

let write_message output body =
  Out_channel.output_string output
    (Printf.sprintf "Content-Length: %d\r\n\r\n%s" (String.length body) body);
  Out_channel.flush output

type server = {
  write : Json.t -> unit;
  check : root:string -> encoding -> (string * string) list -> string option;
  mutable root : string;
  mutable encoding : encoding;
  mutable buffers : (string * string) list;
  mutable shut_down : bool;
  mutable published : string list;
}

let notify server name params =
  server.write
    (Json.Object
       [ ("jsonrpc", Json.String "2.0"); ("method", Json.String name); ("params", params) ])

let respond server id result =
  server.write (Json.Object [ ("jsonrpc", Json.String "2.0"); ("id", id); ("result", result) ])

let respond_error server id code message =
  server.write
    (Json.Object
       [
         ("jsonrpc", Json.String "2.0");
         ("id", id);
         ("error", Json.Object [ ("code", Json.Int code); ("message", Json.String message) ]);
       ])

let log server message =
  notify server "window/logMessage"
    (Json.Object [ ("type", Json.Int 1); ("message", Json.String message) ])

let publish server uri diagnostics =
  notify server "textDocument/publishDiagnostics"
    (Json.Object [ ("uri", Json.String uri); ("diagnostics", diagnostics) ])

let refresh server =
  let open_uris = List.map fst server.buffers in
  List.iter
    (fun uri -> if not (List.mem uri open_uris) then publish server uri (Json.List []))
    server.published;
  server.published <- open_uris;
  if server.buffers <> [] then
    match server.check ~root:server.root server.encoding server.buffers with
    | None -> log server "The open files could not be checked."
    | Some text -> (
        match Json.parse text with
        | exception Json.Malformed -> log server "The check gave no answer."
        | answer -> (
            match Json.lookup_field "files" answer with
            | Json.List files ->
                List.iter
                  (fun file ->
                    match Json.lookup_field "uri" file with
                    | Json.String uri ->
                        publish server uri (Json.lookup_field "diagnostics" file);
                        notify server "truss/proofStates"
                          (Json.Object
                             [
                               ("uri", Json.String uri); ("states", Json.lookup_field "states" file);
                             ])
                    | _ -> ())
                  files
            | _ -> log server "The check gave no answer."))

let choose_client_encoding params =
  match
    Json.lookup_field "positionEncodings"
      (Json.lookup_field "general" (Json.lookup_field "capabilities" params))
  with
  | Json.List encodings when List.mem (Json.String "utf-8") encodings -> Utf_8
  | _ -> Utf_16

let extract_root params =
  match (Json.lookup_field "rootUri" params, Json.lookup_field "rootPath" params) with
  | Json.String uri, _ when decode_file_uri uri <> None -> Option.get (decode_file_uri uri)
  | _, Json.String path -> path
  | _ -> Sys.getcwd ()

let encode_capabilities server =
  Json.Object
    [
      ( "capabilities",
        Json.Object
          [
            ("positionEncoding", Json.String (show_encoding server.encoding));
            ( "textDocumentSync",
              Json.Object
                [
                  ("openClose", Json.Bool true);
                  ("change", Json.Int 1);
                  ("save", Json.Object [ ("includeText", Json.Bool false) ]);
                ] );
          ] );
      ("serverInfo", Json.Object [ ("name", Json.String "truss") ]);
    ]

let apply_changes encoding text changes =
  List.fold_left
    (fun text change ->
      match (Json.lookup_field "range" change, Json.lookup_field "text" change) with
      | Json.Null, Json.String whole -> whole
      | range, Json.String replacement ->
          let source = Source.create ~path:"" text in
          let read_point name =
            match
              ( Json.lookup_field "line" (Json.lookup_field name range),
                Json.lookup_field "character" (Json.lookup_field name range) )
            with
            | Json.Int line, Json.Int column -> locate_offset encoding source ~line ~column
            | _ -> 0
          in
          let start = read_point "start" and stop = read_point "end" in
          String.sub text 0 start ^ replacement ^ String.drop_first stop text
      | _ -> text)
    text changes

type step = Continue | Recheck | Stop of int

let handle server message =
  let id = Json.lookup_field "id" message and params = Json.lookup_field "params" message in
  let document = Json.lookup_field "textDocument" params in
  let uri = match Json.lookup_field "uri" document with Json.String uri -> Some uri | _ -> None in
  match Json.lookup_field "method" message with
  | Json.String "initialize" ->
      server.root <- extract_root params;
      server.encoding <- choose_client_encoding params;
      respond server id (encode_capabilities server);
      Continue
  | Json.String "shutdown" ->
      server.shut_down <- true;
      respond server id Json.Null;
      Continue
  | Json.String "exit" -> Stop (if server.shut_down then 0 else 1)
  | Json.String "textDocument/didOpen" -> (
      match (uri, Json.lookup_field "text" document) with
      | Some uri, Json.String text when decode_file_uri uri <> None ->
          server.buffers <- (uri, text) :: List.remove_assoc uri server.buffers;
          Recheck
      | _ -> Continue)
  | Json.String "textDocument/didChange" -> (
      match (uri, Json.lookup_field "contentChanges" params) with
      | Some uri, Json.List changes when List.mem_assoc uri server.buffers ->
          let text = List.assoc uri server.buffers in
          server.buffers <-
            List.map
              (fun (open_uri, open_text) ->
                if open_uri = uri then (uri, apply_changes server.encoding text changes)
                else (open_uri, open_text))
              server.buffers;
          Recheck
      | _ -> Continue)
  | Json.String "textDocument/didSave" -> Recheck
  | Json.String "textDocument/didClose" -> (
      match uri with
      | Some uri ->
          server.buffers <- List.remove_assoc uri server.buffers;
          Recheck
      | None -> Continue)
  | Json.String name when id <> Json.Null ->
      respond_error server id (-32601) (Printf.sprintf "`%s` is not supported." name);
      Continue
  | _ -> Continue

let create ~write ~check =
  {
    write;
    check;
    root = Sys.getcwd ();
    encoding = Utf_16;
    buffers = [];
    shut_down = false;
    published = [];
  }

let serve ~input ~output ~check =
  let server = create ~write:(fun value -> write_message output (Json.to_string value)) ~check in
  let is_waiting () =
    match Unix.select [ Unix.descr_of_in_channel input ] [] [] 0.0 with
    | readable, _, _ -> readable <> []
    | exception Unix.Unix_error _ -> false
  in
  let rec loop pending =
    if pending && not (is_waiting ()) then begin
      refresh server;
      loop false
    end
    else
      match read_message input with
      | None -> if server.shut_down then 0 else 1
      | Some body -> (
          match Json.parse body with
          | exception Json.Malformed ->
              respond_error server Json.Null (-32700) "The message is not JSON.";
              loop pending
          | message -> (
              match handle server message with
              | Continue -> loop pending
              | Recheck -> loop true
              | Stop status -> status))
  in
  loop false

module For_testing = struct
  let locate_position = locate_position
  let locate_offset = locate_offset

  type nonrec server = server

  let create = create
  let handle server message = ignore (handle server message)
  let refresh = refresh
end
