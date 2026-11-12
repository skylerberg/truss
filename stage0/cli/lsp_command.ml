(* [truss lsp]: the language server, speaking the Language Server Protocol
   on standard input and output.

   The server holds the text of each file the editor has open. After each
   change it asks for the open files' diagnostics through [check], which
   runs where every other command runs, in the project's background
   process unless [--no-server] says otherwise, and checks a trial session
   with the open files' texts in place of the files on disk. Nothing is
   written to a file. *)

(* An LSP position counts columns in UTF-16 code units unless the client
   accepts UTF-8, which is the file's bytes. *)
type encoding = Utf_8 | Utf_16

let encoding_name = function Utf_8 -> "utf-8" | Utf_16 -> "utf-16"
let units = function Utf_8 -> Source.Bytes | Utf_16 -> Source.Utf_16_code_units
let position encoding source offset = Source.location (units encoding) source offset
let offset encoding source ~line ~column = Source.offset (units encoding) source ~line ~column

let range encoding source (span : Diagnostic.span) =
  let point offset =
    let line, character = position encoding source offset in
    Json.Object [ ("line", Json.Int line); ("character", Json.Int character) ]
  in
  Json.Object [ ("start", point span.start); ("end", point span.stop) ]

let hex_digit character =
  match character with
  | '0' .. '9' -> Some (Char.code character - Char.code '0')
  | 'a' .. 'f' -> Some (Char.code character - Char.code 'a' + 10)
  | 'A' .. 'F' -> Some (Char.code character - Char.code 'A' + 10)
  | _ -> None

(* The absolute path a [file:] URI names, with its escapes decoded. *)
let path_of_uri uri =
  let prefix = "file://" in
  if not (String.starts_with ~prefix uri) then None
  else
    let encoded =
      String.sub uri (String.length prefix) (String.length uri - String.length prefix)
    in
    let buffer = Buffer.create (String.length encoded) in
    let rec decode at =
      if at < String.length encoded then
        match encoded.[at] with
        | '%' when at + 2 < String.length encoded -> (
            match (hex_digit encoded.[at + 1], hex_digit encoded.[at + 2]) with
            | Some high, Some low ->
                Buffer.add_char buffer (Char.chr ((high * 16) + low));
                decode (at + 3)
            | _ ->
                Buffer.add_char buffer '%';
                decode (at + 1))
        | character ->
            Buffer.add_char buffer character;
            decode (at + 1)
    in
    decode 0;
    Some (Buffer.contents buffer)

(* A diagnostic as the protocol states it, with its notes as related
   information in the same file. *)
let lsp_diagnostic encoding ~uri source (diagnostic : Diagnostic.t) =
  Json.Object
    [
      ("range", range encoding source diagnostic.span);
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
                     Json.Object [ ("uri", Json.String uri); ("range", range encoding source span) ]
                   );
                   ("message", Json.String message);
                 ])
             diagnostic.notes) );
    ]

(* An obligation's state: where it is, its goal, whether it is
   proven, and whether its proof trusts compiled code. *)
let lsp_state encoding source (state : Diagnostic.span Prover.state) =
  Json.Object
    [
      ("range", range encoding source state.span);
      ("code", Json.String (Diagnostic.Code.name (Prover state.code)));
      ("shows", Json.String state.shows);
      ("proven", Json.Bool (state.failure = None));
      ("trustsCompiledCode", Json.Bool state.trusts_compiled_code);
    ]

(* The diagnostics of each open file, by its URI as the client writes it,
   and the states of its obligations, with each file's text in place of
   the file on disk: a JSON object with a field [files], each with its
   [uri], [diagnostics], and [states]. A file's proofs are checked once it
   has no other diagnostic, as [truss check] does. A file in no package of
   the project has neither. *)
let check ~root encoding (buffers : (string * string) list) =
  let buffers =
    List.filter_map
      (fun (uri, text) -> Option.map (fun path -> (uri, path, text)) (path_of_uri uri))
      buffers
  in
  let project = Project.load root in
  let base = Database.root project.session in
  let trial =
    Database.trial project.session
      (List.map (fun (_, path, text) -> (Project.relative ~from:base path, Some text)) buffers)
  in
  let packages =
    List.map
      (fun (relative, name) ->
        {
          Project.name;
          directory = (if relative = "" then base else Filename.concat base relative);
        })
      (Database.packages trial)
  in
  let project : Project.t =
    {
      session = trial;
      context = Database.context trial;
      packages;
      files = Project.module_files trial packages;
    }
  in
  let module_of path =
    List.find_map
      (fun (module_, file) -> if Project.normalize file = path then Some module_ else None)
      project.files
  in
  let checked =
    List.map
      (fun (uri, path, text) ->
        let module_ = module_of (Project.normalize path) in
        let module_diagnostics = Option.map (Database.diagnostics trial) module_ in
        (uri, Source.create ~path text, module_, module_diagnostics))
      buffers
  in
  let provable =
    List.filter_map
      (fun (_, _, module_, module_diagnostics) ->
        if module_diagnostics = Some [] then module_ else None)
      checked
  in
  let proofs = Proofs.checked project provable in
  Json.Object
    [
      ( "files",
        Json.List
          (List.map
             (fun (uri, source, module_, module_diagnostics) ->
               let diagnostics, states =
                 match (module_, module_diagnostics) with
                 | Some module_, Some [] -> proofs module_
                 | _, Some module_diagnostics -> (Diagnostic.shown module_diagnostics, [])
                 | _, None -> ([], [])
               in
               Json.Object
                 [
                   ("uri", Json.String uri);
                   ( "diagnostics",
                     Json.List (List.map (lsp_diagnostic encoding ~uri source) diagnostics) );
                   ("states", Json.List (List.map (lsp_state encoding source) states));
                 ])
             checked) );
    ]

(* One message's body from a stream of messages, each after a header that
   gives its length, or [None] at the stream's end. *)
let read_message input =
  let rec headers length =
    match In_channel.input_line input with
    | None -> None
    | Some line -> (
        let line = String.trim line in
        if line = "" then length
        else
          match String.index_opt line ':' with
          | Some colon when String.lowercase_ascii (String.sub line 0 colon) = "content-length" ->
              headers
                (int_of_string_opt
                   (String.trim (String.sub line (colon + 1) (String.length line - colon - 1))))
          | _ -> headers length)
  in
  match headers None with
  | None -> None
  | Some length -> really_input_string input length |> Option.some

let write_message output body =
  Out_channel.output_string output
    (Printf.sprintf "Content-Length: %d\r\n\r\n%s" (String.length body) body);
  Out_channel.flush output

type server = {
  write : Json.t -> unit;
  check : root:string -> encoding -> (string * string) list -> string option;
      (** The JSON text of [check], computed where commands run; [None] when it could not be. *)
  mutable root : string;
  mutable encoding : encoding;
  mutable buffers : (string * string) list;  (** Each open file's text, by its URI. *)
  mutable shut_down : bool;
  mutable published : string list;  (** The URIs given diagnostics, to clear once closed. *)
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

(* Checks the open files and publishes the results: each file's
   diagnostics, and its obligations' states as [truss/proofStates]. A
   closed file's diagnostics are cleared. *)
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
            match Json.field "files" answer with
            | Json.List files ->
                List.iter
                  (fun file ->
                    match Json.field "uri" file with
                    | Json.String uri ->
                        publish server uri (Json.field "diagnostics" file);
                        notify server "truss/proofStates"
                          (Json.Object
                             [ ("uri", Json.String uri); ("states", Json.field "states" file) ])
                    | _ -> ())
                  files
            | _ -> log server "The check gave no answer."))

let client_encoding params =
  match
    Json.field "positionEncodings" (Json.field "general" (Json.field "capabilities" params))
  with
  | Json.List encodings when List.mem (Json.String "utf-8") encodings -> Utf_8
  | _ -> Utf_16

let root_of params =
  match (Json.field "rootUri" params, Json.field "rootPath" params) with
  | Json.String uri, _ when path_of_uri uri <> None -> Option.get (path_of_uri uri)
  | _, Json.String path -> path
  | _ -> Sys.getcwd ()

let capabilities server =
  Json.Object
    [
      ( "capabilities",
        Json.Object
          [
            ("positionEncoding", Json.String (encoding_name server.encoding));
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

(* The text a change gives: the whole file, since the server asks for
   full changes, or, from a client that sends ranges anyway, the old text
   with each range replaced. *)
let changed encoding text changes =
  List.fold_left
    (fun text change ->
      match (Json.field "range" change, Json.field "text" change) with
      | Json.Null, Json.String whole -> whole
      | range, Json.String replacement ->
          let source = Source.create ~path:"" text in
          let point name =
            match
              ( Json.field "line" (Json.field name range),
                Json.field "character" (Json.field name range) )
            with
            | Json.Int line, Json.Int column -> offset encoding source ~line ~column
            | _ -> 0
          in
          let start = point "start" and stop = point "end" in
          String.sub text 0 start ^ replacement ^ String.sub text stop (String.length text - stop)
      | _ -> text)
    text changes

type step = Continue | Recheck | Stop of int

(* Handles one message. *)
let handle server message =
  let id = Json.field "id" message and params = Json.field "params" message in
  let document = Json.field "textDocument" params in
  let uri = match Json.field "uri" document with Json.String uri -> Some uri | _ -> None in
  match Json.field "method" message with
  | Json.String "initialize" ->
      server.root <- root_of params;
      server.encoding <- client_encoding params;
      respond server id (capabilities server);
      Continue
  | Json.String "shutdown" ->
      server.shut_down <- true;
      respond server id Json.Null;
      Continue
  | Json.String "exit" -> Stop (if server.shut_down then 0 else 1)
  | Json.String "textDocument/didOpen" -> (
      match (uri, Json.field "text" document) with
      | Some uri, Json.String text when path_of_uri uri <> None ->
          server.buffers <- (uri, text) :: List.remove_assoc uri server.buffers;
          Recheck
      | _ -> Continue)
  | Json.String "textDocument/didChange" -> (
      match (uri, Json.field "contentChanges" params) with
      | Some uri, Json.List changes when List.mem_assoc uri server.buffers ->
          let text = List.assoc uri server.buffers in
          server.buffers <-
            List.map
              (fun (open_uri, open_text) ->
                if open_uri = uri then (uri, changed server.encoding text changes)
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

(* Answers messages until the client says to exit, or the input ends.
   Checking waits until no message is waiting, so a burst of edits is
   checked once. *)
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
  let waiting () =
    match Unix.select [ Unix.descr_of_in_channel input ] [] [] 0.0 with
    | readable, _, _ -> readable <> []
    | exception Unix.Unix_error _ -> false
  in
  let rec loop pending =
    if pending && not (waiting ()) then begin
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

(* The hidden command [__check-buffers ROOT ENCODING URI TEXT ...], which
   the server runs where commands run: [check], printed. *)
let check_buffers = function
  | root :: encoding :: rest ->
      let rec pairs = function uri :: text :: rest -> (uri, text) :: pairs rest | _ -> [] in
      let encoding = if encoding = "utf-8" then Utf_8 else Utf_16 in
      Json.print (check ~root encoding (pairs rest));
      0
  | _ -> 2

let check_arguments ~root encoding buffers =
  "__check-buffers" :: root :: encoding_name encoding
  :: List.concat_map (fun (uri, text) -> [ uri; text ]) buffers
