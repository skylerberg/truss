(* The parser's entry point. See PARSER.md. *)

open Token

type piece = Split.item = { first : int; stop : int }

let split = Split.items
let is_use (tokens : Token.t array) piece = tokens.(piece.first).kind = Keyword Use
let spelled_words = List.map fst Cost_word.spellings

type relative_diagnostics = Diagnostic.t list
type 'value parsed = { value : 'value Syntax.item; diagnostics : relative_diagnostics }

let placed parsed = List.map (Diagnostic.move parsed.value.base) parsed.diagnostics

(* Parses a piece with a cursor of its own, which collects the piece's
   diagnostics apart from the rest of the file's. *)
let with_cursor source (tokens : Token.t array) piece parse =
  let diagnostics = Diagnostic.Collector.create () in
  let base = tokens.(piece.first).span.start in
  let cursor =
    Cursor.create ~source ~diagnostics ~base tokens ~first:piece.first ~stop:piece.stop
  in
  let value = parse cursor in
  (value, cursor, Diagnostic.Collector.to_list diagnostics)

let item (cursor : Cursor.t) value : _ Syntax.item =
  let last = cursor.tokens.(cursor.stop - 1) in
  {
    base = cursor.base;
    text = Cursor.text cursor (Source.span cursor.base last.span.stop);
    blank_line_before = cursor.tokens.(cursor.first).blank_line_before;
    value;
  }

let parsed cursor value diagnostics =
  { value = item cursor value; diagnostics = List.map (Diagnostic.move (-cursor.base)) diagnostics }

(* Runs the checks that need a definition's whole tree. *)
let check cursor definition =
  Operators.definition cursor definition;
  Check.definition cursor definition

let definition source tokens piece =
  let value, cursor, diagnostics =
    with_cursor source tokens piece (fun cursor ->
        match Parse_definition.definition cursor with
        | definition ->
            check cursor definition;
            definition
        | exception Cursor.Failed ->
            let keyword, name = Parse_definition.header (Cursor.reread cursor) in
            {
              visibility = Private;
              kind = Definition_error { keyword; name };
              span = Cursor.span_from cursor cursor.first;
            })
  in
  parsed cursor value diagnostics

(* [use standard::file_system]. *)
let use_path cursor : Syntax.path option =
  match
    Cursor.expect_keyword cursor Use;
    let rec loop names =
      let names = Atoms.lower cursor "a module name" :: names in
      if Cursor.accept_punctuation cursor Colon_colon then loop names else names
    in
    let names = loop [] in
    if not (Cursor.at_end cursor) then Cursor.fail cursor "a line break after the module path";
    names
  with
  | last :: modules -> Some { modules = List.rev modules; last }
  | [] -> None
  | exception Cursor.Failed -> None

let use_line source tokens piece =
  let value, cursor, diagnostics = with_cursor source tokens piece use_path in
  parsed cursor value diagnostics

(* A [use] line after a definition moves up, to [destination]: after the
   other [use] lines, or above the first definition. *)
let use_after_definition source (line : _ Syntax.item) ~destination =
  let text = Source.text source in
  let stop_offset = line.base + String.length line.text in
  let start = Source.line_start source line.base in
  let line_end = Source.line_end source stop_offset in
  let stop = if line_end < String.length text then line_end + 1 else line_end in
  Diagnostic.make ~code:(Parser Use_after_definition)
    (Source.span line.base stop_offset)
    "`use` lines come before every definition in a file."
    ~fixes:
      [
        Diagnostic.fix "Move it up to the other `use` lines"
          [
            Diagnostic.insert destination (line.text ^ "\n");
            Diagnostic.delete (Source.span start stop);
          ];
      ]

let parse source tokens =
  let text = Source.text source in
  (* Where a [use] line found after a definition moves to: the start of the
     line after the last [use] line before any definition, or else the
     start of the first definition's line. *)
  let rec gather pieces ~uses ~definitions ~diagnostics ~destination =
    match pieces with
    | [] -> (List.rev uses, List.rev definitions, List.concat (List.rev diagnostics))
    | piece :: rest when is_use tokens piece ->
        let line = use_line source tokens piece in
        let line_diagnostics = placed line in
        let moved, destination =
          match (definitions, destination) with
          | [], _ ->
              let line_end =
                Source.line_end source (line.value.base + String.length line.value.text)
              in
              ([], Some (min (line_end + 1) (String.length text)))
          | _ :: _, Some destination ->
              ([ use_after_definition source line.value ~destination ], Some destination)
          | _ :: _, None -> ([], None)
        in
        let uses =
          match line.value.value with
          | Some path -> { line.value with value = path } :: uses
          | None -> uses
        in
        gather rest ~uses ~definitions
          ~diagnostics:((line_diagnostics @ moved) :: diagnostics)
          ~destination
    | piece :: rest ->
        let parsed = definition source tokens piece in
        let destination =
          match (definitions, destination) with
          | [], None -> Some (Source.line_start source parsed.value.base)
          | _ -> destination
        in
        gather rest ~uses ~definitions:(parsed.value :: definitions)
          ~diagnostics:(placed parsed :: diagnostics) ~destination
  in
  let uses, definitions, diagnostics =
    gather (split tokens) ~uses:[] ~definitions:[] ~diagnostics:[] ~destination:None
  in
  ( { Syntax.uses; definitions },
    List.stable_sort
      (fun (a : Diagnostic.t) (b : Diagnostic.t) -> compare a.span.start b.span.start)
      diagnostics )

(* The documents' examples *)

type example = Example_definition | Example_signature

let example_definition source tokens piece =
  let example, _, diagnostics =
    with_cursor source tokens piece (fun cursor ->
        match Parse_definition.example cursor with
        | Whole definition ->
            check cursor definition;
            Example_definition
        | Signature_alone (_, signature) ->
            Syntax_walk.signature (fun value -> Operators.expression cursor value) signature;
            Check.signature cursor signature;
            Example_signature
        | exception Cursor.Failed -> Example_definition)
  in
  (example, diagnostics)

let example_statement source tokens piece =
  let (), _, diagnostics =
    with_cursor source tokens piece (fun cursor ->
        match
          let statement = Parse_expression.statement_line cursor ~previous:None in
          if not (Cursor.at_end cursor) then Cursor.fail cursor "a line break after the statement";
          statement
        with
        | statement ->
            Syntax_walk.statement (fun value -> Operators.expression cursor value) statement
        | exception Cursor.Failed -> ())
  in
  diagnostics
