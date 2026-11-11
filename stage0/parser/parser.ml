(* The parser's entry point. *)

open Token

type piece = Split.piece = { first : int; stop : int }

let split = Split.pieces
let is_use (tokens : Token.t array) piece = tokens.(piece.first).kind = Keyword Use
let begins_statement = Atoms.begins_statement
let spelled_words = List.map fst Cost_word.spellings

type relative_diagnostics = Diagnostic.t list
type 'value parsed = { value : 'value Syntax.item; diagnostics : relative_diagnostics }

let placed parsed = List.map (Diagnostic.move parsed.value.base) parsed.diagnostics

(* Parses a piece with a cursor of its own, whose collector holds only the
   piece's diagnostics. *)
let with_cursor source (tokens : Token.t array) piece parse =
  let diagnostics = Diagnostic.Collector.create () in
  let base = tokens.(piece.first).span.start in
  let text = String.sub (Source.text source) base (tokens.(piece.stop - 1).span.stop - base) in
  let cursor = Cursor.create ~text ~diagnostics ~base tokens ~first:piece.first ~stop:piece.stop in
  let value = parse cursor in
  (value, cursor, Diagnostic.Collector.to_list diagnostics)

let item (cursor : Cursor.t) value : _ Syntax.item =
  {
    base = cursor.base;
    text = cursor.text;
    blank_line_before = cursor.tokens.(cursor.first).blank_line_before;
    value;
    container = None;
  }

let parsed cursor value diagnostics =
  { value = item cursor value; diagnostics = List.map (Diagnostic.move (-cursor.base)) diagnostics }

(* Runs the checks that need a definition's whole tree. *)
let check cursor definition =
  Operators.definition cursor definition;
  Check.definition cursor definition

(* The definition that [parse] builds from a piece, or a
   [Definition_error] when its header does not parse. *)
let one_definition source tokens piece parse =
  let value, cursor, diagnostics =
    with_cursor source tokens piece (fun cursor ->
        let definition : Syntax.definition =
          match parse cursor with
          | definition ->
              check cursor definition;
              definition
          | exception Cursor.Failed ->
              let keyword, name = Parse_definition.header (Cursor.restarted cursor) in
              {
                visibility = Private;
                kind = Definition_error { keyword; name };
                span = Cursor.span_from cursor cursor.first;
                recovered = [];
                id = Cursor.fresh_id cursor;
              }
        in
        let recovered =
          List.sort_uniq compare (List.map (Cursor.span cursor) !(cursor.recoveries))
        in
        { definition with recovered })
  in
  (parsed cursor value diagnostics, List.rev !(cursor.methods))

(* A definition, and the methods declared inside it when it is a trait, an
   [impl], or a capability. Each method is a separate definition, with its
   own tokens, base, and node ids, so that an edit to one method changes no
   other definition's tree. *)
let methods source tokens (container : Syntax.definition) token_ranges =
  let kind : Parse_definition.container option =
    match container.kind with
    | Trait _ -> Some In_trait
    | Impl _ -> Some In_impl
    | Capability _ -> Some In_capability
    | _ -> None
  in
  match kind with
  | Some kind ->
      List.map
        (fun (first, stop) ->
          fst
            (one_definition source tokens { first; stop }
               (Parse_definition.method_ ~container:kind ~visibility:container.visibility)))
        token_ranges
  | None -> []

let definition source tokens piece =
  let parsed, token_ranges = one_definition source tokens piece Parse_definition.definition in
  (parsed, methods source tokens parsed.value.value token_ranges)

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
        let parsed, methods = definition source tokens piece in
        let destination =
          match (definitions, destination) with
          | [], None -> Some (Source.line_start source parsed.value.base)
          | _ -> destination
        in
        let container = Some (List.length definitions) in
        gather rest ~uses
          ~definitions:
            (List.rev_map (fun (method_ : _ parsed) -> { method_.value with container }) methods
            @ (parsed.value :: definitions))
          ~diagnostics:(List.rev_map placed methods @ (placed parsed :: diagnostics))
          ~destination
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
  let (example, container), cursor, diagnostics =
    with_cursor source tokens piece (fun cursor ->
        match Parse_definition.example cursor with
        | Whole definition ->
            check cursor definition;
            (Example_definition, Some definition)
        | Signature_alone (_, signature) ->
            Syntax_walk.signature (fun value -> Operators.expression cursor value) signature;
            Check.signature cursor signature;
            (Example_signature, None)
        | exception Cursor.Failed -> (Example_definition, None))
  in
  (* The methods declared inside a trait, an [impl], or a capability are
     separate definitions, so their diagnostics are not the container's. *)
  let method_diagnostics =
    match container with
    | Some container ->
        List.concat_map placed (methods source tokens container (List.rev !(cursor.methods)))
    | None -> []
  in
  (example, diagnostics @ method_diagnostics)

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
