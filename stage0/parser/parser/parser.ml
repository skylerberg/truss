(* The parser's entry point. *)

open Token

type piece = Split.piece = { first : int; stop : int }

let split = Split.pieces
let is_use (tokens : Token.t array) piece = tokens.(piece.first).kind = Keyword Use
let begins_statement = Atoms.begins_statement
let spelled_words = List.map fst Cost_word.spellings @ [ "by"; "bit_vector" ]

type 'value parsed = { value : 'value Syntax.item; diagnostics : Syntax.diagnostic list }

let diagnostics_in_file parsed =
  List.map (Diagnostic.map_spans (Syntax.Span.to_source ~base:parsed.value.base)) parsed.diagnostics

let piece_text source (tokens : Token.t array) piece =
  let base = tokens.(piece.first).span.start in
  String.sub (Source.text source) base (tokens.(piece.stop - 1).span.stop - base)

(* Parses a piece with a cursor of its own, whose collector holds only the
   piece's diagnostics. *)
let with_cursor source (tokens : Token.t array) piece parse =
  let diagnostics = Diagnostic.Collector.create () in
  let base = tokens.(piece.first).span.start in
  let text = piece_text source tokens piece in
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
  {
    value = item cursor value;
    diagnostics =
      List.map (Diagnostic.map_spans (Syntax.Span.of_source ~base:cursor.base)) diagnostics;
  }

(* Removes each parser fix that, applied and parsed again by [unchecked],
   adds an error. *)
let checked_fixes ~unchecked source (tokens : Token.t array) piece (diagnostics : Diagnostic.t list)
    =
  let has_parser_fix (diagnostic : Diagnostic.t) =
    match diagnostic.code with Parser _ -> diagnostic.fixes <> [] | _ -> false
  in
  if not (List.exists has_parser_fix diagnostics) then diagnostics
  else
    let base = tokens.(piece.first).span.start and text = piece_text source tokens piece in
    let diagnostics_of text =
      let source = Source.create ~path:(Source.path source) text in
      let tokens, lexer_diagnostics = Lexer.lex source in
      match Split.pieces tokens with
      | [ piece ] -> Some (lexer_diagnostics @ unchecked source tokens piece)
      | _ -> None
    in
    match diagnostics_of text with
    | None -> diagnostics
    | Some before ->
        let works (diagnostic : Diagnostic.t) (fix : Diagnostic.span Diagnostic.fix) =
          let in_piece (edit : Diagnostic.span Diagnostic.edit) =
            base <= edit.span.start && edit.span.stop <= base + String.length text
          in
          if not (List.for_all in_piece fix.edits) then true
          else
            let edits =
              List.map
                (fun (edit : Diagnostic.span Diagnostic.edit) ->
                  Diagnostic.replace
                    (Source.span (edit.span.start - base) (edit.span.stop - base))
                    edit.replacement)
                fix.edits
            in
            match Diagnostic.apply_edits text edits with
            | exception Invalid_argument _ -> false
            | fixed -> (
                match diagnostics_of fixed with
                | None -> false
                | Some after ->
                    let rec remove_one = function
                      | [] -> []
                      | (first : Diagnostic.t) :: rest ->
                          if first.code = diagnostic.code then rest else first :: remove_one rest
                    in
                    Diagnostic.adds_none ~before:(remove_one before) ~after)
        in
        List.map
          (fun (diagnostic : Diagnostic.t) ->
            if has_parser_fix diagnostic then
              { diagnostic with fixes = List.filter (works diagnostic) diagnostic.fixes }
            else diagnostic)
          diagnostics

(* Runs the checks that need a definition's whole tree. *)
let check cursor definition =
  Operators.definition cursor definition;
  Check.definition cursor definition

(* The definition that [parse] builds from a piece, or a
   [Definition_error] when its header does not parse. *)
let rec one_definition ?(checks_fixes = true) source tokens piece parse =
  let value, cursor, diagnostics =
    with_cursor source tokens piece (fun cursor ->
        let definition : Syntax.definition =
          match parse cursor with
          | definition ->
              check cursor definition;
              definition
          | exception Cursor.Failed ->
              let intended, name = Parse_definition.header (Cursor.restarted cursor) in
              {
                visibility = Private;
                kind = Definition_error { intended; name };
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
  let diagnostics =
    if checks_fixes then
      checked_fixes source tokens piece diagnostics ~unchecked:(fun source tokens piece ->
          diagnostics_in_file (fst (one_definition ~checks_fixes:false source tokens piece parse)))
    else diagnostics
  in
  (parsed cursor value diagnostics, List.rev !(cursor.methods))

(* A definition, and the methods declared inside it when it is a trait, an
   [impl], or a capability. Each method is a separate definition, with its
   own tokens, base, and node ids, so that an edit to one method changes no
   other definition's tree. *)
let methods ?(checks_fixes = true) source tokens (container : Syntax.definition) token_ranges =
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
            (one_definition ~checks_fixes source tokens { first; stop }
               (Parse_definition.method_ ~container:kind ~visibility:container.visibility)))
        token_ranges
  | None -> []

let parse_definition ~checks_fixes source tokens piece =
  let parsed, token_ranges =
    one_definition ~checks_fixes source tokens piece Parse_definition.definition
  in
  (parsed, methods ~checks_fixes source tokens parsed.value.value token_ranges)

let definition source tokens piece = parse_definition ~checks_fixes:true source tokens piece

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
            Diagnostic.insert (Source.zero_width destination) (line.text ^ "\n");
            Diagnostic.delete (Source.span start stop);
          ];
      ]

let rec parse_file ~checks_fixes source tokens =
  let text = Source.text source in
  (* Where a [use] line found after a definition moves to: the start of the
     line after the last [use] line before any definition, or else the
     start of the first definition's line. *)
  let rec gather pieces ~uses ~definitions ~diagnostics ~destination =
    match pieces with
    | [] -> (List.rev uses, List.rev definitions, List.concat (List.rev diagnostics))
    | piece :: rest when is_use tokens piece ->
        let line = use_line source tokens piece in
        let line_diagnostics = diagnostics_in_file line in
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
        let parsed, methods = parse_definition ~checks_fixes source tokens piece in
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
          ~diagnostics:
            (List.rev_map diagnostics_in_file methods @ (diagnostics_in_file parsed :: diagnostics))
          ~destination
  in
  let uses, definitions, diagnostics =
    gather (split tokens) ~uses:[] ~definitions:[] ~diagnostics:[] ~destination:None
  in
  (* A [use] line's move, made over the whole file, keeps its fix only if the
     moved file, lexed and parsed again, adds no error. *)
  let diagnostics =
    if not checks_fixes then diagnostics
    else
      let lexer_diagnostics = lazy (snd (Lexer.lex source)) in
      List.map
        (fun (diagnostic : Diagnostic.t) ->
          match diagnostic.code with
          | Parser Use_after_definition ->
              let works fix =
                let moved =
                  Source.create ~path:(Source.path source) (Diagnostic.apply_fix text fix)
                in
                let moved_tokens, moved_lexer = Lexer.lex moved in
                let _, moved_parser = parse_file ~checks_fixes:false moved moved_tokens in
                Diagnostic.adds_none
                  ~before:
                    (Lazy.force lexer_diagnostics
                    @ List.filter (fun other -> other != diagnostic) diagnostics)
                  ~after:(moved_lexer @ moved_parser)
              in
              { diagnostic with fixes = List.filter works diagnostic.fixes }
          | _ -> diagnostic)
        diagnostics
  in
  ( { Syntax.uses; definitions },
    List.stable_sort
      (fun (left : Diagnostic.t) (right : Diagnostic.t) -> compare left.span.start right.span.start)
      diagnostics )

let parse source tokens = parse_file ~checks_fixes:true source tokens

type example = Example_definition | Example_signature

let rec parse_example_definition ~checks_fixes source tokens piece =
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
        List.concat_map diagnostics_in_file
          (methods ~checks_fixes source tokens container (List.rev !(cursor.methods)))
    | None -> []
  in
  let diagnostics =
    if checks_fixes then
      checked_fixes source tokens piece diagnostics ~unchecked:(fun source tokens piece ->
          snd (parse_example_definition ~checks_fixes:false source tokens piece))
    else diagnostics
  in
  (example, diagnostics @ method_diagnostics)

let rec parse_example_statement ~checks_fixes source tokens piece =
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
  if checks_fixes then
    checked_fixes source tokens piece diagnostics ~unchecked:(fun source tokens piece ->
        parse_example_statement ~checks_fixes:false source tokens piece)
  else diagnostics

let example_definition source tokens piece =
  parse_example_definition ~checks_fixes:true source tokens piece

let example_statement source tokens piece =
  parse_example_statement ~checks_fixes:true source tokens piece

module For_testing = struct
  let definition = definition
  let begins_statement = begins_statement
  let spelled_words = spelled_words
end
