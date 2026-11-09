(* The parser's entry point. See PARSER.md.

   A file's tokens are split into [use] lines and definitions, and each is
   parsed on its own, from its own slice of the tokens, into a tree whose
   spans are relative to its first token. The tree of a definition depends
   only on its own tokens. *)

open Token

(* The names the parser recognizes by their spelling, in a [cost] clause.
   GRAMMAR.md lists them with the words name resolution gives a meaning. *)
let spelled_words = Parse_expression.cost_words

let cursor source diagnostics (tokens : Token.t array) (item : Split.item) =
  Cursor.create ~source ~diagnostics ~base:tokens.(item.first).span.start tokens ~first:item.first
    ~stop:item.stop

let item (cursor : Cursor.t) value : _ Syntax.item =
  let last = cursor.tokens.(cursor.stop - 1) in
  {
    base = cursor.base;
    text = Cursor.text cursor (Source.span cursor.base last.span.stop);
    blank_line_before = cursor.tokens.(cursor.first).blank_line_before;
    value;
  }

let starts_use (cursor : Cursor.t) = Cursor.is_keyword cursor Use

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

(* A [use] line after a definition moves up, to after the other [use] lines,
   or above the first definition. *)
let use_after_definition (cursor : Cursor.t) ~destination =
  let source = cursor.source in
  let text = Source.text source in
  let start = Source.line_start source cursor.base in
  let line_end = Source.line_end source (Cursor.previous_stop cursor) in
  let stop = if line_end < String.length text then line_end + 1 else line_end in
  let line = Cursor.text cursor (Source.span cursor.base (Cursor.previous_stop cursor)) in
  Cursor.report cursor Use_after_definition
    (Source.span cursor.base (Cursor.previous_stop cursor))
    "`use` lines come before every definition in a file"
    ~fixes:
      [
        Diagnostic.fix "Move it up to the other `use` lines"
          [
            Diagnostic.insert destination (line ^ "\n"); Diagnostic.delete (Source.span start stop);
          ];
      ]

let definition ?rule cursor : Syntax.definition =
  match Parse_definition.definition ?rule cursor with
  | definition ->
      Operators.definition cursor definition;
      Check.definition cursor definition;
      definition
  | exception Cursor.Failed ->
      { visibility = Private; kind = Definition_error; span = Cursor.span_from cursor cursor.first }

let parse source tokens =
  let diagnostics = Diagnostic.Collector.create () in
  let uses = ref [] and definitions = ref [] in
  (* Where a [use] line found after a definition moves to. *)
  let destination = ref None in
  List.iter
    (fun (split : Split.item) ->
      let cursor = cursor source diagnostics tokens split in
      if starts_use cursor then begin
        let path = use_path cursor in
        (match (!definitions, !destination) with
        | [], _ ->
            let line_end = Source.line_end source (Cursor.previous_stop cursor) in
            destination := Some (min (line_end + 1) (String.length (Source.text source)))
        | _ :: _, Some destination -> use_after_definition cursor ~destination
        | _ :: _, None -> ());
        Option.iter (fun path -> uses := item cursor path :: !uses) path
      end
      else begin
        if !definitions = [] && !destination = None then
          destination := Some (Source.line_start source cursor.base);
        definitions := item cursor (definition cursor) :: !definitions
      end)
    (Split.items tokens);
  ( { Syntax.uses = List.rev !uses; definitions = List.rev !definitions },
    Diagnostic.Collector.to_list diagnostics )

(* The documents' examples mix definitions, signatures without bodies, and
   statements, and only the tests of the documents parse them, with this
   entry point. *)
module Snippet = struct
  type kind = Use | Definition | Signature | Statement
  type item = { kind : kind; first : int; stop : int }

  let starts_definition (cursor : Cursor.t) =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Keyword (Public | Internal | Type | Trait | Impl | Capability | Test | Theorem), _ -> true
    | Keyword Fn, (Lower _ | Upper _) -> true
    | Keyword Proof, Upper _ -> true
    | Keyword Let, Upper _ -> (
        match Cursor.peek_ahead cursor 2 with Punctuation (Dot | Open Square) -> true | _ -> false)
    | _ -> false

  let parse source tokens =
    let diagnostics = Diagnostic.Collector.create () in
    let items =
      List.map
        (fun (split : Split.item) ->
          let cursor = cursor source diagnostics tokens split in
          let kind =
            if starts_use cursor then begin
              ignore (use_path cursor);
              Use
            end
            else if starts_definition cursor then
              match definition ~rule:Parse_definition.Body_optional cursor with
              | { kind = Function { body = None; _ }; _ } -> Signature
              | _ -> Definition
            else begin
              (match
                 let statement = Parse_expression.statement_line cursor ~previous:None in
                 if not (Cursor.at_end cursor) then
                   Cursor.fail cursor "a line break after the statement";
                 statement
               with
              | statement ->
                  Syntax_walk.statement (fun value -> Operators.expression cursor value) statement
              | exception Cursor.Failed -> ());
              Statement
            end
          in
          { kind; first = split.first; stop = split.stop })
        (Split.items tokens)
    in
    (items, Diagnostic.Collector.to_list diagnostics)
end
