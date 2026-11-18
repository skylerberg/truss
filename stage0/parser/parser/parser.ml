type piece = Split.piece = { first : int; stop : int }

let split = Split.split_pieces
let is_use (tokens : Token.t array) piece = tokens.(piece.first).kind = Keyword Use

let parse_piece (tokens : Token.t array) piece parse =
  let diagnostics = Diagnostic.Collector.create () in
  let base = tokens.(piece.first).span.start in
  let cursor = Cursor.create ~diagnostics ~base tokens ~first:piece.first ~stop:piece.stop in
  let value = parse cursor in
  ( ({
       base;
       stop = tokens.(piece.stop - 1).span.stop;
       value;
       positions = Cursor.collect_positions cursor;
     }
      : _ Syntax.item),
    Diagnostic.Collector.to_list diagnostics )

let overlaps (tokens : Token.t array) piece (span : Source.span) =
  let start = tokens.(piece.first).span.start and stop = tokens.(piece.stop - 1).span.stop in
  if span.start = span.stop then start <= span.start && span.start <= stop
  else span.start < stop && start < span.stop

let attach_lexer_errors tokens ~lexer_diagnostics ~nested piece
    ((item : _ Syntax.item), (diagnostics : Diagnostic.t list)) =
  let errors =
    List.filter
      (fun (span : Source.span) ->
        overlaps tokens piece span
        && not (List.exists (fun inner -> overlaps tokens inner span) nested))
      (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.span) lexer_diagnostics)
  in
  match errors with
  | [] -> (item, diagnostics)
  | _ ->
      let recovered =
        List.map
          (fun (span : Source.span) ->
            Source.Definition_span.of_file ~base:item.base
              (Source.make_span (max span.start item.base) (min span.stop item.stop)))
          errors
      in
      ( {
          item with
          positions =
            {
              item.positions with
              recovered = List.sort_uniq compare (recovered @ item.positions.recovered);
            };
        },
        List.map (fun (diagnostic : Diagnostic.t) -> { diagnostic with fixes = [] }) diagnostics )

let check_definition cursor (definition : Syntax.definition) =
  Precedence.check_definition cursor definition;
  Check.check_definition cursor definition;
  definition

let parse_methods tokens ~lexer_diagnostics (container : Syntax.definition) pieces =
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
        (fun piece ->
          attach_lexer_errors tokens ~lexer_diagnostics ~nested:[] piece
            (parse_piece tokens piece (fun cursor ->
                 check_definition cursor (Parse_definition.parse_method cursor ~container:kind))))
        pieces
  | None -> []

let parse_definition tokens ~lexer_diagnostics piece : Syntax.top_level * Diagnostic.t list =
  let parsed, diagnostics =
    parse_piece tokens piece (fun cursor ->
        let definition, methods = Parse_definition.parse_definition cursor in
        (check_definition cursor definition, methods))
  in
  let definition, method_pieces = parsed.value in
  let definition, diagnostics =
    attach_lexer_errors tokens ~lexer_diagnostics ~nested:method_pieces piece
      ({ parsed with value = definition }, diagnostics)
  in
  let methods = parse_methods tokens ~lexer_diagnostics definition.value method_pieces in
  ({ definition; methods = List.map fst methods }, diagnostics @ List.concat_map snd methods)

let use_path cursor : Syntax.path option =
  match
    Cursor.expect_keyword cursor Use;
    let names =
      List.rev
        (Cursor.parse_separated cursor ~separator:Colon_colon (fun cursor ->
             Atoms.lower_name cursor "a module name"))
    in
    if not (Cursor.is_at_end cursor) then Cursor.fail cursor "a line break after the module path";
    names
  with
  | last :: modules -> Some { modules = List.rev modules; last }
  | [] -> None
  | exception Cursor.Failed -> None

let parse_use_line tokens piece = parse_piece tokens piece use_path

let compute_line_stop (tokens : Token.t array) piece =
  match tokens.(piece.stop).kind with
  | Newline -> tokens.(piece.stop).span.stop
  | _ -> tokens.(piece.stop - 1).span.stop

let use_after_definition (tokens : Token.t array) piece (line : _ Syntax.item) ~destination =
  let fixes =
    match Token.spell_tokens (Array.sub tokens piece.first (piece.stop - piece.first)) with
    | Some spelling ->
        [
          Diagnostic.fix "Move it up to the other `use` lines"
            [
              Diagnostic.insert (Source.make_zero_width destination) (spelling ^ "\n");
              Diagnostic.delete (Source.make_span line.base (compute_line_stop tokens piece));
            ];
        ]
    | None -> []
  in
  Diagnostic.make ~code:(Parser Use_after_definition)
    (Source.make_span line.base line.stop)
    "`use` lines come before every definition in a file." ~fixes

let parse tokens ~lexer_diagnostics =
  let rec gather pieces ~uses ~definitions ~diagnostics ~destination =
    match pieces with
    | [] -> (List.rev uses, List.rev definitions, List.concat (List.rev diagnostics))
    | piece :: rest when is_use tokens piece ->
        let line, line_diagnostics = parse_use_line tokens piece in
        let moved, destination =
          match (definitions, destination) with
          | [], _ -> ([], Some (compute_line_stop tokens piece))
          | _ :: _, Some destination ->
              ([ use_after_definition tokens piece line ~destination ], Some destination)
          | _ :: _, None -> ([], None)
        in
        let uses =
          match line.value with Some path -> { line with value = path } :: uses | None -> uses
        in
        gather rest ~uses ~definitions
          ~diagnostics:((line_diagnostics @ moved) :: diagnostics)
          ~destination
    | piece :: rest ->
        let top_level, definition_diagnostics = parse_definition tokens ~lexer_diagnostics piece in
        let destination =
          match (definitions, destination) with
          | [], None -> Some top_level.definition.base
          | _ -> destination
        in
        gather rest ~uses ~definitions:(top_level :: definitions)
          ~diagnostics:(definition_diagnostics :: diagnostics)
          ~destination
  in
  let uses, definitions, diagnostics =
    gather (split tokens) ~uses:[] ~definitions:[] ~diagnostics:[] ~destination:None
  in
  ( { Syntax.uses; definitions },
    List.stable_sort
      (fun (left : Diagnostic.t) (right : Diagnostic.t) -> compare left.span.start right.span.start)
      diagnostics )

module For_testing = struct
  type piece = Split.piece = { first : int; stop : int }
  type example = Example_definition | Example_signature

  let split = split
  let is_use = is_use
  let parse_use_line = parse_use_line
  let parse_definition tokens piece = parse_definition tokens ~lexer_diagnostics:[] piece

  let parse_example_definition tokens piece =
    let parsed, diagnostics =
      parse_piece tokens piece (fun cursor ->
          match Parse_definition.parse_example cursor with
          | Whole (definition, methods) ->
              (Example_definition, Some (check_definition cursor definition, methods))
          | Signature_alone (_, signature) ->
              Syntax_walk.visit_signature
                (fun value -> Precedence.check_expression cursor value)
                signature;
              Check.check_signature cursor signature;
              (Example_signature, None))
    in
    let example, container = parsed.value in
    let method_diagnostics =
      match container with
      | Some (container, pieces) ->
          List.concat_map snd (parse_methods tokens ~lexer_diagnostics:[] container pieces)
      | None -> []
    in
    (example, diagnostics @ method_diagnostics)

  let parse_example_statement tokens piece =
    let _, diagnostics =
      parse_piece tokens piece (fun cursor ->
          match
            let statement = Parse_expression.parse_statement_line cursor ~previous:None in
            if not (Cursor.is_at_end cursor) then
              Cursor.fail cursor "a line break after the statement";
            statement
          with
          | statement ->
              Syntax_walk.visit_statement
                (fun value -> Precedence.check_expression cursor value)
                statement
          | exception Cursor.Failed -> ())
    in
    diagnostics

  let begins_statement = Atoms.begins_statement
  let contextual_keywords = List.map fst Contextual_keyword.spellings
end
