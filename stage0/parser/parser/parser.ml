open Token

type piece = Split.piece = { first : int; stop : int }

let split = Split.pieces
let is_use (tokens : Token.t array) piece = tokens.(piece.first).kind = Keyword Use
let recovers = Cursor.recovers
let begins_statement = Atoms.begins_statement
let spelled_words = List.map fst Cost_word.spellings @ [ "by"; "bit_vector" ]

type 'value parsed = { value : 'value Syntax.item; diagnostics : Diagnostic.in_definition list }

let diagnostics_in_file parsed =
  List.map
    (Diagnostic.map_spans (Source.Definition_span.to_file ~base:parsed.value.base))
    parsed.diagnostics

let with_cursor (tokens : Token.t array) piece parse =
  let diagnostics = Diagnostic.Collector.create () in
  let base = tokens.(piece.first).span.start in
  let cursor = Cursor.create ~diagnostics ~base tokens ~first:piece.first ~stop:piece.stop in
  let value = parse cursor in
  let item : _ Syntax.item =
    {
      base;
      stop = tokens.(piece.stop - 1).span.stop;
      blank_line_before = tokens.(piece.first).blank_line_before;
      value;
      container_index = None;
    }
  in
  (item, cursor, Diagnostic.Collector.to_list diagnostics)

let parsed (item : _ Syntax.item) diagnostics =
  {
    value = item;
    diagnostics =
      List.map (Diagnostic.map_spans (Source.Definition_span.of_file ~base:item.base)) diagnostics;
  }

let check cursor definition =
  Operators.definition cursor definition;
  Check.definition cursor definition

let one_definition tokens piece parse =
  let item, cursor, diagnostics =
    with_cursor tokens piece (fun cursor ->
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
                span = Cursor.span_from cursor piece.first;
                recovered = [];
                id = Cursor.fresh_id cursor;
              }
        in
        { definition with recovered = Cursor.recovered cursor })
  in
  (parsed item diagnostics, Cursor.methods cursor)

let methods tokens (container : Syntax.definition) pieces =
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
          fst
            (one_definition tokens piece
               (Parse_definition.method_ ~container:kind ~visibility:container.visibility)))
        pieces
  | None -> []

let definition tokens piece =
  let parsed, method_pieces = one_definition tokens piece Parse_definition.definition in
  (parsed, methods tokens parsed.value.value method_pieces)

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

let use_line tokens piece =
  let item, _, diagnostics = with_cursor tokens piece use_path in
  parsed item diagnostics

let line_stop (tokens : Token.t array) piece =
  match tokens.(piece.stop).kind with
  | Newline -> tokens.(piece.stop).span.stop
  | _ -> tokens.(piece.stop - 1).span.stop

let use_after_definition (tokens : Token.t array) piece (line : _ Syntax.item) ~destination =
  let fixes =
    match Token.spelling (Array.sub tokens piece.first (piece.stop - piece.first)) with
    | Some spelling ->
        [
          Diagnostic.fix "Move it up to the other `use` lines"
            [
              Diagnostic.insert (Source.zero_width destination) (spelling ^ "\n");
              Diagnostic.delete (Source.span line.base (line_stop tokens piece));
            ];
        ]
    | None -> []
  in
  Diagnostic.make ~code:(Parser Use_after_definition) (Source.span line.base line.stop)
    "`use` lines come before every definition in a file." ~fixes

let parse tokens =
  let rec gather pieces ~uses ~definitions ~diagnostics ~destination =
    match pieces with
    | [] -> (List.rev uses, List.rev definitions, List.concat (List.rev diagnostics))
    | piece :: rest when is_use tokens piece ->
        let line = use_line tokens piece in
        let line_diagnostics = diagnostics_in_file line in
        let moved, destination =
          match (definitions, destination) with
          | [], _ -> ([], Some (line_stop tokens piece))
          | _ :: _, Some destination ->
              ([ use_after_definition tokens piece line.value ~destination ], Some destination)
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
        let parsed, methods = definition tokens piece in
        let destination =
          match (definitions, destination) with
          | [], None -> Some parsed.value.base
          | _ -> destination
        in
        let container_index = Some (List.length definitions) in
        gather rest ~uses
          ~definitions:
            (List.rev_map
               (fun (method_ : _ parsed) -> { method_.value with container_index })
               methods
            @ (parsed.value :: definitions))
          ~diagnostics:
            (List.rev_map diagnostics_in_file methods @ (diagnostics_in_file parsed :: diagnostics))
          ~destination
  in
  let uses, definitions, diagnostics =
    gather (split tokens) ~uses:[] ~definitions:[] ~diagnostics:[] ~destination:None
  in
  ( { Syntax.uses; definitions },
    List.stable_sort
      (fun (left : Diagnostic.t) (right : Diagnostic.t) -> compare left.span.start right.span.start)
      diagnostics )

type example = Example_definition | Example_signature

let example_definition tokens piece =
  let item, cursor, diagnostics =
    with_cursor tokens piece (fun cursor ->
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
  let example, container = item.value in
  let method_diagnostics =
    match container with
    | Some container ->
        List.concat_map diagnostics_in_file (methods tokens container (Cursor.methods cursor))
    | None -> []
  in
  (example, diagnostics @ method_diagnostics)

let example_statement tokens piece =
  let _, _, diagnostics =
    with_cursor tokens piece (fun cursor ->
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

module For_testing = struct
  let definition = definition
  let begins_statement = begins_statement
  let spelled_words = spelled_words
end
