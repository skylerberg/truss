open Token

type piece = Split.piece = { first : int; stop : int }

let split = Split.pieces
let is_use (tokens : Token.t array) piece = tokens.(piece.first).kind = Keyword Use
let recovers = Cursor.recovers

let parse_piece (tokens : Token.t array) piece parse =
  let diagnostics = Diagnostic.Collector.create () in
  let base = tokens.(piece.first).span.start in
  let value = parse (Cursor.create ~diagnostics ~base tokens ~first:piece.first ~stop:piece.stop) in
  (value, Diagnostic.Collector.to_list diagnostics)

let item (tokens : Token.t array) piece value : _ Syntax.item =
  { base = tokens.(piece.first).span.start; stop = tokens.(piece.stop - 1).span.stop; value }

let checked cursor (definition : Syntax.definition) =
  Precedence.definition cursor definition;
  Check.definition cursor definition;
  { definition with recovered = Cursor.recovered cursor }

let parse_methods tokens (container : Syntax.definition) pieces =
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
          let definition, diagnostics =
            parse_piece tokens piece (fun cursor ->
                checked cursor
                  (Parse_definition.method_ cursor ~container:kind ~visibility:container.visibility))
          in
          (item tokens piece definition, diagnostics))
        pieces
  | None -> []

let parse_definition tokens piece : Syntax.top_level * Diagnostic.t list =
  let (definition, method_pieces), diagnostics =
    parse_piece tokens piece (fun cursor ->
        let definition, methods = Parse_definition.definition cursor in
        (checked cursor definition, methods))
  in
  let methods = parse_methods tokens definition method_pieces in
  ( { definition = item tokens piece definition; methods = List.map fst methods },
    diagnostics @ List.concat_map snd methods )

let use_path cursor : Syntax.path option =
  match
    Cursor.expect_keyword cursor Use;
    let names =
      List.rev
        (Cursor.separated cursor ~separator:Colon_colon (fun cursor ->
             Atoms.lower_name cursor "a module name"))
    in
    if not (Cursor.at_end cursor) then Cursor.fail cursor "a line break after the module path";
    names
  with
  | last :: modules -> Some { modules = List.rev modules; last }
  | [] -> None
  | exception Cursor.Failed -> None

let parse_use_line tokens piece = parse_piece tokens piece use_path

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
        let path, line_diagnostics = parse_use_line tokens piece in
        let line = item tokens piece path in
        let moved, destination =
          match (definitions, destination) with
          | [], _ -> ([], Some (line_stop tokens piece))
          | _ :: _, Some destination ->
              ([ use_after_definition tokens piece line ~destination ], Some destination)
          | _ :: _, None -> ([], None)
        in
        let uses =
          match path with Some path -> { line with value = path } :: uses | None -> uses
        in
        gather rest ~uses ~definitions
          ~diagnostics:((line_diagnostics @ moved) :: diagnostics)
          ~destination
    | piece :: rest ->
        let top_level, definition_diagnostics = parse_definition tokens piece in
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
  let parse_definition = parse_definition

  let parse_example_definition tokens piece =
    let (example, container), diagnostics =
      parse_piece tokens piece (fun cursor ->
          match Parse_definition.example cursor with
          | Whole (definition, methods) ->
              (Example_definition, Some (checked cursor definition, methods))
          | Signature_alone (_, signature) ->
              Syntax_walk.signature (fun value -> Precedence.expression cursor value) signature;
              Check.signature cursor signature;
              (Example_signature, None))
    in
    let method_diagnostics =
      match container with
      | Some (container, pieces) -> List.concat_map snd (parse_methods tokens container pieces)
      | None -> []
    in
    (example, diagnostics @ method_diagnostics)

  let parse_example_statement tokens piece =
    let (), diagnostics =
      parse_piece tokens piece (fun cursor ->
          match
            let statement = Parse_expression.statement_line cursor ~previous:None in
            if not (Cursor.at_end cursor) then Cursor.fail cursor "a line break after the statement";
            statement
          with
          | statement ->
              Syntax_walk.statement (fun value -> Precedence.expression cursor value) statement
          | exception Cursor.Failed -> ())
    in
    diagnostics

  let begins_statement = Atoms.begins_statement
  let contextual_keywords = List.map fst Contextual_keyword.spellings
end
