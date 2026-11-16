exception Failed

type t = {
  tokens : Token.t array;
  first : int;
  stop : int;
  base : int;
  group_ends : int array;
  diagnostics : Diagnostic.Collector.t;
  mutable index : int;
  mutable nesting_depth : int;
  spans : Source.Definition_span.t Dynarray.t;
  recoveries : Source.span list ref;
  mutable after_inserted_closer : bool;
  is_unterminated_interpolation : bool;
}

let nesting_limit = 256

let group_ends tokens ~first ~stop =
  let ends = Array.init (stop - first) (fun offset -> first + offset) in
  let openers = ref [] in
  for index = first to stop - 1 do
    match tokens.(index).Token.kind with
    | Punctuation (Open _) -> openers := index :: !openers
    | Punctuation (Close _) -> (
        match !openers with
        | opener :: rest ->
            ends.(opener - first) <- index;
            openers := rest
        | [] -> ())
    | _ -> ()
  done;
  ends

let create ~diagnostics ~base tokens ~first ~stop =
  {
    tokens;
    first;
    stop;
    base;
    group_ends = group_ends tokens ~first ~stop;
    diagnostics;
    index = first;
    nesting_depth = 0;
    spans = Dynarray.create ();
    recoveries = ref [];
    after_inserted_closer = false;
    is_unterminated_interpolation = false;
  }

let interpolation cursor (inner : Token.interpolation) =
  {
    (create ~diagnostics:cursor.diagnostics ~base:cursor.base inner.tokens ~first:0
       ~stop:(Array.length inner.tokens - 1))
    with
    nesting_depth = cursor.nesting_depth;
    recoveries = cursor.recoveries;
    spans = cursor.spans;
    is_unterminated_interpolation = not inner.is_closed;
  }

let index cursor = cursor.index

let end_token cursor =
  let position =
    if cursor.stop > cursor.first then cursor.tokens.(cursor.stop - 1).span.stop else cursor.base
  in
  {
    Token.kind = End_of_file;
    span = Source.zero_width position;
    line_break_before = false;
    blank_line_before = false;
    is_inserted_closer = false;
  }

let token_at cursor index = if index < cursor.stop then cursor.tokens.(index) else end_token cursor
let peek cursor = token_at cursor cursor.index
let peek_kind cursor = (peek cursor).kind
let peek_ahead cursor count = (token_at cursor (cursor.index + count)).kind

let record_recovery cursor ~index (span : Source.span) =
  let span =
    if span.start = span.stop && index > cursor.first then
      Source.span (min span.start (token_at cursor (index - 1)).span.start) span.stop
    else span
  in
  cursor.recoveries := span :: !(cursor.recoveries)

let advance cursor =
  if cursor.index < cursor.stop then begin
    let token = cursor.tokens.(cursor.index) in
    (match token.kind with
    | Punctuation (Close _) when token.is_inserted_closer ->
        cursor.after_inserted_closer <- true;
        record_recovery cursor ~index:cursor.index token.span
    | _ -> ());
    cursor.index <- cursor.index + 1
  end

let next cursor =
  let token = peek cursor in
  advance cursor;
  token

let at_end cursor = cursor.index >= cursor.stop
let is cursor kind = peek_kind cursor = kind

let is_punctuation cursor punctuation =
  match peek_kind cursor with
  | Punctuation current -> Token.equal_punctuation current punctuation
  | _ -> false

let is_keyword cursor (keyword : Token.keyword) =
  match peek_kind cursor with Keyword current -> current = keyword | _ -> false

let accept_punctuation cursor punctuation =
  if is_punctuation cursor punctuation then begin
    advance cursor;
    true
  end
  else false

let accept_keyword cursor keyword =
  if is_keyword cursor keyword then begin
    advance cursor;
    true
  end
  else false

let definition_span cursor span = Source.Definition_span.of_file ~base:cursor.base span

let previous_token cursor =
  if cursor.index > cursor.first then Some cursor.tokens.(cursor.index - 1) else None

let previous_stop cursor =
  match previous_token cursor with Some token -> token.span.stop | None -> cursor.base

let span_from cursor start_index =
  let start = (token_at cursor start_index).span.start in
  let stop = max start (previous_stop cursor) in
  definition_span cursor (Source.span start stop)

let file_span cursor span = Source.Definition_span.to_file ~base:cursor.base span

let allocate_id cursor span =
  Dynarray.add_last cursor.spans span;
  Dynarray.length cursor.spans - 1

let allocate_id_from cursor start_index = allocate_id cursor (span_from cursor start_index)
let read_span cursor id = Dynarray.get cursor.spans id
let set_span cursor id span = Dynarray.set cursor.spans id span
let read_file_span cursor id = file_span cursor (read_span cursor id)

let rec tokens_within (tokens : Token.t array) ~first ~stop (span : Source.span) =
  let inside = ref [] and enclosing = ref None in
  for index = first to stop - 1 do
    let token = tokens.(index) in
    if span.start <= token.span.start && token.span.stop <= span.stop then
      inside := token :: !inside
    else if token.span.start <= span.start && span.stop <= token.span.stop then
      enclosing := Some token
  done;
  match (!inside, !enclosing) with
  | [], Some { kind = String literal; _ } -> (
      match
        List.find_opt
          (fun (interpolation : Token.interpolation) ->
            interpolation.span.start <= span.start && span.stop <= interpolation.span.stop)
          (Array.to_list (Token.interpolations literal))
      with
      | Some interpolation ->
          tokens_within interpolation.tokens ~first:0 ~stop:(Array.length interpolation.tokens) span
      | None -> [||])
  | inside, _ -> Array.of_list (List.rev inside)

let spelling cursor ?insertions span =
  match tokens_within cursor.tokens ~first:cursor.first ~stop:cursor.stop span with
  | [||] -> None
  | tokens -> Token.spelling ?insertions tokens

let joins_neighbors cursor (span : Source.span) code =
  let adjacent is_adjacent =
    let rec search index =
      if index >= cursor.stop then None
      else
        let token = cursor.tokens.(index) in
        if token.span.start < token.span.stop && is_adjacent token then Token.spelling [| token |]
        else search (index + 1)
    in
    Option.bind (search cursor.first) (fun spelling ->
        if spelling = "" then None else Some spelling)
  in
  let before =
    Option.map
      (fun spelling -> spelling.[String.length spelling - 1])
      (adjacent (fun token -> token.span.stop = span.start))
  and after =
    Option.map (fun spelling -> spelling.[0]) (adjacent (fun token -> token.span.start = span.stop))
  in
  Token.joins_neighbor ~before ~after code

let has_reported cursor = Diagnostic.Collector.to_list cursor.diagnostics <> []

let report cursor ?notes ?fixes code span message =
  (match code with
  | Diagnostic.Code.Missing_body -> cursor.recoveries := span :: !(cursor.recoveries)
  | _ -> record_recovery cursor ~index:cursor.index span);
  Diagnostic.Collector.add cursor.diagnostics
    (Diagnostic.make ?notes ?fixes ~code:(Diagnostic.Code.Parser code) span message)

let describe (token : Token.t) =
  match token.kind with
  | Newline -> "a line break"
  | End_of_file -> "the end of the definition"
  | Upper name | Lower name -> Printf.sprintf "the name `%s`" name
  | Underscore -> "`_`"
  | Keyword keyword -> Printf.sprintf "`%s`" (Token.keyword_spelling keyword)
  | Reserved reserved -> Printf.sprintf "`%s`" (Token.reserved_spelling reserved)
  | Integer _ | Float _ -> "a number"
  | String _ -> "a string"
  | Punctuation punctuation -> Printf.sprintf "`%s`" (Token.punctuation_spelling punctuation)
  | Foreign foreign -> Printf.sprintf "`%s`" (Token.foreign_spelling foreign)

let fail cursor expected =
  let token = peek cursor in
  let is_reported_by_lexer =
    token.is_inserted_closer || cursor.after_inserted_closer
    || (token.kind = End_of_file && cursor.is_unterminated_interpolation)
  in
  (match token.kind with
  | _ when is_reported_by_lexer -> record_recovery cursor ~index:cursor.index token.span
  | Reserved reserved ->
      report cursor Reserved_word token.span
        (Printf.sprintf "`%s` is reserved for possible later use, and means nothing in Truss yet."
           (Token.reserved_spelling reserved))
  | _ ->
      report cursor Unexpected_token token.span
        (Printf.sprintf "Expected %s, found %s." expected (describe token)));
  raise Failed

let expect_punctuation cursor punctuation =
  if not (accept_punctuation cursor punctuation) then
    fail cursor (Printf.sprintf "`%s`" (Token.punctuation_spelling punctuation))

let expect_keyword cursor keyword =
  if not (accept_keyword cursor keyword) then
    fail cursor (Printf.sprintf "`%s`" (Token.keyword_spelling keyword))

let nested cursor parse =
  if cursor.nesting_depth >= nesting_limit then begin
    report cursor Nesting_too_deep (peek cursor).span
      (Printf.sprintf "This is nested more than %d levels deep." nesting_limit);
    raise Failed
  end;
  cursor.nesting_depth <- cursor.nesting_depth + 1;
  match parse cursor with
  | value ->
      cursor.nesting_depth <- cursor.nesting_depth - 1;
      value
  | exception exception_ ->
      cursor.nesting_depth <- cursor.nesting_depth - 1;
      raise exception_

let chain_limit = 10_000

let check_chain_length cursor ~chain_length =
  if chain_length >= chain_limit then begin
    report cursor Nesting_too_deep (peek cursor).span
      (Printf.sprintf
         "This chains more than %d operations, each of which nests one level deeper. Give parts of \
          it names with `let`."
         chain_limit);
    raise Failed
  end

let closer cursor index = cursor.group_ends.(index - cursor.first)

let skip_to cursor limit =
  while cursor.index < min limit cursor.stop do
    advance cursor
  done

let skip_one cursor =
  if cursor.index < cursor.stop then skip_to cursor (closer cursor cursor.index + 1)

let group cursor =
  Array.sub cursor.tokens cursor.index (closer cursor cursor.index - cursor.index + 1)

let separated cursor ~separator item =
  let rec gather items =
    let items = item cursor :: items in
    if accept_punctuation cursor separator then gather items else List.rev items
  in
  gather []

let skip_piece cursor : Split.piece =
  let piece : Split.piece =
    { first = cursor.index; stop = Split.stop cursor.tokens ~first:cursor.index }
  in
  skip_to cursor piece.stop;
  piece

let is_after_inserted_closer cursor = cursor.after_inserted_closer

let skip_line cursor ~closer_index =
  while cursor.index < closer_index && cursor.index < cursor.stop && peek_kind cursor <> Newline do
    skip_one cursor
  done

let bracketed cursor ~item ~recover =
  let opener = cursor.index in
  let closer_index = closer cursor opener in
  advance cursor;
  let rec gather items =
    if cursor.index >= closer_index then List.rev items
    else
      let start = cursor.index in
      match
        let value = item cursor in
        if cursor.index < closer_index then expect_punctuation cursor Comma;
        value
      with
      | value -> gather (value :: items)
      | exception Failed ->
          while cursor.index < closer_index && peek_kind cursor <> Punctuation Comma do
            skip_one cursor
          done;
          let span =
            definition_span cursor
              (Source.span (token_at cursor start).span.start (peek cursor).span.start)
          in
          if cursor.index < closer_index then advance cursor;
          gather (recover span :: items)
  in
  let items = gather [] in
  skip_to cursor (closer_index + 1);
  items

let lines cursor ~item ~recover =
  let enclosing_after_inserted_closer = cursor.after_inserted_closer in
  let opener = cursor.index in
  let closer_index = closer cursor opener in
  advance cursor;
  let rec gather items =
    if cursor.index >= closer_index then List.rev items
    else
      let start = cursor.index in
      let value =
        match
          cursor.after_inserted_closer <- false;
          let value = item cursor in
          let ends_with_comma =
            match previous_token cursor with
            | Some { kind = Punctuation Comma; _ } -> true
            | _ -> false
          in
          let separated =
            peek_kind cursor = Newline || (ends_with_comma && (peek cursor).line_break_before)
          in
          if cursor.index < closer_index && not separated then fail cursor "a line break or `}`";
          value
        with
        | value -> value
        | exception Failed ->
            skip_line cursor ~closer_index;
            recover (span_from cursor start)
      in
      if cursor.index < closer_index && peek_kind cursor = Newline then advance cursor;
      gather (value :: items)
  in
  let items = gather [] in
  cursor.after_inserted_closer <- enclosing_after_inserted_closer;
  skip_to cursor (closer_index + 1);
  items

let collect_positions cursor : Syntax.positions =
  {
    spans = Dynarray.to_array cursor.spans;
    recovered = List.sort_uniq compare (List.map (definition_span cursor) !(cursor.recoveries));
  }
