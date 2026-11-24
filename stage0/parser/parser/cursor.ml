exception Failed

type t = {
  tokens : Token.t array;
  first : int;
  stop : int;
  base : int;
  group_ends : int array;
  angle_closers : int option array;
  diagnostics : Diagnostic.Collector.t;
  mutable index : int;
  mutable nesting_depth : int;
  spans : Source.Definition_span.t Dynarray.t;
  syntax_errors : Source.span list ref;
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

let continues_type_arguments : Token.kind -> bool = function
  | Upper _ | Lower _ | Integer _
  | Punctuation (Comma | Colon | Dot | Equal | Plus | Arrow)
  | Keyword (Self_type | Fn | Mut | Own | Capability) ->
      true
  | _ -> false

let list_angle_closers (tokens : Token.t array) ~first ~stop =
  let closers = Array.make (stop - first) None in
  let rec scan index ~openers ~enclosing =
    if index < stop then
      match tokens.(index).kind with
      | Punctuation Less -> scan (index + 1) ~openers:(index :: openers) ~enclosing
      | Punctuation Greater -> (
          match openers with
          | innermost :: outer ->
              closers.(innermost - first) <- Some index;
              scan (index + 1) ~openers:outer ~enclosing
          | [] -> scan (index + 1) ~openers ~enclosing)
      | Punctuation Shift_right -> (
          match openers with
          | _ :: second :: outer ->
              closers.(second - first) <- Some index;
              scan (index + 1) ~openers:outer ~enclosing
          | _ -> scan (index + 1) ~openers:[] ~enclosing)
      | Punctuation (Open _) -> scan (index + 1) ~openers:[] ~enclosing:(openers :: enclosing)
      | Punctuation (Close _) -> (
          match enclosing with
          | outer :: rest -> scan (index + 1) ~openers:outer ~enclosing:rest
          | [] -> scan (index + 1) ~openers:[] ~enclosing)
      | kind when continues_type_arguments kind -> scan (index + 1) ~openers ~enclosing
      | _ -> scan (index + 1) ~openers:[] ~enclosing
  in
  scan first ~openers:[] ~enclosing:[];
  closers

let create ~diagnostics ~base tokens ~first ~stop =
  {
    tokens;
    first;
    stop;
    base;
    group_ends = group_ends tokens ~first ~stop;
    angle_closers = list_angle_closers tokens ~first ~stop;
    diagnostics;
    index = first;
    nesting_depth = 0;
    spans = Dynarray.create ();
    syntax_errors = ref [];
    after_inserted_closer = false;
    is_unterminated_interpolation = false;
  }

let enter_interpolation cursor (inner : Token.interpolation) =
  {
    (create ~diagnostics:cursor.diagnostics ~base:cursor.base inner.tokens ~first:0
       ~stop:(Array.length inner.tokens - 1))
    with
    nesting_depth = cursor.nesting_depth;
    syntax_errors = cursor.syntax_errors;
    spans = cursor.spans;
    is_unterminated_interpolation = not inner.is_closed;
  }

let index cursor = cursor.index

let make_end_token cursor =
  let position =
    if cursor.stop > cursor.first then cursor.tokens.(cursor.stop - 1).span.stop else cursor.base
  in
  {
    Token.kind = End_of_file;
    span = Source.make_zero_width position;
    line_break_before = false;
    blank_line_before = false;
    is_inserted_closer = false;
  }

let lookup_token cursor index =
  if index < cursor.stop then cursor.tokens.(index) else make_end_token cursor

let peek cursor = lookup_token cursor cursor.index
let peek_kind cursor = (peek cursor).kind
let peek_ahead cursor count = (lookup_token cursor (cursor.index + count)).kind

let record_syntax_error cursor ~index (span : Source.span) =
  let span =
    if span.start = span.stop && index > cursor.first then
      Source.make_span (min span.start (lookup_token cursor (index - 1)).span.start) span.stop
    else span
  in
  cursor.syntax_errors := span :: !(cursor.syntax_errors)

let advance cursor =
  if cursor.index < cursor.stop then begin
    let token = cursor.tokens.(cursor.index) in
    (match token.kind with
    | Punctuation (Close _) when token.is_inserted_closer ->
        cursor.after_inserted_closer <- true;
        record_syntax_error cursor ~index:cursor.index token.span
    | _ -> ());
    cursor.index <- cursor.index + 1
  end

let take cursor =
  let token = peek cursor in
  advance cursor;
  token

let is_at_end cursor = cursor.index >= cursor.stop
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

let make_definition_span cursor span = Source.Definition_span.of_file ~base:cursor.base span

let find_previous_token cursor =
  if cursor.index > cursor.first then Some cursor.tokens.(cursor.index - 1) else None

let compute_previous_stop cursor =
  match find_previous_token cursor with Some token -> token.span.stop | None -> cursor.base

let make_span_from cursor start_index =
  let start = (lookup_token cursor start_index).span.start in
  let stop = max start (compute_previous_stop cursor) in
  make_definition_span cursor (Source.make_span start stop)

let make_file_span cursor span = Source.Definition_span.to_file ~base:cursor.base span

let allocate_id cursor span =
  Dynarray.add_last cursor.spans span;
  Dynarray.length cursor.spans - 1

let allocate_id_from cursor start_index = allocate_id cursor (make_span_from cursor start_index)
let read_span cursor id = Dynarray.get cursor.spans id
let set_span cursor id span = Dynarray.set cursor.spans id span
let read_file_span cursor id = make_file_span cursor (read_span cursor id)

let locate_first (tokens : Token.t array) ~first ~stop is_reached =
  let rec search low high =
    if low >= high then low
    else
      let middle = low + ((high - low) / 2) in
      if is_reached tokens.(middle) then search low middle else search (middle + 1) high
  in
  search first stop

let rec list_tokens_within (tokens : Token.t array) ~first ~stop (span : Source.span) =
  let inside_first =
    locate_first tokens ~first ~stop (fun (token : Token.t) -> token.span.start >= span.start)
  in
  let inside_stop =
    locate_first tokens ~first:inside_first ~stop (fun (token : Token.t) ->
        token.span.stop > span.stop)
  in
  let encloses index =
    first <= index && index < stop
    && tokens.(index).span.start <= span.start
    && span.stop <= tokens.(index).span.stop
  in
  if inside_first < inside_stop then Array.sub tokens inside_first (inside_stop - inside_first)
  else
    match List.find_opt encloses [ inside_stop; inside_first - 1 ] with
    | Some index -> (
        match tokens.(index).kind with
        | String literal -> (
            match
              List.find_opt
                (fun (interpolation : Token.interpolation) ->
                  interpolation.span.start <= span.start && span.stop <= interpolation.span.stop)
                (Array.to_list (Token.list_interpolations literal))
            with
            | Some interpolation ->
                list_tokens_within interpolation.tokens ~first:0
                  ~stop:(Array.length interpolation.tokens)
                  span
            | None -> [||])
        | _ -> [||])
    | None -> [||]

let spell cursor ?insertions span =
  match list_tokens_within cursor.tokens ~first:cursor.first ~stop:cursor.stop span with
  | [||] -> None
  | tokens -> Token.spell_tokens ?insertions tokens

let joins_neighbors cursor (span : Source.span) code =
  let find_spelling ~offset_of offset =
    let rec search index =
      if index < cursor.stop && offset_of cursor.tokens.(index) = offset then
        let token = cursor.tokens.(index) in
        if token.span.start < token.span.stop then Token.spell_tokens [| token |]
        else search (index + 1)
      else None
    in
    Option.bind
      (search
         (locate_first cursor.tokens ~first:cursor.first ~stop:cursor.stop (fun token ->
              offset_of token >= offset)))
      (fun spelling -> if spelling = "" then None else Some spelling)
  in
  let before =
    Option.map
      (fun spelling -> spelling.[String.length spelling - 1])
      (find_spelling ~offset_of:(fun (token : Token.t) -> token.span.stop) span.start)
  and after =
    Option.map
      (fun spelling -> spelling.[0])
      (find_spelling ~offset_of:(fun (token : Token.t) -> token.span.start) span.stop)
  in
  Token.joins_neighbor ~before ~after code

let has_reported cursor = Diagnostic.Collector.to_list cursor.diagnostics <> []

let report cursor ?(fixes = []) at (problem : Syntax_catalog.Parsing.problem) =
  (match problem with
  | Missing_body -> cursor.syntax_errors := at :: !(cursor.syntax_errors)
  | _ -> record_syntax_error cursor ~index:cursor.index at);
  Diagnostic.Collector.add cursor.diagnostics
    (Syntax_catalog.Parsing_description.render { at; problem; fixes })

let fail cursor expected =
  let token = peek cursor in
  let is_reported_by_lexer =
    token.is_inserted_closer || cursor.after_inserted_closer
    || (token.kind = End_of_file && cursor.is_unterminated_interpolation)
  in
  (match token.kind with
  | _ when is_reported_by_lexer -> record_syntax_error cursor ~index:cursor.index token.span
  | Reserved reserved ->
      report cursor token.span (Reserved_word { word = Token.spell_reserved reserved })
  | _ -> report cursor token.span (Unexpected { expected; found = token.kind }));
  raise Failed

let expect_punctuation cursor punctuation =
  if not (accept_punctuation cursor punctuation) then fail cursor (Token_punctuation punctuation)

let expect_keyword cursor keyword =
  if not (accept_keyword cursor keyword) then fail cursor (Token_keyword keyword)

let run_nested cursor parse =
  if cursor.nesting_depth >= nesting_limit then begin
    report cursor (peek cursor).span (Nesting_too_deep { limit = nesting_limit });
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
    report cursor (peek cursor).span (Chain_too_long { limit = chain_limit });
    raise Failed
  end

let lookup_closer cursor index = cursor.group_ends.(index - cursor.first)
let find_angle_closer cursor = cursor.angle_closers.(cursor.index - cursor.first)

let skip_to cursor limit =
  while cursor.index < min limit cursor.stop do
    advance cursor
  done

let skip_one cursor =
  if cursor.index < cursor.stop then skip_to cursor (lookup_closer cursor cursor.index + 1)

let group cursor =
  Array.sub cursor.tokens cursor.index (lookup_closer cursor cursor.index - cursor.index + 1)

let parse_separated cursor ~separator parse_item =
  let rec gather items =
    let items = parse_item cursor :: items in
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

let parse_bracketed cursor ~parse_item ~recover =
  let opener = cursor.index in
  let closer_index = lookup_closer cursor opener in
  advance cursor;
  let rec gather items =
    if cursor.index >= closer_index then List.rev items
    else
      let start = cursor.index in
      match
        let value = parse_item cursor in
        if cursor.index < closer_index then expect_punctuation cursor Comma;
        value
      with
      | value -> gather (value :: items)
      | exception Failed ->
          while cursor.index < closer_index && peek_kind cursor <> Punctuation Comma do
            skip_one cursor
          done;
          let span =
            make_definition_span cursor
              (Source.make_span (lookup_token cursor start).span.start (peek cursor).span.start)
          in
          if cursor.index < closer_index then advance cursor;
          gather (recover span :: items)
  in
  let items = gather [] in
  skip_to cursor (closer_index + 1);
  items

let parse_lines cursor ~parse_item ~recover =
  let enclosing_after_inserted_closer = cursor.after_inserted_closer in
  let opener = cursor.index in
  let closer_index = lookup_closer cursor opener in
  advance cursor;
  let rec gather items =
    if cursor.index >= closer_index then List.rev items
    else
      let start = cursor.index in
      let value =
        match
          cursor.after_inserted_closer <- false;
          let value = parse_item cursor in
          let ends_with_comma =
            match find_previous_token cursor with
            | Some { kind = Punctuation Comma; _ } -> true
            | _ -> false
          in
          let separated =
            peek_kind cursor = Newline || (ends_with_comma && (peek cursor).line_break_before)
          in
          if cursor.index < closer_index && not separated then fail cursor Line_break_or_brace;
          value
        with
        | value -> value
        | exception Failed ->
            skip_line cursor ~closer_index;
            recover (make_span_from cursor start)
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
    syntax_errors =
      List.sort_uniq compare (List.map (make_definition_span cursor) !(cursor.syntax_errors));
  }
