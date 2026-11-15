open Token

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
  next_id : int ref;
  recoveries : Source.span list ref;
  mutable methods : Split.piece list;
  mutable after_inserted_closer : bool;
  is_unterminated_interpolation : bool;
  mutable skipped_trailing_comma : bool;
}

let nesting_limit = 256

let group_ends tokens ~first ~stop =
  let ends = Array.init (stop - first) (fun offset -> first + offset) in
  let openers = ref [] in
  for index = first to stop - 1 do
    match tokens.(index).kind with
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
    next_id = ref 0;
    recoveries = ref [];
    methods = [];
    after_inserted_closer = false;
    is_unterminated_interpolation = false;
    skipped_trailing_comma = false;
  }

let interpolation cursor (inner : Token.interpolation) =
  {
    (create ~diagnostics:cursor.diagnostics ~base:cursor.base inner.tokens ~first:0
       ~stop:(Array.length inner.tokens - 1))
    with
    nesting_depth = cursor.nesting_depth;
    recoveries = cursor.recoveries;
    next_id = cursor.next_id;
    is_unterminated_interpolation = not inner.is_closed;
  }

let index cursor = cursor.index

let fresh_id cursor =
  let id = !(cursor.next_id) in
  cursor.next_id := id + 1;
  id

let end_token cursor =
  let position =
    if cursor.stop > cursor.first then cursor.tokens.(cursor.stop - 1).span.stop else cursor.base
  in
  {
    kind = End_of_file;
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

let is_keyword cursor (keyword : keyword) =
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

let span cursor span = Source.Definition_span.of_file ~base:cursor.base span

let previous_token cursor =
  if cursor.index > cursor.first then Some cursor.tokens.(cursor.index - 1) else None

let previous_stop cursor =
  match previous_token cursor with Some token -> token.span.stop | None -> cursor.base

let span_from cursor start_index =
  let start = (token_at cursor start_index).span.start in
  let stop = max start (previous_stop cursor) in
  span cursor (Source.span start stop)

let absolute cursor span = Source.Definition_span.to_file ~base:cursor.base span

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

let recovers : Diagnostic.Code.parser -> bool = function
  | Unexpected_token | Needs_parentheses | Reserved_word | Statement_at_top_level | Missing_body
  | Open_range | Interpolation_not_allowed | Float_pattern | Nesting_too_deep | Cost_word
  | Misplaced_potential | Increment | Double_negation | Match_arm_comma | Conditional_operator
  | Let_mut | Address_of | Closure_bars | Brace_record | Turbofish | Trailing_lambda | As_conversion
  | Elif | Angle_brackets | Path_separator | Qualified_variant | Macro_call | Tuple | Power_operator
  | Short_declaration | Pipe_operator | Lambda_annotation | Impl_parameters | Null_coalescing ->
      true
  | Use_after_definition | Let_else_brace | Misplaced_opaque | Misplaced_visibility | Misplaced_self
  | Lends_own | Repeated_clause | Finite_not_time | Loop_cost_bound | Function_type_names
  | Misplaced_requires | Specification_only | Misplaced_assert | Misplaced_proof
  | Misplaced_loop_exit | Exits_parallel | Echo_in_specification | Reserved_specification_name ->
      false

let report cursor ?notes ?fixes code span message =
  (match code with
  | Diagnostic.Code.Missing_body -> cursor.recoveries := span :: !(cursor.recoveries)
  | _ when recovers code -> record_recovery cursor ~index:cursor.index span
  | _ -> ());
  Diagnostic.Collector.add cursor.diagnostics
    (Diagnostic.make ?notes ?fixes ~code:(Diagnostic.Code.Parser code) span message)

let describe (token : Token.t) =
  match token.kind with
  | Newline -> "a line break"
  | End_of_file -> "the end of the definition"
  | Upper name | Lower name -> Printf.sprintf "the name `%s`" name
  | Underscore -> "`_`"
  | Keyword keyword -> Printf.sprintf "`%s`" (keyword_spelling keyword)
  | Reserved reserved -> Printf.sprintf "`%s`" (reserved_spelling reserved)
  | Integer _ | Float _ -> "a number"
  | String _ -> "a string"
  | Punctuation punctuation -> Printf.sprintf "`%s`" (punctuation_spelling punctuation)
  | Foreign foreign -> Printf.sprintf "`%s`" (foreign_spelling foreign)

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
           (reserved_spelling reserved))
  | _ ->
      report cursor Unexpected_token token.span
        (Printf.sprintf "Expected %s, found %s." expected (describe token)));
  raise Failed

let expect_punctuation cursor punctuation =
  if not (accept_punctuation cursor punctuation) then
    fail cursor (Printf.sprintf "`%s`" (punctuation_spelling punctuation))

let expect_keyword cursor keyword =
  if not (accept_keyword cursor keyword) then
    fail cursor (Printf.sprintf "`%s`" (keyword_spelling keyword))

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

let skip_method cursor =
  let stop = Split.stop cursor.tokens ~first:cursor.index in
  cursor.methods <- { first = cursor.index; stop } :: cursor.methods;
  skip_to cursor stop

let skip_trailing_comma cursor =
  advance cursor;
  cursor.skipped_trailing_comma <- true

let is_after_inserted_closer cursor = cursor.after_inserted_closer

let skip_line cursor ~closer_index =
  while cursor.index < closer_index && cursor.index < cursor.stop && peek_kind cursor <> Newline do
    skip_one cursor
  done

let bracketed cursor ~item ~recover =
  let opener = cursor.index in
  let closer_index = closer cursor opener in
  advance cursor;
  let rec loop items =
    if cursor.index >= closer_index then List.rev items
    else
      let start = cursor.index in
      match
        let value = item cursor in
        if cursor.index < closer_index then expect_punctuation cursor Comma;
        value
      with
      | value -> loop (value :: items)
      | exception Failed ->
          while cursor.index < closer_index && peek_kind cursor <> Punctuation Comma do
            skip_one cursor
          done;
          let span =
            span cursor (Source.span (token_at cursor start).span.start (peek cursor).span.start)
          in
          if cursor.index < closer_index then advance cursor;
          loop (recover span :: items)
  in
  let items = loop [] in
  skip_to cursor (closer_index + 1);
  items

let lines cursor ~item ~recover =
  let enclosing_after_inserted_closer = cursor.after_inserted_closer
  and enclosing_skipped_trailing_comma = cursor.skipped_trailing_comma in
  let opener = cursor.index in
  let closer_index = closer cursor opener in
  advance cursor;
  let rec loop items =
    if cursor.index >= closer_index then List.rev items
    else
      let start = cursor.index in
      let value =
        match
          cursor.skipped_trailing_comma <- false;
          cursor.after_inserted_closer <- false;
          let value = item cursor in
          let separated =
            peek_kind cursor = Newline
            || (cursor.skipped_trailing_comma && (peek cursor).line_break_before)
          in
          if cursor.index < closer_index && not separated then fail cursor "a line break or `}`";
          value
        with
        | value -> value
        | exception Failed ->
            skip_line cursor ~closer_index;
            recover start (span_from cursor start)
      in
      if cursor.index < closer_index && peek_kind cursor = Newline then advance cursor;
      loop (value :: items)
  in
  let items = loop [] in
  cursor.after_inserted_closer <- enclosing_after_inserted_closer;
  cursor.skipped_trailing_comma <- enclosing_skipped_trailing_comma;
  skip_to cursor (closer_index + 1);
  items

let blank_line_before cursor index = (token_at cursor index).blank_line_before
let recovered cursor = List.sort_uniq compare (List.map (span cursor) !(cursor.recoveries))
let methods cursor = List.rev cursor.methods
