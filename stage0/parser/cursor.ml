(* Reading one definition's tokens, or one interpolation's: the current
   token, lookahead, and the jumps error recovery makes. See PARSER.md,
   "Parsing one definition" and "Recovery".

   A parsing function that cannot go on reports one error with [fail], which
   raises [Failed]. The nearest place that can recover catches it, skips to
   where parsing can go on, and builds an [Error] node, so nothing in the
   skipped region is reported. *)

open Token

exception Failed

type t = {
  tokens : Token.t array;
  first : int;  (** The index of the slice's first token. *)
  stop : int;  (** One past the index of its last token. *)
  base : int;  (** The absolute offset spans in the tree are relative to. *)
  closers : int array;  (** For each opener in the slice, the index of its closer; otherwise -1. *)
  source : Source.t;
  diagnostics : Diagnostic.Collector.t;
  mutable index : int;
  mutable depth : int;  (** Expressions, types, patterns, and prefix operators being parsed. *)
  mutable cut_off : bool;
      (** The current item has consumed a closer the lexer inserted, so what follows in it is not
          what the author wrote, and no more syntax errors are reported in it. *)
  mutable line_ended : bool;
      (** A habit consumed a token, such as the [,] after a [match] arm, that kept the lexer from
          ending the line, so the next token starts a new item. *)
}

(* Nesting is limited, so that hostile input cannot make the parser, or any
   later stage that walks the tree, recurse without bound, as the lexer
   limits interpolations. The parser counts each expression, type, pattern,
   and prefix operator it is inside, since every way it recurses goes
   through one of them. *)
let nesting_limit = 256

let compute_closers tokens ~first ~stop =
  let closers = Array.make (stop - first) (-1) in
  let stack = ref [] in
  for index = first to stop - 1 do
    match tokens.(index).kind with
    | Punctuation (Open _) -> stack := index :: !stack
    | Punctuation (Close _) -> (
        match !stack with
        | opener :: rest ->
            closers.(opener - first) <- index;
            stack := rest
        | [] -> ())
    | _ -> ()
  done;
  closers

let create ~source ~diagnostics ~base tokens ~first ~stop =
  {
    tokens;
    first;
    stop;
    base;
    closers = compute_closers tokens ~first ~stop;
    source;
    diagnostics;
    index = first;
    depth = 0;
    cut_off = false;
    line_ended = false;
  }

(* A cursor over other tokens, such as an interpolation's, up to [stop],
   that reports to the same diagnostics with the same base, at the same
   depth. *)
let over ?stop cursor tokens =
  let stop = Option.value stop ~default:(Array.length tokens) in
  let inner =
    create ~source:cursor.source ~diagnostics:cursor.diagnostics ~base:cursor.base tokens ~first:0
      ~stop
  in
  inner.depth <- cursor.depth;
  inner

(* The end of the slice reads as an End_of_file token, zero-width, just after
   the slice's last token. *)
let end_token cursor =
  let position =
    if cursor.stop > cursor.first then cursor.tokens.(cursor.stop - 1).span.stop else cursor.base
  in
  {
    kind = End_of_file;
    span = Source.zero_width position;
    line_break_before = false;
    blank_line_before = false;
  }

let token_at cursor index = if index < cursor.stop then cursor.tokens.(index) else end_token cursor
let peek cursor = token_at cursor cursor.index
let peek_kind cursor = (peek cursor).kind
let peek_ahead cursor count = (token_at cursor (cursor.index + count)).kind

let advance cursor =
  if cursor.index < cursor.stop then begin
    let token = cursor.tokens.(cursor.index) in
    (match token.kind with
    | Punctuation (Close _) when token.span.start = token.span.stop -> cursor.cut_off <- true
    | _ -> ());
    cursor.index <- cursor.index + 1
  end

let next cursor =
  let token = peek cursor in
  advance cursor;
  token

let at_end cursor = cursor.index >= cursor.stop
let is cursor kind = peek_kind cursor = kind
let is_punctuation cursor punctuation = is cursor (Punctuation punctuation)
let is_keyword cursor keyword = is cursor (Keyword keyword)

let accept cursor kind =
  if is cursor kind then begin
    advance cursor;
    true
  end
  else false

let accept_punctuation cursor punctuation = accept cursor (Punctuation punctuation)
let accept_keyword cursor keyword = accept cursor (Keyword keyword)

(* Positions *)

let relative cursor offset = offset - cursor.base

let span cursor (span : Source.span) =
  Syntax.Span.make (relative cursor span.start) (relative cursor span.stop)

(* The end of the token before the current one, which is where a node that
   ends here stops. *)
let previous_stop cursor =
  if cursor.index > cursor.first then cursor.tokens.(cursor.index - 1).span.stop else cursor.base

(* The span from the start of the token at [start_index] to the end of the
   last token consumed. *)
let span_from cursor start_index =
  let start = (token_at cursor start_index).span.start in
  let stop = max start (previous_stop cursor) in
  Syntax.Span.make (relative cursor start) (relative cursor stop)

let absolute cursor (span : Syntax.span) =
  Source.span (span.start + cursor.base) (span.stop + cursor.base)

let text cursor (span : Source.span) =
  String.sub (Source.text cursor.source) span.start (span.stop - span.start)

(* A closer the lexer inserted for an unclosed opener already has its error,
   so the parser reports nothing that is missing before it. *)
let inserted_closer (token : Token.t) =
  match token.kind with Punctuation (Close _) -> token.span.start = token.span.stop | _ -> false

(* Diagnostics *)

let report cursor ?notes ?fixes code span message =
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

(* Reports that the current token is not what [expected] describes, unless it
   is a closer the lexer inserted, and raises [Failed]. *)
let fail cursor expected =
  let token = peek cursor in
  (match token.kind with
  | _ when inserted_closer token || cursor.cut_off -> ()
  | Reserved reserved ->
      report cursor Reserved_word token.span
        (Printf.sprintf "`%s` is reserved for possible later use, and means nothing in Truss yet"
           (reserved_spelling reserved))
  | _ ->
      report cursor Unexpected_token token.span
        (Printf.sprintf "expected %s, found %s" expected (describe token)));
  raise Failed

let expect cursor kind expected = if not (accept cursor kind) then fail cursor expected

let expect_punctuation cursor punctuation =
  expect cursor (Punctuation punctuation) (Printf.sprintf "`%s`" (punctuation_spelling punctuation))

let expect_keyword cursor keyword =
  expect cursor (Keyword keyword) (Printf.sprintf "`%s`" (keyword_spelling keyword))

(* Nesting *)

let nested cursor parse =
  if cursor.depth >= nesting_limit then begin
    report cursor Nesting_too_deep (peek cursor).span
      (Printf.sprintf "this is nested more than %d levels deep" nesting_limit);
    raise Failed
  end;
  cursor.depth <- cursor.depth + 1;
  match parse cursor with
  | value ->
      cursor.depth <- cursor.depth - 1;
      value
  | exception exception_ ->
      cursor.depth <- cursor.depth - 1;
      raise exception_

(* Recovery *)

let closer cursor index =
  if index >= cursor.first && index < cursor.stop then cursor.closers.(index - cursor.first) else -1

(* Skips to the token at [limit]. *)
let skip_to cursor limit =
  while cursor.index < min limit cursor.stop do
    advance cursor
  done

(* Moves past one token, or past a whole bracketed group if the token opens
   one. *)
let skip_one cursor =
  let closer_index = closer cursor cursor.index in
  if closer_index >= 0 then skip_to cursor (closer_index + 1) else advance cursor

(* Skips to the next [Newline] outside any bracket opened after the current
   position, or to [limit], the index of the enclosing closer. *)
let skip_line cursor ~limit =
  while cursor.index < limit && cursor.index < cursor.stop && peek_kind cursor <> Newline do
    skip_one cursor
  done

(* A comma-separated list in brackets, which may be empty and may end with a
   comma; the current token is the opener. An error in an item skips to the
   closer, and [recover] makes the item that stands for the rest, from the
   span it covered. *)
let bracketed cursor ~item ~recover =
  (fun cursor ->
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
            let span =
              span cursor
                (Source.span (token_at cursor start).span.start
                   (token_at cursor closer_index).span.start)
            in
            List.rev (recover span :: items)
    in
    let items = loop [] in
    skip_to cursor (closer_index + 1);
    items)
    cursor

(* Items separated by line breaks in braces, as statements, members, and
   arms are; the current token is the [{]. An error in an item skips to the
   end of its line, and [recover] makes the item that stands for it, from the
   index of its first token and the span it covered.

   [cut_off] and [line_ended] describe the item being parsed, so each
   item's starts clear, and the enclosing item's are back when the items
   end. The enclosing item is cut off too if its closing [}] is one the
   lexer inserted. *)
let lines cursor ~item ~recover =
  let enclosing_cut_off = cursor.cut_off and enclosing_line_ended = cursor.line_ended in
  (fun cursor ->
    let opener = cursor.index in
    let closer_index = closer cursor opener in
    advance cursor;
    let rec loop items =
      if cursor.index >= closer_index then List.rev items
      else
        let start = cursor.index in
        let value =
          match
            cursor.line_ended <- false;
            cursor.cut_off <- false;
            let value = item cursor in
            let separated =
              peek_kind cursor = Newline || (cursor.line_ended && (peek cursor).line_break_before)
            in
            if cursor.index < closer_index && not separated then fail cursor "a line break or `}`";
            value
          with
          | value -> value
          | exception Failed ->
              skip_line cursor ~limit:closer_index;
              recover start (span_from cursor start)
        in
        if cursor.index < closer_index && peek_kind cursor = Newline then advance cursor;
        loop (value :: items)
    in
    let items = loop [] in
    cursor.cut_off <- enclosing_cut_off;
    cursor.line_ended <- enclosing_line_ended;
    skip_to cursor (closer_index + 1);
    items)
    cursor

let blank_line_before cursor index = (token_at cursor index).blank_line_before
