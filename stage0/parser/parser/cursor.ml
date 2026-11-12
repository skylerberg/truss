(* A cursor over one definition's tokens, or one interpolation's: the
   current token, lookahead, and the skips that error recovery makes.

   A parsing function that cannot continue reports one error with [fail],
   which raises [Failed]. The nearest enclosing function that can recover
   catches it, skips to a synchronization point, and builds an [Error]
   node, so nothing in the skipped tokens is reported. *)

open Token

exception Failed

type t = {
  tokens : Token.t array;
  first : int;  (** The index of the slice's first token. *)
  stop : int;  (** One past the index of its last token. *)
  base : int;  (** The absolute offset spans in the tree are relative to. *)
  closers : int array;  (** For each opener in the slice, the index of its closer; otherwise -1. *)
  text : string;
      (** The definition's source text: the bytes from its first token to the end of its last. The
          cursor holds no other part of the file, so a parsing function cannot read outside the
          definition. *)
  diagnostics : Diagnostic.Collector.t;
  mutable index : int;
  mutable depth : int;  (** Expressions, types, patterns, and prefix operators being parsed. *)
  next_id : int ref;
      (** The id of the next node. The definition's interpolations and the second parse of a header
          that failed share the counter, so that ids are unique within the definition. *)
  recoveries : Source.span list ref;
      (** Where the parser recovered, in this definition and its interpolations, newest first. *)
  methods : (int * int) list ref;
      (** The methods declared inside this definition, each as the indexes of its first token and
          one past its last, newest first. Each is a separate definition, parsed with a cursor of
          its own. *)
  mutable after_inserted_closer : bool;
      (** The current item has consumed a closer the lexer inserted. The tokens after it in the item
          were not delimited by the author, so no more syntax errors are reported in it. *)
  mutable unterminated : bool;
      (** The tokens are an interpolation that a line break ended, an error the lexer already
          reported, so no missing token is reported at their end. *)
  mutable line_ended : bool;
      (** A habit consumed a token, such as the [,] after a [match] arm, after which the lexer emits
          no [Newline], so the next token starts a new item. *)
}

(* Nesting is limited, so that hostile input cannot make the parser, or any
   later stage that walks the tree, recurse without bound, as the lexer
   limits interpolations. The parser counts each expression, type, pattern,
   block, and prefix operator that encloses the current token, since every
   recursive call of a parsing function passes through one of them. *)
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

let create ~text ~diagnostics ~base tokens ~first ~stop =
  {
    tokens;
    first;
    stop;
    base;
    closers = compute_closers tokens ~first ~stop;
    text;
    diagnostics;
    index = first;
    depth = 0;
    next_id = ref 0;
    recoveries = ref [];
    methods = ref [];
    after_inserted_closer = false;
    unterminated = false;
    line_ended = false;
  }

(* A cursor over other tokens, such as an interpolation's, up to [stop],
   that reports to the same diagnostics with the same base, at the same
   depth. *)
let sub_cursor ?stop cursor tokens =
  let stop = Option.value stop ~default:(Array.length tokens) in
  let inner =
    create ~text:cursor.text ~diagnostics:cursor.diagnostics ~base:cursor.base tokens ~first:0 ~stop
  in
  inner.depth <- cursor.depth;
  { inner with recoveries = cursor.recoveries; next_id = cursor.next_id }

(* A cursor at the start of the same slice, whose diagnostics are
   discarded, for parsing a second time the header that an error left
   unparsed. *)
let restarted cursor =
  let restarted =
    create ~text:cursor.text ~diagnostics:(Diagnostic.Collector.create ()) ~base:cursor.base
      cursor.tokens ~first:cursor.first ~stop:cursor.stop
  in
  { restarted with next_id = cursor.next_id }

(* A new node's id. *)
let fresh_id cursor =
  let id = !(cursor.next_id) in
  cursor.next_id := id + 1;
  id

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

(* Records a recovery at the token at [index]. One with no width, at the
   end of the slice or at a closer the lexer inserted, would sit on the
   boundary after the part it is in, so it reaches back to the start of the
   token before it, which lies in that part. *)
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
    | Punctuation (Close _) when token.span.start = token.span.stop ->
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

(* These two are the parser's most frequent tests. They compare
   constructors, where [is] would compare two token kinds structurally. *)
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

(* Positions *)

let span cursor span = Syntax.Span.of_source ~base:cursor.base span

(* The end of the token before the current one, which is where a node that
   ends here stops. *)
let previous_stop cursor =
  if cursor.index > cursor.first then cursor.tokens.(cursor.index - 1).span.stop else cursor.base

(* The span from the start of the token at [start_index] to the end of the
   last token consumed. *)
let span_from cursor start_index =
  let start = (token_at cursor start_index).span.start in
  let stop = max start (previous_stop cursor) in
  span cursor (Source.span start stop)

let absolute cursor span = Syntax.Span.to_source ~base:cursor.base span

(* The source text under [span], which must lie in the definition. *)
let text cursor (span : Source.span) =
  String.sub cursor.text (span.start - cursor.base) (span.stop - span.start)

(* A closer the lexer inserted for an unclosed opener already has its error,
   so the parser reports nothing that is missing before it. *)
let inserted_closer (token : Token.t) =
  match token.kind with Punctuation (Close _) -> token.span.start = token.span.stop | _ -> false

(* Diagnostics *)

(* Whether a diagnostic means the parser recovered: that the source is not
   valid Truss, so the tree there is what the parser inferred, as opposed
   to valid syntax that breaks a rule checked after parsing. *)
let recovers : Diagnostic.Code.parser -> bool = function
  | Unexpected_token | Needs_parentheses | Reserved_word | Statement_at_top_level | Missing_body
  | Open_range | Interpolation_not_allowed | Float_pattern | Nesting_too_deep | Cost_word
  | Misplaced_potential | Increment | Double_negation | Match_arm_comma | Conditional_operator
  | Let_mut | Address_of | Closure_bars | Brace_record | Turbofish | Trailing_lambda | As_conversion
  | Elif | Angle_brackets | Path_separator | Qualified_variant | Macro_call | Tuple | Power_operator
  | Short_declaration | Pipe_operator | Lambda_annotation | Impl_parameters | Null_coalescing ->
      true
  | Use_after_definition | Let_else_brace | Misplaced_opaque | Misplaced_transparent
  | Misplaced_visibility | Misplaced_self | Lends_own | Repeated_clause | Finite_not_time
  | Loop_cost_bound | Function_type_names | Misplaced_requires | Specification_only
  | Misplaced_assert | Misplaced_proof | Misplaced_yield | Misplaced_loop_exit | Leaves_parallel
  | Echo_in_specification | Reserved_specification_name ->
      false

let report cursor ?notes ?fixes code span message =
  (match code with
  (* Where a body should be inserted, which belongs to the body that starts
     there, not to the signature before it. *)
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

(* Reports that the current token is not what [expected] describes, unless it
   is a closer the lexer inserted, and raises [Failed]. *)
let fail cursor expected =
  let token = peek cursor in
  (* Silent or not, a failure leaves the parser to recover. *)
  if
    inserted_closer token || cursor.after_inserted_closer
    || (token.kind = End_of_file && cursor.unterminated)
  then record_recovery cursor ~index:cursor.index token.span;
  (match token.kind with
  | _ when inserted_closer token || cursor.after_inserted_closer -> ()
  | End_of_file when cursor.unterminated -> ()
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

(* Nesting *)

let nested cursor parse =
  if cursor.depth >= nesting_limit then begin
    report cursor Nesting_too_deep (peek cursor).span
      (Printf.sprintf "This is nested more than %d levels deep." nesting_limit);
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

(* A chain is a run of operations that each take the result of the one
   before as an operand: binary operators at one level, as in [a + b + c],
   postfix operations, as in [a.b.c], and [else if] branches. The nesting
   limit does not count a chain's links, but each link nests the tree one
   level deeper, so a chain's length is limited too. [length] is the number
   of links the chain already has. *)
let chain_limit = 10_000

let check_chain_length cursor ~length =
  if length >= chain_limit then begin
    report cursor Nesting_too_deep (peek cursor).span
      (Printf.sprintf
         "This chains more than %d operations, each of which nests one level deeper. Give parts of \
          it names with `let`."
         chain_limit);
    raise Failed
  end

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
   next comma of the list, and [recover] builds the error item for it from
   the span it covered. *)
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
          (* The item becomes [recover] of what it covered, up to the next
             comma of this list, and the items after that comma are parsed,
             so that each invalid item gets an error of its own. *)
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

(* Items separated by line breaks in braces, as statements, members, and
   arms are; the current token is the [{]. An error in an item skips to the
   end of its line, and [recover] builds the error item for it from the
   index of its first token and the span it covered.

   [after_inserted_closer] and [line_ended] describe the item being parsed,
   so both are false when an item starts, and the enclosing item's values
   are restored after the last item. Consuming the closing [}] sets
   [after_inserted_closer] for the enclosing item if the lexer inserted
   that [}]. *)
let lines cursor ~item ~recover =
  let enclosing_after_inserted_closer = cursor.after_inserted_closer
  and enclosing_line_ended = cursor.line_ended in
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
          cursor.after_inserted_closer <- false;
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
  cursor.after_inserted_closer <- enclosing_after_inserted_closer;
  cursor.line_ended <- enclosing_line_ended;
  skip_to cursor (closer_index + 1);
  items

let blank_line_before cursor index = (token_at cursor index).blank_line_before
