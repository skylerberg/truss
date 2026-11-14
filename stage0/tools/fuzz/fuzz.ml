(* Fuzzing the lexer. This is a tool, not a test: run it by hand to look for
   inputs that break the lexer, and turn each one it finds into a focused
   test.

     dune exec stage0/tools/fuzz/fuzz.exe -- [--seed N] [--count N] FILE...

   The files are Markdown documents; their ```truss blocks are the inputs it
   mutates. It checks that:

   - no input raises, every span of a token, a string's piece, or a
     diagnostic is in bounds, no two tokens overlap, and brackets are
     balanced;
   - for one mistake made in an example, every fix removes its diagnostic
     and adds no other, and the lexer's tokens equal those of the text one
     of its fixes writes;
   - valid tokens printed with spaces between them lex back to the same
     tokens;
   - the parser never raises, every span in a tree is in bounds and inside
     the node around it, and no two expressions share an id;
   - for one mistake made in an example, every fix of the lexer's or
     the parser's removes its diagnostic and adds no other;
   - the parser and the reference grammar accept and reject the same pieces
     of mutated examples.

   It prints each failing input and exits with status 1 if there was one. *)

open Token

let failures = ref 0

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      if !failures <= 50 then print_endline message)
    format

let lex text = Lexer.lex (Source.create ~path:"fuzz.truss" text)

let rec check_tokens text ~start ~stop (tokens : Token.t array) =
  let quoted = Diagnostic.quote text in
  let length = Array.length tokens in
  if length = 0 || tokens.(length - 1).kind <> End_of_file then fail "no End_of_file in %s" quoted;
  (* Each span starts at or after the end of the one before, so no byte of
     the source belongs to two tokens. *)
  let check_spans ~start ~stop spans =
    ignore
      (List.fold_left
         (fun previous_stop (span : span) ->
           if span.start < start || span.stop > stop then fail "span out of bounds in %s" quoted
           else if span.start < previous_stop then fail "spans overlap in %s" quoted;
           span.stop)
         start spans)
  in
  check_spans ~start ~stop (Array.to_list (Array.map (fun (token : Token.t) -> token.span) tokens));
  let stack = ref [] in
  Array.iter
    (fun (token : Token.t) ->
      match token.kind with
      | Punctuation (Open bracket) -> stack := bracket :: !stack
      | Punctuation (Close bracket) -> (
          match !stack with
          | top :: rest when top = bracket -> stack := rest
          | _ -> fail "unbalanced brackets in %s" quoted)
      | String literal ->
          check_spans ~start:token.span.start ~stop:token.span.stop
            (literal.first.span
            :: List.concat_map
                 (fun ((interpolation : interpolation), (text : text)) ->
                   [ interpolation.span; text.span ])
                 (Array.to_list literal.rest));
          Array.iter
            (fun (interpolation : interpolation) ->
              check_tokens text ~start:interpolation.span.start ~stop:interpolation.span.stop
                interpolation.tokens)
            (interpolations literal)
      | _ -> ())
    tokens;
  if !stack <> [] then fail "unbalanced brackets in %s" quoted

(* Every span a diagnostic gives, its own, its notes', and its fixes' edits',
   is in bounds. *)
let check_diagnostic_spans text (diagnostic : Diagnostic.t) =
  let spans =
    (diagnostic.span :: List.map fst diagnostic.notes)
    @ List.concat_map
        (fun (fix : Diagnostic.span Diagnostic.fix) ->
          List.map (fun (edit : Diagnostic.span Diagnostic.edit) -> edit.span) fix.edits)
        diagnostic.fixes
  in
  if List.exists (fun (span : Diagnostic.span) -> span.stop > String.length text) spans then
    fail "a span of %s is out of bounds in %s"
      (Diagnostic.Code.name diagnostic.code)
      (Diagnostic.quote text)

let check_robust text =
  match lex text with
  | exception exception_ ->
      fail "raised %s on %s" (Printexc.to_string exception_) (Diagnostic.quote text)
  | tokens, diagnostics ->
      check_tokens text ~start:0 ~stop:(String.length text) tokens;
      List.iter (check_diagnostic_spans text) diagnostics

(* An example lexed and parsed piece by piece, as the documents' tests do. *)
let snippet text =
  let source = Source.create ~path:"fuzz.truss" text in
  let tokens, lexer_diagnostics = Lexer.lex source in
  let items, parser_diagnostics = Reference.Snippet.parse source tokens in
  (tokens, items, lexer_diagnostics @ parser_diagnostics)

let check_tree text (item : Syntax.definition Syntax.item) =
  let quoted = Diagnostic.quote text in
  let contains_span (outer : Syntax.span) (inner : Syntax.span) =
    outer.start <= inner.start && inner.stop <= outer.stop
  in
  let ids = Hashtbl.create 64 in
  let rec expression (outer : Syntax.span) (value : Syntax.expression) =
    if not (contains_span outer value.span) then
      fail "an expression's span is outside its parent in %s" quoted;
    if Hashtbl.mem ids value.id then fail "an id repeats in %s" quoted;
    Hashtbl.replace ids value.id ();
    if value.id >= item.value.id then fail "an id is not before its definition's in %s" quoted;
    let previous = ref value.span.start in
    Syntax_walk.children
      (fun (inner : Syntax.expression) ->
        if inner.span.start < !previous then fail "expressions out of order in %s" quoted;
        previous := inner.span.start;
        expression value.span inner)
      value
  in
  if item.value.span.start <> 0 || item.value.span.stop > String.length item.text then
    fail "a definition's span is out of bounds in %s" quoted;
  List.iter
    (fun (span : Syntax.span) ->
      if span.stop > String.length item.text then fail "a recovery is out of bounds in %s" quoted)
    item.value.recovered;
  Syntax_walk.definition (expression item.value.span) item.value

let check_parse_robust text =
  let source = Source.create ~path:"fuzz.truss" text in
  match
    let tokens, _ = Lexer.lex source in
    (Parser.parse source tokens, snippet text)
  with
  | exception exception_ ->
      fail "the parser raised %s on %s" (Printexc.to_string exception_) (Diagnostic.quote text)
  | (file, diagnostics), _ ->
      List.iter (check_tree text) file.definitions;
      List.iter (check_diagnostic_spans text) diagnostics

(* A parser diagnostic's claim about the reference grammar: that it
   rejects the tokens, that it accepts them because the rule is checked
   after parsing, or nothing. The grammar accepts any name where a cost word
   goes, and reads a string as one token, so it cannot check either. *)
type verdict = Grammar_rejects | Grammar_accepts | Unknown

let verdict : Diagnostic.Code.t -> verdict = function
  | Parser
      ( Unexpected_token | Needs_parentheses | Reserved_word | Statement_at_top_level | Missing_body
      | Open_range | Float_pattern | Increment | Double_negation | Match_arm_comma
      | Conditional_operator | Let_mut | Address_of | Closure_bars | Brace_record | Turbofish
      | Trailing_lambda | As_conversion | Elif | Angle_brackets | Path_separator | Qualified_variant
      | Macro_call | Tuple | Power_operator | Short_declaration | Pipe_operator | Lambda_annotation
      | Impl_parameters | Null_coalescing ) ->
      Grammar_rejects
  | Parser (Cost_word | Misplaced_potential | Interpolation_not_allowed) -> Unknown
  | Parser
      ( Use_after_definition | Let_else_brace | Nesting_too_deep | Misplaced_opaque
      | Misplaced_visibility | Misplaced_self | Lends_own | Repeated_clause | Finite_not_time
      | Loop_cost_bound | Function_type_names | Misplaced_requires | Specification_only
      | Misplaced_assert | Misplaced_proof | Misplaced_loop_exit | Exits_parallel
      | Echo_in_specification | Reserved_specification_name )
  | Lexer _ | Resolve _ | Package _ | Prover _ | Capabilities _ | Ownership _ | Usage _ | Patterns _
  | Types _ | Too_many_diagnostics ->
      Grammar_accepts

(* Each piece of an example, as the parser split it, is rejected by the
   parser exactly when the reference grammar rejects it. Errors inside an
   interpolation are left out: the grammar reads a string as one token. *)
let check_parsers_agree text =
  let tokens, items, diagnostics = snippet text in
  let interpolations =
    Array.to_list tokens
    |> List.concat_map (fun (token : Token.t) ->
        match token.kind with
        | String literal ->
            List.map
              (fun (inner : interpolation) -> inner.span)
              (Array.to_list (interpolations literal))
        | _ -> [])
  in
  let inside_interpolation (span : Source.span) =
    List.exists
      (fun (inner : Source.span) -> inner.start <= span.start && span.start < inner.stop)
      interpolations
  in
  List.iter
    (fun (item : Reference.Snippet.item) ->
      let start = tokens.(item.first).span.start and stop = tokens.(item.stop - 1).span.stop in
      (* Whether a position is in a [cost] clause, where the grammar's rule
         takes any names, so that its structure depends on their spelling. *)
      let in_cost_clause offset =
        let rec back index =
          if index < item.first then false
          else
            let token = tokens.(index) in
            if token.span.start > offset then back (index - 1)
            else
              match token.kind with
              | Keyword Cost -> true
              | Keyword (Uses | Requires | Ensures | Decreases | Invariant | Derives)
              | Punctuation (Open Curly)
              | Newline ->
                  false
              | _ -> back (index - 1)
        in
        back (item.stop - 1)
      in
      let verdicts =
        List.filter_map
          (fun (diagnostic : Diagnostic.t) ->
            if
              start <= diagnostic.span.start && diagnostic.span.start <= stop
              && not (inside_interpolation diagnostic.span)
            then
              Some
                (if in_cost_clause diagnostic.span.start then Unknown else verdict diagnostic.code)
            else None)
          diagnostics
      in
      let parser_rejects = List.mem Grammar_rejects verdicts in
      let slice = Array.to_list (Array.sub tokens item.first (item.stop - item.first)) in
      (* The parser reports nothing missing before a closer the lexer
         inserted, which already has its error. *)
      if
        (not (List.mem Unknown verdicts))
        && not
             (List.exists
                (fun (token : Token.t) ->
                  token.span.start = token.span.stop && token.kind <> End_of_file)
                slice)
      then
        let reference_rejects = not (Reference.accepts (Reference.Snippet.entry item.kind) slice) in
        if parser_rejects <> reference_rejects then
          fail "the parser %s and the reference grammar %s tokens %d to %d of %s"
            (if parser_rejects then "rejects" else "accepts")
            (if reference_rejects then "rejects" else "accepts")
            item.first item.stop (Diagnostic.quote text))
    items

(* Applying a fix removes its diagnostic and adds no other: the remaining
   diagnostics are the others, or fewer. *)
let check_fixes_work text =
  let all text =
    let _, _, diagnostics = snippet text in
    diagnostics
  in
  (* A lexer's fix is judged by the lexer alone: it can bring back a parser
     error that a closer the lexer inserted was hiding. *)
  let codes ~lexer_only text =
    List.sort compare
      (List.filter_map
         (fun (diagnostic : Diagnostic.t) ->
           match diagnostic.code with
           | Lexer _ -> Some diagnostic.code
           | _ when lexer_only -> None
           | _ -> Some diagnostic.code)
         (all text))
  in
  List.iter
    (fun (diagnostic : Diagnostic.t) ->
      let lexer_only = match diagnostic.code with Lexer _ -> true | _ -> false in
      let before = codes ~lexer_only text in
      let codes = codes ~lexer_only in
      List.iter
        (fun (fix : Diagnostic.span Diagnostic.fix) ->
          let rec remove_one = function
            | [] -> []
            | code :: rest -> if code = diagnostic.code then rest else code :: remove_one rest
          in
          let rec contained smaller larger =
            match (smaller, larger) with
            | [], _ -> true
            | _ :: _, [] -> false
            | first :: rest, candidate :: larger_rest ->
                if first = candidate then contained rest larger_rest
                else if first > candidate then contained smaller larger_rest
                else false
          in
          match Diagnostic.apply_fix text fix with
          | exception Invalid_argument _ ->
              fail "the fix %S has overlapping edits in %s" fix.title (Diagnostic.quote text)
          | fixed ->
              if not (contained (codes fixed) (remove_one before)) then
                fail "the fix %S for %s leaves or adds an error in %s" fix.title
                  (Diagnostic.Code.name diagnostic.code)
                  (Diagnostic.quote text))
        diagnostic.fixes)
    (all text)

(* The lexer recovers from a mistake by lexing the text that a fix of the
   mistake writes: its tokens are the tokens of the fixed text, up to
   offsets. Recovery that reads the text any other way gives the parser
   tokens that no fixed program has, so the parser reports errors that the
   fix would not leave.

   Two exceptions are left out. An unclosed bracket's fix closes it where
   the indentation says it was meant to close, which can be before tokens
   that layout has already emitted, so layout inserts its closer later:
   before the next definition, or at the end of the file. And a string is
   compared by its tag and form alone: the fix of a format string of
   another language, such as `f"{name}"`, rewrites its text into
   interpolations, and recovery keeps the text as written. *)
let check_recovery_matches_fix text =
  let nowhere = Source.zero_width 0 in
  let without_spans (token : Token.t) =
    let kind =
      match token.kind with
      | String literal ->
          String
            {
              tag = Option.map (fun (tag, _) -> (tag, nowhere)) literal.tag;
              form = literal.form;
              first = { value = ""; span = nowhere };
              rest = [||];
            }
      | kind -> kind
    in
    { token with kind; span = nowhere }
  in
  (* The first token has no token before it, so the line breaks before it,
     which a fix that removes the file's first lines removes, separate
     nothing. *)
  let shape text =
    let tokens, diagnostics = lex text in
    ( Array.mapi
        (fun index token ->
          let token = without_spans token in
          if index = 0 then { token with line_break_before = false; blank_line_before = false }
          else token)
        tokens,
      diagnostics )
  in
  let tokens, diagnostics = shape text in
  List.iter
    (fun (diagnostic : Diagnostic.t) ->
      if
        diagnostic.fixes <> []
        && diagnostic.code <> Lexer Unclosed_bracket
        && not
             (List.exists
                (fun fix ->
                  (* [check_fixes_work] reports a fix whose edits overlap. *)
                  match Diagnostic.apply_fix text fix with
                  | exception Invalid_argument _ -> true
                  | fixed -> fst (shape fixed) = tokens)
                diagnostic.fixes)
      then
        fail "the lexer recovers from %s other than as its fix writes in %s"
          (Diagnostic.Code.name diagnostic.code)
          (Diagnostic.quote text))
    diagnostics

let mistakes =
  [|
    "\"";
    "\"\"\"";
    "$";
    "${";
    "}";
    "{";
    "(";
    ")";
    "[";
    "]";
    "\n";
    "\r";
    "\\";
    "'";
    "/*";
    "//";
    "#";
    ";";
    "0x";
    "1e";
    "_";
    "\xe2\x80\xae";
    "\xe2\x80\x8b";
    "\xff";
    "\x01";
    "===";
    "++";
    "@";
    "aB";
    "A_b";
    ",";
    ":";
    ".";
    "=";
    "=>";
    "|";
    "&";
    "?";
    "-";
    "..";
    " && ";
    " || ";
    " == ";
    " < ";
    " + ";
    " << ";
    "let ";
    "mut ";
    "if ";
    "else ";
    "fn ";
    "match ";
    "return ";
    "forall x in s => ";
    "x";
    "Point";
    "as ";
    "loop ";
    "elif ";
    "{ it }";
    (* Strings of other languages, and Truss's raw strings. *)
    "r\"";
    "r#\"";
    "\"#";
    "b\"";
    "b'";
    "f\"";
    "@\"";
    "$\"";
    "`";
    "$$\"\"\"";
    "\"\"\"\n";
    "$${";
    "'a'";
    "'a";
    (* Escapes, which matter inside a string. *)
    "\\n";
    "\\u{";
    "\\u{1F600}";
    "\\u{D800}";
    "\\x41";
    (* Operators of other languages. *)
    "...";
    "..<";
    "<>";
    "!==";
    ":=";
    "|>";
    "**";
    "--";
    (* Numbers. *)
    "1.";
    ".5";
    "0b2";
    "1__0";
    "0X1";
    "1E5";
    "1u8";
    "99999999999999999999999";
    (* Comments and line breaks. *)
    "/* /* */";
    "*/";
    "\r\n";
    "\t";
    "\u{2028}";
    "\u{0085}";
    "\u{FEFF}";
    (* Characters that look like ASCII spaces or punctuation. *)
    "\u{00A0}";
    "\u{3000}";
    "\u{2003}";
    "\u{201C}";
    "\u{201D}";
    "\u{2018}";
    "\u{2019}";
    "\u{FF08}";
    "\u{FF09}";
    "\u{FF5B}";
    "\u{FF0C}";
    "\u{FF1D}";
    "\u{2013}";
    "\u{2264}";
    "\u{2260}";
    "\u{2192}";
    "\u{21D2}";
    "\u{2200}";
    (* Names outside ASCII: accented, decomposed, Greek, a Cyrillic letter
       that looks Latin, a ligature, and the ohm sign that NFC replaces. *)
    "caf\u{00E9}";
    "e\u{0301}";
    "\u{03BB}";
    "\u{0430}";
    "\u{FB01}";
    "\u{2126}";
  |]

let round_trip random =
  let pick array = array.(Random.State.int random (Array.length array)) in
  let names =
    [|
      ("count", Lower "count");
      ("user_name", Lower "user_name");
      ("Point", Upper "Point");
      ("O", Upper "O");
    |]
  in
  let others =
    Array.of_list
      (List.map (fun (spelling, keyword) -> (spelling, Keyword keyword)) Token.keywords
      @ List.map (fun (spelling, reserved) -> (spelling, Reserved reserved)) Token.reserved_words
      @ List.filter_map
          (fun (spelling, punctuation) ->
            match punctuation with
            | Open _ | Close _ -> None
            | _ -> Some (spelling, Punctuation punctuation))
          Token.punctuation)
  in
  let items =
    List.init
      (1 + Random.State.int random 30)
      (fun _ ->
        if Random.State.bool random then pick names
        else if Random.State.int random 4 = 0 then
          let value = Z.of_int (Random.State.bits random) in
          (Z.to_string value, Integer value)
        else pick others)
  in
  let text = String.concat " " (List.map fst items) in
  let tokens, diagnostics = lex text in
  if diagnostics <> [] then fail "diagnostics for valid tokens %s" (Diagnostic.quote text);
  let kinds =
    Array.to_list tokens
    |> List.map (fun (token : Token.t) -> token.kind)
    |> List.filter (fun kind -> kind <> Newline && kind <> End_of_file)
  in
  if kinds <> List.map snd items then
    fail "the tokens of %s do not round-trip" (Diagnostic.quote text)

let () =
  let seed = ref 0 and count = ref 10_000 and files = ref [] in
  Arg.parse
    [
      ("--seed", Arg.Set_int seed, " The random seed");
      ("--count", Arg.Set_int count, " How many inputs of each kind");
    ]
    (fun file -> files := file :: !files)
    "fuzz [--seed N] [--count N] FILE...";
  let random = Random.State.make [| !seed |] in
  let examples =
    Array.of_list
      (List.concat_map (fun file -> Documents.truss_blocks (Documents.read file)) !files)
  in
  if Array.length examples = 0 then (
    prerr_endline "fuzz: give Markdown files with ```truss blocks";
    exit 2);
  let example () = examples.(Random.State.int random (Array.length examples)) in
  (* Bytes at random, or characters at random: uniform bytes are almost
     never valid UTF-8 beyond one byte, so names and confusable characters
     outside ASCII need code points of their own. *)
  let random_text () =
    let length = Random.State.int random 120 in
    if Random.State.bool random then
      String.init length (fun _ -> Char.chr (Random.State.int random 256))
    else
      let buffer = Buffer.create length in
      for _ = 1 to length do
        let code_point =
          match Random.State.int random 4 with
          | 0 | 1 -> 0x20 + Random.State.int random 0x5F
          | 2 -> 0x80 + Random.State.int random (0x3000 - 0x80)
          | _ -> Random.State.int random 0x110000
        in
        if Uchar.is_valid code_point then Buffer.add_utf_8_uchar buffer (Uchar.of_int code_point)
      done;
      Buffer.contents buffer
  in
  (* One mistake: a range of the text replaced by a mistake from the list,
     by a piece of another example, or by nothing. An empty range makes it
     an insertion. *)
  let mutate text =
    let length = String.length text in
    let at = Random.State.int random (length + 1) in
    let removed =
      if Random.State.bool random then 0 else min (length - at) (1 + Random.State.int random 8)
    in
    let piece =
      match Random.State.int random 6 with
      | 0 when removed > 0 -> ""
      | 1 ->
          let other = example () in
          let start = Random.State.int random (String.length other + 1) in
          String.sub other start (min (String.length other - start) (Random.State.int random 40))
      | _ -> mistakes.(Random.State.int random (Array.length mistakes))
    in
    String.sub text 0 at ^ piece ^ String.sub text (at + removed) (length - at - removed)
  in
  for _ = 1 to !count do
    check_robust (random_text ());
    let several = ref (example ()) in
    for _ = 1 to 1 + Random.State.int random 4 do
      several := mutate !several
    done;
    check_robust !several;
    check_parse_robust !several;
    check_parsers_agree !several;
    let one = mutate (example ()) in
    check_fixes_work one;
    check_recovery_matches_fix one;
    round_trip random
  done;
  if !failures > 0 then begin
    Printf.printf "%d failures\n" !failures;
    exit 1
  end
  else Printf.printf "%d inputs of each kind pass\n" !count
