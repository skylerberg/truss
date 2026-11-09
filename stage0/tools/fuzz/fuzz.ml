(* Fuzzing the lexer. This is a tool, not a test: run it by hand to look for
   inputs that break the lexer, and turn each one it finds into a focused
   test. See IMPLEMENTATION.md, "Testing".

     dune exec stage0/tools/fuzz/fuzz.exe -- [--seed N] [--count N] FILE...

   The files are Markdown documents; their ```truss blocks are the inputs it
   mutates. It checks that:

   - no input raises, every token and diagnostic span is in bounds and in
     order, and brackets are balanced;
   - for one mistake inserted into an example, every fix removes its
     diagnostic and adds no other;
   - valid tokens printed with spaces between them lex back to the same
     tokens;
   - the parser never raises, and every span in a tree is in bounds and
     inside the node around it;
   - for one mistake inserted into an example, every fix of the lexer's or
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

(* Robustness *)

let rec check_tokens text ~start ~stop (tokens : Token.t array) =
  let quoted = Diagnostic.quote text in
  let length = Array.length tokens in
  if length = 0 || tokens.(length - 1).kind <> End_of_file then fail "no End_of_file in %s" quoted;
  let stack = ref [] and previous = ref start in
  Array.iter
    (fun (token : Token.t) ->
      if token.span.start < start || token.span.stop > stop then
        fail "span out of bounds in %s" quoted;
      if token.span.start < !previous then fail "tokens out of order in %s" quoted;
      previous := token.span.start;
      match token.kind with
      | Punctuation (Open bracket) -> stack := bracket :: !stack
      | Punctuation (Close bracket) -> (
          match !stack with
          | top :: rest when top = bracket -> stack := rest
          | _ -> fail "unbalanced brackets in %s" quoted)
      | String literal ->
          Array.iter
            (fun (interpolation : interpolation) ->
              check_tokens text ~start:interpolation.span.start ~stop:interpolation.span.stop
                interpolation.tokens)
            (interpolations literal)
      | _ -> ())
    tokens;
  if !stack <> [] then fail "unbalanced brackets in %s" quoted

let check_robust text =
  match lex text with
  | exception exception_ ->
      fail "raised %s on %s" (Printexc.to_string exception_) (Diagnostic.quote text)
  | tokens, diagnostics ->
      check_tokens text ~start:0 ~stop:(String.length text) tokens;
      List.iter
        (fun (d : Diagnostic.t) ->
          if d.span.stop > String.length text then
            fail "diagnostic out of bounds in %s" (Diagnostic.quote text))
        diagnostics

(* Parsing *)

(* An example lexed and parsed piece by piece, as the documents' tests do. *)
let snippet text =
  let source = Source.create ~path:"fuzz.truss" text in
  let tokens, lexer_diagnostics = Lexer.lex source in
  let items, parser_diagnostics = Parser.Snippet.parse source tokens in
  (tokens, items, lexer_diagnostics @ parser_diagnostics)

let check_tree text (item : Syntax.definition Syntax.item) =
  let quoted = Diagnostic.quote text in
  let within (outer : Syntax.span) (inner : Syntax.span) =
    outer.start <= inner.start && inner.stop <= outer.stop
  in
  let rec expression (outer : Syntax.span) (value : Syntax.expression) =
    if not (within outer value.span) then
      fail "an expression's span is outside its parent in %s" quoted;
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
      List.iter
        (fun (d : Diagnostic.t) ->
          if d.span.stop > String.length text then
            fail "a parser diagnostic is out of bounds in %s" (Diagnostic.quote text))
        diagnostics

(* What a parser diagnostic says about the reference grammar: that it
   rejects the tokens, that it accepts them because the rule is checked
   after parsing, or nothing. The grammar accepts any name where a cost word
   goes, and reads a string as one token, so it cannot check either. *)
type verdict = Grammar_rejects | Grammar_accepts | Unknown

let verdict : Diagnostic.Code.t -> verdict = function
  | Parser
      ( Unexpected_token | Needs_parentheses | Reserved_word | Statement_at_top_level | Missing_body
      | Open_range | Increment | Double_negation | Match_arm_comma | Conditional_operator | Let_mut
      | Address_of | Closure_bars | Brace_record | Turbofish | Trailing_lambda | As_conversion
      | Elif ) ->
      Grammar_rejects
  | Parser (Cost_word | Misplaced_potential | Interpolation_not_allowed) -> Unknown
  | Parser
      ( Use_after_definition | Let_else_brace | Nesting_too_deep | Misplaced_opaque
      | Misplaced_visibility | Misplaced_self | Repeated_clause | Finite_not_time
      | Specification_only | Misplaced_assert | Misplaced_proof | Misplaced_yield
      | Misplaced_loop_exit | Leaves_parallel | Echo_in_proof | Reserved_name )
  | Lexer _ | Too_many_diagnostics ->
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
    (fun (item : Parser.Snippet.item) ->
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
          (fun (d : Diagnostic.t) ->
            if start <= d.span.start && d.span.start <= stop && not (inside_interpolation d.span)
            then Some (if in_cost_clause d.span.start then Unknown else verdict d.code)
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
        let reference_rejects = not (Reference.accepts (Reference.entry item.kind) slice) in
        if parser_rejects <> reference_rejects then
          fail "the parser %s and the reference grammar %s tokens %d to %d of %s"
            (if parser_rejects then "rejects" else "accepts")
            (if reference_rejects then "rejects" else "accepts")
            item.first item.stop (Diagnostic.quote text))
    items

(* Fixes for single mistakes *)

(* Applying a fix removes its diagnostic and adds no other: what is left is
   the other diagnostics, or fewer. *)
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
         (fun (d : Diagnostic.t) ->
           match d.code with Lexer _ -> Some d.code | _ when lexer_only -> None | _ -> Some d.code)
         (all text))
  in
  List.iter
    (fun (diagnostic : Diagnostic.t) ->
      let lexer_only = match diagnostic.code with Lexer _ -> true | _ -> false in
      let before = codes ~lexer_only text in
      let codes = codes ~lexer_only in
      List.iter
        (fun (fix : Diagnostic.fix) ->
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
  |]

(* Round trips *)

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
    |> List.map (fun (t : Token.t) -> t.kind)
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
  let insert text piece =
    let at = Random.State.int random (String.length text + 1) in
    String.sub text 0 at ^ piece ^ String.sub text at (String.length text - at)
  in
  for _ = 1 to !count do
    check_robust
      (String.init (Random.State.int random 120) (fun _ -> Char.chr (Random.State.int random 256)));
    let several = ref (example ()) in
    for _ = 1 to 1 + Random.State.int random 4 do
      several := insert !several mistakes.(Random.State.int random (Array.length mistakes))
    done;
    check_robust !several;
    check_parse_robust !several;
    check_parsers_agree !several;
    check_fixes_work
      (insert (example ()) mistakes.(Random.State.int random (Array.length mistakes)));
    round_trip random
  done;
  if !failures > 0 then begin
    Printf.printf "%d failures\n" !failures;
    exit 1
  end
  else Printf.printf "%d inputs of each kind pass\n" !count
