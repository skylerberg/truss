(* Fuzzing the lexer. This is a tool, not a test: run it by hand to look for
   inputs that break the lexer, and turn each one it finds into a focused
   test.

     dune exec stage0/tools/fuzz/fuzz.exe -- [--seed N] [--count N] PATH...

   Each path is a .truss file or a directory of them. Each top-level piece of
   each file, a definition or a `use` line, is an input it mutates. It checks
   that:

   - no input raises, every span of a token, a string's piece, or a
     diagnostic is in bounds, no two tokens overlap, and brackets are
     balanced;
   - for one mistake, every fix removes its diagnostic and adds no other,
     and for several, the lexer's machine-applicable fixes together remove
     theirs and add no other;
   - valid tokens printed with spaces between them lex back to the same
     tokens;
   - the parser never raises, every span in a tree is in bounds and inside
     the node around it, children are in source order where the parser did
     not recover, and no two expressions share an id;
   - the parser and the reference grammar accept and reject the same
     mutated inputs.

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

let parse text =
  let source = Source.create ~path:"fuzz.truss" text in
  let tokens, lexer_diagnostics = Lexer.lex source in
  let file, parser_diagnostics = Parser.parse source tokens in
  (tokens, file, lexer_diagnostics @ parser_diagnostics)

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
    (* A recovery may build the node a habit's fix writes, out of source order. *)
    let holds_recovery =
      List.exists (fun recovery -> contains_span value.span recovery) item.value.recovered
    in
    let previous = ref value.span.start in
    Syntax_walk.children
      (fun (inner : Syntax.expression) ->
        if inner.span.start < !previous && not holds_recovery then
          fail "expressions out of order in %s" quoted;
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
  match parse text with
  | exception exception_ ->
      fail "the parser raised %s on %s" (Printexc.to_string exception_) (Diagnostic.quote text)
  | _, file, diagnostics ->
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

(* The parser rejects an input exactly when the reference grammar does.
   Errors inside an interpolation are left out: the grammar reads a string
   as one token. *)
let check_parsers_agree text =
  let tokens, _, diagnostics = parse text in
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
  (* Whether a position is in a [cost] clause, where the grammar's rule takes
     any names. *)
  let in_cost_clause offset =
    let rec back index =
      if index < 0 then false
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
    back (Array.length tokens - 1)
  in
  let verdicts =
    List.filter_map
      (fun (diagnostic : Diagnostic.t) ->
        if inside_interpolation diagnostic.span then None
        else if in_cost_clause diagnostic.span.start then Some Unknown
        else Some (verdict diagnostic.code))
      diagnostics
  in
  let all = Array.to_list tokens in
  (* The parser reports nothing missing before a closer the lexer inserted,
     which already has its error. *)
  if
    (not (List.mem Unknown verdicts))
    && not
         (List.exists
            (fun (token : Token.t) ->
              token.span.start = token.span.stop && token.kind <> End_of_file)
            all)
  then
    let parser_rejects = List.mem Grammar_rejects verdicts
    and reference_rejects = not (Reference.accepts Reference.file all) in
    if parser_rejects <> reference_rejects then
      fail "the parser %s and the reference grammar %s %s"
        (if parser_rejects then "rejects" else "accepts")
        (if reference_rejects then "rejects" else "accepts")
        (Diagnostic.quote text)

let rec contained smaller larger =
  match (smaller, larger) with
  | [], _ -> true
  | _ :: _, [] -> false
  | first :: rest, candidate :: larger_rest ->
      if first = candidate then contained rest larger_rest
      else if first > candidate then contained smaller larger_rest
      else false

(* Applying a fix removes its diagnostic and adds no other: the remaining
   diagnostics are the others, or fewer. *)
let check_fixes_work text =
  let all text =
    let _, _, diagnostics = parse text in
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

(* The lexer's machine-applicable fixes, applied together, add no error. *)
let check_machine_fixes_work text =
  let _, diagnostics = lex text in
  match Diagnostic.machine_applicable diagnostics with
  | [] -> ()
  | applied ->
      let edits =
        List.concat_map
          (fun (diagnostic : Diagnostic.t) ->
            match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
          applied
      in
      let _, remaining = lex (Diagnostic.apply_edits text edits) in
      let others = List.filter (fun diagnostic -> not (List.memq diagnostic applied)) diagnostics in
      if not (Diagnostic.adds_none ~before:others ~after:remaining) then
        fail "the machine-applicable fixes of the lexer leave or add an error in %s"
          (Diagnostic.quote text)

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
    (* Names outside ASCII. *)
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
  let seed = ref 0 and count = ref 10_000 and paths = ref [] in
  Arg.parse
    [
      ("--seed", Arg.Set_int seed, " The random seed");
      ("--count", Arg.Set_int count, " How many inputs of each kind");
    ]
    (fun path -> paths := path :: !paths)
    "fuzz [--seed N] [--count N] PATH...";
  let random = Random.State.make [| !seed |] in
  let rec truss_files path =
    if Sys.is_directory path then
      List.concat_map
        (fun name -> truss_files (Filename.concat path name))
        (List.sort compare (Array.to_list (Sys.readdir path)))
    else if Filename.check_suffix path ".truss" then [ path ]
    else []
  in
  let pieces path =
    let source = Source.read_file path in
    let tokens, _ = Lexer.lex source in
    List.map
      (fun (piece : Parser.piece) ->
        let start = tokens.(piece.first).span.start in
        String.sub (Source.text source) start (tokens.(piece.stop - 1).span.stop - start))
      (Parser.split tokens)
  in
  let examples =
    Array.of_list (List.concat_map pieces (List.concat_map truss_files (List.rev !paths)))
  in
  if Array.length examples = 0 then (
    prerr_endline "fuzz: give .truss files, or directories of them";
    exit 2);
  let example () = examples.(Random.State.int random (Array.length examples)) in
  (* Uniform bytes are rarely valid UTF-8, so half are characters instead. *)
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
  (* A range replaced by a mistake, a piece of another input, or nothing. *)
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
    check_machine_fixes_work one;
    check_machine_fixes_work !several;
    round_trip random
  done;
  if !failures > 0 then begin
    Printf.printf "%d failures\n" !failures;
    exit 1
  end
  else Printf.printf "%d inputs of each kind pass, from %d pieces\n" !count (Array.length examples)
