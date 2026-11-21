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
         (fun previous_stop (span : Source.span) ->
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
                 (fun ((interpolation : Token.interpolation), (text : Token.text)) ->
                   [ interpolation.span; text.span ])
                 (Array.to_list literal.rest));
          Array.iter
            (fun (interpolation : Token.interpolation) ->
              check_tokens text ~start:interpolation.span.start ~stop:interpolation.span.stop
                interpolation.tokens)
            (Token.list_interpolations literal)
      | _ -> ())
    tokens;
  if !stack <> [] then fail "unbalanced brackets in %s" quoted

let check_diagnostic_spans text (diagnostic : Diagnostic.t) =
  let spans =
    (diagnostic.span :: List.map fst diagnostic.notes)
    @ List.concat_map
        (fun (fix : Source.span Diagnostic.fix) ->
          List.map (fun (edit : Source.span Diagnostic.edit) -> edit.span) fix.edits)
        diagnostic.fixes
  in
  if List.exists (fun (span : Source.span) -> span.stop > String.length text) spans then
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
  let file, parser_diagnostics = Parser.parse tokens ~lexer_diagnostics in
  (tokens, file, lexer_diagnostics @ parser_diagnostics)

let check_tree text (item : Syntax.definition Syntax.item) =
  let quoted = Diagnostic.quote text in
  let contains_span (outer : Source.Definition_span.t) (inner : Source.Definition_span.t) =
    outer.start <= inner.start && inner.stop <= outer.stop
  in
  let spans = item.positions.spans in
  let ids = Hashtbl.create 64 in
  let rec visit_expression (outer : Source.Definition_span.t) (value : Syntax.expression) =
    let span = spans.(value.id) in
    if not (contains_span outer span) then
      fail "an expression's span is outside its parent in %s" quoted;
    if Hashtbl.mem ids value.id then fail "an id repeats in %s" quoted;
    Hashtbl.replace ids value.id ();
    if value.id >= item.value.id then fail "an id is not before its definition's in %s" quoted;
    let previous = ref span.start in
    Syntax_walk.visit_children
      (fun (inner : Syntax.expression) ->
        let inner_start = spans.(inner.id).start in
        if inner_start < !previous then fail "expressions out of order in %s" quoted;
        previous := inner_start;
        visit_expression span inner)
      value
  in
  let length = item.stop - item.base in
  if Array.length spans <> item.value.id + 1 then
    fail "the span table does not end at the definition's id in %s" quoted;
  let definition_span = spans.(item.value.id) in
  if definition_span.start <> 0 || definition_span.stop > length then
    fail "a definition's span is out of bounds in %s" quoted;
  List.iter
    (fun (span : Source.Definition_span.t) ->
      if span.stop > length then fail "a syntax error is out of bounds in %s" quoted)
    item.positions.syntax_errors;
  Syntax_walk.visit_definition (visit_expression definition_span) item.value

let check_parse_robust text =
  match parse text with
  | exception exception_ ->
      fail "the parser raised %s on %s" (Printexc.to_string exception_) (Diagnostic.quote text)
  | _, file, diagnostics ->
      let items =
        List.concat_map
          (fun (top_level : Syntax.top_level) -> top_level.definition :: top_level.methods)
          file.definitions
      in
      List.iter (check_tree text) items;
      List.iter (check_diagnostic_spans text) diagnostics;
      if
        diagnostics = []
        && List.exists
             (fun (item : Syntax.definition Syntax.item) -> item.positions.syntax_errors <> [])
             items
      then fail "a syntax error has no diagnostic in %s" (Diagnostic.quote text)

type verdict = Grammar_rejects | Grammar_accepts | Unknown

let judge : Diagnostic.Code.t -> verdict = function
  | Parser
      ( Unexpected_token | Needs_parentheses | Reserved_word | Statement_at_top_level | Missing_body
      | Open_range | Float_pattern | Increment | Double_negation | Match_arm_comma
      | Conditional_operator | Let_mut | Address_of | Closure_bars | Brace_record | Turbofish
      | Trailing_lambda | As_conversion | Elif | Angle_brackets | Qualified_variant | Macro_call
      | Tuple | Power_operator | Short_declaration | Pipe_operator | Lambda_annotation
      | Impl_parameters | Null_coalescing | Misplaced_condition ) ->
      Grammar_rejects
  | Parser (Cost_word | Misplaced_potential | Interpolation_not_allowed) -> Unknown
  | Parser
      ( Use_after_definition | Let_else_brace | Nesting_too_deep | Misplaced_opaque
      | Misplaced_tuple | Misplaced_visibility | Misplaced_self | Lends_own | Repeated_clause
      | Loop_cost_bound | Function_type_cost_bound | Function_type_names
      | Misplaced_callback_contract | Misplaced_function_type | Misplaced_associated_type
      | Misplaced_constraint | Specification_only | Misplaced_assert | Misplaced_proof
      | Misplaced_loop_exit | Exits_parallel | Echo_in_specification | Reserved_specification_name
        )
  | Lexer _ | Resolve _ | Package _ | Prover _ | Capabilities _ | Ownership _ | Usage _ | Patterns _
  | Types _ | Too_many_diagnostics ->
      Grammar_accepts

let check_parsers_agree text =
  let tokens, _, diagnostics = parse text in
  let interpolations =
    Array.to_list tokens
    |> List.concat_map (fun (token : Token.t) ->
        match token.kind with
        | String literal ->
            List.map
              (fun (inner : Token.interpolation) -> inner.span)
              (Array.to_list (Token.list_interpolations literal))
        | _ -> [])
  in
  let is_inside_interpolation (span : Source.span) =
    List.exists
      (fun (inner : Source.span) -> inner.start <= span.start && span.start < inner.stop)
      interpolations
  in
  let is_in_cost_clause offset =
    let rec look_back index =
      if index < 0 then false
      else
        let token = tokens.(index) in
        if token.span.start > offset then look_back (index - 1)
        else
          match token.kind with
          | Keyword Cost -> true
          | Keyword (Uses | Requires | Ensures | Decreases | Invariant | Derives)
          | Punctuation (Open Curly)
          | Newline ->
              false
          | _ -> look_back (index - 1)
    in
    look_back (Array.length tokens - 1)
  in
  let verdicts =
    List.filter_map
      (fun (diagnostic : Diagnostic.t) ->
        if is_inside_interpolation diagnostic.span then None
        else if is_in_cost_clause diagnostic.span.start then Some Unknown
        else Some (judge diagnostic.code))
      diagnostics
  in
  let all = Array.to_list tokens in
  if
    (not (List.mem Unknown verdicts))
    && not
         (List.exists
            (fun (token : Token.t) ->
              token.span.start = token.span.stop && token.kind <> End_of_file)
            all)
  then
    let parser_rejects = List.mem Grammar_rejects verdicts
    and reference_rejects = not (Reference_parser.accepts Reference_parser.parse_file all) in
    if parser_rejects <> reference_rejects then
      fail "the parser %s and the reference grammar %s %s"
        (if parser_rejects then "rejects" else "accepts")
        (if reference_rejects then "rejects" else "accepts")
        (Diagnostic.quote text)

let adds_none ~(before : Diagnostic.t list) ~(after : Diagnostic.t list) =
  let list_codes diagnostics =
    List.sort compare (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.code) diagnostics)
  in
  let rec is_contained smaller larger =
    match (smaller, larger) with
    | [], _ -> true
    | _ :: _, [] -> false
    | first :: rest, candidate :: larger_rest ->
        if first = candidate then is_contained rest larger_rest
        else if first > candidate then is_contained smaller larger_rest
        else false
  in
  is_contained (list_codes after) (list_codes before)

let rec list_joined_spans ~(edits : Source.span Diagnostic.edit list) ~(written : Token.t array)
    ~(fixed : Token.t array) =
  let is_replaced (span : Source.span) =
    List.exists
      (fun (edit : Source.span Diagnostic.edit) ->
        edit.span.start < edit.span.stop && edit.span.start <= span.start
        && span.stop <= edit.span.stop)
      edits
  in
  let list_tokens ~is_kept array =
    List.filter
      (fun (token : Token.t) ->
        token.kind <> Newline && token.kind <> End_of_file
        && token.span.start < token.span.stop
        && is_kept token)
      (Array.to_list array)
  in
  let list_inside (token : Token.t) =
    match token.kind with
    | String literal ->
        Array.concat
          (Array.to_list
             (Array.map
                (fun (interpolation : Token.interpolation) -> interpolation.tokens)
                (Token.list_interpolations literal)))
    | _ -> [||]
  in
  let rec walk (written : Token.t list) (fixed : Token.t list) =
    match fixed with
    | [] -> []
    | token :: rest -> (
        let rec list_after = function
          | (other : Token.t) :: others when other.span.stop <= token.span.start ->
              list_after others
          | written -> written
        in
        let written = list_after written in
        let overlaps (other : Token.t) = other.span.start < token.span.stop in
        match written with
        | first :: second :: _ when overlaps first && overlaps second ->
            token.span :: walk written rest
        | first :: _ when overlaps first ->
            list_joined_spans ~edits ~written:(list_inside first) ~fixed:(list_inside token)
            @ walk written rest
        | _ -> walk written rest)
  in
  walk
    (list_tokens ~is_kept:(fun _ -> true) written)
    (list_tokens ~is_kept:(fun (token : Token.t) -> not (is_replaced token.span)) fixed)

let alters_neighbors text ~edits ~fixed_text =
  let scan text = fst (Lexer.For_testing.scan (Source.create ~path:"fuzz.truss" text)) in
  let written = scan text and fixed = Lexer.For_testing.to_original edits (scan fixed_text) in
  list_joined_spans ~edits ~written ~fixed @ list_joined_spans ~edits ~written:fixed ~fixed:written
  <> []

let check_fixes_work text =
  let list_all_diagnostics text =
    let _, _, diagnostics = parse text in
    diagnostics
  in
  let is_lexer (diagnostic : Diagnostic.t) =
    match diagnostic.code with Lexer _ -> true | _ -> false
  in
  let diagnostics = list_all_diagnostics text in
  List.iter
    (fun (diagnostic : Diagnostic.t) ->
      let select_judged = if is_lexer diagnostic then List.filter is_lexer else Fun.id in
      let before = select_judged (List.filter (fun other -> other != diagnostic) diagnostics) in
      List.iter
        (fun (fix : Source.span Diagnostic.fix) ->
          match Diagnostic.apply_edits text fix.edits with
          | exception Invalid_argument _ ->
              fail "the fix %S has overlapping edits in %s" fix.title (Diagnostic.quote text)
          | fixed ->
              if not (adds_none ~before ~after:(select_judged (list_all_diagnostics fixed))) then
                fail "the fix %S for %s leaves or adds an error in %s" fix.title
                  (Diagnostic.Code.name diagnostic.code)
                  (Diagnostic.quote text);
              if alters_neighbors text ~edits:fix.edits ~fixed_text:fixed then
                fail "the fix %S for %s joins or splits a neighboring token in %s" fix.title
                  (Diagnostic.Code.name diagnostic.code)
                  (Diagnostic.quote text))
        diagnostic.fixes)
    diagnostics

let check_machine_fixes_work text =
  let _, diagnostics = lex text in
  let applies_cleanly applied =
    let edits =
      List.concat_map
        (fun (diagnostic : Diagnostic.t) ->
          match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
        applied
    in
    let _, remaining = lex (Diagnostic.apply_edits text edits) in
    let others = List.filter (fun diagnostic -> not (List.memq diagnostic applied)) diagnostics in
    adds_none ~before:others ~after:remaining
  in
  match Diagnostic.list_machine_applicable diagnostics with
  | [] -> ()
  | applied ->
      if not (applies_cleanly applied) then
        fail "the machine-applicable fixes of the lexer leave or add an error in %s"
          (Diagnostic.quote text);
      if List.length applied > 1 then
        List.iter
          (fun (diagnostic : Diagnostic.t) ->
            if not (applies_cleanly [ diagnostic ]) then
              fail "the machine-applicable fix for %s leaves or adds an error alone in %s"
                (Diagnostic.Code.name diagnostic.code)
                (Diagnostic.quote text))
          applied

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
    "\\n";
    "\\u{";
    "\\u{1F600}";
    "\\u{D800}";
    "\\x41";
    "...";
    "..<";
    "<>";
    "!==";
    ":=";
    "|>";
    "**";
    "--";
    "1.";
    ".5";
    "0b2";
    "1__0";
    "0X1";
    "1E5";
    "1u8";
    "99999999999999999999999";
    "/* /* */";
    "*/";
    "\r\n";
    "\t";
    "\u{2028}";
    "\u{0085}";
    "\u{FEFF}";
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
    "caf\u{00E9}";
    "e\u{0301}";
    "\u{03BB}";
    "\u{0430}";
    "\u{FB01}";
    "\u{2126}";
  |]

let spellings =
  Array.concat
    [
      mistakes;
      Array.of_list (List.map fst Token.For_testing.keywords);
      Array.of_list (List.map fst Token.For_testing.reserved_words);
      Array.of_list (List.map fst Token.punctuation);
      Array.of_list Parser.For_testing.contextual_keywords;
    ]

let round_trip random =
  let pick array = array.(Random.State.int random (Array.length array)) in
  let names =
    [|
      ("count", Token.Lower "count");
      ("user_name", Lower "user_name");
      ("Point", Upper "Point");
      ("O", Upper "O");
    |]
  in
  let others =
    Array.of_list
      (List.map
         (fun (spelling, keyword) -> (spelling, Token.Keyword keyword))
         Token.For_testing.keywords
      @ List.map
          (fun (spelling, reserved) -> (spelling, Token.Reserved reserved))
          Token.For_testing.reserved_words
      @ List.filter_map
          (fun (spelling, punctuation) ->
            match punctuation with
            | Token.Open _ | Close _ -> None
            | _ -> Some (spelling, Token.Punctuation punctuation))
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
    |> List.filter (fun kind -> kind <> Token.Newline && kind <> End_of_file)
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
  let rec list_truss_files path =
    if Sys.is_directory path then
      List.concat_map
        (fun name -> list_truss_files (Filename.concat path name))
        (List.sort compare (Array.to_list (Sys.readdir path)))
    else if Filename.check_suffix path ".truss" then [ path ]
    else []
  in
  let list_pieces path =
    let source = Source.For_testing.read_file path in
    let tokens, _ = Lexer.lex source in
    List.map
      (fun (piece : Parser.For_testing.piece) ->
        let start = tokens.(piece.first).span.start in
        String.sub (Source.text source) start (tokens.(piece.stop - 1).span.stop - start))
      (Parser.For_testing.split tokens)
  in
  let examples =
    Array.of_list (List.concat_map list_pieces (List.concat_map list_truss_files (List.rev !paths)))
  in
  if Array.length examples = 0 then (
    prerr_endline "fuzz: give .truss files, or directories of them";
    exit 2);
  let pick_example () = examples.(Random.State.int random (Array.length examples)) in
  let make_random_text () =
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
          let other = pick_example () in
          let start = Random.State.int random (String.length other + 1) in
          String.sub other start (min (String.length other - start) (Random.State.int random 40))
      | _ -> mistakes.(Random.State.int random (Array.length mistakes))
    in
    String.sub text 0 at ^ piece ^ String.sub text (at + removed) (length - at - removed)
  in
  let insert_token_run text =
    let at = Random.State.int random (String.length text + 1) in
    let run =
      List.init
        (1 + Random.State.int random 24)
        (fun _ -> spellings.(Random.State.int random (Array.length spellings)))
    in
    String.sub text 0 at ^ " " ^ String.concat " " run ^ " "
    ^ String.sub text at (String.length text - at)
  in
  for _ = 1 to !count do
    check_robust (make_random_text ());
    let several = ref (pick_example ()) in
    for _ = 1 to 1 + Random.State.int random 4 do
      several := mutate !several
    done;
    check_robust !several;
    check_parse_robust !several;
    let with_token_run = insert_token_run (pick_example ()) in
    check_robust with_token_run;
    check_parse_robust with_token_run;
    check_parsers_agree !several;
    let one = mutate (pick_example ()) in
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
