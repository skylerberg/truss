(* The lexer's tests. Each test gives an input and states exactly what the
   lexer must do with it: the tokens, or the one diagnostic with its code,
   position, and fix. See IMPLEMENTATION.md, "Testing".

   Fuzzing and benchmarks are tools in stage0/tools, not tests. *)

open Token

(* Running tests *)

let failures = ref 0
let count = ref 0
let current_test = ref ""

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      Printf.printf "FAIL %s: %s\n" !current_test message)
    format

let test name body =
  incr count;
  current_test := name;
  match body () with () -> () | exception exception_ -> fail "raised %s" (Printexc.to_string exception_)

let equal_lists show name expected actual =
  if expected <> actual then
    fail "%s: expected [%s], got [%s]" name
      (String.concat "; " (List.map show expected))
      (String.concat "; " (List.map show actual))

(* Lexing *)

let lex text = Lexer.lex (Source.create ~path:"test.truss" text)
let codes text = List.map (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code) (snd (lex text))

(* A token, shown compactly: names and literals as written, punctuation and
   keywords by spelling, NEWLINE as "NL", and a zero-width closer that layout
   inserted with a "+" in front. A string shows its texts, with "${}" for
   each interpolation. *)
let show (token : Token.t) =
  match token.kind with
  | Upper name | Lower name -> name
  | Underscore -> "_"
  | Keyword keyword -> keyword_spelling keyword
  | Reserved reserved -> "reserved " ^ reserved_spelling reserved
  | Integer value -> Z.to_string value
  | Float { significand; exponent } -> Printf.sprintf "%se%s" (Z.to_string significand) (Z.to_string exponent)
  | String literal ->
      let tag = match literal.tag with Some (tag, _) -> tag | None -> "" in
      tag
      ^ Diagnostic.quote
          (String.concat "${}" (List.map (fun (text : text) -> text.value) (Array.to_list (texts literal))))
  | Punctuation punctuation -> (if token.span.start = token.span.stop then "+" else "") ^ punctuation_spelling punctuation
  | Foreign foreign -> foreign_spelling foreign
  | Newline -> "NL"
  | End_of_file -> "EOF"

let shown tokens =
  Array.to_list tokens |> List.filter (fun (token : Token.t) -> token.kind <> End_of_file) |> List.map show

let tokens_of text = shown (fst (lex text))

(* Asserts that [text] lexes with no diagnostics into [expected]. *)
let tokens text expected =
  List.iter (fun code -> fail "unexpected %s" code) (codes text);
  equal_lists Fun.id "tokens" expected (tokens_of text)

(* The tokens of the [index]th interpolation of the first string in [text]. *)
let interpolation_tokens text index =
  let first_string =
    Array.to_list (fst (lex text))
    |> List.find_map (fun (token : Token.t) -> match token.kind with String literal -> Some literal | _ -> None)
  in
  match first_string with Some literal -> shown (interpolations literal).(index).tokens | None -> []

let find text part ~occurrence =
  let rec search index seen =
    if index + String.length part > String.length text then -1
    else if String.sub text index (String.length part) = part then
      if seen + 1 = occurrence then index else search (index + 1) (seen + 1)
    else search (index + 1) seen
  in
  search 0 0

(* Asserts that [text] gives exactly one diagnostic, with [code], starting at
   the [occurrence]th occurrence of [at]. With [fixed], its fixes must turn
   [text] into [fixed] and then [alternatives], each of which must lex with
   no diagnostics. Without [fixed], it must have no fix. *)
let error ?fixed ?(alternatives = []) ?(occurrence = 1) text ~code ~at =
  match snd (lex text) with
  | [ diagnostic ] -> (
      if diagnostic.code <> Lexer code then
        fail "expected %s, got %s" (Diagnostic.Code.name (Lexer code)) (Diagnostic.Code.name diagnostic.code);
      let expected = find text at ~occurrence in
      if diagnostic.span.start <> expected then
        fail "expected the error at %d (%S), got %d" expected at diagnostic.span.start;
      let results = List.map (Diagnostic.apply_fix text) diagnostic.fixes in
      match (fixed, results) with
      | None, [] -> ()
      | None, result :: _ -> fail "expected no fix, got one giving %S" result
      | Some _, [] -> fail "expected a fix, got none"
      | Some fixed, results ->
          equal_lists (Printf.sprintf "%S") "fixed text" (fixed :: alternatives) results;
          List.iter (fun result -> List.iter (fail "the fixed text %S has %s" result) (codes result)) results)
  | diagnostics ->
      fail "expected one diagnostic, got [%s]"
        (String.concat "; " (List.map (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code) diagnostics))

(* Source text *)

let () =
  test "a byte order mark at the start is skipped" (fun () -> tokens "\xEF\xBB\xBFx" [ "x"; "NL" ]);
  test "a byte order mark elsewhere is forbidden" (fun () ->
      error "a \xEF\xBB\xBF b" ~code:Forbidden_character ~at:"\xEF" ~fixed:"a b");
  test "a carriage return and line feed is one line break" (fun () -> tokens "a\r\nb\r\n" [ "a"; "NL"; "b"; "NL" ]);
  test "a carriage return on its own is an error and a line break" (fun () ->
      error "a\rb" ~code:Carriage_return ~at:"\r" ~fixed:"a\nb";
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (tokens_of "a\rb"));
  test "a forbidden character in code is deleted" (fun () ->
      error "let b\xE2\x80\x8B = 1" ~code:Forbidden_character ~at:"\xE2" ~fixed:"let b = 1");
  test "a forbidden character between names becomes a space" (fun () ->
      error "a\x01b" ~code:Forbidden_character ~at:"\x01" ~fixed:"a b");
  test "a forbidden character in a string becomes an escape" (fun () ->
      error "\"\xE2\x80\xAE\"" ~code:Forbidden_character ~at:"\xE2" ~fixed:"\"\\u{202E}\"");
  test "a forbidden character in a raw string has no fix" (fun () ->
      error "\"\"\"\xE2\x80\x8Bx\"\"\"" ~code:Forbidden_character ~at:"\xE2");
  test "joiners and variation selectors are allowed in strings" (fun () ->
      tokens "\"\xE2\x80\x8D\xEF\xB8\x8F\"" [ "\"\xE2\x80\x8D\xEF\xB8\x8F\""; "NL" ]);
  test "bytes that are not UTF-8 are one error" (fun () -> error "a \xFF\xFE b" ~code:Invalid_utf8 ~at:"\xFF");
  test "JSON output is valid UTF-8 when a message is about a bad byte" (fun () ->
      let source = Source.create ~path:"test.truss" "\"\\\xFF\"" in
      let json = Diagnostic.to_json source (snd (Lexer.lex source)) in
      let rec valid index =
        index >= String.length json
        ||
        let packed = Unicode.decode json index in
        packed >= 0 && valid (index + Unicode.decoded_length packed)
      in
      if not (valid 0) then fail "the JSON is not valid UTF-8: %S" json)

(* Names *)

let () =
  test "keywords, reserved words, and contextual words" (fun () ->
      tokens "fn Self self loop result time O _"
        [ "fn"; "Self"; "self"; "reserved loop"; "result"; "time"; "O"; "_"; "NL" ]);
  test "userName is lower_snake_case" (fun () -> error "userName" ~code:Name_case ~at:"userName" ~fixed:"user_name");
  test "an acronym in a name" (fun () ->
      error "parseHTTPResponse" ~code:Name_case ~at:"parse" ~fixed:"parse_http_response");
  test "MAX_SIZE is a constant from another language" (fun () ->
      error "MAX_SIZE" ~code:Name_case ~at:"MAX" ~fixed:"max_size");
  test "Http_Client is UpperCamelCase" (fun () -> error "Http_Client" ~code:Name_case ~at:"Http" ~fixed:"HttpClient");
  test "underscores at the ends and doubled" (fun () ->
      error "count_" ~code:Name_case ~at:"count" ~fixed:"count";
      error "user__name" ~code:Name_case ~at:"user" ~fixed:"user_name";
      error "_unused" ~code:Name_case ~at:"_" ~fixed:"unused");
  test "no fix that would make a keyword" (fun () -> error "_type" ~code:Name_case ~at:"_");
  test "a name with a letter outside ASCII is one name with one error" (fun () ->
      error "let caf\xC3\xA9 = 1" ~code:Name_not_ascii ~at:"caf";
      equal_lists Fun.id "tokens" [ "let"; "caf\xC3\xA9"; "="; "1"; "NL" ] (tokens_of "let caf\xC3\xA9 = 1"));
  test "every use of a misspelled name gets the same fix" (fun () ->
      let replacements =
        List.concat_map
          (fun (d : Diagnostic.t) ->
            List.concat_map (fun (fix : Diagnostic.fix) -> List.map (fun (e : Diagnostic.edit) -> e.replacement) fix.edits) d.fixes)
          (snd (lex "userName(userName)"))
      in
      equal_lists Fun.id "replacements" [ "user_name"; "user_name" ] replacements)

(* Numbers *)

let () =
  test "integer literals" (fun () ->
      tokens "42 1_000_000 0xFF 0xdead_beef 0b1010 0o755 99999999999999999999999"
        [ "42"; "1000000"; "255"; "3735928559"; "10"; "493"; "99999999999999999999999"; "NL" ]);
  test "float literals are exact, with trailing zeros removed" (fun () ->
      tokens "0.5 1.50 6.02e23 1.0e-09 100e-2 0.0" [ "5e-1"; "15e-1"; "602e21"; "1e-9"; "1e0"; "0e0"; "NL" ]);
  test "a dot after a number" (fun () ->
      tokens "1..2" [ "1"; ".."; "2"; "NL" ];
      tokens "1.max" [ "1"; "."; "max"; "NL" ];
      tokens "1.0.max" [ "1e0"; "."; "max"; "NL" ]);
  test "type suffixes" (fun () ->
      error "3u8" ~code:Number_suffix ~at:"u8" ~fixed:"3";
      error "1.5f" ~code:Number_suffix ~at:"f" ~fixed:"1.5";
      error "3f" ~code:Number_suffix ~at:"f" ~fixed:"3.0");
  test "prefixes and exponents are lowercase" (fun () ->
      error "0X1F" ~code:Number_uppercase_prefix ~at:"0X" ~fixed:"0x1F";
      error "1E9" ~code:Number_uppercase_exponent ~at:"E" ~fixed:"1e9");
  test "underscores go between digits" (fun () ->
      error "1__000" ~code:Number_underscore ~at:"_" ~fixed:"1_000";
      error "0x_FF" ~code:Number_underscore ~at:"_" ~fixed:"0xFF");
  test "one fix corrects every problem in a literal" (fun () ->
      error "1_u8" ~code:Number_underscore ~at:"_" ~fixed:"1");
  test "a leading zero" (fun () ->
      error "0755" ~code:Number_leading_zero ~at:"0755" ~fixed:"0o755" ~alternatives:[ "755" ];
      error "09" ~code:Number_leading_zero ~at:"09" ~fixed:"9";
      error "00.5" ~code:Number_leading_zero ~at:"00" ~fixed:"0.5");
  test "errors without a fix" (fun () ->
      error "0b102" ~code:Number_invalid_digit ~at:"2";
      error "0o8" ~code:Number_invalid_digit ~at:"8";
      error "0x" ~code:Number_missing_digits ~at:"0x";
      error "1e" ~code:Number_missing_digits ~at:"e";
      error "1abc" ~code:Number_followed_by_name ~at:"a")

(* Strings *)

let () =
  test "escapes" (fun () ->
      tokens {|"\n\t\r\0\\\"\${ \u{1F600} $ { }"|} [ Diagnostic.quote "\n\t\r\000\\\"${ \xF0\x9F\x98\x80 $ { }"; "NL" ]);
  test "an interpolation holds the tokens of an expression" (fun () ->
      tokens {|"Hello, ${name}!"|} [ {|"Hello, ${}!"|}; "NL" ];
      equal_lists Fun.id "interpolation" [ "name" ] (interpolation_tokens {|"Hello, ${name}!"|} 0));
  test "a string inside an interpolation" (fun () ->
      equal_lists Fun.id "interpolation"
        [ "names"; "."; "join"; "("; {|", "|}; ")" ]
        (interpolation_tokens {|"${names.join(", ")}"|} 0));
  test "braces inside an interpolation" (fun () ->
      equal_lists Fun.id "interpolation" [ "{"; "a"; "}" ] (interpolation_tokens {|"${ {a} }"|} 0));
  test "a tag touches its string" (fun () ->
      tokens {|Regex"[a-z]+"|} [ {|Regex"[a-z]+"|}; "NL" ];
      tokens {|Regex "x"|} [ "Regex"; {|"x"|}; "NL" ];
      tokens {|return"x"|} [ "return"; {|"x"|}; "NL" ]);
  test "an unterminated string closes at the end of its line" (fun () ->
      error "\"never closed\nx" ~code:Unterminated_string ~at:"\"" ~fixed:"\"never closed\"\nx");
  test "escapes that do not exist" (fun () ->
      error {|"\q"|} ~code:Invalid_escape ~at:"\\";
      error {|"\u{D800}"|} ~code:Invalid_escape ~at:"\\");
  test "an empty interpolation" (fun () -> error {|"a${}b"|} ~code:Empty_interpolation ~at:"$" ~fixed:{|"ab"|});
  test "a line break ends an interpolation and its string" (fun () ->
      error "\"${a\nlet b = 1" ~code:Line_break_in_interpolation ~at:"$";
      equal_lists Fun.id "tokens" [ {|"${}"|}; "NL"; "let"; "b"; "="; "1"; "NL" ] (tokens_of "\"${a\nlet b = 1"));
  test "interpolations nest at most 32 deep" (fun () ->
      let rec nested depth = if depth = 0 then "x" else "\"${" ^ nested (depth - 1) ^ "}\"" in
      equal_lists Fun.id "codes" [] (codes (nested 32));
      equal_lists Fun.id "codes" [ "lexer.interpolation_too_deep" ] (codes (nested 33)));
  test "a character literal becomes a tagged string" (fun () ->
      error "'a'" ~code:Character_literal ~at:"'" ~fixed:{|Character"a"|};
      error {|'\n'|} ~code:Character_literal ~at:"'" ~fixed:{|Character"\n"|};
      error {|'"'|} ~code:Character_literal ~at:"'" ~fixed:{|Character"\""|});
  test "quotes touching a name are not a character literal" (fun () ->
      equal_lists Fun.id "codes" [ "lexer.unexpected_character"; "lexer.unexpected_character" ] (codes "value's'debug"))

(* Raw strings *)

let lines = String.concat "\n"

let () =
  test "a one-line raw string has no escapes" (fun () -> tokens {|"""\d{3}"""|} [ {|"\\d{3}"|}; "NL" ]);
  test "dollar signs before an interpolation" (fun () ->
      tokens {|"""Total: $${price}"""|} [ {|"Total: $${}"|}; "NL" ];
      tokens {|$$"""${HOME} $${folder}"""|} [ {|"${HOME} ${}"|}; "NL" ]);
  test "a longer delimiter" (fun () -> tokens {|""""a """ b""""|} [ {|"a \"\"\" b"|}; "NL" ]);
  test "the closing delimiter's indentation is removed" (fun () ->
      tokens
        (lines [ {|x = """|}; "  select"; "    where"; ""; "  end"; {|  """|} ])
        [ "x"; "="; Diagnostic.quote "select\n  where\n\nend"; "NL" ]);
  test "spaces after the opening delimiter are ignored" (fun () ->
      tokens (lines [ {|"""   |}; "  text"; {|  """|} ]) [ {|"text"|}; "NL" ]);
  test "line endings in a raw string are line feeds" (fun () ->
      tokens "\"\"\"\r\n  a\r\n  b\r\n  \"\"\"" [ {|"a\nb"|}; "NL" ]);
  test "a run of more quotes than the delimiter" (fun () -> error {|"""a""""|} ~code:Raw_string_quotes ~at:{|""""|});
  test "a closing delimiter after text moves to its own line" (fun () ->
      error
        (lines [ {|"""|}; {|  text"""|} ])
        ~code:Raw_string_closing_not_alone ~at:{|"""|} ~occurrence:2
        ~fixed:(lines [ {|"""|}; "  text"; {|  """|} ]));
  test "a line that does not start with the indentation" (fun () ->
      error (lines [ {|"""|}; "  spaces"; "\ttab"; {|  """|} ]) ~code:Raw_string_indentation ~at:"\ttab");
  test "an unterminated one-line raw string closes at the end of its line" (fun () ->
      error "\"\"\"abc\nx" ~code:Unterminated_string ~at:"\"" ~fixed:"\"\"\"abc\"\"\"\nx");
  test "an unterminated multi-line raw string runs to the end of the file" (fun () ->
      let text = lines [ "fn f() {"; {|  let s = """|}; "    text"; "}"; "fn g() {}" ] in
      error text ~code:Unterminated_string ~at:{|"""|};
      match snd (lex text) with
      | [ { notes = [ (span, _) ]; _ } ] when span.start = find text "}" ~occurrence:1 -> ()
      | _ -> fail "expected a note at the line where the string seems to end")

(* Rejected sequences *)

let () =
  test "a comment at the end of a line" (fun () ->
      error "let a = 1 // one" ~code:Comment ~at:"//" ~fixed:"let a = 1");
  test "a comment on its own line" (fun () ->
      error "a\n// note\nb" ~code:Comment ~at:"//" ~fixed:"a\nb";
      error "a\n# note\nb" ~code:Comment ~at:"#" ~fixed:"a\nb");
  test "a block comment between tokens" (fun () ->
      error "a /* x */ + b" ~code:Comment ~at:"/*" ~fixed:"a + b";
      error "a /* x /* y */ */ b" ~code:Comment ~at:"/*" ~fixed:"a b");
  test "an unterminated block comment has no fix" (fun () -> error "a /* never closed\nb" ~code:Comment ~at:"/*");
  test "a block comment across lines separates statements" (fun () ->
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (tokens_of "a /* x\n */ b"));
  test "a semicolon" (fun () ->
      error "let a = 1;" ~code:Semicolon ~at:";" ~fixed:"let a = 1";
      error "  a; b" ~code:Semicolon ~at:";" ~fixed:"  a\n  b";
      error "{ a; }" ~code:Semicolon ~at:";" ~fixed:"{ a }");
  test "a semicolon mid-line separates statements" (fun () ->
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (tokens_of "a; b"));
  test "strict equality" (fun () ->
      error "a === b" ~code:Strict_equality ~at:"===" ~fixed:"a == b";
      error "a !== b" ~code:Strict_equality ~at:"!==" ~fixed:"a != b");
  test "a longer run of = is not strict equality" (fun () -> tokens "a ==== b" [ "a"; "=="; "=="; "b"; "NL" ]);
  test "characters Truss does not use" (fun () ->
      error "@a" ~code:Unexpected_character ~at:"@";
      error "a ` b" ~code:Unexpected_character ~at:"`";
      error "a $ b" ~code:Unexpected_character ~at:"$");
  test "increment and decrement are left for the parser" (fun () ->
      tokens "i++\ni--\n--x" [ "i"; "++"; "NL"; "i"; "--"; "NL"; "--"; "x"; "NL" ])

(* Punctuation *)

let () =
  test "every punctuation lexes as itself" (fun () ->
      List.iter
        (fun (spelling, punctuation) ->
          match punctuation with
          | Open _ | Close _ -> ()
          | _ -> tokens ("a " ^ spelling ^ " b") [ "a"; spelling; "b"; "NL" ])
        Token.punctuation);
  test "the longest match" (fun () ->
      tokens "a<<=b" [ "a"; "<<="; "b"; "NL" ];
      tokens "a...b" [ "a"; ".."; "."; "b"; "NL" ];
      tokens "a==>b" [ "a"; "==>"; "b"; "NL" ];
      tokens "a::b" [ "a"; "::"; "b"; "NL" ])

(* Layout *)

let () =
  test "a line break ends a statement" (fun () -> tokens "a\nb" [ "a"; "NL"; "b"; "NL" ]);
  test "a line that starts with an operator continues" (fun () ->
      tokens "a\n  .b()\n  + c" [ "a"; "."; "b"; "("; ")"; "+"; "c"; "NL" ]);
  test "a line that starts with - is a new statement" (fun () -> tokens "a\n- b" [ "a"; "NL"; "-"; "b"; "NL" ]);
  test "line breaks inside parentheses are ignored" (fun () ->
      tokens "f(a,\n  b)" [ "f"; "("; "a"; ","; "b"; ")"; "NL" ]);
  test "line breaks inside braces count again" (fun () ->
      tokens "f({\n  a\n  b\n})" [ "f"; "("; "{"; "a"; "NL"; "b"; "}"; ")"; "NL" ]);
  test "clauses and else continue the line" (fun () ->
      tokens "fn f()\n  requires a\n{\n}\nelse {}"
        [ "fn"; "f"; "("; ")"; "requires"; "a"; "NL"; "{"; "}"; "else"; "{"; "}"; "NL" ]);
  test "several line breaks give one NEWLINE, and a blank line is noted" (fun () ->
      let tokens, _ = lex "a\n\n\nb" in
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (shown tokens);
      if not tokens.(2).blank_line_before then fail "b has a blank line before it");
  test "a comment line is not a blank line" (fun () ->
      let tokens, _ = lex "a\n// c\nb" in
      if tokens.(2).blank_line_before then fail "b has no blank line before it")

(* Brackets *)

let () =
  test "an unclosed bracket inside another" (fun () ->
      error "f(1, [2)" ~code:Unclosed_bracket ~at:"[" ~fixed:"f(1, [2])";
      equal_lists Fun.id "tokens" [ "f"; "("; "1"; ","; "["; "2"; "+]"; ")"; "NL" ] (tokens_of "f(1, [2)"));
  test "a closer that matches nothing is dropped" (fun () ->
      error "a }" ~code:Unmatched_closing_bracket ~at:"}";
      equal_lists Fun.id "tokens" [ "a"; "NL" ] (tokens_of "a }"));
  test "a bracket still open at the end of the file" (fun () ->
      error "let x = (1\n" ~code:Unclosed_bracket ~at:"(" ~fixed:"let x = (1\n)\n");
  test "a definition in column 0 closes open brackets" (fun () ->
      let text = "fn a() {\n  f(1,\nfn b() {}\n" in
      error text ~code:Unclosed_bracket ~at:"(" ~occurrence:2 ~fixed:"fn a() {\n  f(1,\n)}\nfn b() {}\n";
      equal_lists Fun.id "tokens"
        [ "fn"; "a"; "("; ")"; "{"; "f"; "("; "1"; ","; "+)"; "+}"; "NL"; "fn"; "b"; "("; ")"; "{"; "}"; "NL" ]
        (tokens_of text));
  test "brackets swallowed by an unterminated comment are not reported" (fun () ->
      equal_lists Fun.id "codes" [ "lexer.comment" ] (codes "f( /* never closed"))

(* Diagnostics *)

let () =
  test "at most 200 diagnostics are shown, then a count" (fun () ->
      let diagnostic offset = Diagnostic.make ~code:(Lexer Semicolon) (Source.span offset (offset + 1)) "x" in
      let shown = Diagnostic.shown (List.init 250 diagnostic) in
      if List.length shown <> Diagnostic.limit + 1 then fail "%d shown" (List.length shown);
      match List.rev shown with
      | last :: _ when last.code = Too_many_diagnostics -> ()
      | _ -> fail "the last one counts the rest");
  test "diagnostics past the limit do not cost the shown ones their fixes" (fun () ->
      let text = String.concat "" (List.init 250 (Printf.sprintf "a%d;\n")) in
      List.iteri
        (fun index (d : Diagnostic.t) -> if index < Diagnostic.limit && d.fixes = [] then fail "diagnostic %d has no fix" index)
        (snd (lex text)));
  test "overlapping edits are refused" (fun () ->
      let fix = Diagnostic.fix "x" [ Diagnostic.delete (Source.span 0 2); Diagnostic.delete (Source.span 1 3) ] in
      match Diagnostic.apply_fix "abc" fix with
      | _ -> fail "expected Invalid_argument"
      | exception Invalid_argument _ -> ())

(* Checking fixes *)

let semicolon_fixes (_, diagnostics) =
  List.concat_map (fun (d : Diagnostic.t) -> if d.code = Lexer Semicolon then d.fixes else []) diagnostics

let () =
  test "a fix that would change how another part of the file lexes is left out" (fun () ->
      (* Replacing the `;` with a line break puts `fn` in column 0, where
         bracket recovery, which the open `{` of g turns on, closes the
         parenthesis around it. *)
      let source = Source.create ~path:"test.truss" "let p = s.filter(;fn(x) { x })\nfn g() {\n" in
      if semicolon_fixes (Lexer.lex ~check_fixes:false source) = [] then fail "the fix is built";
      if semicolon_fixes (Lexer.lex source) <> [] then fail "the checked fix is left out");
  test "the fixes for errors in two definitions each remove only their own error" (fun () ->
      let text = "fn a() {\n  let userName = 1;\n  f(1,\n}\nfn b() {\n  let x = 0755 // note\n}\n" in
      let before = List.sort compare (codes text) in
      List.iter
        (fun (d : Diagnostic.t) ->
          List.iter
            (fun fix ->
              let expected =
                let rec remove_one = function
                  | [] -> []
                  | code :: rest -> if code = Diagnostic.Code.name d.code then rest else code :: remove_one rest
                in
                remove_one before
              in
              equal_lists Fun.id "codes after the fix" expected (List.sort compare (codes (Diagnostic.apply_fix text fix))))
            d.fixes)
        (snd (lex text)))

(* The documents *)

let read path =
  let channel = open_in_bin path in
  let text = really_input_string channel (in_channel_length channel) in
  close_in channel;
  text

let document name = read (Filename.concat "../.." name)
let contains text part = find text part ~occurrence:1 >= 0

(* The lines of the first fenced block after the first line containing
   [marker]. *)
let block_after document marker =
  let rec after_marker = function [] -> [] | line :: rest -> if contains line marker then rest else after_marker rest in
  let rec after_fence = function
    | [] -> []
    | line :: rest -> if String.starts_with ~prefix:"```" line then rest else after_fence rest
  in
  let rec until_fence lines = function
    | [] -> List.rev lines
    | line :: rest -> if String.starts_with ~prefix:"```" line then List.rev lines else until_fence (line :: lines) rest
  in
  until_fence [] (after_fence (after_marker (String.split_on_char '\n' document)))

let words lines = List.sort_uniq compare (List.filter (( <> ) "") (List.concat_map (String.split_on_char ' ') lines))

(* The prose between two markers, with line breaks made spaces. *)
let between document first second =
  let start = find document first ~occurrence:1 + String.length first in
  let rest = String.sub document start (String.length document - start) in
  String.sub rest 0 (find rest second ~occurrence:1)
  |> String.split_on_char '\n' |> List.map String.trim |> String.concat " "

let backticked text =
  match String.split_on_char '`' text with [] -> [] | _ :: rest -> List.filteri (fun index _ -> index mod 2 = 0) rest

(* The ```truss blocks of a document, with the indentation of blocks inside
   list items removed. *)
let truss_blocks name =
  let rec loop inside current blocks = function
    | [] -> List.rev blocks
    | line :: rest ->
        let trimmed = String.trim line in
        if inside then
          if String.starts_with ~prefix:"```" trimmed then loop false [] (List.rev current :: blocks) rest
          else loop true (line :: current) blocks rest
        else loop (trimmed = "```truss") [] blocks rest
  in
  let dedent block =
    let leading line =
      let rec count index = if index < String.length line && line.[index] = ' ' then count (index + 1) else index in
      count 0
    in
    let indentation =
      match List.find_opt (fun line -> String.trim line <> "") block with Some line -> leading line | None -> 0
    in
    String.concat "\n"
      (List.map
         (fun line ->
           if String.length line >= indentation then String.sub line indentation (String.length line - indentation) else "")
         block)
  in
  List.map dedent (loop false [] [] (String.split_on_char '\n' (document name)))

let () =
  let grammar = document "GRAMMAR.md" in
  let spellings list = List.sort_uniq compare (List.map fst list) in
  test "GRAMMAR.md lists the keywords" (fun () ->
      equal_lists Fun.id "keywords" (spellings Token.keywords) (words (block_after grammar "Reserved everywhere:")));
  test "GRAMMAR.md lists the reserved words" (fun () ->
      equal_lists Fun.id "reserved" (spellings Token.reserved_words) (words (block_after grammar "Reserved for later use")));
  test "GRAMMAR.md lists the punctuation" (fun () ->
      equal_lists Fun.id "punctuation" (spellings Token.punctuation) (words (block_after grammar "### Punctuation")));
  test "GRAMMAR.md's line-break lists match Layout" (fun () ->
      let kind_of spelling =
        match Token.word spelling with
        | Some kind -> Some kind
        | None ->
            if spelling = "_" then Some Underscore
            else Option.map (fun p -> Punctuation p) (List.assoc_opt spelling Token.punctuation)
      in
      let listed first second = List.filter_map kind_of (backticked (between grammar first second)) in
      let can_end = listed "**can end a statement**:" "- the first token after it" in
      let can_begin = listed "**can begin a statement**:" "3. Several line feeds" in
      let spelling = function
        | Keyword keyword -> keyword_spelling keyword
        | Punctuation punctuation -> punctuation_spelling punctuation
        | _ -> "_"
      in
      List.iter
        (fun kind ->
          if Layout.can_end kind <> List.mem kind can_end then fail "can_end %s" (spelling kind);
          if Layout.can_begin kind <> List.mem kind can_begin then fail "can_begin %s" (spelling kind))
        (List.map (fun (_, keyword) -> Keyword keyword) Token.keywords
        @ List.map (fun (_, punctuation) -> Punctuation punctuation) Token.punctuation
        @ [ Underscore ]));
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          test (Printf.sprintf "%s block %d lexes cleanly" name (index + 1)) (fun () ->
              equal_lists Fun.id "codes" [] (codes text)))
        (truss_blocks name))
    [ "SYNTAX.md"; "DESIGN.md"; "GRAMMAR.md"; "CODEGEN.md" ]

let () =
  if !failures > 0 then begin
    Printf.printf "%d failures in %d tests\n" !failures !count;
    exit 1
  end
  else Printf.printf "%d tests pass\n" !count
