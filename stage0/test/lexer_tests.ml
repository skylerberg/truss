let equal_lists show name expected actual =
  if expected <> actual then
    Harness.fail "%s: expected [%s], got [%s]" name
      (String.concat "; " (List.map show expected))
      (String.concat "; " (List.map show actual))

let lex text = Lexer.lex (Source.create ~path:"test.truss" text)

let codes text =
  List.map
    (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code)
    (snd (lex text))

let show (token : Token.t) =
  match token.kind with
  | Upper name | Lower name -> name
  | Underscore -> "_"
  | Keyword keyword -> Token.keyword_spelling keyword
  | Reserved reserved -> "reserved " ^ Token.reserved_spelling reserved
  | Integer value -> Z.to_string value
  | Float { significand; exponent } ->
      Printf.sprintf "%se%s" (Z.to_string significand) (Z.to_string exponent)
  | String literal ->
      let tag = match literal.tag with Some (tag, _) -> tag | None -> "" in
      tag
      ^ Diagnostic.quote
          (String.concat "${}"
             (List.map
                (fun (text : Token.text) -> text.value)
                (Array.to_list (Token.texts literal))))
  | Punctuation punctuation ->
      (if token.span.start = token.span.stop then "+" else "")
      ^ Token.punctuation_spelling punctuation
  | Foreign foreign -> Token.foreign_spelling foreign
  | Newline -> "NL"
  | End_of_file -> "EOF"

let shown tokens =
  Array.to_list tokens
  |> List.filter (fun (token : Token.t) -> token.kind <> End_of_file)
  |> List.map show

let tokens_of text = shown (fst (lex text))

let recovered_tokens text =
  List.map
    (fun shown ->
      if String.length shown > 1 && shown.[0] = '+' then String.sub shown 1 (String.length shown - 1)
      else shown)
    (tokens_of text)

let tokens text expected =
  List.iter (fun code -> Harness.fail "unexpected %s" code) (codes text);
  equal_lists Fun.id "tokens" expected (tokens_of text)

let interpolation_tokens text index =
  let first_string =
    Array.to_list (fst (lex text))
    |> List.find_map (fun (token : Token.t) ->
        match token.kind with String literal -> Some literal | _ -> None)
  in
  match first_string with
  | Some literal -> shown (Token.interpolations literal).(index).tokens
  | None -> []

let find text part ~occurrence = Option.get (Substring.For_testing.find ~occurrence text part)

let error ?fixed ?(alternatives = []) ?(occurrence = 1) text ~code ~at =
  match snd (lex text) with
  | [ diagnostic ] -> (
      if diagnostic.code <> Lexer code then
        Harness.fail "expected %s, got %s"
          (Diagnostic.Code.name (Lexer code))
          (Diagnostic.Code.name diagnostic.code);
      let expected = find text at ~occurrence in
      if diagnostic.span.start <> expected then
        Harness.fail "expected the error at %d (%S), got %d" expected at diagnostic.span.start;
      let results = List.map (Diagnostic.apply_fix text) diagnostic.fixes in
      match (fixed, results) with
      | None, [] -> ()
      | None, result :: _ -> Harness.fail "expected no fix, got one giving %S" result
      | Some _, [] -> Harness.fail "expected a fix, got none"
      | Some fixed, results ->
          equal_lists (Printf.sprintf "%S") "fixed text" (fixed :: alternatives) results;
          List.iter
            (fun result ->
              List.iter (Harness.fail "the fixed text %S has %s" result) (codes result))
            results;
          let recovered = recovered_tokens text in
          if
            List.length results = 1
            && not (List.exists (fun result -> recovered_tokens result = recovered) results)
          then
            Harness.fail "%S recovers as [%s], which no fix writes" text
              (String.concat "; " recovered))
  | diagnostics ->
      Harness.fail "expected one diagnostic, got [%s]"
        (String.concat "; "
           (List.map
              (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code)
              diagnostics))

let fixed_texts text ~code =
  List.concat_map
    (fun (diagnostic : Diagnostic.t) ->
      if diagnostic.code = Lexer code then List.map (Diagnostic.apply_fix text) diagnostic.fixes
      else [])
    (snd (lex text))

let machine_fixed text =
  Diagnostic.apply_edits text
    (List.concat_map
       (fun (diagnostic : Diagnostic.t) ->
         match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
       (Diagnostic.machine_applicable (snd (lex text))))

let () =
  Harness.test "two sources of the same text are equal" (fun () ->
      if Source.create ~path:"test.truss" "a\nb" <> Source.create ~path:"test.truss" "a\nb" then
        Harness.fail "they differ");
  Harness.test "a byte order mark at the start is skipped" (fun () ->
      tokens "\xEF\xBB\xBFx" [ "x"; "NL" ]);
  Harness.test "a byte order mark elsewhere is forbidden" (fun () ->
      error "a \xEF\xBB\xBF b" ~code:Forbidden_character ~at:"\xEF" ~fixed:"a b");
  Harness.test "the first line starts after a byte order mark" (fun () ->
      let source = Source.create ~path:"test.truss" "\xEF\xBB\xBFab\ncd" in
      let shown offset =
        let line, column = Source.position source offset in
        Printf.sprintf "%d:%d" line column
      in
      equal_lists Fun.id "positions" [ "1:1"; "1:2"; "2:1" ] (List.map shown [ 3; 4; 6 ]);
      if Source.line_start source 4 <> 3 then Harness.fail "the first line starts at 3";
      if not (Source.starts_line source 3) then Harness.fail "offset 3 starts its line");
  Harness.test "a diagnostic after a byte order mark shows its line without it" (fun () ->
      let text = "\xEF\xBB\xBFlet x = 1;" in
      let source = Source.create ~path:"test.truss" text in
      match snd (Lexer.lex source) with
      | [ diagnostic ] ->
          let rendered = Diagnostic.render source diagnostic in
          if not (String.starts_with ~prefix:"test.truss:1:10:" rendered) then
            Harness.fail "expected the position 1:10, got %s" rendered;
          if String.contains rendered '\xEF' then
            Harness.fail "expected the line without the byte order mark, got %s" rendered
      | diagnostics -> Harness.fail "expected one diagnostic, got %d" (List.length diagnostics));
  Harness.test "a carriage return and line feed is one line break" (fun () ->
      tokens "a\r\nb\r\n" [ "a"; "NL"; "b"; "NL" ]);
  Harness.test "a carriage return on its own is an error and a line break" (fun () ->
      error "a\rb" ~code:Carriage_return ~at:"\r" ~fixed:"a\nb";
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (tokens_of "a\rb"));
  Harness.test "a forbidden character in code is deleted" (fun () ->
      error "let b\xE2\x80\x8B = 1" ~code:Forbidden_character ~at:"\xE2" ~fixed:"let b = 1");
  Harness.test "a forbidden character between names becomes a space" (fun () ->
      error "a\x01b" ~code:Forbidden_character ~at:"\x01" ~fixed:"a b");
  Harness.test "a forbidden character in a string becomes an escape" (fun () ->
      error "\"\xE2\x80\xAE\"" ~code:Forbidden_character ~at:"\xE2" ~fixed:"\"\\u{202E}\"";
      equal_lists Fun.id "tokens" (tokens_of "\"\\u{202E}\"") (tokens_of "\"\xE2\x80\xAE\""));
  Harness.test "a forbidden character in a raw string has no fix" (fun () ->
      error "\"\"\"\xE2\x80\x8Bx\"\"\"" ~code:Forbidden_character ~at:"\xE2");
  Harness.test "joiners and variation selectors are allowed in strings" (fun () ->
      tokens "\"\xE2\x80\x8D\xEF\xB8\x8F\"" [ "\"\xE2\x80\x8D\xEF\xB8\x8F\""; "NL" ]);
  Harness.test "bytes that are not UTF-8 are one error" (fun () ->
      error "a \xFF\xFE b" ~code:Invalid_utf8 ~at:"\xFF");
  Harness.test "JSON output is valid UTF-8 when a message is about a bad byte" (fun () ->
      let source = Source.create ~path:"test.truss" "\"\\\xFF\"" in
      let json = Diagnostic.to_json source (snd (Lexer.lex source)) in
      let rec valid index =
        index >= String.length json
        ||
        let decoded = Unicode.decode json index in
        Unicode.Decoded.is_valid decoded && valid (index + Unicode.Decoded.length decoded)
      in
      if not (valid 0) then Harness.fail "the JSON is not valid UTF-8: %S" json)

let () =
  Harness.test "keywords, reserved words, and contextual words" (fun () ->
      tokens "fn Self self loop result time O _"
        [ "fn"; "Self"; "self"; "reserved loop"; "result"; "time"; "O"; "_"; "NL" ]);
  Harness.test "userName is lower_snake_case" (fun () ->
      error "userName" ~code:Name_case ~at:"userName" ~fixed:"user_name");
  Harness.test "an acronym in a name" (fun () ->
      error "parseHTTPResponse" ~code:Name_case ~at:"parse" ~fixed:"parse_http_response");
  Harness.test "MAX_SIZE is a constant from another language" (fun () ->
      error "MAX_SIZE" ~code:Name_case ~at:"MAX" ~fixed:"max_size");
  Harness.test "Http_Client is UpperCamelCase" (fun () ->
      error "Http_Client" ~code:Name_case ~at:"Http" ~fixed:"HttpClient");
  Harness.test "underscores at the ends and doubled" (fun () ->
      error "count_" ~code:Name_case ~at:"count" ~fixed:"count";
      error "user__name" ~code:Name_case ~at:"user" ~fixed:"user_name";
      error "_unused" ~code:Name_case ~at:"_" ~fixed:"unused");
  Harness.test "no fix that would make a keyword" (fun () -> error "_type" ~code:Name_case ~at:"_");
  Harness.test "no fix that would make a name a string's prefix or tag" (fun () ->
      equal_lists Fun.id "fixed" [] (fixed_texts "_f\"a\"" ~code:Name_case);
      equal_lists Fun.id "fixed" [] (fixed_texts "HTTP_OK\"a\"" ~code:Name_case);
      equal_lists Fun.id "fixed" [ "HttpClient\"a\"" ]
        (fixed_texts "Http_Client\"a\"" ~code:Name_case));
  Harness.test "no fix that would rename to a name the file already has" (fun () ->
      error "my_var + myVar" ~code:Name_case ~at:"myVar";
      equal_lists Fun.id "tokens" [ "my_var"; "+"; "myVar"; "NL" ] (tokens_of "my_var + myVar");
      equal_lists Fun.id "fixed" [] (fixed_texts "myVar + my_Var" ~code:Name_case));
  Harness.test "a name with a letter outside ASCII is one name with one error" (fun () ->
      error "let caf\xC3\xA9 = 1" ~code:Name_not_ascii ~at:"caf";
      equal_lists Fun.id "tokens"
        [ "let"; "caf\xC3\xA9"; "="; "1"; "NL" ]
        (tokens_of "let caf\xC3\xA9 = 1"));
  Harness.test "every use of a misspelled name gets the same fix" (fun () ->
      let replacements =
        List.concat_map
          (fun (diagnostic : Diagnostic.t) ->
            List.concat_map
              (fun (fix : _ Diagnostic.fix) ->
                List.map (fun (edit : _ Diagnostic.edit) -> edit.replacement) fix.edits)
              diagnostic.fixes)
          (snd (lex "userName(userName)"))
      in
      equal_lists Fun.id "replacements" [ "user_name"; "user_name" ] replacements)

let () =
  Harness.test "integer literals" (fun () ->
      tokens "42 1_000_000 0xFF 0xdead_beef 0b1010 0o755 99999999999999999999999"
        [ "42"; "1000000"; "255"; "3735928559"; "10"; "493"; "99999999999999999999999"; "NL" ]);
  Harness.test "float literals are exact, with trailing zeros removed" (fun () ->
      tokens "0.5 1.50 6.02e23 1.0e-09 100e-2 0.0"
        [ "5e-1"; "15e-1"; "602e21"; "1e-9"; "1e0"; "0e0"; "NL" ]);
  Harness.test "a dot after a number" (fun () ->
      tokens "1..2" [ "1"; ".."; "2"; "NL" ];
      tokens "1.max" [ "1"; "."; "max"; "NL" ];
      tokens "1.0.max" [ "1e0"; "."; "max"; "NL" ]);
  Harness.test "a type suffix has no fix" (fun () ->
      error "3u8" ~code:Number_suffix ~at:"u8";
      error "1.5f" ~code:Number_suffix ~at:"f";
      error "3f" ~code:Number_suffix ~at:"f";
      error "1_u8" ~code:Number_suffix ~at:"u8");
  Harness.test "an integer with a float suffix is a float" (fun () ->
      equal_lists Fun.id "tokens" [ "3e0"; "NL" ] (tokens_of "3f");
      equal_lists Fun.id "tokens" [ "5e0"; "NL" ] (tokens_of "5d"));
  Harness.test "prefixes and exponents are lowercase" (fun () ->
      error "0X1F" ~code:Number_uppercase_prefix ~at:"0X" ~fixed:"0x1F";
      error "1E9" ~code:Number_uppercase_exponent ~at:"E" ~fixed:"1e9");
  Harness.test "underscores go between digits" (fun () ->
      error "1__000" ~code:Number_underscore ~at:"_" ~fixed:"1_000";
      error "0x_FF" ~code:Number_underscore ~at:"_" ~fixed:"0xFF");
  Harness.test "one fix corrects every problem in a literal" (fun () ->
      error "1__0__0" ~code:Number_underscore ~at:"_" ~fixed:"1_0_0");
  Harness.test "a form of another language with another problem has no fix" (fun () ->
      error "0X_FF" ~code:Number_uppercase_prefix ~at:"0X");
  Harness.test "a leading zero" (fun () ->
      error "0755" ~code:Number_leading_zero ~at:"0755" ~fixed:"0o755" ~alternatives:[ "755" ];
      error "09" ~code:Number_leading_zero ~at:"09" ~fixed:"9";
      error "00.5" ~code:Number_leading_zero ~at:"00" ~fixed:"0.5");
  Harness.test "errors without a fix" (fun () ->
      error "0b102" ~code:Number_invalid_digit ~at:"2";
      error "0o8" ~code:Number_invalid_digit ~at:"8";
      error "0x" ~code:Number_missing_digits ~at:"0x";
      error "1e" ~code:Number_missing_digits ~at:"e";
      error "1abc" ~code:Number_followed_by_name ~at:"a")

let () =
  Harness.test "escapes" (fun () ->
      tokens {|"\n\t\r\0\\\"\${ \u{1F600} $ { }"|}
        [ Diagnostic.quote "\n\t\r\000\\\"${ \xF0\x9F\x98\x80 $ { }"; "NL" ]);
  Harness.test "an interpolation holds the tokens of an expression" (fun () ->
      tokens {|"Hello, ${name}!"|} [ {|"Hello, ${}!"|}; "NL" ];
      equal_lists Fun.id "interpolation" [ "name" ] (interpolation_tokens {|"Hello, ${name}!"|} 0));
  Harness.test "a string inside an interpolation" (fun () ->
      equal_lists Fun.id "interpolation"
        [ "names"; "."; "join"; "("; {|", "|}; ")" ]
        (interpolation_tokens {|"${names.join(", ")}"|} 0));
  Harness.test "braces inside an interpolation" (fun () ->
      equal_lists Fun.id "interpolation" [ "{"; "a"; "}" ] (interpolation_tokens {|"${ {a} }"|} 0));
  Harness.test "a tag touches its string" (fun () ->
      tokens {|Regex"[a-z]+"|} [ {|Regex"[a-z]+"|}; "NL" ];
      tokens {|Regex "x"|} [ "Regex"; {|"x"|}; "NL" ];
      tokens {|return"x"|} [ "return"; {|"x"|}; "NL" ]);
  Harness.test "an unterminated string closes at the end of its line" (fun () ->
      error "\"never closed\nx" ~code:Unterminated_string ~at:"\"" ~fixed:"\"never closed\"\nx");
  Harness.test "escapes that do not exist" (fun () ->
      error {|"\q"|} ~code:Invalid_escape ~at:"\\";
      error {|"\u{D800}"|} ~code:Invalid_escape ~at:"\\");
  Harness.test "an empty interpolation" (fun () ->
      error {|"a${}b"|} ~code:Empty_interpolation ~at:"$" ~fixed:{|"ab"|});
  Harness.test "a line break ends an interpolation and its string" (fun () ->
      error "\"${a\nlet b = 1" ~code:Line_break_in_interpolation ~at:"$";
      equal_lists Fun.id "tokens"
        [ {|"${}"|}; "NL"; "let"; "b"; "="; "1"; "NL" ]
        (tokens_of "\"${a\nlet b = 1"));
  Harness.test "interpolations nest at most 32 deep" (fun () ->
      let rec nested depth = if depth = 0 then "x" else "\"${" ^ nested (depth - 1) ^ "}\"" in
      equal_lists Fun.id "codes" [] (codes (nested 32));
      equal_lists Fun.id "codes" [ "lexer.interpolation_too_deep" ] (codes (nested 33)));
  Harness.test "a character literal becomes a tagged string" (fun () ->
      error "'a'" ~code:Character_literal ~at:"'" ~fixed:{|Character"a"|};
      error {|'\n'|} ~code:Character_literal ~at:"'" ~fixed:{|Character"\n"|};
      error {|'"'|} ~code:Character_literal ~at:"'" ~fixed:{|Character"\""|});
  Harness.test "an escape of another language becomes a code point" (fun () ->
      error {|"\x41"|} ~code:Invalid_escape ~at:"\\" ~fixed:{|"\u{41}"|};
      error {|"\u00E9"|} ~code:Invalid_escape ~at:"\\" ~fixed:{|"\u{E9}"|};
      error {|"\U0001F600"|} ~code:Invalid_escape ~at:"\\" ~fixed:{|"\u{1F600}"|};
      error {|"\a"|} ~code:Invalid_escape ~at:"\\" ~fixed:{|"\u{7}"|});
  Harness.test "an escape of another language gives the string its character" (fun () ->
      equal_lists Fun.id "tokens" [ {|"A\x1Bé"|}; "NL" ] (tokens_of {|"\x41\e\u00E9"|}));
  Harness.test "an escaped single quote needs no escape" (fun () ->
      error {|"it\'s"|} ~code:Invalid_escape ~at:"\\" ~fixed:{|"it's"|});
  Harness.test "a surrogate written with four digits has no fix" (fun () ->
      error {|"\uD800"|} ~code:Invalid_escape ~at:"\\");
  Harness.test "an f-string becomes an ordinary string" (fun () ->
      error {|f"Hello {name}"|} ~code:String_prefix ~at:"f" ~fixed:{|"Hello ${name}"|};
      error {|f"{{{user.name}}}"|} ~code:String_prefix ~at:"f" ~fixed:{|"{${user.name}}"|};
      error {|f""|} ~code:String_prefix ~at:"f" ~fixed:{|""|});
  Harness.test "an f-string with a format specification has no fix" (fun () ->
      error {|f"{value:.2f}"|} ~code:String_prefix ~at:"f";
      error {|f"{}"|} ~code:String_prefix ~at:"f");
  Harness.test "an f-string recovers as the string its fix writes" (fun () ->
      equal_lists Fun.id "tokens" [ "x"; "="; {|"a ${}"|}; "NL" ] (tokens_of {|x = f"a {b}"|}));
  Harness.test "an r-string becomes a raw string" (fun () ->
      error {|r"\d+"|} ~code:String_prefix ~at:"r" ~fixed:{|"""\d+"""|};
      equal_lists Fun.id "tokens" [ {|"\\d+"|}; "NL" ] (tokens_of {|r"\d+"|}));
  Harness.test "a byte string has no fix" (fun () ->
      error {|b"abc"|} ~code:String_prefix ~at:"b";
      equal_lists Fun.id "tokens" [ {|"abc"|}; "NL" ] (tokens_of {|b"abc"|}));
  Harness.test "a byte literal becomes a tagged string" (fun () ->
      error "b'a'" ~code:Character_literal ~at:"b" ~fixed:{|UInt8"a"|});
  Harness.test "a name before a string that is not a prefix is a name" (fun () ->
      equal_lists Fun.id "tokens" [ "g"; {|"a"|}; "NL" ] (tokens_of {|g"a"|}));
  Harness.test "a Rust raw string with hashes becomes a raw string" (fun () ->
      error {|r#"\d+"#|} ~code:String_prefix ~at:"r" ~fixed:{|"""\d+"""|};
      error {|r##"say "hi" now"##|} ~code:String_prefix ~at:"r" ~fixed:{|"""say "hi" now"""|};
      error {|r#"a"""b"#|} ~code:String_prefix ~at:"r" ~fixed:{|""""a"""b""""|};
      equal_lists Fun.id "tokens" [ {|"say \"hi\" now"|}; "NL" ] (tokens_of {|r#"say "hi" now"#|}));
  Harness.test "a Rust raw string whose fix would interpolate has no fix" (fun () ->
      error {|r#"a${b}"#|} ~code:String_prefix ~at:"r");
  Harness.test "a Rust raw string that starts with a quote has no fix" (fun () ->
      error {|r#""a"#|} ~code:String_prefix ~at:"r");
  Harness.test "a Rust raw string outside ASCII becomes a raw string" (fun () ->
      error "r#\"caf\u{E9}\"#" ~code:String_prefix ~at:"r" ~fixed:"\"\"\"caf\u{E9}\"\"\"");
  Harness.test "a Rust raw string that ends with a quote has no fix" (fun () ->
      error {|r#"say "hi""#|} ~code:String_prefix ~at:"r");
  Harness.test "a Python string with three quotes loses its prefix" (fun () ->
      error "f\"\"\"\n  Hello {name}\n  \"\"\"" ~code:String_prefix ~at:"f"
        ~fixed:"\"\"\"\n  Hello ${name}\n  \"\"\"";
      error {|r"""\d+"""|} ~code:String_prefix ~at:"r" ~fixed:{|"""\d+"""|});
  Harness.test "a Python string with three quotes and a backslash has no fix" (fun () ->
      error "f\"\"\"\n  a\\nb\n  \"\"\"" ~code:String_prefix ~at:"f");
  Harness.test "a C# verbatim string with a doubled quote has no fix" (fun () ->
      equal_lists Fun.id "fixed" [] (fixed_texts {|@"a""b"|} ~code:String_prefix));
  Harness.test "a C# string becomes a Truss string" (fun () ->
      error {|$"Hello {name}"|} ~code:String_prefix ~at:"$" ~fixed:{|"Hello ${name}"|};
      error {|@"C:\logs"|} ~code:String_prefix ~at:"@" ~fixed:{|"""C:\logs"""|};
      error {|Path$"{name}"|} ~code:String_prefix ~at:"$");
  Harness.test "a template literal becomes an ordinary string" (fun () ->
      error "`Hello ${name}`" ~code:String_delimiter ~at:"`" ~fixed:{|"Hello ${name}"|};
      error "`say \"hi\"`" ~code:String_delimiter ~at:"`" ~fixed:{|"say \"hi\""|};
      equal_lists Fun.id "tokens" [ {|"Hello ${}"|}; "NL" ] (tokens_of "`Hello ${name}`"));
  Harness.test "a string between single quotes becomes an ordinary string" (fun () ->
      error "'abc'" ~code:String_delimiter ~at:"'" ~fixed:{|"abc"|};
      error "''" ~code:String_delimiter ~at:"'" ~fixed:{|""|};
      equal_lists Fun.id "fixed"
        [ {|print("say \"hi\"", 'x y')|}; {|print('say "hi"', "x y")|} ]
        (fixed_texts {|print('say "hi"', 'x y')|} ~code:String_delimiter));
  Harness.test "a lifetime has no fix" (fun () ->
      error "x: &'a str" ~code:Lifetime ~at:"'";
      equal_lists Fun.id "codes" [ "lexer.lifetime"; "lexer.lifetime" ] (codes "f<'a>(x: &'a str)"));
  Harness.test "Swift's interpolation becomes ${...}" (fun () ->
      error {|"Hello \(user.name)"|} ~code:Invalid_escape ~at:"\\" ~fixed:{|"Hello ${user.name}"|});
  Harness.test "curly quotes around text that a string reads differently have no fix" (fun () ->
      error "\u{201C}a\\nb\u{201D}" ~code:Confusable_character ~at:"\u{201C}";
      error "\u{201C}a${b}\u{201D}" ~code:Confusable_character ~at:"\u{201C}";
      error "\u{201C}say \"hi\"\u{201D}" ~code:Confusable_character ~at:"\u{201C}");
  Harness.test "curly quotes become straight quotes" (fun () ->
      error "\u{201C}text\u{201D}" ~code:Confusable_character ~at:"\u{201C}" ~fixed:{|"text"|};
      error "\u{2018}text\u{2019}" ~code:Confusable_character ~at:"\u{2018}" ~fixed:{|"text"|};
      equal_lists Fun.id "tokens" [ {|"text"|}; "NL" ] (tokens_of "\u{201C}text\u{201D}"));
  Harness.test "quotes touching a name are not a character literal" (fun () ->
      equal_lists Fun.id "codes"
        [ "lexer.unexpected_character"; "lexer.unexpected_character" ]
        (codes "value's'debug"))

let lines = String.concat "\n"

let () =
  Harness.test "a one-line raw string has no escapes" (fun () ->
      tokens {|"""\d{3}"""|} [ {|"\\d{3}"|}; "NL" ]);
  Harness.test "dollar signs before an interpolation" (fun () ->
      tokens {|"""Total: $${price}"""|} [ {|"Total: $${}"|}; "NL" ];
      tokens {|$$"""${HOME} $${folder}"""|} [ {|"${HOME} ${}"|}; "NL" ]);
  Harness.test "a longer delimiter" (fun () ->
      tokens {|""""a """ b""""|} [ {|"a \"\"\" b"|}; "NL" ]);
  Harness.test "the closing delimiter's indentation is removed" (fun () ->
      tokens
        (lines [ {|x = """|}; "  select"; "    where"; ""; "  end"; {|  """|} ])
        [ "x"; "="; Diagnostic.quote "select\n  where\n\nend"; "NL" ]);
  Harness.test "spaces after the opening delimiter are ignored" (fun () ->
      tokens (lines [ {|"""   |}; "  text"; {|  """|} ]) [ {|"text"|}; "NL" ]);
  Harness.test "line endings in a raw string are line feeds" (fun () ->
      tokens "\"\"\"\r\n  a\r\n  b\r\n  \"\"\"" [ {|"a\nb"|}; "NL" ]);
  Harness.test "a run of more quotes than the delimiter" (fun () ->
      error {|"""a""""|} ~code:Raw_string_quotes ~at:{|""""|});
  Harness.test "a closing delimiter after text moves to its own line" (fun () ->
      error
        (lines [ {|"""|}; {|  text"""|} ])
        ~code:Raw_string_closing_not_alone ~at:{|"""|} ~occurrence:2
        ~fixed:(lines [ {|"""|}; "  text"; {|  """|} ]));
  Harness.test "a line that does not start with the indentation" (fun () ->
      error
        (lines [ {|"""|}; "  spaces"; "\ttab"; {|  """|} ])
        ~code:Raw_string_indentation ~at:"\ttab"
        ~fixed:(lines [ {|"""|}; "  spaces"; "  tab"; {|  """|} ]));
  Harness.test "Python's empty triple-quoted string gets a note" (fun () ->
      match snd (lex {|x = """"""|}) with
      | [ { notes = [ (_, note) ]; _ } ] when String.ends_with ~suffix:{|`""`.|} note -> ()
      | _ -> Harness.fail "expected one diagnostic, with a note suggesting an empty string");
  Harness.test "an unterminated one-line raw string closes at the end of its line" (fun () ->
      error "\"\"\"abc\nx" ~code:Unterminated_string ~at:"\"" ~fixed:"\"\"\"abc\"\"\"\nx");
  Harness.test "an unterminated multi-line raw string runs to the end of the file" (fun () ->
      let text = lines [ "fn f() {"; {|  let s = """|}; "    text"; "}"; "fn g() {}" ] in
      error text ~code:Unterminated_string ~at:{|"""|};
      match snd (lex text) with
      | [ { notes = [ (span, _) ]; _ } ] when span.start = find text "}" ~occurrence:1 -> ()
      | _ -> Harness.fail "expected a note at the line where the string seems to end")

let () =
  Harness.test "a comment at the end of a line has no fix" (fun () ->
      error "let a = 1 // one" ~code:Comment ~at:"//");
  Harness.test "a comment on its own line has no fix" (fun () ->
      error "a\n// note\nb" ~code:Comment ~at:"//";
      error "a\n# note\nb" ~code:Comment ~at:"#");
  Harness.test "a block comment between tokens has no fix" (fun () ->
      error "a /* x */ + b" ~code:Comment ~at:"/*";
      error "a /* x /* y */ */ b" ~code:Comment ~at:"/*");
  Harness.test "an unterminated block comment has no fix" (fun () ->
      error "a /* never closed\nb" ~code:Comment ~at:"/*");
  Harness.test "a block comment across lines separates statements" (fun () ->
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (tokens_of "a /* x\n */ b"));
  Harness.test "a semicolon" (fun () ->
      error "let a = 1;" ~code:Semicolon ~at:";" ~fixed:"let a = 1";
      error "  a; b" ~code:Semicolon ~at:";" ~fixed:"  a\n  b";
      error "{ a; }" ~code:Semicolon ~at:";" ~fixed:"{ a }");
  Harness.test "a semicolon mid-line separates statements" (fun () ->
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (tokens_of "a; b"));
  Harness.test "a semicolon before a comment ends no statement" (fun () ->
      equal_lists Fun.id "fixed" [ "a // note" ] (fixed_texts "a; // note" ~code:Semicolon));
  Harness.test "a semicolon before a multi-line comment separates statements once" (fun () ->
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (tokens_of "a; /* x\n */ b"));
  Harness.test "an apostrophe after a name is not a string" (fun () ->
      equal_lists Fun.id "codes"
        [ "lexer.unexpected_character"; "lexer.unexpected_character" ]
        (codes "don't it's");
      error "f('ab')" ~code:String_delimiter ~at:"'" ~fixed:{|f("ab")|});
  Harness.test "strict equality" (fun () ->
      error "a === b" ~code:Strict_equality ~at:"===" ~fixed:"a == b";
      error "a !== b" ~code:Strict_equality ~at:"!==" ~fixed:"a != b");
  Harness.test "a longer run of = is not strict equality" (fun () ->
      tokens "a ==== b" [ "a"; "=="; "=="; "b"; "NL" ]);
  Harness.test "characters Truss does not use" (fun () ->
      error "@a" ~code:Unexpected_character ~at:"@";
      error "a ` b" ~code:Unexpected_character ~at:"`";
      error "a $ b" ~code:Unexpected_character ~at:"$");
  Harness.test "increment and decrement are left for the parser" (fun () ->
      tokens "i++\ni--\n--x" [ "i"; "++"; "NL"; "i"; "--"; "NL"; "--"; "x"; "NL" ])

let () =
  Harness.test "every punctuation lexes as itself" (fun () ->
      List.iter
        (fun (spelling, punctuation) ->
          match punctuation with
          | Token.Open _ | Close _ -> ()
          | _ -> tokens ("a " ^ spelling ^ " b") [ "a"; spelling; "b"; "NL" ])
        Token.punctuation);
  Harness.test "the longest match" (fun () ->
      tokens "a<<=b" [ "a"; "<<="; "b"; "NL" ];
      tokens "a==>b" [ "a"; "==>"; "b"; "NL" ];
      tokens "a::b" [ "a"; "::"; "b"; "NL" ])

let () =
  Harness.test "a float with no digit on one side of its point" (fun () ->
      error "x = 1." ~code:Number_missing_digits ~at:"." ~fixed:"x = 1.0";
      error "x = .5" ~code:Number_missing_digits ~at:"." ~fixed:"x = 0.5";
      error "f(.5e3, y)" ~code:Number_missing_digits ~at:"." ~fixed:"f(0.5e3, y)";
      error "return .25" ~code:Number_missing_digits ~at:"." ~fixed:"return 0.25";
      equal_lists Fun.id "tokens" [ "x"; "="; "1e0"; "NL" ] (tokens_of "x = 1."));
  Harness.test "a point after an operand is a member access" (fun () ->
      tokens "1.max(2)" [ "1"; "."; "max"; "("; "2"; ")"; "NL" ];
      tokens "1 . max" [ "1"; "."; "max"; "NL" ];
      tokens "1..2" [ "1"; ".."; "2"; "NL" ];
      tokens "pair.5" [ "pair"; "."; "5"; "NL" ];
      tokens "items[0].5" [ "items"; "["; "0"; "]"; "."; "5"; "NL" ]);
  Harness.test "C++'s digit separator becomes an underscore" (fun () ->
      error "1'000'000" ~code:Number_digit_separator ~at:"'" ~fixed:"1_000_000";
      equal_lists Fun.id "tokens" [ "1000000"; "NL" ] (tokens_of "1'000'000"));
  Harness.test "a hexadecimal float has no fix" (fun () ->
      error "0x1p3" ~code:Number_hexadecimal_float ~at:"0";
      error "0x1.8p-3" ~code:Number_hexadecimal_float ~at:"0";
      equal_lists Fun.id "tokens" [ "1"; "NL" ] (tokens_of "0x1.8p3"));
  Harness.test "a method call on a hexadecimal literal is not a hexadecimal float" (fun () ->
      tokens "0xFF.abs()" [ "255"; "."; "abs"; "("; ")"; "NL" ];
      tokens "0x1.bad" [ "1"; "."; "bad"; "NL" ]);
  Harness.test "an attribute has no fix" (fun () ->
      error "#[derive(Debug)]\ntype Point(x: Int64)" ~code:Attribute ~at:"#";
      error "#![allow(unused)]\nx" ~code:Attribute ~at:"#");
  Harness.test "an operator of another language becomes Truss's" (fun () ->
      error "a <> b" ~code:Foreign_operator ~at:"<>" ~fixed:"a != b";
      error "0..<count" ~code:Foreign_operator ~at:"..<" ~fixed:"0..count";
      equal_lists Fun.id "tokens" [ "a"; "!="; "b"; "NL" ] (tokens_of "a <> b"));
  Harness.test "three dots between operands are either range" (fun () ->
      error "1...5" ~code:Foreign_operator ~at:"..." ~fixed:"1..5" ~alternatives:[ "1..=5" ];
      equal_lists Fun.id "tokens" [ "a"; "..="; "b"; "NL" ] (tokens_of "a...b"));
  Harness.test "three dots alone are todo" (fun () ->
      error "fn f() { ... }" ~code:Foreign_operator ~at:"..." ~fixed:"fn f() { todo }";
      equal_lists Fun.id "tokens" [ "{"; "todo"; "}"; "NL" ] (tokens_of "{ ... }"));
  Harness.test "three dots before an operand have no fix" (fun () ->
      error "f(...items)" ~code:Foreign_operator ~at:"...";
      equal_lists Fun.id "tokens" [ "f"; "("; "items"; ")"; "NL" ] (tokens_of "f(...items)"));
  Harness.test "three dots that lex as nothing keep the line break before them" (fun () ->
      equal_lists Fun.id "tokens" (tokens_of "a,\nb") (tokens_of "a,\n...b");
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (tokens_of "a\n...\nb"));
  Harness.test "a chain of three dots decides each from the token after it" (fun () ->
      equal_lists Fun.id "tokens" [ "a"; "..="; "todo"; "NL" ] (tokens_of "a ... ... ..."));
  Harness.test "**, :=, and |> are tokens for the parser to report" (fun () ->
      tokens "a ** b" [ "a"; "**"; "b"; "NL" ];
      tokens "a := b" [ "a"; ":="; "b"; "NL" ];
      tokens "a |> b" [ "a"; "|>"; "b"; "NL" ];
      tokens "a\n  |> b" [ "a"; "|>"; "b"; "NL" ]);
  Harness.test "a character that looks like punctuation becomes it" (fun () ->
      error "f\u{FF08}x)" ~code:Confusable_character ~at:"\u{FF08}" ~fixed:"f(x)";
      error "a \u{2264} b" ~code:Confusable_character ~at:"\u{2264}" ~fixed:"a <= b";
      error "a\u{00A0}b" ~code:Confusable_character ~at:"\u{00A0}" ~fixed:"a b";
      error "\u{2200} x" ~code:Confusable_character ~at:"\u{2200}" ~fixed:"forall x";
      equal_lists Fun.id "tokens" [ "a"; "<="; "b"; "NL" ] (tokens_of "a \u{2264} b"));
  Harness.test "a string fix right after a string is withheld" (fun () ->
      List.iter
        (fun (text, code) -> equal_lists Fun.id ("fixed " ^ text) [] (fixed_texts text ~code))
        [
          ("x = \"\"$\"\"", Diagnostic.Code.String_prefix);
          ("x = \"\"f\"a\"", String_prefix);
          ("x = \"\"@\"a\"", String_prefix);
          ("x = \"\"r#\"a\"#", String_prefix);
          ("x = \"\"`a`", String_delimiter);
          ("x = \"\"\u{201C}a\u{201D}", Confusable_character);
        ]);
  Harness.test "a fix whose code would join a neighbor is withheld" (fun () ->
      error "p\u{2200}x" ~code:Confusable_character ~at:"\u{2200}";
      error "a\u{2013}>b" ~code:Confusable_character ~at:"\u{2013}";
      error "a\u{2013}b" ~code:Confusable_character ~at:"\u{2013}" ~fixed:"a-b";
      error "fn.5" ~code:Number_missing_digits ~at:".";
      error "a<>=b" ~code:Foreign_operator ~at:"<>";
      error "a..<.b" ~code:Foreign_operator ~at:"..<";
      error "Co@\"x\"" ~code:String_prefix ~at:"@";
      error "Co`x`" ~code:String_delimiter ~at:"`";
      error "x = 1u8.4" ~code:Number_suffix ~at:"u8";
      equal_lists Fun.id "fixed" [] (fixed_texts "x =..<.y" ~code:Foreign_operator);
      equal_lists Fun.id "fixed" [] (fixed_texts "f(01.: 0)" ~code:Number_leading_zero);
      equal_lists Fun.id "fixed" [] (fixed_texts "x = 0..<.0" ~code:Foreign_operator);
      equal_lists Fun.id "fixed" [] (fixed_texts "x = 0.'a" ~code:Number_missing_digits);
      equal_lists Fun.id "fixed" [ "a !=\u{21D2} b" ]
        (fixed_texts "a \u{2260}\u{21D2} b" ~code:Confusable_character));
  Harness.test "a float with no digit before its `.` and a suffix" (fun () ->
      error "x = .5f" ~code:Number_missing_digits ~at:".";
      equal_lists Fun.id "tokens" [ "x"; "="; "5e-1"; "NL" ] (tokens_of "x = .5f"));
  Harness.test "a confusable character after `1.` is not a member" (fun () ->
      equal_lists Fun.id "tokens" [ "0e0"; "-"; "1"; "NL" ] (tokens_of "0.\u{2013}1");
      equal_lists Fun.id "tokens" [ "1"; "."; "forall" ] (tokens_of "1.\u{2200}");
      equal_lists Fun.id "tokens" (tokens_of "1. .max") (tokens_of "1.\u{00A0}.max");
      equal_lists Fun.id "tokens" (tokens_of "f( .5)") (tokens_of "f(\u{00A0}.5)");
      equal_lists Fun.id "tokens" (tokens_of "f(\u{FF08}.5))") (tokens_of "f((.5))"));
  Harness.test "`...` before a float with no digit before its `.` is a range" (fun () ->
      equal_lists Fun.id "tokens" [ "3"; "..="; "14e-2"; "NL" ] (tokens_of "3....14"));
  Harness.test "equal floats are equal tokens" (fun () ->
      let kind text = (fst (lex text)).(0).kind in
      if kind "1.50" <> kind "1.5" || kind "15e-1" <> kind "1.5" || kind "100.0" <> kind "1e2" then
        Harness.fail "equal floats lex as different tokens");
  Harness.test "`1.` at the end of a line is a float" (fun () ->
      error "x = 1.\nmax" ~code:Number_missing_digits ~at:"." ~fixed:"x = 1.0\nmax");
  Harness.test "`1.` in an interpolation is a float" (fun () ->
      equal_lists Fun.id "tokens"
        (interpolation_tokens "\"${1.0}\"" 0)
        (interpolation_tokens "\"${1.}\"" 0));
  Harness.test "`1.` before a member is an integer" (fun () ->
      tokens "1.max" [ "1"; "."; "max"; "NL" ];
      tokens "1..2" [ "1"; ".."; "2"; "NL" ]);
  Harness.test "a file recovers as its machine-applicable fixes write" (fun () ->
      List.iter
        (fun text ->
          equal_lists Fun.id
            ("recovered tokens of " ^ String.escaped text)
            (recovered_tokens (machine_fixed text))
            (recovered_tokens text))
        [
          "f(a\n\u{202E}let x = 1\n";
          "let middle = items[;let total = 1\n";
          "a = 1\n\u{2003}\nlet b = 2\n";
          "x = f\"a {b} c\"\n";
          "if a === b \u{2264} c { f(x\u{FF09} }\n";
          "push(item: name\u{2192}'e)\n";
        ]);
  Harness.test "an interpolation that holds a rejected character has no fix" (fun () ->
      equal_lists Fun.id "fixed" [] (fixed_texts "\"a ${\\} b\"" ~code:Empty_interpolation));
  Harness.test "the indentation fix keeps a forbidden character whole" (fun () ->
      equal_lists Fun.id "fixed"
        [ "x = \"\"\"\n  \u{0085} a\n  \"\"\"\n" ]
        (fixed_texts "x = \"\"\"\n\u{0085} a\n  \"\"\"\n" ~code:Raw_string_indentation))

let () =
  Harness.test "a line break ends a statement" (fun () -> tokens "a\nb" [ "a"; "NL"; "b"; "NL" ]);
  Harness.test "a line that starts with an operator continues" (fun () ->
      tokens "a\n  .b()\n  + c" [ "a"; "."; "b"; "("; ")"; "+"; "c"; "NL" ]);
  Harness.test "a line that starts with - is a new statement" (fun () ->
      tokens "a\n- b" [ "a"; "NL"; "-"; "b"; "NL" ]);
  Harness.test "line breaks inside parentheses are ignored" (fun () ->
      tokens "f(a,\n  b)" [ "f"; "("; "a"; ","; "b"; ")"; "NL" ]);
  Harness.test "line breaks inside braces count again" (fun () ->
      tokens "f({\n  a\n  b\n})" [ "f"; "("; "{"; "a"; "NL"; "b"; "}"; ")"; "NL" ]);
  Harness.test "clauses and else continue the line" (fun () ->
      tokens "fn f()\n  requires a\n{\n}\nelse {}"
        [ "fn"; "f"; "("; ")"; "requires"; "a"; "NL"; "{"; "}"; "else"; "{"; "}"; "NL" ]);
  Harness.test "several line breaks give one NEWLINE, and a blank line is noted" (fun () ->
      let tokens, _ = lex "a\n\n\nb" in
      equal_lists Fun.id "tokens" [ "a"; "NL"; "b"; "NL" ] (shown tokens);
      if not tokens.(2).blank_line_before then Harness.fail "b has a blank line before it");
  Harness.test "a comment line is not a blank line" (fun () ->
      let tokens, _ = lex "a\n// c\nb" in
      if tokens.(2).blank_line_before then Harness.fail "b has no blank line before it")

let () =
  Harness.test "two unclosed brackets inside another each close before its closer" (fun () ->
      equal_lists Fun.id "fixed" [ "f({[1, 2})"; "f({[1, 2])" ]
        (fixed_texts "f({[1, 2)" ~code:Unclosed_bracket));
  Harness.test "a closer with no opener among open brackets is dropped" (fun () ->
      error "f(1 ] , 2)" ~code:Unmatched_closing_bracket ~at:"]";
      equal_lists Fun.id "tokens" [ "f"; "("; "1"; ","; "2"; ")"; "NL" ] (tokens_of "f(1 ] , 2)"));
  Harness.test "an unclosed bracket inside another" (fun () ->
      error "f(1, [2)" ~code:Unclosed_bracket ~at:"[" ~fixed:"f(1, [2])";
      equal_lists Fun.id "tokens"
        [ "f"; "("; "1"; ","; "["; "2"; "+]"; ")"; "NL" ]
        (tokens_of "f(1, [2)"));
  Harness.test "the indentation says where a bracket was meant to close" (fun () ->
      error "fn f() {\n  let x = [1, 2\n  g(x)\n}\n" ~code:Unclosed_bracket ~at:"["
        ~fixed:"fn f() {\n  let x = [1, 2]\n  g(x)\n}\n";
      error "f(\n  a,\n  b\n" ~code:Unclosed_bracket ~at:"(" ~fixed:"f(\n  a,\n  b)\n");
  Harness.test "a closer goes after the last token, not inside a comment that ends the line"
    (fun () ->
      equal_lists Fun.id "fixed" [ "f(a, b) // note\n" ]
        (fixed_texts "f(a, b // note\n" ~code:Unclosed_bracket));
  Harness.test "a closer goes after a nested group, not inside it" (fun () ->
      equal_lists Fun.id "fixed" [ "x = m(a {\n  b\n})\n" ]
        (fixed_texts "x = m(a {\n  b\n}\n" ~code:Unclosed_bracket));
  Harness.test "a bracket whose closer a cut-off string swallowed has no fix" (fun () ->
      equal_lists Fun.id "fixed" [] (fixed_texts "f(a, \"b)\n" ~code:Unclosed_bracket);
      equal_lists Fun.id "fixed" [] (fixed_texts "f(a, \"b)\n" ~code:Unterminated_string);
      equal_lists Fun.id "fixed" [ "f(a, \"b\"\n" ]
        (fixed_texts "f(a, \"b\n" ~code:Unterminated_string));
  Harness.test "a missing } goes on a line of its own" (fun () ->
      error "fn f() {\n  body\n" ~code:Unclosed_bracket ~at:"{" ~fixed:"fn f() {\n  body\n}\n");
  Harness.test "a closer that matches nothing is dropped" (fun () ->
      error "a }" ~code:Unmatched_closing_bracket ~at:"}";
      equal_lists Fun.id "tokens" [ "a"; "NL" ] (tokens_of "a }"));
  Harness.test "a bracket still open at the end of the file" (fun () ->
      error "let x = (1\n" ~code:Unclosed_bracket ~at:"(" ~fixed:"let x = (1)\n");
  Harness.test "a definition in column 0 closes open brackets" (fun () ->
      let text = "fn a() {\n  f(1,\nfn b() {}\n" in
      error text ~code:Unclosed_bracket ~at:"(" ~occurrence:2
        ~fixed:"fn a() {\n  f(1,)\n}\nfn b() {}\n";
      equal_lists Fun.id "tokens"
        [
          "fn";
          "a";
          "(";
          ")";
          "{";
          "f";
          "(";
          "1";
          ",";
          "+)";
          "+}";
          "NL";
          "fn";
          "b";
          "(";
          ")";
          "{";
          "}";
          "NL";
        ]
        (tokens_of text));
  Harness.test "a closer before a deleted character stays inside its interpolation" (fun () ->
      let text = "x = \"${f(a\u{200B}\n" in
      match (fst (lex text)).(2).kind with
      | String { rest = [| (interpolation, _) |]; _ } ->
          Array.iter
            (fun (token : Token.t) ->
              if
                token.span.start < interpolation.span.start
                || token.span.stop > interpolation.span.stop
              then
                Harness.fail "%s at %d-%d is outside the interpolation at %d-%d" (show token)
                  token.span.start token.span.stop interpolation.span.start interpolation.span.stop)
            interpolation.tokens
      | _ -> Harness.fail "expected a string with one interpolation");
  Harness.test "a balanced file gets no closers before a definition keyword in column 0" (fun () ->
      tokens "f(\nfn)" [ "f"; "("; "fn"; ")"; "NL" ]);
  Harness.test "brackets swallowed by an unterminated comment are not reported" (fun () ->
      equal_lists Fun.id "codes" [ "lexer.comment" ] (codes "f( /* never closed"))

let () =
  Harness.test "at most 200 diagnostics are shown, then a count" (fun () ->
      let diagnostic offset =
        Diagnostic.make ~code:(Lexer Semicolon) (Source.span offset (offset + 1)) "x"
      in
      let shown = Diagnostic.shown (List.init 250 diagnostic) in
      if List.length shown <> Diagnostic.For_testing.limit + 1 then
        Harness.fail "%d shown" (List.length shown);
      match List.rev shown with
      | last :: _ when last.code = Too_many_diagnostics -> ()
      | _ -> Harness.fail "the last one counts the rest");
  Harness.test "diagnostics past the limit do not cost the shown ones their fixes" (fun () ->
      let text = String.concat "" (List.init 250 (Printf.sprintf "a%d;\n")) in
      List.iteri
        (fun index (diagnostic : Diagnostic.t) ->
          if index < Diagnostic.For_testing.limit && diagnostic.fixes = [] then
            Harness.fail "diagnostic %d has no fix" index)
        (snd (lex text)));
  Harness.test "overlapping edits are refused" (fun () ->
      let fix =
        Diagnostic.fix "x"
          [ Diagnostic.delete (Source.span 0 2); Diagnostic.delete (Source.span 1 3) ]
      in
      match Diagnostic.apply_fix "abc" fix with
      | _ -> Harness.fail "expected Invalid_argument"
      | exception Invalid_argument _ -> ())

let () =
  Harness.test "the fixes for errors in two definitions each remove only their own error" (fun () ->
      let text =
        "fn a() {\n  let userName = 1;\n  f(1,\n}\nfn b() {\n  let x = 0755 // note\n}\n"
      in
      let before = List.sort compare (codes text) in
      List.iter
        (fun (diagnostic : Diagnostic.t) ->
          List.iter
            (fun fix ->
              let expected =
                let rec remove_one = function
                  | [] -> []
                  | code :: rest ->
                      if code = Diagnostic.Code.name diagnostic.code then rest
                      else code :: remove_one rest
                in
                remove_one before
              in
              equal_lists Fun.id "codes after the fix" expected
                (List.sort compare (codes (Diagnostic.apply_fix text fix))))
            diagnostic.fixes)
        (snd (lex text)))

let document = Parse_support.document
let truss_blocks name = Documents.truss_blocks (document name)
let block_after = Documents.block_after
let words = Documents.words

let between text first second =
  let start = Option.get (Substring.For_testing.find text first) + String.length first in
  let rest = String.sub text start (String.length text - start) in
  String.sub rest 0 (Option.get (Substring.For_testing.find rest second))
  |> String.split_on_char '\n' |> List.map String.trim |> String.concat " "

let backticked text =
  match String.split_on_char '`' text with
  | [] -> []
  | _ :: rest -> List.filteri (fun index _ -> index mod 2 = 0) rest

let () =
  let specification = document "SPECIFICATION.md" in
  let spellings list = List.sort_uniq compare (List.map fst list) in
  Harness.test "SPECIFICATION.md lists the keywords" (fun () ->
      equal_lists Fun.id "keywords" (spellings Token.keywords)
        (words (block_after specification "Reserved everywhere:")));
  Harness.test "SPECIFICATION.md lists the reserved words" (fun () ->
      equal_lists Fun.id "reserved" (spellings Token.reserved_words)
        (words (block_after specification "Reserved for later use")));
  Harness.test "SPECIFICATION.md lists the punctuation" (fun () ->
      equal_lists Fun.id "punctuation" (spellings Token.punctuation)
        (words (block_after specification "### Punctuation")));
  Harness.test "SPECIFICATION.md's line-break lists match Layout" (fun () ->
      let kind_of spelling =
        match Token.word spelling with
        | Some kind -> Some kind
        | None ->
            if spelling = "_" then Some Underscore
            else
              Option.map
                (fun punctuation -> Token.Punctuation punctuation)
                (List.assoc_opt spelling Token.punctuation)
      in
      let listed first second =
        List.filter_map kind_of (backticked (between specification first second))
      in
      let can_end = listed "**can end a statement**:" "- the first token after it" in
      let can_begin = listed "**can begin a statement**:" "3. Several line feeds" in
      let spelling = function
        | Token.Keyword keyword -> Token.keyword_spelling keyword
        | Punctuation punctuation -> Token.punctuation_spelling punctuation
        | _ -> "_"
      in
      List.iter
        (fun kind ->
          if Token.can_end kind <> List.mem kind can_end then
            Harness.fail "can_end %s" (spelling kind);
          if Token.can_begin kind <> List.mem kind can_begin then
            Harness.fail "can_begin %s" (spelling kind))
        (List.map (fun (_, keyword) -> Token.Keyword keyword) Token.keywords
        @ List.map (fun (_, punctuation) -> Token.Punctuation punctuation) Token.punctuation
        @ [ Underscore ]));
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          Harness.test
            (Printf.sprintf "%s block %d lexes cleanly" name (index + 1))
            (fun () -> equal_lists Fun.id "codes" [] (codes text)))
        (truss_blocks name))
    (Harness.markdown_documents ())
