(* truss-lex [--json] [--tokens] FILE

   Lexes one file and prints its diagnostics, for people or, with --json,
   for tools. With --tokens it also prints the tokens, one per line. Exits
   with status 1 if there are diagnostics. *)

open Token

let float_to_string significand exponent =
  Printf.sprintf "%se%s" (Z.to_string significand) (Z.to_string exponent)

let rec describe kind =
  match kind with
  | Upper name -> Printf.sprintf "Upper %s" name
  | Lower name -> Printf.sprintf "Lower %s" name
  | Underscore -> "_"
  | Keyword keyword -> Printf.sprintf "Keyword %s" (Token.keyword_spelling keyword)
  | Reserved reserved -> Printf.sprintf "Reserved %s" (Token.reserved_spelling reserved)
  | Integer value -> Printf.sprintf "Integer %s" (Z.to_string value)
  | Float { significand; exponent } -> "Float " ^ float_to_string significand exponent
  | String literal -> describe_string literal
  | Punctuation punctuation -> Printf.sprintf "'%s'" (Token.punctuation_spelling punctuation)
  | Foreign foreign -> Printf.sprintf "Foreign %s" (Token.foreign_spelling foreign)
  | Newline -> "Newline"
  | End_of_file -> "End_of_file"

and describe_string literal =
  let form =
    match literal.form with
    | Ordinary -> "String"
    | Raw { quotes; dollars; multi_line } ->
        Printf.sprintf "Raw(%d quotes, %d dollars%s)" quotes dollars
          (if multi_line then ", multi-line" else "")
  in
  let tag = match literal.tag with Some (tag, _) -> tag ^ " " | None -> "" in
  let parts = Buffer.create 32 in
  Array.iteri
    (fun index (text : Token.text) ->
      if index > 0 then Buffer.add_string parts " ${...} ";
      Buffer.add_string parts (Diagnostic.quote text.value))
    (Token.texts literal);
  Printf.sprintf "%s%s %s" tag form (Buffer.contents parts)

let print_tokens source tokens =
  let rec print indent (tokens : Token.t array) =
    Array.iter
      (fun (token : Token.t) ->
        let line, column = Source.position source token.span.start in
        let flags =
          (if token.line_break_before then " [line break]" else "")
          ^ if token.blank_line_before then " [blank line]" else ""
        in
        Printf.printf "%s%d:%d+%d %s%s\n" indent line column
          (token.span.stop - token.span.start)
          (describe token.kind) flags;
        match token.kind with
        | String literal ->
            Array.iter
              (fun (interpolation : Token.interpolation) -> print (indent ^ "    ") interpolation.tokens)
              (Token.interpolations literal)
        | _ -> ())
      tokens
  in
  print "" tokens

let () =
  let json = ref false and show_tokens = ref false and files = ref [] in
  Arg.parse
    [
      ("--json", Arg.Set json, " Print diagnostics as JSON");
      ("--tokens", Arg.Set show_tokens, " Print the tokens too");
    ]
    (fun file -> files := file :: !files)
    "truss-lex [--json] [--tokens] FILE";
  match !files with
  | [ file ] ->
      let source = Source.read_file file in
      let tokens, diagnostics = Lexer.lex source in
      if !show_tokens then print_tokens source tokens;
      let shown = Diagnostic.shown diagnostics in
      if !json then print_string (Diagnostic.to_json source shown)
      else List.iter (fun diagnostic -> print_string (Diagnostic.render source diagnostic)) shown;
      exit (if diagnostics = [] then 0 else 1)
  | _ ->
      prerr_endline "truss-lex: expected one file";
      exit 2
