(* [truss debug tokens] and [truss debug tree], for working on the compiler:
   a file's tokens, or its syntax trees as S-expressions, and its
   diagnostics. See CLI.md, "For working on the compiler". *)

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
              (fun (interpolation : Token.interpolation) ->
                print (indent ^ "    ") interpolation.tokens)
              (Token.interpolations literal)
        | _ -> ())
      tokens
  in
  print "" tokens

let show_diagnostics ~json source diagnostics =
  let shown = Diagnostic.shown diagnostics in
  if json then print_string (Diagnostic.to_json source shown)
  else List.iter (fun diagnostic -> prerr_string (Diagnostic.render source diagnostic)) shown;
  if diagnostics = [] then 0 else 1

let read file =
  if not (Sys.file_exists file) then Project.cannot_run "%s does not exist." file;
  Source.read_file file

(* Lexes one file and prints its tokens, one per line, unless [json], when
   it prints only the diagnostics as JSON. *)
let tokens ~file ~json =
  let source = read file in
  let tokens, diagnostics = Lexer.lex source in
  if not json then print_tokens source tokens;
  show_diagnostics ~json source diagnostics

(* Lexes and parses one file and prints each definition's tree, unless
   [json], when it prints only the diagnostics as JSON. *)
let tree ~file ~json =
  let source = read file in
  let tokens, lexer_diagnostics = Lexer.lex source in
  let tree, parser_diagnostics = Parser.parse source tokens in
  let diagnostics =
    List.stable_sort
      (fun (a : Diagnostic.t) (b : Diagnostic.t) -> compare a.span.start b.span.start)
      (lexer_diagnostics @ parser_diagnostics)
  in
  if not json then print_endline (Syntax_print.file tree);
  show_diagnostics ~json source diagnostics
