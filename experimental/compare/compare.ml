let read_file path = In_channel.with_open_bin path In_channel.input_all

let escape value =
  let buffer = Buffer.create (String.length value + 2) in
  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | character -> Buffer.add_char buffer character)
    value;
  Buffer.contents buffer

let show_span (span : Source.span) = Printf.sprintf "%d..%d" span.start span.stop

let show_diagnostic (diagnostic : Diagnostic.t) =
  let lines =
    Printf.sprintf "%s %s \"%s\""
      (Diagnostic.Code.name diagnostic.code)
      (show_span diagnostic.span) (escape diagnostic.message)
    :: List.map
         (fun ((span : Source.span), message) ->
           Printf.sprintf "  note %s \"%s\"" (show_span span) (escape message))
         diagnostic.notes
    @ List.concat_map
        (fun (fix : Source.span Diagnostic.fix) ->
          Printf.sprintf "  fix \"%s\"" (escape fix.title)
          :: List.map
               (fun (edit : Source.span Diagnostic.edit) ->
                 Printf.sprintf "    edit %s \"%s\"" (show_span edit.span) (escape edit.replacement))
               fix.edits)
        diagnostic.fixes
  in
  String.concat "\n" lines

let show_form (form : Token.form) =
  match form with
  | Ordinary -> "ordinary"
  | Raw { quotes; dollars; multi_line } -> Printf.sprintf "raw %d %d %b" quotes dollars multi_line

let show_text (text : Token.text) =
  Printf.sprintf "\"%s\" %s" (escape text.value) (show_span text.span)

let rec show_token (token : Token.t) =
  let kind =
    match token.kind with
    | Upper name -> "upper " ^ name
    | Lower name -> "lower " ^ name
    | Underscore -> "underscore"
    | Keyword keyword -> "keyword " ^ Token.spell_keyword keyword
    | Reserved reserved -> "reserved " ^ Token.spell_reserved reserved
    | Integer value -> "integer " ^ Z.to_string value
    | Float { significand; exponent } ->
        Printf.sprintf "float %se%s" (Z.to_string significand) (Z.to_string exponent)
    | String literal -> "string " ^ show_literal literal
    | Punctuation punctuation -> "punctuation " ^ Token.spell_punctuation punctuation
    | Foreign foreign -> "foreign " ^ Token.spell_foreign foreign
    | Newline -> "newline"
    | End_of_file -> "end"
  in
  Printf.sprintf "%s %s%s%s%s" kind (show_span token.span)
    (if token.line_break_before then " line" else "")
    (if token.blank_line_before then " blank" else "")
    (if token.is_inserted_closer then " inserted" else "")

and show_literal (literal : Token.string_literal) =
  let tag =
    match literal.tag with
    | Some (name, span) -> Printf.sprintf "tag %s %s " name (show_span span)
    | None -> ""
  in
  tag ^ show_form literal.form ^ " " ^ show_text literal.first
  ^ String.concat ""
      (Array.to_list
         (Array.map
            (fun ((interpolation : Token.interpolation), text) ->
              Printf.sprintf " { %s %b [ %s ] } %s" (show_span interpolation.span)
                interpolation.is_closed
                (String.concat " ; " (Array.to_list (Array.map show_token interpolation.tokens)))
                (show_text text))
            literal.rest))

let print_tokens path =
  let text = read_file path in
  let tokens, diagnostics = Lexer.lex (Source.create ~path text) in
  let diagnostics = List.map (Syntax_catalog.Lexing_description.render ~text) diagnostics in
  print_string ("== " ^ path ^ "\n");
  Array.iter (fun token -> print_string (show_token token ^ "\n")) tokens;
  List.iter (fun diagnostic -> print_string (show_diagnostic diagnostic ^ "\n")) diagnostics

let print_file path =
  let text = read_file path in
  let file, diagnostics = Parser.parse_source (Source.create ~path text) in
  let diagnostics = List.map (Syntax_catalog.Syntax_diagnostic.render ~text) diagnostics in
  print_string ("== " ^ path ^ "\n");
  let tree = Syntax_print.show_file file in
  if tree <> "" then print_string (tree ^ "\n");
  List.iter (fun diagnostic -> print_string (show_diagnostic diagnostic ^ "\n")) diagnostics

let measure_best_time ~rounds run =
  let best = ref infinity in
  for _ = 1 to rounds do
    let start = Unix.gettimeofday () in
    run ();
    best := Float.min !best (Unix.gettimeofday () -. start)
  done;
  Int64.of_float (!best *. 1e9)

let time_file ~rounds path =
  let text = read_file path in
  let lexing =
    measure_best_time ~rounds (fun () -> ignore (Lexer.lex (Source.create ~path text)))
  in
  let tokens, lexer_diagnostics = Lexer.lex (Source.create ~path text) in
  let parsing =
    measure_best_time ~rounds (fun () -> ignore (Parser.parse tokens ~lexer_diagnostics))
  in
  Printf.printf "%Ld %Ld %d %s\n" lexing parsing (String.length text) path;
  (lexing, parsing)

let () =
  match Array.to_list Sys.argv with
  | _ :: "print" :: paths -> List.iter print_file paths
  | _ :: "tokens" :: paths -> List.iter print_tokens paths
  | _ :: "time" :: rounds :: paths ->
      let rounds = int_of_string rounds in
      let lexing, parsing =
        List.fold_left
          (fun (lexing, parsing) path ->
            let file_lexing, file_parsing = time_file ~rounds path in
            (Int64.add lexing file_lexing, Int64.add parsing file_parsing))
          (0L, 0L) paths
      in
      Printf.printf "%Ld %Ld total\n" lexing parsing
  | _ ->
      prerr_endline "compare print FILE...\ncompare tokens FILE...\ncompare time ROUNDS FILE...";
      exit 2
