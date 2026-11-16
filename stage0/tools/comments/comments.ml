type syntax = Ocaml | Markers of string list | Hash_at_word_start | Truss | Generated

let syntax path =
  match (Filename.basename path, Filename.extension path) with
  | _, (".ml" | ".mli") -> Some Ocaml
  | _, ".mly" -> Some (Markers [ "/*"; "//"; "(*" ])
  | _, (".c" | ".js") -> Some (Markers [ "/*"; "//" ])
  | _, ".css" -> Some (Markers [ "/*" ])
  | _, (".html" | ".md") -> Some (Markers [ "<!--" ])
  | ("dune" | "dune-project"), _ -> Some (Markers [ ";"; "#|" ])
  | (".gitignore" | ".ocamlformat" | ".ocamlformat-ignore"), _ | _, (".sh" | ".yml" | ".txt") ->
      Some Hash_at_word_start
  | _, ".truss" -> Some Truss
  | _, ".opam" -> Some Generated
  | _ -> None

let has_hash_at_word_start line =
  let rec scan start =
    match String.index_from_opt line start '#' with
    | None -> false
    | Some index ->
        index = 0 || line.[index - 1] = ' ' || line.[index - 1] = '\t' || scan (index + 1)
  in
  scan 0

let is_shebang index line = index = 0 && String.starts_with ~prefix:"#!" line

let matching_lines is_comment text =
  List.concat
    (List.mapi
       (fun index line -> if is_comment index line then [ index + 1 ] else [])
       (String.split_on_char '\n' text))

let ocaml_comment_lines text =
  let lexbuf = Lexing.from_string text in
  Lexer.init ();
  let rec lex () = match Lexer.token lexbuf with Parser.EOF -> () | _ -> lex () in
  lex ();
  List.map (fun (_, (location : Location.t)) -> location.loc_start.pos_lnum) (Lexer.comments ())

let comment_lines path syntax =
  let text = In_channel.with_open_bin path In_channel.input_all in
  match syntax with
  | Ocaml -> ocaml_comment_lines text
  | Markers markers ->
      matching_lines
        (fun _ line -> List.exists (fun affix -> String.includes ~affix line) markers)
        text
  | Hash_at_word_start ->
      matching_lines
        (fun index line -> has_hash_at_word_start line && not (is_shebang index line))
        text
  | Truss | Generated -> []

let () =
  let failures =
    List.concat_map
      (fun path ->
        match syntax path with
        | None ->
            [
              Printf.sprintf
                "%s: no comment syntax is known for this type of file; add it to \
                 stage0/tools/comments/comments.ml"
                path;
            ]
        | Some syntax ->
            List.map (Printf.sprintf "%s:%d: remove this comment" path) (comment_lines path syntax))
      (List.tl (Array.to_list Sys.argv))
  in
  List.iter print_endline failures;
  if failures <> [] then exit 1
