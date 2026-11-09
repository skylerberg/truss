type anchor = { definition : Ground.definition; path : string; first_line : int }

let c_string text =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (fun c ->
      match c with
      | '"' | '\\' | '?' -> Buffer.add_string buffer (Printf.sprintf "\\%03o" (Char.code c))
      | c when Char.code c < 0x20 || Char.code c >= 0x7f ->
          Buffer.add_string buffer (Printf.sprintf "\\%03o" (Char.code c))
      | c -> Buffer.add_char buffer c)
    text;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let anchors_file target anchors =
  Emit_c.runtime_declarations target
  ^ String.concat ""
      (List.map
         (fun anchor ->
           (* A site's line counts from 0 at the definition's first line. *)
           Printf.sprintf "const struct t_anchor %s = { (const uint8_t *)%s, %d, %d };\n"
             (Emit_c.anchor_symbol anchor.definition)
             (c_string anchor.path) (String.length anchor.path) anchor.first_line)
         anchors)
