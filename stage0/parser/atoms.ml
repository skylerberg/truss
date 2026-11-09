(* The smallest pieces the other parsing modules share: names, module
   prefixes, and string literals. *)

open Token

let name cursor (token : Token.t) text : Syntax.name =
  { text; span = Cursor.span cursor token.span }

let lower cursor what =
  match Cursor.peek_kind cursor with
  | Lower text -> name cursor (Cursor.next cursor) text
  | _ -> Cursor.fail cursor what

let upper cursor what =
  match Cursor.peek_kind cursor with
  | Upper text -> name cursor (Cursor.next cursor) text
  | _ -> Cursor.fail cursor what

(* The modules of a path, [standard::json::] in [standard::json::parse]:
   each lowercase name followed by [::]. *)
let module_prefix cursor =
  let rec loop modules =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Lower text, Punctuation Colon_colon ->
        let module_name = name cursor (Cursor.next cursor) text in
        Cursor.advance cursor;
        loop (module_name :: modules)
    | _ -> List.rev modules
  in
  loop []

(* A path to an uppercase name, with optional modules: [geometry::Shape]. *)
let upper_path cursor what : Syntax.path =
  let modules = module_prefix cursor in
  { modules; last = upper cursor what }

let text cursor (text : Token.text) : Syntax.text =
  { value = text.value; span = Cursor.span cursor text.span }

(* A string literal whose token is the current one, after [modules], the
   module path written before its tag. Its interpolations are parsed by
   [interpolation]. *)
let string_literal cursor ~start ~modules (literal : Token.string_literal) ~interpolation :
    Syntax.string_literal =
  Cursor.advance cursor;
  let tag =
    Option.map
      (fun (text, span) : Syntax.path ->
        { modules; last = { text; span = Cursor.span cursor span } })
      literal.tag
  in
  {
    tag;
    first = text cursor literal.first;
    rest =
      Array.to_list
        (Array.map (fun (inner, piece) -> (interpolation inner, text cursor piece)) literal.rest);
    span = Cursor.span_from cursor start;
  }
