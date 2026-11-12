(* Functions that the other parsing modules share: constructors for tree
   nodes, parsers for names, module prefixes, string literals, and modes,
   and the first sets of expressions and statements. *)

open Token
open Syntax

let expression_node cursor start kind : expression =
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

let type_node cursor start kind : type_expression =
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

let error_expression cursor start : expression = expression_node cursor start Expression_error

(* Whether a token is in the first set of an expression. *)
let begins_expression = function
  | Upper _ | Lower _ | Integer _ | Float _ | String _ -> true
  | Punctuation (Open _ | Minus | Bang | Tilde | Dot_dot | Dot_dot_equal) -> true
  | Keyword
      ( True | False | Todo | Unreachable | Break | Continue | Self_value | Self_type | Fn | If
      | Match | Provide | Mut | Own | Any | Echo | Return | Forall | Exists ) ->
      true
  | _ -> false

(* Whether a token is in the first set of a statement: of a statement that
   is not an expression, or of an expression. *)
let begins_statement = function
  | Keyword (Let | Var | For | While | Parallel | Concurrent | Proof | Assert | Yield) -> true
  | kind -> begins_expression kind

let mode cursor =
  if Cursor.accept_keyword cursor Mut then Some Mut
  else if Cursor.accept_keyword cursor Own then Some Own
  else None

let name cursor (token : Token.t) text : Syntax.name =
  { text; span = Cursor.span cursor token.span; id = Cursor.fresh_id cursor }

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
        { modules; last = { text; span = Cursor.span cursor span; id = Cursor.fresh_id cursor } })
      literal.tag
  in
  {
    tag;
    first = text cursor literal.first;
    rest =
      Array.to_list
        (Array.map (fun (inner, piece) -> (interpolation inner, text cursor piece)) literal.rest);
    span = Cursor.span_from cursor start;
    id = Cursor.fresh_id cursor;
  }
