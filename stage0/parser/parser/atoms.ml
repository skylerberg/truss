open Token
open Syntax

let expression_node cursor start kind : expression =
  { kind; id = Cursor.allocate_id_from cursor start }

let type_node cursor start kind : type_expression =
  { kind; id = Cursor.allocate_id_from cursor start }

let error_expression cursor start : expression = expression_node cursor start Expression_error

let begins_expression = function
  | Upper _ | Lower _ | Integer _ | Float _ | String _ -> true
  | Punctuation (Open _ | Minus | Bang | Tilde | Dot_dot | Dot_dot_equal) -> true
  | Keyword
      ( True | False | Todo | Unreachable | Break | Continue | Self_value | Self_type | Fn | If
      | Match | Provide | Mut | Own | Any | Echo | Return | Forall | Exists ) ->
      true
  | _ -> false

let begins_statement = function
  | Keyword (Let | Var | For | While | Parallel | Concurrent | Proof | Assert) -> true
  | kind -> begins_expression kind

let mode cursor =
  if Cursor.accept_keyword cursor Mut then Some Mut
  else if Cursor.accept_keyword cursor Own then Some Own
  else None

let name cursor (token : Token.t) text : Syntax.name =
  { text; id = Cursor.allocate_id cursor (Cursor.definition_span cursor token.span) }

let lower_name cursor expected =
  match Cursor.peek_kind cursor with
  | Lower text -> name cursor (Cursor.next cursor) text
  | _ -> Cursor.fail cursor expected

let upper_name cursor expected =
  match Cursor.peek_kind cursor with
  | Upper text -> name cursor (Cursor.next cursor) text
  | _ -> Cursor.fail cursor expected

let module_prefix cursor =
  let rec gather modules =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Lower text, Punctuation Colon_colon ->
        let module_name = name cursor (Cursor.next cursor) text in
        Cursor.advance cursor;
        gather (module_name :: modules)
    | _ -> List.rev modules
  in
  gather []

let upper_path cursor expected : Syntax.path =
  let modules = module_prefix cursor in
  { modules; last = upper_name cursor expected }

let text cursor (text : Token.text) : Syntax.text =
  { value = text.value; id = Cursor.allocate_id cursor (Cursor.definition_span cursor text.span) }

let string_literal cursor ~start ~modules (literal : Token.string_literal) ~interpolation :
    Syntax.string_literal =
  Cursor.advance cursor;
  let tag =
    Option.map
      (fun (text, span) : Syntax.path ->
        {
          modules;
          last = { text; id = Cursor.allocate_id cursor (Cursor.definition_span cursor span) };
        })
      literal.tag
  in
  {
    tag;
    form = literal.form;
    first = text cursor literal.first;
    rest =
      Array.to_list
        (Array.map (fun (inner, piece) -> (interpolation inner, text cursor piece)) literal.rest);
    id = Cursor.allocate_id_from cursor start;
  }
