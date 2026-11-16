let make_expression_node cursor start kind : Syntax.expression =
  { kind; id = Cursor.allocate_id_from cursor start }

let make_type_node cursor start kind : Syntax.type_expression =
  { kind; id = Cursor.allocate_id_from cursor start }

let make_error_expression cursor start : Syntax.expression =
  make_expression_node cursor start Expression_error

let begins_expression = function
  | Token.Upper _ | Lower _ | Integer _ | Float _ | String _ -> true
  | Punctuation (Open _ | Minus | Bang | Tilde | Dot_dot | Dot_dot_equal) -> true
  | Keyword
      ( True | False | Todo | Unreachable | Break | Continue | Self_value | Self_type | Fn | If
      | Match | Provide | Mut | Own | Any | Echo | Return | Forall | Exists ) ->
      true
  | _ -> false

let begins_statement = function
  | Token.Keyword (Let | Var | For | While | Parallel | Concurrent | Proof | Assert) -> true
  | kind -> begins_expression kind

let parse_mode cursor =
  if Cursor.accept_keyword cursor Mut then Some Syntax.Mut
  else if Cursor.accept_keyword cursor Own then Some Own
  else None

let make_name cursor (token : Token.t) text : Syntax.name =
  { text; id = Cursor.allocate_id cursor (Cursor.make_definition_span cursor token.span) }

let lower_name cursor expected =
  match Cursor.peek_kind cursor with
  | Lower text -> make_name cursor (Cursor.take cursor) text
  | _ -> Cursor.fail cursor expected

let parse_upper_name cursor expected =
  match Cursor.peek_kind cursor with
  | Upper text -> make_name cursor (Cursor.take cursor) text
  | _ -> Cursor.fail cursor expected

let parse_module_prefix cursor =
  let rec gather modules =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Lower text, Punctuation Colon_colon ->
        let module_name = make_name cursor (Cursor.take cursor) text in
        Cursor.advance cursor;
        gather (module_name :: modules)
    | _ -> List.rev modules
  in
  gather []

let parse_upper_path cursor expected : Syntax.path =
  let modules = parse_module_prefix cursor in
  { modules; last = parse_upper_name cursor expected }

let make_text cursor (text : Token.text) : Syntax.text =
  {
    value = text.value;
    id = Cursor.allocate_id cursor (Cursor.make_definition_span cursor text.span);
  }

let make_string_literal cursor ~start ~modules (literal : Token.string_literal) ~interpolation :
    Syntax.string_literal =
  Cursor.advance cursor;
  let tag =
    Option.map
      (fun (text, span) : Syntax.path ->
        {
          modules;
          last = { text; id = Cursor.allocate_id cursor (Cursor.make_definition_span cursor span) };
        })
      literal.tag
  in
  {
    tag;
    form = literal.form;
    first = make_text cursor literal.first;
    rest =
      Array.to_list
        (Array.map
           (fun (inner, piece) -> (interpolation inner, make_text cursor piece))
           literal.rest);
    id = Cursor.allocate_id_from cursor start;
  }
