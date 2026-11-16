let make_pattern_node cursor start kind : Syntax.pattern =
  { kind; id = Cursor.allocate_id_from cursor start }

let range_bound = "a literal or a constant with its module or type, such as `http::last`"

let parse_string_literal cursor ~start ~modules literal =
  let string = Cursor.peek cursor in
  let interpolation (_ : Token.interpolation) =
    Cursor.report cursor Interpolation_not_allowed string.span
      "A string in a pattern cannot have interpolations.";
    raise Cursor.Failed
  in
  Atoms.make_string_literal cursor ~start ~modules literal ~interpolation

let parse_literal cursor : Syntax.literal option =
  let start = Cursor.index cursor in
  let take literal =
    Cursor.advance cursor;
    Some literal
  in
  match Cursor.peek_kind cursor with
  | Integer value -> take (Syntax.Literal_integer value)
  | Punctuation Minus -> (
      Cursor.advance cursor;
      match Cursor.peek_kind cursor with
      | Integer value -> take (Syntax.Literal_integer (Z.neg value))
      | _ -> Cursor.fail cursor "a number after `-` in a pattern")
  | Float _ ->
      Cursor.report cursor Float_pattern (Cursor.peek cursor).span
        "A float literal cannot be a pattern, since `==` on floats treats `-0.0` and `0.0` as \
         equal; match with a guard instead, as in `value if value == 0.0`.";
      raise Cursor.Failed
  | Keyword True -> take Syntax.Literal_true
  | Keyword False -> take Syntax.Literal_false
  | String literal -> Some (Literal_string (parse_string_literal cursor ~start ~modules:[] literal))
  | _ -> None

let rec parse_variant_or_constant cursor start (path : Syntax.path) =
  if Cursor.is_punctuation cursor Dot then begin
    Cursor.advance cursor;
    let constant =
      Syntax.Type_constant (path, Atoms.lower_name cursor "the name of a constant after `.`")
    in
    parse_range_or_single cursor start (Syntax.End_constant constant)
      (Syntax.Qualified_constant constant)
  end
  else
    let fields =
      if Cursor.is_punctuation cursor (Open Paren) then Some (parse_pattern_fields cursor) else None
    in
    make_pattern_node cursor start (Variant { name = path.last; fields })

and parse_range_or_single cursor start end_kind kind =
  let first : Syntax.range_end = { kind = end_kind; id = Cursor.allocate_id_from cursor start } in
  match Cursor.peek_kind cursor with
  | Punctuation ((Dot_dot | Dot_dot_equal) as operator) ->
      Cursor.advance cursor;
      let stop_start = Cursor.index cursor in
      let stop =
        match parse_literal cursor with
        | Some literal ->
            ({ kind = End_literal literal; id = Cursor.allocate_id_from cursor stop_start }
              : Syntax.range_end)
        | None -> (
            match Cursor.peek_kind cursor with
            | Lower _ | Upper _ -> parse_constant_end cursor stop_start
            | _ -> Cursor.fail cursor "the end of the range; a range pattern needs both ends")
      in
      make_pattern_node cursor start
        (Pattern_range { start = first; stop; inclusive = operator = Dot_dot_equal })
  | _ -> make_pattern_node cursor start kind

and parse_constant_end cursor start : Syntax.range_end =
  let modules = Atoms.parse_module_prefix cursor in
  let kind =
    match Cursor.peek_kind cursor with
    | Lower _ when modules = [] -> Cursor.fail cursor range_bound
    | Lower text ->
        Syntax.End_constant
          (Module_constant { modules; last = Atoms.make_name cursor (Cursor.take cursor) text })
    | Upper text ->
        let path = { Syntax.modules; last = Atoms.make_name cursor (Cursor.take cursor) text } in
        Cursor.expect_punctuation cursor Dot;
        End_constant (Type_constant (path, Atoms.lower_name cursor "the name of a constant"))
    | _ -> Cursor.fail cursor "a constant"
  in
  { kind; id = Cursor.allocate_id_from cursor start }

and parse_primary cursor : Syntax.pattern =
  let start = Cursor.index cursor in
  match parse_literal cursor with
  | Some literal -> parse_range_or_single cursor start (End_literal literal) (Literal literal)
  | None -> (
      match Cursor.peek_kind cursor with
      | Underscore ->
          Cursor.advance cursor;
          make_pattern_node cursor start Wildcard
      | Punctuation (Open Paren) ->
          make_pattern_node cursor start (Record (parse_pattern_fields cursor))
      | Lower _ | Upper _ -> parse_name_pattern cursor start
      | _ -> Cursor.fail cursor "a pattern")

and parse_name_pattern cursor start =
  let modules = Atoms.parse_module_prefix cursor in
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Lower _, Punctuation (Dot_dot | Dot_dot_equal) when modules = [] ->
      Cursor.fail cursor range_bound
  | Lower text, _ when modules = [] ->
      make_pattern_node cursor start (Binding (Atoms.make_name cursor (Cursor.take cursor) text))
  | Lower text, _ ->
      let constant =
        Syntax.Module_constant { modules; last = Atoms.make_name cursor (Cursor.take cursor) text }
      in
      parse_range_or_single cursor start (End_constant constant) (Qualified_constant constant)
  | Upper text, _ ->
      let path = { Syntax.modules; last = Atoms.make_name cursor (Cursor.take cursor) text } in
      parse_variant_or_constant cursor start (parse_unqualified_variant cursor start path)
  | String ({ tag = Some _; _ } as literal), _ ->
      let literal = Syntax.Literal_string (parse_string_literal cursor ~start ~modules literal) in
      parse_range_or_single cursor start (End_literal literal) (Literal literal)
  | _ -> Cursor.fail cursor "a name after `::`"

and parse_unqualified_variant cursor start (path : Syntax.path) =
  let rec last_name (qualified : Token.t option) =
    match (Cursor.peek_kind cursor, Cursor.lookup_token cursor (Cursor.index cursor + 1)) with
    | Punctuation (Dot | Colon_colon), ({ kind = Upper _; _ } as variant) ->
        Cursor.advance cursor;
        Cursor.advance cursor;
        last_name (Some variant)
    | _ -> qualified
  in
  let qualifier_start = (Cursor.lookup_token cursor start).span.start in
  match last_name None with
  | Some ({ kind = Upper text; _ } as variant) ->
      let variant = Atoms.make_name cursor variant text in
      Habits.report_qualified_variant cursor ~qualifier_start ~variant;
      { modules = []; last = variant }
  | _ when path.modules <> [] && not (Cursor.is_punctuation cursor Dot) ->
      Habits.report_qualified_variant cursor ~qualifier_start ~variant:path.last;
      { path with modules = [] }
  | _ -> path

and parse_pattern_fields cursor =
  let field cursor : Syntax.pattern_field =
    let start = Cursor.index cursor in
    let kind =
      match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
      | Punctuation Dot_dot, _ ->
          Cursor.advance cursor;
          Syntax.Rest
      | Lower text, Punctuation Colon ->
          let name = Atoms.make_name cursor (Cursor.take cursor) text in
          Cursor.advance cursor;
          Named_field (name, parse_pattern cursor)
      | _ -> Field (parse_pattern cursor)
    in
    { kind; id = Cursor.allocate_id_from cursor start }
  in
  let fields =
    Cursor.parse_bracketed cursor ~item:field ~recover:(fun span ->
        {
          kind = Field { kind = Pattern_error; id = Cursor.allocate_id cursor span };
          id = Cursor.allocate_id cursor span;
        })
  in
  List.iteri
    (fun index (field : Syntax.pattern_field) ->
      if field.kind = Rest && index < List.length fields - 1 then
        Cursor.report cursor Unexpected_token
          (Cursor.read_file_span cursor field.id)
          "`..` must be the last field of a pattern.")
    fields;
  fields

and parse_pattern cursor : Syntax.pattern = Cursor.nested cursor parse_alternatives

and parse_alternatives cursor : Syntax.pattern =
  let start = Cursor.index cursor in
  match Cursor.parse_separated cursor ~separator:Bar parse_primary with
  | [ single ] -> single
  | alternatives -> make_pattern_node cursor start (Alternatives alternatives)
