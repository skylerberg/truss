(* Patterns.

   A pattern position is always known from the token before it, and a
   pattern contains no expressions, so this module needs nothing from the
   others. A bare lowercase name binds. A constant is written with its
   module or its type, so the parser decides every pattern's meaning. *)

open Token
open Syntax

let pattern_node cursor start kind : pattern =
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

let range_bound = "a literal or a constant with its module or type, such as `http::last`"

(* A string in a pattern is a literal, so it cannot interpolate. *)
let string_literal cursor ~start ~modules literal =
  let string = Cursor.peek cursor in
  let interpolation (_ : Token.interpolation) =
    Cursor.report cursor Interpolation_not_allowed string.span
      "A string in a pattern cannot have interpolations.";
    raise Cursor.Failed
  in
  Atoms.string_literal cursor ~start ~modules literal ~interpolation

(* A literal pattern, or [None] when the current token does not start one. *)
let literal cursor : literal option =
  let start = cursor.Cursor.index in
  let take literal =
    Cursor.advance cursor;
    Some literal
  in
  match Cursor.peek_kind cursor with
  | Integer value -> take (Literal_integer value)
  | Punctuation Minus -> (
      Cursor.advance cursor;
      match Cursor.peek_kind cursor with
      | Integer value -> take (Literal_integer (Z.neg value))
      | _ -> Cursor.fail cursor "a number after `-` in a pattern")
  | Float _ ->
      Cursor.report cursor Float_pattern (Cursor.peek cursor).span
        "A float literal cannot be a pattern, since `==` on floats treats `-0.0` and `0.0` as \
         equal; match with a guard instead, as in `value if value == 0.0`.";
      raise Cursor.Failed
  | Keyword True -> take Literal_true
  | Keyword False -> take Literal_false
  | String literal -> Some (Literal_string (string_literal cursor ~start ~modules:[] literal))
  | _ -> None

(* The rest of a pattern after a module path and an uppercase name. With
   [.name], the pattern is a constant of the type, and otherwise it is a
   variant. *)
let rec after_upper cursor start (path : path) =
  if Cursor.is_punctuation cursor Dot then begin
    Cursor.advance cursor;
    let constant = Type_constant (path, Atoms.lower cursor "the name of a constant after `.`") in
    range_or cursor start (End_constant constant) (Qualified_constant constant)
  end
  else
    let fields =
      if Cursor.is_punctuation cursor (Open Paren) then Some (pattern_fields cursor) else None
    in
    pattern_node cursor start (Variant { name = path.last; fields })

(* A pattern of [kind], or, if [..] or [..=] follows, a range pattern that
   starts with [end_kind]. *)
and range_or cursor start end_kind kind =
  let first : range_end =
    { kind = end_kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }
  in
  match Cursor.peek_kind cursor with
  | Punctuation ((Dot_dot | Dot_dot_equal) as operator) ->
      Cursor.advance cursor;
      let stop_start = cursor.index in
      let stop =
        match literal cursor with
        | Some literal ->
            ({
               kind = End_literal literal;
               span = Cursor.span_from cursor stop_start;
               id = Cursor.fresh_id cursor;
             }
              : range_end)
        | None -> (
            match Cursor.peek_kind cursor with
            | Lower _ | Upper _ -> constant_end cursor stop_start
            | _ -> Cursor.fail cursor "the end of the range; a range pattern needs both ends")
      in
      pattern_node cursor start
        (Pattern_range { start = first; stop; inclusive = operator = Dot_dot_equal })
  | _ -> pattern_node cursor start kind

(* A constant at the end of a range: [http::last] or [UInt16.maximum]. *)
and constant_end cursor start : range_end =
  let modules = Atoms.module_prefix cursor in
  let kind =
    match Cursor.peek_kind cursor with
    | Lower _ when modules = [] -> Cursor.fail cursor range_bound
    | Lower text ->
        End_constant
          (Module_constant { modules; last = Atoms.name cursor (Cursor.next cursor) text })
    | Upper text ->
        let path = { modules; last = Atoms.name cursor (Cursor.next cursor) text } in
        Cursor.expect_punctuation cursor Dot;
        End_constant (Type_constant (path, Atoms.lower cursor "the name of a constant"))
    | _ -> Cursor.fail cursor "a constant"
  in
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

and primary cursor : pattern =
  let start = cursor.Cursor.index in
  match literal cursor with
  | Some literal -> range_or cursor start (End_literal literal) (Literal literal)
  | None -> (
      match Cursor.peek_kind cursor with
      | Underscore ->
          Cursor.advance cursor;
          pattern_node cursor start Wildcard
      | Punctuation (Open Paren) -> pattern_node cursor start (Record (pattern_fields cursor))
      | Lower _ | Upper _ -> named cursor start
      | _ -> Cursor.fail cursor "a pattern")

(* A pattern that starts with a name: a binding, a qualified constant, a
   variant, or a tagged string. *)
and named cursor start =
  let modules = Atoms.module_prefix cursor in
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Lower _, Punctuation (Dot_dot | Dot_dot_equal) when modules = [] ->
      Cursor.fail cursor range_bound
  | Lower text, _ when modules = [] ->
      pattern_node cursor start (Binding (Atoms.name cursor (Cursor.next cursor) text))
  | Lower text, _ ->
      let constant =
        Module_constant { modules; last = Atoms.name cursor (Cursor.next cursor) text }
      in
      range_or cursor start (End_constant constant) (Qualified_constant constant)
  | Upper text, _ ->
      let path = { modules; last = Atoms.name cursor (Cursor.next cursor) text } in
      after_upper cursor start (unqualified_variant cursor start path)
  | String ({ tag = Some _; _ } as literal), _ ->
      let literal = Literal_string (string_literal cursor ~start ~modules literal) in
      range_or cursor start (End_literal literal) (Literal literal)
  | _ -> Cursor.fail cursor "a name after `::`"

(* [Shape.Circle(radius)], [Shape::Circle(radius)], and
   [geometry::Circle(radius)]: a variant written with its type or its
   module, as an expression names it and as Rust and Swift write a pattern.
   The qualifier is reported, and the result is the variant alone, as after
   the fix. A [.] that remains begins a constant of the type, as in
   [geometry::Status.teapot], whose module qualifier is valid. *)
and unqualified_variant cursor start (path : path) =
  let rec last_name (qualified : Token.t option) =
    match (Cursor.peek_kind cursor, Cursor.token_at cursor (cursor.index + 1)) with
    | Punctuation (Dot | Colon_colon), ({ kind = Upper _; _ } as variant) ->
        Cursor.advance cursor;
        Cursor.advance cursor;
        last_name (Some variant)
    | _ -> qualified
  in
  let qualifier_start = (Cursor.token_at cursor start).span.start in
  match last_name None with
  | Some ({ kind = Upper text; _ } as variant) ->
      Habits.qualified_variant cursor ~qualifier_start ~variant;
      { modules = []; last = Atoms.name cursor variant text }
  | _ when path.modules <> [] && not (Cursor.is_punctuation cursor Dot) ->
      Habits.qualified_variant cursor ~qualifier_start
        ~variant:(Cursor.token_at cursor (cursor.index - 1));
      { path with modules = [] }
  | _ -> path

(* [(index, element: score, ..)]. [..] may only be the last field. *)
and pattern_fields cursor =
  let field cursor : pattern_field =
    let start = cursor.Cursor.index in
    let kind =
      match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
      | Punctuation Dot_dot, _ ->
          Cursor.advance cursor;
          Rest
      | Lower text, Punctuation Colon ->
          let name = Atoms.name cursor (Cursor.next cursor) text in
          Cursor.advance cursor;
          Named_field (name, pattern cursor)
      | _ -> Field (pattern cursor)
    in
    { kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }
  in
  let fields =
    Cursor.bracketed cursor ~item:field ~recover:(fun span ->
        {
          kind = Field { kind = Pattern_error; span; id = Cursor.fresh_id cursor };
          span;
          id = Cursor.fresh_id cursor;
        })
  in
  List.iteri
    (fun index (field : pattern_field) ->
      if field.kind = Rest && index < List.length fields - 1 then
        Cursor.report cursor Unexpected_token
          (Cursor.absolute cursor field.span)
          "`..` must be the last field of a pattern.")
    fields;
  fields

(* A pattern, with alternatives: [Low | Normal]. *)
and pattern cursor : pattern = Cursor.nested cursor alternatives

and alternatives cursor : pattern =
  let start = cursor.Cursor.index in
  let first = primary cursor in
  if Cursor.is_punctuation cursor Bar then begin
    let rec loop alternatives =
      if Cursor.accept_punctuation cursor Bar then loop (primary cursor :: alternatives)
      else List.rev alternatives
    in
    pattern_node cursor start (Alternatives (loop [ first ]))
  end
  else first
