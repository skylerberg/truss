(* Patterns. See GRAMMAR.md, "Patterns".

   A pattern position is always known from the token before it, and a
   pattern contains no expressions, so this module needs nothing from the
   others. A bare lowercase name is [Binding_or_constant]: name resolution
   decides which. At the end of a range, a name can only be a constant. *)

open Token
open Syntax

let pattern_node cursor start kind : pattern = { kind; span = Cursor.span_from cursor start }

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

(* What follows a module path and an uppercase name: [.name] makes a
   constant under the type, and otherwise it is a variant. *)
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
    pattern_node cursor start (Variant { name = path; fields })

(* [kind] is the pattern on its own; [end_kind] is it as the start of a
   range, if [..] or [..=] follows. *)
and range_or cursor start end_kind kind =
  let first : range_end = { kind = end_kind; span = Cursor.span_from cursor start } in
  match Cursor.peek_kind cursor with
  | Punctuation ((Dot_dot | Dot_dot_equal) as operator) ->
      Cursor.advance cursor;
      let stop_start = cursor.index in
      let stop =
        match literal cursor with
        | Some literal ->
            ({ kind = End_literal literal; span = Cursor.span_from cursor stop_start } : range_end)
        | None -> (
            match Cursor.peek_kind cursor with
            | Lower _ | Upper _ -> constant_end cursor stop_start
            | _ -> Cursor.fail cursor "the end of the range; a range pattern needs both ends")
      in
      pattern_node cursor start
        (Pattern_range { start = first; stop; inclusive = operator = Dot_dot_equal })
  | _ -> pattern_node cursor start kind

(* A constant at the end of a range: [max_port], [http::last], or
   [UInt16.maximum]. *)
and constant_end cursor start : range_end =
  let modules = Atoms.module_prefix cursor in
  let kind =
    match Cursor.peek_kind cursor with
    | Lower text when modules = [] -> End_name (Atoms.name cursor (Cursor.next cursor) text)
    | Lower text ->
        End_constant
          (Module_constant { modules; last = Atoms.name cursor (Cursor.next cursor) text })
    | Upper text ->
        let path = { modules; last = Atoms.name cursor (Cursor.next cursor) text } in
        Cursor.expect_punctuation cursor Dot;
        End_constant (Type_constant (path, Atoms.lower cursor "the name of a constant"))
    | _ -> Cursor.fail cursor "a constant"
  in
  { kind; span = Cursor.span_from cursor start }

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

(* A pattern that starts with a name: a binding or constant, a qualified
   constant, a variant, or a tagged string. *)
and named cursor start =
  let modules = Atoms.module_prefix cursor in
  match Cursor.peek_kind cursor with
  | Lower text ->
      let name = Atoms.name cursor (Cursor.next cursor) text in
      if modules = [] then range_or cursor start (End_name name) (Binding_or_constant name)
      else
        let constant = Module_constant { modules; last = name } in
        range_or cursor start (End_constant constant) (Qualified_constant constant)
  | Upper text ->
      after_upper cursor start { modules; last = Atoms.name cursor (Cursor.next cursor) text }
  | String ({ tag = Some _; _ } as literal) ->
      let literal = Literal_string (string_literal cursor ~start ~modules literal) in
      range_or cursor start (End_literal literal) (Literal literal)
  | _ -> Cursor.fail cursor "a name after `::`"

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
    { kind; span = Cursor.span_from cursor start }
  in
  let fields =
    Cursor.bracketed cursor ~item:field ~recover:(fun span ->
        { kind = Field { kind = Pattern_error; span }; span })
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
