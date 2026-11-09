(* Types, generic parameters and bounds, and clauses. See PARSER.md and
   GRAMMAR.md. A clause holds expressions, which [Parse_hooks] reaches. *)

open Token
open Syntax
open Atoms
open Parse_hooks

let is_clause_keyword = function
  | Keyword (Uses | Requires | Ensures | Decreases | Cost) -> true
  | _ -> false

let rec type_expression cursor : type_expression = Cursor.nested cursor type_expression_in

and type_expression_in cursor : type_expression =
  let start = cursor.Cursor.index in
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1, Cursor.peek_ahead cursor 2) with
  | Keyword Self_type, _, _ ->
      Cursor.advance cursor;
      let associated =
        if Cursor.accept_punctuation cursor Dot then
          Some (Atoms.upper cursor "an associated type after `Self.`")
        else None
      in
      type_node cursor start (Self_type associated)
  | Keyword Any, _, _ ->
      Cursor.advance cursor;
      type_node cursor start (Any_type (path_type cursor))
  | Keyword Fn, _, _ -> type_node cursor start (Function_type (function_type cursor ~clauses:false))
  | Punctuation (Open Paren), _, _ -> parenthesized_function_type cursor
  | Upper text, Punctuation Dot, Upper _ ->
      let parameter = Atoms.name cursor (Cursor.next cursor) text in
      Cursor.advance cursor;
      type_node cursor start (Associated (parameter, Atoms.upper cursor "an associated type"))
  | (Upper _ | Lower _), _, _ -> type_node cursor start (Path_type (path_type cursor))
  | _ -> Cursor.fail cursor "a type"

(* [geometry::Shape], [List[String]], [Array[UInt8, 32]]. *)
and path_type cursor : path_type =
  let start = cursor.Cursor.index in
  let path = Atoms.upper_path cursor "a type name" in
  let arguments =
    if Cursor.is_punctuation cursor (Open Square) then type_arguments cursor else []
  in
  { path; arguments; span = Cursor.span_from cursor start; id = Cursor.fresh cursor }

and type_arguments cursor =
  let start = cursor.Cursor.index in
  let arguments =
    Cursor.bracketed cursor ~item:type_argument ~recover:(fun span ->
        Type_argument { kind = Type_error; span; id = Cursor.fresh cursor })
  in
  if arguments = [] then begin
    Cursor.report cursor Unexpected_token (Cursor.token_at cursor start).span
      "Type arguments cannot be empty.";
    raise Cursor.Failed
  end;
  arguments

and type_argument cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Integer value, _ ->
      let token = Cursor.next cursor in
      Count (value, Cursor.span cursor token.span)
  | Lower text, next when next <> Punctuation Colon_colon ->
      Count_name (Atoms.name cursor (Cursor.next cursor) text)
  | Upper text, Punctuation Equal ->
      let name = Atoms.name cursor (Cursor.next cursor) text in
      Cursor.advance cursor;
      Constraint (name, type_expression cursor)
  | _ -> Type_argument (type_expression cursor)

(* [fn(Element, Element) -> Ordering], with [uses] and [cost] clauses only
   when it is in parentheses. *)
and function_type cursor ~clauses:with_clauses =
  Cursor.expect_keyword cursor Fn;
  if not (Cursor.is_punctuation cursor (Open Paren)) then
    Cursor.fail cursor "`(` after `fn` in a function type";
  let inputs =
    Cursor.bracketed cursor
      ~item:(fun cursor ->
        let mode = mode cursor in
        (mode, type_expression cursor))
      ~recover:(fun span -> (None, { kind = Type_error; span; id = Cursor.fresh cursor }))
  in
  let output =
    if Cursor.accept_punctuation cursor Arrow then Some (type_expression cursor) else None
  in
  let clauses =
    if with_clauses then
      let rec loop clauses =
        match Cursor.peek_kind cursor with
        | Keyword (Uses | Cost) -> loop (clause cursor :: clauses)
        | Keyword (Requires | Ensures | Decreases) ->
            Cursor.fail cursor
              "`uses` or `cost`; the clauses of a function type cannot mention its parameters"
        | _ -> List.rev clauses
      in
      loop []
    else []
  in
  { inputs; output; clauses }

and parenthesized_function_type cursor =
  let start = cursor.Cursor.index in
  let closer = Cursor.closer cursor start in
  Cursor.advance cursor;
  match
    if not (Cursor.is_keyword cursor Fn) then
      Cursor.fail cursor
        "a function type; parentheses in a type only hold a function type with clauses";
    let function_type = function_type cursor ~clauses:true in
    if function_type.clauses = [] then begin
      Cursor.report cursor Unexpected_token (Cursor.token_at cursor start).span
        "Parentheses around a function type are only for its clauses; remove them.";
      raise Cursor.Failed
    end;
    if cursor.index < closer then Cursor.fail cursor "`)` after the clauses of the function type";
    function_type
  with
  | function_type ->
      Cursor.skip_to cursor (closer + 1);
      type_node cursor start (Function_type function_type)
  | exception Cursor.Failed ->
      Cursor.skip_to cursor (closer + 1);
      type_node cursor start Type_error

(* [Element: Hash + Ordered]: one or more path types joined by [+]. *)
and bounds cursor =
  let rec loop bounds =
    let bounds = path_type cursor :: bounds in
    if Cursor.accept_punctuation cursor Plus then loop bounds else List.rev bounds
  in
  loop []

and generics cursor : generic_parameter list =
  if not (Cursor.is_punctuation cursor (Open Square)) then []
  else
    let start = cursor.Cursor.index in
    let parameters =
      Cursor.bracketed cursor ~item:generic_parameter ~recover:(fun span ->
          { kind = Generic_error; span; id = Cursor.fresh cursor })
    in
    if parameters = [] then begin
      Cursor.report cursor Unexpected_token (Cursor.token_at cursor start).span
        "Generic parameters cannot be empty.";
      raise Cursor.Failed
    end;
    parameters

and generic_parameter cursor : generic_parameter =
  let start = cursor.Cursor.index in
  let kind =
    match Cursor.peek_kind cursor with
    | Keyword Capability ->
        Cursor.advance cursor;
        Capability_parameter (Atoms.upper cursor "the name of a capability parameter")
    | Upper text ->
        let name = Atoms.name cursor (Cursor.next cursor) text in
        Type_parameter (name, if Cursor.accept_punctuation cursor Colon then bounds cursor else [])
    | Lower text ->
        let name = Atoms.name cursor (Cursor.next cursor) text in
        Cursor.expect_punctuation cursor Colon;
        Value_parameter (name, type_expression cursor)
    | _ -> Cursor.fail cursor "a generic parameter"
  in
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh cursor }

(* [FileRead, FileWrite]. *)
and capability_list cursor =
  let rec loop capabilities =
    let capabilities = path_type cursor :: capabilities in
    if Cursor.accept_punctuation cursor Comma then loop capabilities else List.rev capabilities
  in
  loop []

and expression_list cursor =
  let rec loop expressions =
    let expressions = expression cursor :: expressions in
    if Cursor.accept_punctuation cursor Comma then loop expressions else List.rev expressions
  in
  loop []

(* One clause of a signature; the current token is its keyword. *)
and clause cursor : clause =
  let start = cursor.Cursor.index in
  let keyword = Cursor.next cursor in
  let kind =
    match keyword.kind with
    | Keyword Uses -> Uses (capability_list cursor)
    | Keyword Requires -> Requires (expression cursor)
    | Keyword Ensures -> Ensures (expression cursor)
    | Keyword Decreases -> Decreases (expression_list cursor)
    | Keyword Cost -> Cost (cost cursor)
    | _ -> Cursor.fail cursor "a clause"
  in
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh cursor }

(* [cost [amortized] resource bound], after [cost]. A type's
   [cost potential expression] is parsed with the type. *)
and cost cursor =
  let amortized =
    match (Cost_word.of_token (Cursor.peek_kind cursor), Cursor.peek_ahead cursor 1) with
    | Some Amortized, Lower _ ->
        Cursor.advance cursor;
        true
    | _ -> false
  in
  if Cost_word.of_token (Cursor.peek_kind cursor) = Some Potential then begin
    Cursor.report cursor Misplaced_potential (Cursor.peek cursor).span
      "`cost potential` belongs to a type, and states the potential its values hold.";
    raise Cursor.Failed
  end;
  let resource =
    match
      Cost_word.expect cursor ~accepted:Cost_word.resources ~what:"a resource"
        ~expected:"a resource: `time`, `allocations`, `allocated_bytes`, or `calls(...)`"
    with
    | Time -> Time
    | Allocations -> Allocations
    | Allocated_bytes -> Allocated_bytes
    | _ -> Calls (call_target cursor)
  in
  let bound_token = Cursor.peek cursor in
  let bound =
    match bound_token.kind with
    | Punctuation Less_equal ->
        Cursor.advance cursor;
        At_most (expression cursor)
    | Punctuation Equal_equal ->
        Cursor.advance cursor;
        Exactly (expression cursor)
    | _ -> (
        (* [finite] is a bound only for [time], so it is suggested only
           there. *)
        let suggested = if resource = Time then [ Cost_word.O; Finite ] else [ O ] in
        match
          Cost_word.expect cursor ~accepted:[ O; Finite ] ~suggested ~what:"a bound"
            ~expected:"a bound: `O(...)`, `finite`, `<=`, or `==`"
        with
        | O -> Big_o (parenthesized_expression cursor)
        | _ ->
            if resource <> Time then
              Cursor.report cursor Finite_not_time bound_token.span
                "`finite` is a bound only for `time`; a countable resource takes `O(...)`, `<=`, \
                 or `==`.";
            Finite)
  in
  { amortized; resource; bound }

(* The target of [calls(...)]: a parameter, a capability, or one of its
   methods. *)
and call_target cursor =
  let opener = cursor.Cursor.index in
  if not (Cursor.is_punctuation cursor (Open Paren)) then Cursor.fail cursor "`(` after `calls`";
  let closer = Cursor.closer cursor opener in
  Cursor.advance cursor;
  let target =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Lower text, next when next <> Punctuation Colon_colon ->
        Call_parameter (Atoms.name cursor (Cursor.next cursor) text)
    | _ ->
        let capability = path_type cursor in
        if Cursor.accept_punctuation cursor Dot then
          Call_method (capability, Atoms.lower cursor "a method name")
        else Call_capability capability
  in
  if cursor.index < closer then Cursor.fail cursor "`)` after the target of `calls`";
  Cursor.skip_to cursor (closer + 1);
  target

(* An expression in parentheses that belong to the construct around it, as
   in [O(...)]. *)
and parenthesized_expression cursor =
  let opener = cursor.Cursor.index in
  if not (Cursor.is_punctuation cursor (Open Paren)) then Cursor.fail cursor "`(`";
  let closer = Cursor.closer cursor opener in
  Cursor.advance cursor;
  let value = expression cursor in
  if cursor.index < closer then Cursor.fail cursor "`)`";
  Cursor.skip_to cursor (closer + 1);
  value
