(* Top-level definitions, and the members of traits, implementations, and
   capabilities. See PARSER.md, "Definitions", and GRAMMAR.md.

   Each definition is chosen by its first token, after its visibility. The
   rules the grammar leaves to a check, such as where [opaque] and [self] may
   appear and which clauses appear at most once, are checked here, where the
   tokens and their spans are at hand. *)

open Token
open Syntax

let finish cursor start visibility kind : definition =
  { visibility; kind; span = Cursor.span_from cursor start }

(* [public], [public opaque], or [internal], with the tokens that spelled
   it, and, for [public opaque], both of its tokens. *)
type written_visibility = {
  visibility : visibility;
  tokens : Token.t list;
  opaque : (Token.t * Token.t) option;
}

let visibility cursor =
  match Cursor.peek_kind cursor with
  | Keyword Public ->
      let public = Cursor.next cursor in
      if Cursor.is_keyword cursor Opaque then
        let opaque = Cursor.next cursor in
        { visibility = Public_opaque; tokens = [ public; opaque ]; opaque = Some (public, opaque) }
      else { visibility = Public; tokens = [ public ]; opaque = None }
  | Keyword Internal -> { visibility = Internal; tokens = [ Cursor.next cursor ]; opaque = None }
  | _ -> { visibility = Private; tokens = []; opaque = None }

(* Removes a visibility keyword that is not allowed, with the space after
   it. *)
let remove_visibility cursor code (tokens : Token.t list) message =
  match tokens with
  | [] -> ()
  | first :: _ ->
      let last = List.nth tokens (List.length tokens - 1) in
      let next = Cursor.peek cursor in
      let span = Source.span first.span.start last.span.stop in
      Cursor.report cursor code span message
        ~fixes:
          [
            Diagnostic.fix "Remove it"
              [ Diagnostic.delete (Source.span first.span.start next.span.start) ];
          ]

(* [List[Element: Ordered]] before the [.] of a method, or [hourly::Forecast]. *)
let type_head cursor : type_head =
  let start = cursor.Cursor.index in
  let path = Atoms.upper_path cursor "a type name" in
  let generics = Parse_expression.generics cursor in
  { path; generics; span = Cursor.span_from cursor start }

(* A function's name, or a constant's: [length], or [List[Element].length]
   under a type. *)
let function_name cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Upper _, _ | Lower _, Punctuation Colon_colon ->
      let head = type_head cursor in
      Cursor.expect_punctuation cursor Dot;
      Method_name (head, Atoms.lower cursor "a method name after `.`")
  | _ -> Plain_name (Atoms.lower cursor "a name")

let parameter cursor : parameter =
  let start = cursor.Cursor.index in
  let kind =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Keyword Self_value, _ | Keyword (Mut | Own), Keyword Self_value ->
        let mode = Parse_expression.mode cursor in
        Cursor.advance cursor;
        Self_parameter mode
    | _ ->
        let name = Atoms.lower cursor "a parameter name" in
        Cursor.expect_punctuation cursor Colon;
        let mode = Parse_expression.mode cursor in
        let type_ = Parse_expression.type_expression cursor in
        let default =
          if Cursor.accept_punctuation cursor Equal then Some (Parse_expression.expression cursor)
          else None
        in
        Named_parameter { name; mode; type_; default }
  in
  { kind; span = Cursor.span_from cursor start }

(* [self] may only be the first parameter, and only of a method. *)
let parameters cursor ~method_ =
  if not (Cursor.is_punctuation cursor (Open Paren)) then
    Cursor.fail cursor "`(` to start the parameters";
  let parameters =
    Cursor.bracketed cursor ~item:parameter ~recover:(fun span -> { kind = Parameter_error; span })
  in
  List.iteri
    (fun index (parameter : parameter) ->
      match parameter.kind with
      | Self_parameter _ when not method_ ->
          Cursor.report cursor Misplaced_self
            (Cursor.absolute cursor parameter.span)
            "only a method takes `self`: one written `fn Type.name`, or one in a trait or an `impl`"
      | Self_parameter _ when index > 0 ->
          Cursor.report cursor Misplaced_self
            (Cursor.absolute cursor parameter.span)
            "`self` must be the first parameter"
      | _ -> ())
    parameters;
  parameters

let result cursor =
  if Cursor.accept_punctuation cursor Arrow then
    Some (Returns (Parse_expression.type_expression cursor))
  else if Cursor.accept_keyword cursor Yields then
    let mode = Parse_expression.mode cursor in
    Some (Yields (mode, Parse_expression.type_expression cursor))
  else None

(* The clauses of a signature. An error in one skips to the next clause
   keyword, or to the body's [{] at the definition's own depth, so a broken
   [requires] still leaves the body parsed. [uses] and [decreases] appear at
   most once. *)
let clauses cursor =
  let rec loop clauses =
    let start = cursor.Cursor.index in
    if not (Parse_expression.is_clause_keyword (Cursor.peek_kind cursor)) then List.rev clauses
    else
      let clause =
        match Parse_expression.clause cursor with
        | clause -> clause
        | exception Cursor.Failed ->
            let rec skip () =
              match Cursor.peek_kind cursor with
              | kind when Parse_expression.is_clause_keyword kind -> ()
              | Punctuation (Open Curly) | End_of_file -> ()
              | Newline when Cursor.peek_ahead cursor 1 = Punctuation (Open Curly) -> ()
              | _ ->
                  Cursor.skip_one cursor;
                  skip ()
            in
            skip ();
            { kind = Clause_error; span = Cursor.span_from cursor start }
      in
      let once kind_name same =
        if List.exists (fun (earlier : clause) -> same earlier.kind) clauses then
          Cursor.report cursor Repeated_clause (Cursor.token_at cursor start).span
            (Printf.sprintf "a signature has at most one `%s` clause%s" kind_name
               (if kind_name = "decreases" then
                  "; list several measures in one, separated by commas"
                else "; list every capability in one, separated by commas"))
      in
      (match clause.kind with
      | Uses _ -> once "uses" (function Uses _ -> true | _ -> false)
      | Decreases _ -> once "decreases" (function Decreases _ -> true | _ -> false)
      | _ -> ());
      loop (clause :: clauses)
  in
  loop []

(* A body after a signature: required, or optional in a trait. A required
   body that is missing gets the body of unwritten code, [{ todo }]. *)
(* A body after a signature, if there is one. *)
let optional_body cursor =
  if Parse_expression.opens_body cursor then Some (Parse_expression.body cursor) else None

(* A body that must come after a signature. A missing one gets the body of
   unwritten code, [{ todo }]. *)
let body cursor =
  match optional_body cursor with
  | Some body -> body
  | None ->
      let stop = Cursor.previous_stop cursor in
      let ends_member =
        match Cursor.peek_kind cursor with
        | Punctuation (Close Curly) | Newline | End_of_file -> true
        | _ -> false
      in
      if ends_member && not cursor.cut_off then begin
        Cursor.report cursor Missing_body (Source.zero_width stop)
          "a function needs a body; write `{ todo }` for one that is not written yet"
          ~fixes:[ Diagnostic.fix "Add `{ todo }`" [ Diagnostic.insert stop " {\n  todo\n}" ] ];
        raise Cursor.Failed
      end
      else Cursor.fail cursor "`{` to start the body"

(* [fn name[...](...) -> Result clauses], after [fn]. *)
let signature cursor ~name ~method_ : signature =
  let generics = Parse_expression.generics cursor in
  let parameters = parameters cursor ~method_ in
  let result = result cursor in
  let clauses = clauses cursor in
  { name; generics; parameters; result; clauses }

let check_name cursor (name : function_name) =
  let name = match name with Plain_name name | Method_name (_, name) -> name in
  if name.text = "old" then
    Cursor.report cursor Reserved_name
      (Cursor.absolute cursor name.span)
      "a function cannot be named `old`, which names a value as it was when a function was called, \
       in specifications"

(* A top-level function's signature, after [fn]. *)
let function_signature cursor =
  Cursor.expect_keyword cursor Fn;
  let name = function_name cursor in
  check_name cursor name;
  let method_ = match name with Method_name _ -> true | Plain_name _ -> false in
  signature cursor ~name ~method_

(* A method declared in a trait, an [impl], or a capability. *)
let member_signature cursor : signature =
  Cursor.expect_keyword cursor Fn;
  let name = Plain_name (Atoms.lower cursor "a method name") in
  check_name cursor name;
  signature cursor ~name ~method_:true

(* The members of a trait, an [impl], or a capability, one per line. *)
let members cursor ~member ~error =
  Parse_expression.body_opening cursor;
  Cursor.lines cursor
    ~item:(fun cursor ->
      let start = cursor.Cursor.index in
      let kind = member cursor in
      {
        kind;
        span = Cursor.span_from cursor start;
        blank_line_before = Cursor.blank_line_before cursor start;
      })
    ~recover:(fun start span ->
      { kind = error; span; blank_line_before = Cursor.blank_line_before cursor start })

(* [type Key], or [type Element: Ordered], in a trait. *)
let trait_member cursor =
  match Cursor.peek_kind cursor with
  | Keyword Fn ->
      let signature = member_signature cursor in
      Trait_method { signature; body = optional_body cursor }
  | Keyword Type ->
      Cursor.advance cursor;
      let name = Atoms.upper cursor "the name of an associated type" in
      Associated_type
        (name, if Cursor.accept_punctuation cursor Colon then Parse_expression.bounds cursor else [])
  | Keyword Law ->
      Cursor.advance cursor;
      let name = Atoms.lower cursor "the name of a law" in
      let parameters = parameters cursor ~method_:false in
      let rec premises list =
        if Cursor.accept_keyword cursor Requires then
          premises (Parse_expression.expression cursor :: list)
        else List.rev list
      in
      let requires = premises [] in
      Law { name; parameters; requires; body = Parse_expression.body cursor }
  | _ -> Cursor.fail cursor "`fn`, `type`, or `law` to start a member of the trait"

let impl_member cursor =
  match Cursor.peek_kind cursor with
  | Keyword Fn ->
      let signature = member_signature cursor in
      Impl_method { signature; body = body cursor }
  | Keyword Type ->
      Cursor.advance cursor;
      let name = Atoms.upper cursor "the name of an associated type" in
      Cursor.expect_punctuation cursor Equal;
      Associated_definition (name, Parse_expression.type_expression cursor)
  | _ -> Cursor.fail cursor "`fn` or `type` to start a member of the `impl`"

let capability_member cursor =
  if not (Cursor.is_keyword cursor Fn) then
    Cursor.fail cursor "`fn` to start a method of the capability";
  let signature = member_signature cursor in
  List.iter
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Self_parameter _ ->
          Cursor.report cursor Misplaced_self
            (Cursor.absolute cursor parameter.span)
            "a capability's methods take no `self`; they are called as `Capability.method(...)`, \
             and only an implementation's methods take `self`"
      | _ -> ())
    signature.parameters;
  Capability_method signature

(* Fields in parentheses, as a record or a variant declares them. *)
let fields cursor : field list =
  let field cursor : field =
    let start = cursor.Cursor.index in
    let name = Atoms.lower cursor "a field name" in
    Cursor.expect_punctuation cursor Colon;
    let type_ = Parse_expression.type_expression cursor in
    let default =
      if Cursor.accept_punctuation cursor Equal then Some (Parse_expression.expression cursor)
      else None
    in
    { kind = Field_declaration { name; type_; default }; span = Cursor.span_from cursor start }
  in
  Cursor.bracketed cursor ~item:field ~recover:(fun span -> { kind = Field_error; span })

let variants cursor =
  ignore (Cursor.accept_punctuation cursor Bar);
  let variant cursor : variant =
    let start = cursor.Cursor.index in
    let indirect = Cursor.accept_keyword cursor Indirect in
    let name = Atoms.upper cursor "the name of a variant" in
    let fields = if Cursor.is_punctuation cursor (Open Paren) then Some (fields cursor) else None in
    { indirect; name; fields; span = Cursor.span_from cursor start }
  in
  let rec loop variants =
    let variants = variant cursor :: variants in
    if Cursor.accept_punctuation cursor Bar then loop variants else List.rev variants
  in
  loop []

let type_clauses cursor =
  let rec loop clauses =
    let start = cursor.Cursor.index in
    let clause kind = loop ({ kind; span = Cursor.span_from cursor start } :: clauses) in
    match Cursor.peek_kind cursor with
    | Keyword Invariant ->
        Cursor.advance cursor;
        clause (Type_invariant (Parse_expression.expression cursor))
    | Keyword Derives ->
        Cursor.advance cursor;
        clause (Derives (Parse_expression.capability_list cursor))
    | Keyword Cost ->
        Cursor.advance cursor;
        ignore
          (Parse_expression.cost_word cursor ~accepted:[ Potential ]
             ~what:"`potential`; a type's only cost clause is `cost potential expression`"
             ~expected:"`potential`; a type's only cost clause is `cost potential expression`");
        clause (Potential (Parse_expression.expression cursor))
    | _ -> List.rev clauses
  in
  loop []

let type_definition cursor =
  Cursor.advance cursor;
  let name = Atoms.upper cursor "the name of the type" in
  let generics = Parse_expression.generics cursor in
  let body =
    if Cursor.is_punctuation cursor (Open Paren) then Fields (fields cursor)
    else if Cursor.accept_punctuation cursor Equal then
      if Cursor.accept_keyword cursor Todo then Type_todo else Variants (variants cursor)
    else Cursor.fail cursor "`(` to start the fields, or `=` before the variants"
  in
  Type_definition { name; generics; body; clauses = type_clauses cursor }

let trait cursor =
  Cursor.advance cursor;
  let name = Atoms.upper cursor "the name of the trait" in
  let generics = Parse_expression.generics cursor in
  let requires =
    if Cursor.accept_punctuation cursor Colon then Parse_expression.bounds cursor else []
  in
  Trait
    {
      name;
      generics;
      requires;
      members = members cursor ~member:trait_member ~error:Trait_member_error;
    }

let impl cursor =
  Cursor.advance cursor;
  let trait_ = Parse_expression.path_type cursor in
  Cursor.expect_keyword cursor For;
  let type_ = type_head cursor in
  let uses =
    if Cursor.accept_keyword cursor Uses then Parse_expression.capability_list cursor else []
  in
  Impl
    { trait_; type_; uses; members = members cursor ~member:impl_member ~error:Impl_member_error }

let capability cursor =
  Cursor.advance cursor;
  let name = Atoms.upper cursor "the name of the capability" in
  Capability
    { name; members = members cursor ~member:capability_member ~error:Capability_member_error }

(* After [let], or after [const] or [static] from another language. *)
let constant cursor =
  Cursor.advance cursor;
  let name = function_name cursor in
  Cursor.expect_punctuation cursor Colon;
  let type_ = Parse_expression.type_expression cursor in
  Cursor.expect_punctuation cursor Equal;
  Constant { name; type_; value = Parse_expression.expression cursor }

let test cursor =
  Cursor.advance cursor;
  let name =
    match Cursor.peek_kind cursor with
    | String ({ tag = None; rest = [||]; _ } as literal) ->
        let start = cursor.index in
        Parse_expression.string_literal cursor ~start ~modules:[] literal
    | String { tag = None; _ } ->
        Cursor.report cursor Interpolation_not_allowed (Cursor.peek cursor).span
          "a test's name cannot have interpolations";
        raise Cursor.Failed
    | String _ -> Cursor.fail cursor "a plain string, with no tag, to name the test"
    | _ -> Cursor.fail cursor "a string to name the test"
  in
  let uses =
    if Cursor.accept_keyword cursor Uses then Parse_expression.capability_list cursor else []
  in
  Test { name; uses; body = Parse_expression.body cursor }

let theorem cursor =
  Cursor.advance cursor;
  let name = Atoms.lower cursor "the name of the theorem" in
  let generics = Parse_expression.generics cursor in
  let parameters = parameters cursor ~method_:false in
  let clauses = clauses cursor in
  Theorem { name; generics; parameters; clauses; body = Parse_expression.body cursor }

(* [proof Monoid.associative for Int64 { ... }]. *)
let law_proof cursor =
  Cursor.advance cursor;
  let trait_ = Parse_expression.path_type cursor in
  Cursor.expect_punctuation cursor Dot;
  let law = Atoms.lower cursor "the name of a law" in
  Cursor.expect_keyword cursor For;
  let type_ = Parse_expression.type_expression cursor in
  Law_proof { trait_; law; type_; body = Parse_expression.body cursor }

type empty = |

(* What is at the top level: a definition, or, where [function_] can give
   one, something else in place of a function, such as the signature alone
   that a document's example may show. *)
let top_level cursor ~function_ =
  let start = cursor.Cursor.index in
  let { visibility; tokens = visibility_tokens; opaque } = visibility cursor in
  let no_visibility what =
    remove_visibility cursor Misplaced_visibility visibility_tokens
      (Printf.sprintf "%s takes no visibility: nothing refers to it by name" what)
  in
  let kind =
    match Cursor.peek_kind cursor with
    | Keyword Fn -> function_ cursor
    | Keyword Type -> Either.Left (type_definition cursor)
    | Keyword Trait -> Left (trait cursor)
    | Keyword Impl ->
        remove_visibility cursor Misplaced_visibility visibility_tokens
          "an `impl` takes no visibility: it applies wherever its trait and its type are both \
           visible";
        Left (impl cursor)
    | Keyword Capability -> Left (capability cursor)
    | Keyword Let -> Left (constant cursor)
    | Reserved (Const | Static) ->
        Habits.constant_keyword cursor ~token:(Cursor.peek cursor);
        Left (constant cursor)
    | Keyword Test ->
        no_visibility "a test";
        Left (test cursor)
    | Keyword Theorem -> Left (theorem cursor)
    | Keyword Proof ->
        no_visibility "a law's proof";
        Left (law_proof cursor)
    | kind when visibility = Private && Parse_expression.begins_statement kind ->
        Cursor.report cursor Statement_at_top_level (Cursor.peek cursor).span
          "statements must be inside a function, a test, or another definition with a body";
        raise Cursor.Failed
    | _ ->
        Cursor.fail cursor
          "a definition: `fn`, `type`, `trait`, `impl`, `capability`, `let`, `test`, `theorem`, or \
           `proof`"
  in
  (match (opaque, kind) with
  | Some _, Left (Type_definition _) | None, _ -> ()
  | Some (public, opaque), _ ->
      (* With the space before it, after [public]. *)
      let before = public.span.stop in
      Cursor.report cursor Misplaced_opaque opaque.span "only a type can be `opaque`"
        ~fixes:
          [
            Diagnostic.fix "Remove `opaque`"
              [ Diagnostic.delete (Source.span before opaque.span.stop) ];
          ]);
  if not (Cursor.at_end cursor) then Cursor.fail cursor "a line break after the definition";
  Either.map ~left:(finish cursor start visibility) ~right:(fun other -> (visibility, other)) kind

(* One definition, from the start of its slice. *)
let definition cursor : definition =
  let function_ cursor : (definition_kind, empty) Either.t =
    let signature = function_signature cursor in
    Left (Function { signature; body = body cursor })
  in
  match top_level cursor ~function_ with Left definition -> definition | Right (_, _) -> .

(* What a document's example shows at the top level: a definition, or a
   function's signature without a body, to focus on the signature. *)
type example = Whole of definition | Signature_alone of visibility * signature

let example cursor =
  let function_ cursor =
    let signature = function_signature cursor in
    match optional_body cursor with
    | Some body -> Either.Left (Function { signature; body })
    | None -> Right signature
  in
  match top_level cursor ~function_ with
  | Left definition -> Whole definition
  | Right (visibility, signature) -> Signature_alone (visibility, signature)
