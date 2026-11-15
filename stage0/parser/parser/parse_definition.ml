open Token
open Syntax

let finish cursor start visibility kind : definition =
  {
    visibility;
    kind;
    span = Cursor.span_from cursor start;
    recovered = [];
    id = Cursor.fresh_id cursor;
  }

type written_visibility = {
  visibility : visibility;
  tokens : Token.t list;
  opaque : (Token.t * Token.t) option;
}

let visibility cursor =
  match Cursor.peek_kind cursor with
  | Keyword Public -> (
      let public = Cursor.next cursor in
      match Cursor.peek_kind cursor with
      | Keyword Opaque ->
          let opaque = Cursor.next cursor in
          {
            visibility = Public_opaque;
            tokens = [ public; opaque ];
            opaque = Some (public, opaque);
          }
      | _ -> { visibility = Public; tokens = [ public ]; opaque = None })
  | Keyword Internal -> { visibility = Internal; tokens = [ Cursor.next cursor ]; opaque = None }
  | _ -> { visibility = Private; tokens = []; opaque = None }

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

let type_head cursor : type_head =
  let start = Cursor.index cursor in
  let path = Atoms.upper_path cursor "a type name" in
  let generics = Parse_expression.generics cursor in
  { path; generics; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

let definition_name cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Upper _, _ | Lower _, Punctuation Colon_colon ->
      let head = type_head cursor in
      Cursor.expect_punctuation cursor Dot;
      Member_name (head, Atoms.lower cursor "a method name after `.`")
  | _ -> Plain_name (Atoms.lower cursor "a name")

let parameter cursor : parameter =
  let start = Cursor.index cursor in
  let kind =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Keyword Self_value, _ | Keyword (Mut | Own), Keyword Self_value ->
        let mode = Atoms.mode cursor in
        Cursor.advance cursor;
        Self_parameter mode
    | _ ->
        let name = Atoms.lower cursor "a parameter name" in
        Cursor.expect_punctuation cursor Colon;
        let mode = Atoms.mode cursor in
        let type_ = Parse_expression.type_expression cursor in
        let default =
          if Cursor.accept_punctuation cursor Equal then Some (Parse_expression.expression cursor)
          else None
        in
        Named_parameter { name; mode; type_; default }
  in
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

let parameters cursor ~method_ =
  if not (Cursor.is_punctuation cursor (Open Paren)) then
    Cursor.fail cursor "`(` to start the parameters";
  let parameters =
    Cursor.bracketed cursor ~item:parameter ~recover:(fun span ->
        { kind = Parameter_error; span; id = Cursor.fresh_id cursor })
  in
  List.iteri
    (fun index (parameter : parameter) ->
      match parameter.kind with
      | Self_parameter _ when not method_ ->
          Cursor.report cursor Misplaced_self
            (Cursor.absolute cursor parameter.span)
            "Only a method takes `self`: one written `fn Type.name`, or one in a trait or an \
             `impl`."
      | Self_parameter _ when index > 0 ->
          Cursor.report cursor Misplaced_self
            (Cursor.absolute cursor parameter.span)
            "`self` must be the first parameter."
      | _ -> ())
    parameters;
  parameters

let result cursor =
  if Cursor.accept_punctuation cursor Arrow then
    Some (Returns (Parse_expression.type_expression cursor))
  else if Cursor.accept_keyword cursor Lends then begin
    let own = Cursor.peek cursor in
    let mode = Atoms.mode cursor in
    if mode = Some Own then
      Cursor.report cursor Lends_own own.span
        "A part a `lends` method lends stays with `self`, so it cannot be `own`. A method that \
         hands over an owned value returns it with `->`."
        ~fixes:
          [
            Diagnostic.fix "Remove `own`"
              [ Diagnostic.delete (Source.span own.span.start (Cursor.peek cursor).span.start) ];
          ];
    Some (Lends (mode, Parse_expression.type_expression cursor))
  end
  else None

let clauses cursor =
  let rec loop clauses =
    let start = Cursor.index cursor in
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
            {
              kind = Clause_error;
              span = Cursor.span_from cursor start;
              id = Cursor.fresh_id cursor;
            }
      in
      let once same message =
        if List.exists (fun (earlier : clause) -> same earlier.kind) clauses then
          Cursor.report cursor Repeated_clause (Cursor.token_at cursor start).span message
      in
      (match clause.kind with
      | Uses _ ->
          once
            (function Uses _ -> true | _ -> false)
            "A signature has at most one `uses` clause; list every capability in one, separated by \
             commas."
      | Decreases _ ->
          once
            (function Decreases _ -> true | _ -> false)
            "A signature has at most one `decreases` clause; list several measures in one, \
             separated by commas."
      | _ -> ());
      loop (clause :: clauses)
  in
  loop []

let optional_body cursor =
  if Parse_expression.opens_body cursor then Some (Parse_expression.body cursor) else None

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
      if ends_member && not (Cursor.is_after_inserted_closer cursor) then begin
        Cursor.report cursor Missing_body (Source.zero_width stop)
          "A function needs a body; write `{ todo }` for one that is not written yet."
          ~fixes:
            [
              Diagnostic.fix "Add `{ todo }`"
                [ Diagnostic.insert (Source.zero_width stop) " { todo }" ];
            ];
        let at = Cursor.span cursor (Source.zero_width stop) in
        {
          statements =
            [
              {
                kind = Statement_error;
                span = at;
                blank_line_before = false;
                id = Cursor.fresh_id cursor;
              };
            ];
          span = at;
          id = Cursor.fresh_id cursor;
        }
      end
      else Cursor.fail cursor "`{` to start the body"

let signature cursor ~name ~method_ : signature =
  let generics = Parse_expression.generics cursor in
  let parameters = parameters cursor ~method_ in
  let result = result cursor in
  let clauses = clauses cursor in
  { name; generics; parameters; result; clauses }

let check_name cursor (name : definition_name) =
  let name = match name with Plain_name name | Member_name (_, name) -> name in
  if name.text = "old" then
    Cursor.report cursor Reserved_specification_name
      (Cursor.absolute cursor name.span)
      "A function cannot be named `old`, which names a value as it was when a function was called, \
       in specifications."
  else if name.text = "identical" then
    Cursor.report cursor Reserved_specification_name
      (Cursor.absolute cursor name.span)
      "A function cannot be named `identical`, which tests whether two values are the same value, \
       in specifications."

let function_signature cursor =
  Cursor.expect_keyword cursor Fn;
  let name = definition_name cursor in
  check_name cursor name;
  let method_ = match name with Member_name _ -> true | Plain_name _ -> false in
  signature cursor ~name ~method_

let member_signature cursor : signature =
  Cursor.expect_keyword cursor Fn;
  let name = Plain_name (Atoms.lower cursor "a method name") in
  check_name cursor name;
  signature cursor ~name ~method_:true

let members cursor ~member ~error =
  Parse_expression.body_opening cursor;
  List.filter_map Fun.id
    (Cursor.lines cursor
       ~item:(fun cursor ->
         let start = Cursor.index cursor in
         if Cursor.is_keyword cursor Fn then begin
           Cursor.skip_method cursor;
           None
         end
         else
           let kind = member cursor in
           Some
             {
               kind;
               span = Cursor.span_from cursor start;
               blank_line_before = Cursor.blank_line_before cursor start;
               id = Cursor.fresh_id cursor;
             })
       ~recover:(fun start span ->
         Some
           {
             kind = error;
             span;
             blank_line_before = Cursor.blank_line_before cursor start;
             id = Cursor.fresh_id cursor;
           }))

let trait_member cursor =
  match Cursor.peek_kind cursor with
  | Keyword Type ->
      Cursor.advance cursor;
      let name = Atoms.upper cursor "the name of an associated type" in
      Associated_type
        (name, if Cursor.accept_punctuation cursor Colon then Parse_expression.bounds cursor else [])
  | Keyword Capability ->
      Cursor.advance cursor;
      Associated_capability (Atoms.upper cursor "the name of an associated capability set")
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
  | _ -> Cursor.fail cursor "`fn`, `type`, `capability`, or `law` to start a member of the trait"

let impl_member cursor =
  match Cursor.peek_kind cursor with
  | Keyword Type ->
      Cursor.advance cursor;
      let name = Atoms.upper cursor "the name of an associated type" in
      Cursor.expect_punctuation cursor Equal;
      Associated_definition (name, Parse_expression.type_expression cursor)
  | Keyword Capability ->
      Cursor.advance cursor;
      let name = Atoms.upper cursor "the name of an associated capability set" in
      Cursor.expect_punctuation cursor Equal;
      Capability_definition (name, Parse_expression.capability_list cursor)
  | _ -> Cursor.fail cursor "`fn`, `type`, or `capability` to start a member of the `impl`"

let capability_member cursor : capability_member =
  Cursor.fail cursor "`fn` to start a method of the capability"

type container = In_trait | In_impl | In_capability

let method_ cursor ~(container : container) ~visibility : definition =
  let start = Cursor.index cursor in
  let signature = member_signature cursor in
  let kind =
    match container with
    | In_trait -> (
        match optional_body cursor with
        | Some body -> Function { signature; body }
        | None -> Method_declaration signature)
    | In_impl -> Function { signature; body = body cursor }
    | In_capability ->
        List.iter
          (fun (parameter : parameter) ->
            match parameter.kind with
            | Self_parameter _ ->
                Cursor.report cursor Misplaced_self
                  (Cursor.absolute cursor parameter.span)
                  "A capability's methods take no `self`; they are called as \
                   `Capability.method(...)`, and only an implementation's methods take `self`."
            | _ -> ())
          signature.parameters;
        Method_declaration signature
  in
  if not (Cursor.at_end cursor) then Cursor.fail cursor "a line break or `}` after the method";
  finish cursor start visibility kind

let fields cursor : field list =
  let field cursor : field =
    let start = Cursor.index cursor in
    let name = Atoms.lower cursor "a field name" in
    Cursor.expect_punctuation cursor Colon;
    let type_ = Parse_expression.type_expression cursor in
    let default =
      if Cursor.accept_punctuation cursor Equal then Some (Parse_expression.expression cursor)
      else None
    in
    {
      kind = Field_declaration { name; type_; default };
      span = Cursor.span_from cursor start;
      id = Cursor.fresh_id cursor;
    }
  in
  Cursor.bracketed cursor ~item:field ~recover:(fun span ->
      { kind = Field_error; span; id = Cursor.fresh_id cursor })

let variants cursor =
  ignore (Cursor.accept_punctuation cursor Bar);
  let variant cursor : variant =
    let start = Cursor.index cursor in
    let indirect = Cursor.accept_keyword cursor Indirect in
    let name = Atoms.upper cursor "the name of a variant" in
    let fields = if Cursor.is_punctuation cursor (Open Paren) then Some (fields cursor) else None in
    { indirect; name; fields; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }
  in
  let rec loop variants =
    let variants = variant cursor :: variants in
    if Cursor.accept_punctuation cursor Bar then loop variants else List.rev variants
  in
  loop []

let type_clauses cursor =
  let rec loop clauses =
    let start = Cursor.index cursor in
    let clause kind =
      loop
        (({ kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor } : type_clause)
        :: clauses)
    in
    match Cursor.peek_kind cursor with
    | Keyword Invariant ->
        Cursor.advance cursor;
        clause (Type_invariant (Parse_expression.expression cursor))
    | Keyword Derives ->
        Cursor.advance cursor;
        clause (Derives (Parse_expression.path_type_list cursor))
    | Keyword Cost ->
        Cursor.advance cursor;
        ignore
          (Cost_word.expect cursor ~accepted:[ Potential ]
             ~category:"`potential`; a type's only cost clause is `cost potential expression`"
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
  (match
     if Cursor.is_punctuation cursor Less then Parse_expression.angle_closer cursor else None
   with
  | Some closer ->
      let opening = Cursor.peek cursor in
      let has_bounds =
        List.exists
          (fun index ->
            match (Cursor.token_at cursor index).kind with
            | Upper _ | Punctuation Comma -> false
            | _ -> true)
          (List.init
             (closer - Cursor.index cursor - 1)
             (fun offset -> Cursor.index cursor + 1 + offset))
      in
      Habits.impl_parameters cursor ~opening ~closing:(Cursor.token_at cursor closer) ~has_bounds;
      Cursor.skip_to cursor (closer + 1)
  | None -> ());
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

let constant cursor =
  Cursor.advance cursor;
  let name = definition_name cursor in
  Cursor.expect_punctuation cursor Colon;
  let type_ = Parse_expression.type_expression cursor in
  Cursor.expect_punctuation cursor Equal;
  Constant { name; type_; value = Parse_expression.expression cursor }

let test cursor =
  Cursor.advance cursor;
  let name =
    match Cursor.peek_kind cursor with
    | String ({ tag = None; rest = [||]; _ } as literal) ->
        let start = Cursor.index cursor in
        Parse_expression.string_literal cursor ~start ~modules:[] literal
    | String { tag = None; _ } ->
        Cursor.report cursor Interpolation_not_allowed (Cursor.peek cursor).span
          "A test's name cannot have interpolations.";
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

let law_proof cursor =
  Cursor.advance cursor;
  let trait_ = Parse_expression.path_type cursor in
  Cursor.expect_punctuation cursor Dot;
  let law = Atoms.lower cursor "the name of a law" in
  Cursor.expect_keyword cursor For;
  let type_ = type_head cursor in
  Law_proof { trait_; law; type_; body = Parse_expression.body cursor }

let header cursor : intended_kind option * definition_name option =
  ignore (visibility cursor);
  let intended =
    match Cursor.peek_kind cursor with
    | Keyword Fn -> Some Intended_function
    | Keyword Let -> Some Intended_constant
    | Keyword Type -> Some Intended_type
    | Keyword Trait -> Some Intended_trait
    | Keyword Capability -> Some Intended_capability
    | Keyword Theorem -> Some Intended_theorem
    | _ -> None
  in
  Cursor.advance cursor;
  let name () : definition_name option =
    match intended with
    | Some (Intended_function | Intended_constant) -> Some (definition_name cursor)
    | Some (Intended_type | Intended_trait | Intended_capability) ->
        Some (Plain_name (Atoms.upper cursor "a name"))
    | Some Intended_theorem -> Some (Plain_name (Atoms.lower cursor "a name"))
    | None -> None
  in
  (intended, match name () with name -> name | exception Cursor.Failed -> None)

type empty = |

let top_level cursor ~function_ =
  let start = Cursor.index cursor in
  let { visibility; tokens = visibility_tokens; opaque } = visibility cursor in
  let no_visibility construct =
    remove_visibility cursor Misplaced_visibility visibility_tokens
      (Printf.sprintf "%s takes no visibility: nothing refers to it by name." construct)
  in
  let kind =
    match Cursor.peek_kind cursor with
    | Keyword Fn -> function_ cursor
    | Keyword Type -> Either.Left (type_definition cursor)
    | Keyword Trait -> Left (trait cursor)
    | Keyword Impl ->
        remove_visibility cursor Misplaced_visibility visibility_tokens
          "An `impl` takes no visibility: it applies wherever its trait and the types it names are \
           visible.";
        Left (impl cursor)
    | Keyword Capability -> Left (capability cursor)
    | Keyword Let -> Left (constant cursor)
    | Reserved ((Const | Static) as reserved) ->
        Habits.constant_keyword cursor ~token:(Cursor.peek cursor) ~reserved;
        Left (constant cursor)
    | Keyword Test ->
        no_visibility "A test";
        Left (test cursor)
    | Keyword Theorem -> Left (theorem cursor)
    | Keyword Proof ->
        no_visibility "A law's proof";
        Left (law_proof cursor)
    | kind when visibility = Private && Atoms.begins_statement kind ->
        Cursor.report cursor Statement_at_top_level (Cursor.peek cursor).span
          "Statements must be inside a function, a test, or another definition with a body.";
        raise Cursor.Failed
    | _ ->
        Cursor.fail cursor
          "a definition: `fn`, `type`, `trait`, `impl`, `capability`, `let`, `test`, `theorem`, or \
           `proof`"
  in
  (match (visibility, opaque, kind) with
  | _, None, _
  | Public_opaque, Some _, Left (Type_definition _)
  | _, Some _, Left (Impl _ | Test _ | Law_proof _) ->
      ()
  | _, Some (public, opaque), _ ->
      Cursor.report cursor Misplaced_opaque opaque.span "Only a type can be `opaque`."
        ~fixes:
          [
            Diagnostic.fix "Remove `opaque`"
              [ Diagnostic.delete (Source.span public.span.stop opaque.span.stop) ];
          ]);
  if not (Cursor.at_end cursor) then Cursor.fail cursor "a line break after the definition";
  Either.map ~left:(finish cursor start visibility) ~right:(fun other -> (visibility, other)) kind

let definition cursor : definition =
  let function_ cursor : (definition_kind, empty) Either.t =
    let signature = function_signature cursor in
    Left (Function { signature; body = body cursor })
  in
  match top_level cursor ~function_ with Left definition -> definition | Right (_, _) -> .

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
