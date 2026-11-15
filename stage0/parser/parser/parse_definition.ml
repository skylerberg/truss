open Token
open Syntax

let definition_node cursor start visibility kind : definition =
  { visibility; kind; id = Cursor.allocate_id_from cursor start }

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

let report_misplaced_visibility cursor code (tokens : Token.t list) message =
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
  { path; generics; id = Cursor.allocate_id_from cursor start }

let definition_name cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Upper _, _ | Lower _, Punctuation Colon_colon ->
      let head = type_head cursor in
      Cursor.expect_punctuation cursor Dot;
      Member_name (head, Atoms.lower_name cursor "a method name after `.`")
  | _ -> Plain_name (Atoms.lower_name cursor "a name")

let parameter cursor : parameter =
  let start = Cursor.index cursor in
  let kind =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Keyword Self_value, _ | Keyword (Mut | Own), Keyword Self_value ->
        let mode = Atoms.mode cursor in
        Cursor.advance cursor;
        Self_parameter mode
    | _ ->
        let name = Atoms.lower_name cursor "a parameter name" in
        Cursor.expect_punctuation cursor Colon;
        let mode = Atoms.mode cursor in
        let type_ = Parse_expression.type_expression cursor in
        let default =
          if Cursor.accept_punctuation cursor Equal then Some (Parse_expression.expression cursor)
          else None
        in
        Named_parameter { name; mode; type_; default }
  in
  { kind; id = Cursor.allocate_id_from cursor start }

let parameters cursor ~method_ =
  if not (Cursor.is_punctuation cursor (Open Paren)) then
    Cursor.fail cursor "`(` to start the parameters";
  let parameters =
    Cursor.bracketed cursor ~item:parameter ~recover:(fun span ->
        { kind = Parameter_error; id = Cursor.allocate_id cursor span })
  in
  List.iteri
    (fun index (parameter : parameter) ->
      match parameter.kind with
      | Self_parameter _ when not method_ ->
          Cursor.report cursor Misplaced_self
            (Cursor.read_file_span cursor parameter.id)
            "Only a method takes `self`: one written `fn Type.name`, or one in a trait or an \
             `impl`."
      | Self_parameter _ when index > 0 ->
          Cursor.report cursor Misplaced_self
            (Cursor.read_file_span cursor parameter.id)
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
  let rec gather clauses =
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
            { kind = Clause_error; id = Cursor.allocate_id_from cursor start }
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
      gather (clause :: clauses)
  in
  gather []

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
        let at = Cursor.definition_span cursor (Source.zero_width stop) in
        {
          statements = [ { kind = Statement_error; id = Cursor.allocate_id cursor at } ];
          id = Cursor.allocate_id cursor at;
        }
      end
      else Cursor.fail cursor "`{` to start the body"

let signature cursor ~name ~method_ : signature =
  let generics = Parse_expression.generics cursor in
  let parameters = parameters cursor ~method_ in
  let result = result cursor in
  let clauses = clauses cursor in
  { name; generics; parameters; result; clauses }

let function_signature cursor ~name =
  let method_ = match name with Member_name _ -> true | Plain_name _ -> false in
  signature cursor ~name ~method_

let members cursor ~member ~error =
  Parse_expression.expect_body_opening cursor;
  List.partition_map Fun.id
    (Cursor.lines cursor
       ~item:(fun cursor ->
         let start = Cursor.index cursor in
         if Cursor.is_keyword cursor Fn then Either.Right (Cursor.skip_piece cursor)
         else
           let kind = member cursor in
           Either.Left { kind; id = Cursor.allocate_id_from cursor start })
       ~recover:(fun span -> Either.Left { kind = error; id = Cursor.allocate_id cursor span }))

let trait_member cursor =
  match Cursor.peek_kind cursor with
  | Keyword Type ->
      Cursor.advance cursor;
      let name = Atoms.upper_name cursor "the name of an associated type" in
      Associated_type
        (name, if Cursor.accept_punctuation cursor Colon then Parse_expression.bounds cursor else [])
  | Keyword Capability ->
      Cursor.advance cursor;
      Associated_capability (Atoms.upper_name cursor "the name of an associated capability set")
  | Keyword Law ->
      Cursor.advance cursor;
      let name = Atoms.lower_name cursor "the name of a law" in
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
      let name = Atoms.upper_name cursor "the name of an associated type" in
      Cursor.expect_punctuation cursor Equal;
      Associated_definition (name, Parse_expression.type_expression cursor)
  | Keyword Capability ->
      Cursor.advance cursor;
      let name = Atoms.upper_name cursor "the name of an associated capability set" in
      Cursor.expect_punctuation cursor Equal;
      Capability_definition (name, Parse_expression.capability_list cursor)
  | _ -> Cursor.fail cursor "`fn`, `type`, or `capability` to start a member of the `impl`"

let capability_member cursor : capability_member =
  Cursor.fail cursor "`fn` to start a method of the capability"

type container = In_trait | In_impl | In_capability

let method_kind cursor ~(container : container) ~name =
  let signature = signature cursor ~name ~method_:true in
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
                  (Cursor.read_file_span cursor parameter.id)
                  "A capability's methods take no `self`; they are called as \
                   `Capability.method(...)`, and only an implementation's methods take `self`."
            | _ -> ())
          signature.parameters;
        Method_declaration signature
  in
  if not (Cursor.at_end cursor) then Cursor.fail cursor "a line break or `}` after the method";
  kind

let method_ cursor ~container ~visibility : definition =
  let start = Cursor.index cursor in
  Cursor.advance cursor;
  let intended = Some Intended_function in
  let kind =
    match Atoms.lower_name cursor "a method name" with
    | exception Cursor.Failed -> Definition_error { intended; name = None }
    | name -> (
        let name = Plain_name name in
        match method_kind cursor ~container ~name with
        | kind -> kind
        | exception Cursor.Failed -> Definition_error { intended; name = Some name })
  in
  definition_node cursor start visibility kind

let fields cursor : field list =
  let field cursor : field =
    let start = Cursor.index cursor in
    let name = Atoms.lower_name cursor "a field name" in
    Cursor.expect_punctuation cursor Colon;
    let type_ = Parse_expression.type_expression cursor in
    let default =
      if Cursor.accept_punctuation cursor Equal then Some (Parse_expression.expression cursor)
      else None
    in
    { kind = Field_declaration { name; type_; default }; id = Cursor.allocate_id_from cursor start }
  in
  Cursor.bracketed cursor ~item:field ~recover:(fun span ->
      { kind = Field_error; id = Cursor.allocate_id cursor span })

let variants cursor =
  ignore (Cursor.accept_punctuation cursor Bar);
  let variant cursor : variant =
    let start = Cursor.index cursor in
    let indirect = Cursor.accept_keyword cursor Indirect in
    let name = Atoms.upper_name cursor "the name of a variant" in
    let fields = if Cursor.is_punctuation cursor (Open Paren) then Some (fields cursor) else None in
    { indirect; name; fields; id = Cursor.allocate_id_from cursor start }
  in
  Cursor.separated cursor ~separator:Bar variant

let type_clauses cursor =
  let rec gather clauses =
    let start = Cursor.index cursor in
    let clause kind =
      gather (({ kind; id = Cursor.allocate_id_from cursor start } : type_clause) :: clauses)
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
          (Contextual_keyword.expect cursor ~accepted:[ Potential ]
             ~category:"`potential`; a type's only cost clause is `cost potential expression`"
             ~expected:"`potential`; a type's only cost clause is `cost potential expression`");
        clause (Potential (Parse_expression.expression cursor))
    | _ -> List.rev clauses
  in
  gather []

let type_definition cursor ~name =
  let generics = Parse_expression.generics cursor in
  let body =
    if Cursor.is_punctuation cursor (Open Paren) then Fields (fields cursor)
    else if Cursor.accept_punctuation cursor Equal then
      if Cursor.accept_keyword cursor Todo then Type_todo else Variants (variants cursor)
    else Cursor.fail cursor "`(` to start the fields, or `=` before the variants"
  in
  Type_definition { name; generics; body; clauses = type_clauses cursor }

let trait cursor ~name =
  let generics = Parse_expression.generics cursor in
  let requires =
    if Cursor.accept_punctuation cursor Colon then Parse_expression.bounds cursor else []
  in
  let members, methods = members cursor ~member:trait_member ~error:Trait_member_error in
  (Trait { name; generics; requires; members }, methods)

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
  let members, methods = members cursor ~member:impl_member ~error:Impl_member_error in
  (Impl { trait_; type_; uses; members }, methods)

let capability cursor ~name =
  let members, methods = members cursor ~member:capability_member ~error:Capability_member_error in
  (Capability { name; members }, methods)

let constant cursor ~name =
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

let theorem cursor ~name =
  let generics = Parse_expression.generics cursor in
  let parameters = parameters cursor ~method_:false in
  let clauses = clauses cursor in
  Theorem { name; generics; parameters; clauses; body = Parse_expression.body cursor }

let law_proof cursor =
  Cursor.advance cursor;
  let trait_ = Parse_expression.path_type cursor in
  Cursor.expect_punctuation cursor Dot;
  let law = Atoms.lower_name cursor "the name of a law" in
  Cursor.expect_keyword cursor For;
  let type_ = type_head cursor in
  Law_proof { trait_; law; type_; body = Parse_expression.body cursor }

type empty = |

let top_level cursor ~function_ =
  let start = Cursor.index cursor in
  let { visibility; tokens = visibility_tokens; opaque } = visibility cursor in
  let no_visibility construct =
    report_misplaced_visibility cursor Misplaced_visibility visibility_tokens
      (Printf.sprintf "%s takes no visibility: nothing refers to it by name." construct)
  in
  let ended kind =
    (match (visibility, opaque, kind) with
    | _, None, _
    | Public_opaque, Some _, Either.Left (Type_definition _, _)
    | _, Some _, Left ((Impl _ | Test _ | Law_proof _), _) ->
        ()
    | _, Some (public, opaque), _ ->
        Cursor.report cursor Misplaced_opaque opaque.span "Only a type can be `opaque`."
          ~fixes:
            [
              Diagnostic.fix "Remove `opaque`"
                [ Diagnostic.delete (Source.span public.span.stop opaque.span.stop) ];
            ]);
    if not (Cursor.at_end cursor) then Cursor.fail cursor "a line break after the definition";
    kind
  in
  let failed intended name = Either.Left (Definition_error { intended; name }, []) in
  let unnamed parse =
    match ended (parse ()) with kind -> kind | exception Cursor.Failed -> failed None None
  in
  let named intended ~name ~written ~parse =
    Cursor.advance cursor;
    match name () with
    | exception Cursor.Failed -> failed (Some intended) None
    | parsed -> (
        match ended (parse parsed) with
        | kind -> kind
        | exception Cursor.Failed -> failed (Some intended) (Some (written parsed)))
  in
  let plain name = Plain_name name in
  let upper expected () = Atoms.upper_name cursor expected in
  let kind =
    match Cursor.peek_kind cursor with
    | Keyword Fn ->
        named Intended_function
          ~name:(fun () -> definition_name cursor)
          ~written:Fun.id ~parse:(function_ cursor)
    | Keyword Type ->
        named Intended_type ~name:(upper "the name of the type") ~written:plain ~parse:(fun name ->
            Either.Left (type_definition cursor ~name, []))
    | Keyword Trait ->
        named Intended_trait ~name:(upper "the name of the trait") ~written:plain
          ~parse:(fun name -> Either.Left (trait cursor ~name))
    | Keyword Impl ->
        report_misplaced_visibility cursor Misplaced_visibility visibility_tokens
          "An `impl` takes no visibility: it applies wherever its trait and the types it names are \
           visible.";
        unnamed (fun () -> Either.Left (impl cursor))
    | Keyword Capability ->
        named Intended_capability ~name:(upper "the name of the capability") ~written:plain
          ~parse:(fun name -> Either.Left (capability cursor ~name))
    | Keyword Let ->
        named Intended_constant
          ~name:(fun () -> definition_name cursor)
          ~written:Fun.id
          ~parse:(fun name -> Either.Left (constant cursor ~name, []))
    | Reserved ((Const | Static) as reserved) ->
        Habits.constant_keyword cursor ~token:(Cursor.peek cursor) ~reserved;
        named Intended_constant
          ~name:(fun () -> definition_name cursor)
          ~written:Fun.id
          ~parse:(fun name -> Either.Left (constant cursor ~name, []))
    | Keyword Test ->
        no_visibility "A test";
        unnamed (fun () -> Either.Left (test cursor, []))
    | Keyword Theorem ->
        named Intended_theorem
          ~name:(fun () -> Atoms.lower_name cursor "the name of the theorem")
          ~written:plain
          ~parse:(fun name -> Either.Left (theorem cursor ~name, []))
    | Keyword Proof ->
        no_visibility "A law's proof";
        unnamed (fun () -> Either.Left (law_proof cursor, []))
    | kind when visibility = Private && Atoms.begins_statement kind ->
        unnamed (fun () ->
            Cursor.report cursor Statement_at_top_level (Cursor.peek cursor).span
              "Statements must be inside a function, a test, or another definition with a body.";
            raise Cursor.Failed)
    | _ ->
        unnamed (fun () ->
            Cursor.fail cursor
              "a definition: `fn`, `type`, `trait`, `impl`, `capability`, `let`, `test`, \
               `theorem`, or `proof`")
  in
  Either.map
    ~left:(fun (kind, methods) -> (definition_node cursor start visibility kind, methods))
    ~right:(fun other -> (visibility, other))
    kind

let definition cursor : definition * Split.piece list =
  let function_ cursor name : (definition_kind * Split.piece list, empty) Either.t =
    let signature = function_signature cursor ~name in
    Left (Function { signature; body = body cursor }, [])
  in
  match top_level cursor ~function_ with Left definition -> definition | Right (_, _) -> .

type example = Whole of definition * Split.piece list | Signature_alone of visibility * signature

let example cursor =
  let function_ cursor name =
    let signature = function_signature cursor ~name in
    match optional_body cursor with
    | Some body -> Either.Left (Function { signature; body }, [])
    | None -> Right signature
  in
  match top_level cursor ~function_ with
  | Left (definition, methods) -> Whole (definition, methods)
  | Right (visibility, signature) -> Signature_alone (visibility, signature)
