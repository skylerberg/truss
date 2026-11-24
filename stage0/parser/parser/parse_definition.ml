let make_definition_node cursor start visibility kind : Syntax.definition =
  { visibility; kind; id = Cursor.allocate_id_from cursor start }

type written_visibility = {
  visibility : Syntax.visibility option;
  tokens : Token.t list;
  opaque : (Token.t * Token.t) option;
}

let parse_visibility cursor =
  match Cursor.peek_kind cursor with
  | Keyword Public -> (
      let public = Cursor.take cursor in
      match Cursor.peek_kind cursor with
      | Keyword Opaque ->
          let opaque = Cursor.take cursor in
          {
            visibility = Some Public_opaque;
            tokens = [ public; opaque ];
            opaque = Some (public, opaque);
          }
      | _ -> { visibility = Some Public; tokens = [ public ]; opaque = None })
  | Keyword Internal ->
      { visibility = Some Internal; tokens = [ Cursor.take cursor ]; opaque = None }
  | _ -> { visibility = None; tokens = []; opaque = None }

let report_misplaced_visibility cursor (tokens : Token.t list) owner =
  match tokens with
  | [] -> ()
  | first :: _ ->
      let last = List.nth tokens (List.length tokens - 1) in
      let next = Cursor.peek cursor in
      let span = Source.make_span first.span.start last.span.stop in
      Cursor.report cursor span (Misplaced_visibility owner)
        ~fixes:
          [
            {
              action = Remove_it;
              edits = [ Diagnostic.delete (Source.make_span first.span.start next.span.start) ];
            };
          ]

let parse_type_head cursor : Syntax.type_head =
  let start = Cursor.index cursor in
  let path = Atoms.parse_upper_path cursor Type_name in
  let generics = Parse_expression.parse_generics cursor in
  { path; generics; id = Cursor.allocate_id_from cursor start }

let parse_definition_name cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Upper _, _ | Lower _, Punctuation Dot ->
      let head = parse_type_head cursor in
      Cursor.expect_punctuation cursor Dot;
      Syntax.Member_name (head, Atoms.lower_name cursor Method_name_after_dot)
  | _ -> Plain_name (Atoms.lower_name cursor Name)

let parse_parameter cursor : Syntax.parameter =
  let start = Cursor.index cursor in
  let kind =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Keyword Self_value, _ | Keyword (Mut | Own), Keyword Self_value ->
        let mode = Atoms.parse_mode cursor in
        Cursor.advance cursor;
        Syntax.Self_parameter mode
    | _ ->
        let name = Atoms.lower_name cursor Parameter_name in
        Cursor.expect_punctuation cursor Colon;
        let mode = Atoms.parse_mode cursor in
        let type_ = Parse_expression.parse_type_expression cursor in
        let default =
          if Cursor.accept_punctuation cursor Equal then
            Some (Parse_expression.parse_expression cursor)
          else None
        in
        Named_parameter { name; mode; type_; default }
  in
  { kind; id = Cursor.allocate_id_from cursor start }

let parse_parameters cursor ~method_ =
  if not (Cursor.is_punctuation cursor (Open Paren)) then Cursor.fail cursor Parameters_start;
  let parameters =
    Cursor.parse_bracketed cursor ~parse_item:parse_parameter ~recover:(fun span ->
        { kind = Parameter_error; id = Cursor.allocate_id cursor span })
  in
  List.iteri
    (fun index (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Self_parameter _ when not method_ ->
          Cursor.report cursor (Cursor.read_file_span cursor parameter.id) Self_outside_method
      | Self_parameter _ when index > 0 ->
          Cursor.report cursor (Cursor.read_file_span cursor parameter.id) Self_not_first
      | _ -> ())
    parameters;
  parameters

let parse_result cursor =
  if Cursor.accept_punctuation cursor Arrow then
    Some (Syntax.Returns (Parse_expression.parse_type_expression cursor))
  else if Cursor.accept_keyword cursor Lends then begin
    let own = Cursor.peek cursor in
    let mode = Atoms.parse_mode cursor in
    if mode = Some Own then
      Cursor.report cursor own.span Lends_own
        ~fixes:
          [
            {
              action = Remove_own;
              edits =
                [
                  Diagnostic.delete
                    (Source.make_span own.span.start (Cursor.peek cursor).span.start);
                ];
            };
          ];
    Some (Lends (mode, Parse_expression.parse_type_expression cursor))
  end
  else None

let parse_clauses cursor =
  let rec gather clauses =
    let start = Cursor.index cursor in
    if not (Parse_expression.is_clause_keyword (Cursor.peek_kind cursor)) then List.rev clauses
    else
      let clause =
        match Parse_expression.parse_clause cursor with
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
            { kind = Clause_error; condition = None; id = Cursor.allocate_id_from cursor start }
      in
      let reject_repeated is_same problem =
        if List.exists (fun (earlier : Syntax.clause) -> is_same earlier.kind) clauses then
          Cursor.report cursor (Cursor.lookup_token cursor start).span problem
      in
      (match clause.kind with
      | Uses _ -> reject_repeated (function Uses _ -> true | _ -> false) Repeated_uses
      | Decreases _ ->
          reject_repeated (function Decreases _ -> true | _ -> false) Repeated_decreases
      | _ -> ());
      gather (clause :: clauses)
  in
  gather []

let parse_optional_body cursor =
  if Parse_expression.opens_body cursor then Some (Parse_expression.parse_body cursor) else None

let parse_body cursor =
  match parse_optional_body cursor with
  | Some body -> body
  | None ->
      let stop = Cursor.compute_previous_stop cursor in
      let ends_member =
        match Cursor.peek_kind cursor with
        | Punctuation (Close Curly) | Newline | End_of_file -> true
        | _ -> false
      in
      if ends_member && not (Cursor.is_after_inserted_closer cursor) then begin
        let has_earlier_error = Cursor.has_reported cursor in
        Cursor.report cursor (Source.make_zero_width stop) Missing_body
          ~fixes:
            (match Cursor.find_previous_token cursor with
            | Some previous when Token.can_end previous.kind && not has_earlier_error ->
                [
                  {
                    action = Add_todo_body;
                    edits = [ Diagnostic.insert (Source.make_zero_width stop) " { todo }" ];
                  };
                ]
            | Some _ | None -> []);
        let at = Cursor.make_definition_span cursor (Source.make_zero_width stop) in
        {
          statements = [ { kind = Statement_error; id = Cursor.allocate_id cursor at } ];
          id = Cursor.allocate_id cursor at;
        }
      end
      else Cursor.fail cursor Body_start

let parse_signature cursor ~name ~method_ : Syntax.signature =
  let generics = Parse_expression.parse_generics cursor in
  let parameters = parse_parameters cursor ~method_ in
  let result = parse_result cursor in
  let clauses = parse_clauses cursor in
  { name; generics; parameters; result; clauses }

let parse_function_signature cursor ~name =
  let method_ = match name with Syntax.Member_name _ -> true | Plain_name _ -> false in
  parse_signature cursor ~name ~method_

let parse_members cursor ~parse_member ~error =
  Parse_expression.expect_body_opening cursor;
  List.partition_map Fun.id
    (Cursor.parse_lines cursor
       ~parse_item:(fun cursor ->
         let start = Cursor.index cursor in
         if Cursor.is_keyword cursor Fn then Either.Right (Cursor.skip_piece cursor)
         else
           let kind = parse_member cursor in
           Either.Left { Syntax.kind; id = Cursor.allocate_id_from cursor start })
       ~recover:(fun span -> Either.Left { kind = error; id = Cursor.allocate_id cursor span }))

let parse_trait_member cursor =
  match Cursor.peek_kind cursor with
  | Keyword Type ->
      Cursor.advance cursor;
      let name = Atoms.parse_upper_name cursor Associated_type_name in
      Syntax.Associated_type
        ( name,
          if Cursor.accept_punctuation cursor Colon then Parse_expression.parse_bounds cursor
          else [] )
  | Keyword Capability ->
      Cursor.advance cursor;
      Associated_capability (Atoms.parse_upper_name cursor Associated_capability_set_name)
  | Keyword Law ->
      Cursor.advance cursor;
      let name = Atoms.lower_name cursor Law_name in
      let parameters = parse_parameters cursor ~method_:false in
      let rec list_premises list =
        if Cursor.accept_keyword cursor Requires then
          list_premises (Parse_expression.parse_expression cursor :: list)
        else List.rev list
      in
      let requires = list_premises [] in
      Law { name; parameters; requires; body = Parse_expression.parse_body cursor }
  | _ -> Cursor.fail cursor Trait_member

let parse_impl_member cursor =
  match Cursor.peek_kind cursor with
  | Keyword Type ->
      Cursor.advance cursor;
      let name = Atoms.parse_upper_name cursor Associated_type_name in
      Cursor.expect_punctuation cursor Equal;
      Syntax.Associated_definition (name, Parse_expression.parse_type_expression cursor)
  | Keyword Capability ->
      Cursor.advance cursor;
      let name = Atoms.parse_upper_name cursor Associated_capability_set_name in
      Cursor.expect_punctuation cursor Equal;
      Capability_definition (name, Parse_expression.parse_capability_uses cursor)
  | _ -> Cursor.fail cursor Impl_member

let parse_capability_member cursor : Syntax.capability_member = Cursor.fail cursor Capability_member

type container = In_trait | In_impl | In_capability

let parse_method_kind cursor ~(container : container) ~name =
  let signature = parse_signature cursor ~name ~method_:true in
  let kind =
    match container with
    | In_trait -> (
        match parse_optional_body cursor with
        | Some body -> Syntax.Function { signature; body }
        | None -> Method_declaration signature)
    | In_impl -> Function { signature; body = parse_body cursor }
    | In_capability ->
        List.iter
          (fun (parameter : Syntax.parameter) ->
            match parameter.kind with
            | Self_parameter _ ->
                Cursor.report cursor (Cursor.read_file_span cursor parameter.id) Self_in_capability
            | _ -> ())
          signature.parameters;
        Method_declaration signature
  in
  if not (Cursor.is_at_end cursor) then Cursor.fail cursor Line_break_after_method;
  kind

let parse_method cursor ~container : Syntax.definition =
  let start = Cursor.index cursor in
  Cursor.advance cursor;
  let intended = Some Syntax.Intended_function in
  let kind =
    match Atoms.lower_name cursor Method_name with
    | exception Cursor.Failed -> Syntax.Definition_error { intended; name = None }
    | name -> (
        let name = Syntax.Plain_name name in
        match parse_method_kind cursor ~container ~name with
        | kind -> kind
        | exception Cursor.Failed -> Definition_error { intended; name = Some name })
  in
  make_definition_node cursor start None kind

let parse_fields cursor : Syntax.field list =
  let parse_field cursor : Syntax.field =
    let start = Cursor.index cursor in
    let name = Atoms.lower_name cursor Field_name in
    Cursor.expect_punctuation cursor Colon;
    let type_ = Parse_expression.parse_type_expression cursor in
    let default =
      if Cursor.accept_punctuation cursor Equal then Some (Parse_expression.parse_expression cursor)
      else None
    in
    { kind = Field_declaration { name; type_; default }; id = Cursor.allocate_id_from cursor start }
  in
  Cursor.parse_bracketed cursor ~parse_item:parse_field ~recover:(fun span ->
      { kind = Field_error; id = Cursor.allocate_id cursor span })

let parse_variants cursor =
  ignore (Cursor.accept_punctuation cursor Bar);
  let parse_variant cursor : Syntax.variant =
    let start = Cursor.index cursor in
    let indirect = Cursor.accept_keyword cursor Indirect in
    let name = Atoms.parse_upper_name cursor Variant_name in
    let fields =
      if Cursor.is_punctuation cursor (Open Paren) then Some (parse_fields cursor) else None
    in
    { indirect; name; fields; id = Cursor.allocate_id_from cursor start }
  in
  Cursor.parse_separated cursor ~separator:Bar parse_variant

let parse_type_clauses cursor =
  let rec gather clauses =
    let start = Cursor.index cursor in
    let parse_clause kind =
      gather (({ kind; id = Cursor.allocate_id_from cursor start } : Syntax.type_clause) :: clauses)
    in
    match Cursor.peek_kind cursor with
    | Keyword Invariant ->
        Cursor.advance cursor;
        parse_clause (Type_invariant (Parse_expression.parse_expression cursor))
    | Keyword Derives ->
        Cursor.advance cursor;
        parse_clause (Derives (Parse_expression.parse_path_type_list cursor))
    | Keyword Cost ->
        Cursor.advance cursor;
        ignore
          (Contextual_keyword.expect cursor ~accepted:[ Potential ] ~category:Potential_cost_word
             ~expected:Potential_word);
        parse_clause (Potential (Parse_expression.parse_expression cursor))
    | _ -> List.rev clauses
  in
  gather []

let parse_type_definition cursor ~name ~(tuple : (Source.span * Source.span) option) =
  let generics = Parse_expression.parse_generics cursor in
  let body =
    if Cursor.is_punctuation cursor (Open Paren) then Syntax.Fields (parse_fields cursor)
    else if Cursor.accept_punctuation cursor Equal then
      if Cursor.accept_keyword cursor Todo then Type_todo else Variants (parse_variants cursor)
    else Cursor.fail cursor Type_body_start
  in
  let is_tuple =
    match (tuple, body) with
    | Some _, Fields (_ :: _ :: _) -> true
    | None, _ -> false
    | Some (word, removal), _ ->
        Cursor.report cursor word One_field_tuple
          ~fixes:[ { action = Remove_word "tuple"; edits = [ Diagnostic.delete removal ] } ];
        false
  in
  Syntax.Type_definition { is_tuple; name; generics; body; clauses = parse_type_clauses cursor }

let parse_trait cursor ~name =
  let generics = Parse_expression.parse_generics cursor in
  let requires =
    if Cursor.accept_punctuation cursor Colon then Parse_expression.parse_bounds cursor else []
  in
  let members, methods =
    parse_members cursor ~parse_member:parse_trait_member ~error:Trait_member_error
  in
  (Syntax.Trait { name; generics; requires; members }, methods)

let parse_impl cursor =
  Cursor.advance cursor;
  (match if Cursor.is_punctuation cursor Less then Cursor.find_angle_closer cursor else None with
  | Some closer ->
      let opening = Cursor.peek cursor in
      let has_bounds =
        List.exists
          (fun index ->
            match (Cursor.lookup_token cursor index).kind with
            | Upper _ | Punctuation Comma -> false
            | _ -> true)
          (List.init
             (closer - Cursor.index cursor - 1)
             (fun offset -> Cursor.index cursor + 1 + offset))
      in
      Habits.report_impl_parameters cursor ~opening
        ~closing:(Cursor.lookup_token cursor closer)
        ~has_bounds;
      Cursor.skip_to cursor (closer + 1)
  | None -> ());
  let trait_ = Parse_expression.parse_path_type cursor in
  Cursor.expect_keyword cursor For;
  let type_ = parse_type_head cursor in
  let uses =
    if Cursor.accept_keyword cursor Uses then Parse_expression.parse_capability_list cursor else []
  in
  let members, methods =
    parse_members cursor ~parse_member:parse_impl_member ~error:Impl_member_error
  in
  (Syntax.Impl { trait_; type_; uses; members }, methods)

let parse_capability cursor ~name =
  let members, methods =
    parse_members cursor ~parse_member:parse_capability_member ~error:Capability_member_error
  in
  (Syntax.Capability { name; members }, methods)

let parse_constant cursor ~name =
  Cursor.expect_punctuation cursor Colon;
  let type_ = Parse_expression.parse_type_expression cursor in
  Cursor.expect_punctuation cursor Equal;
  Syntax.Constant { name; type_; value = Parse_expression.parse_expression cursor }

let test cursor =
  Cursor.advance cursor;
  let name =
    match Cursor.peek_kind cursor with
    | String ({ tag = None; rest = [||]; _ } as literal) ->
        let start = Cursor.index cursor in
        Parse_expression.parse_string_literal cursor ~start ~modules:[] literal
    | String { tag = None; _ } ->
        Cursor.report cursor (Cursor.peek cursor).span Interpolated_test_name;
        raise Cursor.Failed
    | String _ -> Cursor.fail cursor Plain_test_name
    | _ -> Cursor.fail cursor Test_name
  in
  let uses =
    if Cursor.accept_keyword cursor Uses then Parse_expression.parse_capability_list cursor else []
  in
  Syntax.Test { name; uses; body = Parse_expression.parse_body cursor }

let parse_theorem cursor ~name =
  let generics = Parse_expression.parse_generics cursor in
  let parameters = parse_parameters cursor ~method_:false in
  let clauses = parse_clauses cursor in
  Syntax.Theorem { name; generics; parameters; clauses; body = Parse_expression.parse_body cursor }

let parse_law_proof cursor =
  Cursor.advance cursor;
  let trait_ = Parse_expression.parse_path_type cursor in
  Cursor.expect_punctuation cursor Dot;
  let law = Atoms.lower_name cursor Law_name in
  Cursor.expect_keyword cursor For;
  let type_ = parse_type_head cursor in
  Syntax.Law_proof { trait_; law; type_; body = Parse_expression.parse_body cursor }

type empty = |

let parse_top_level cursor ~parse_function =
  let start = Cursor.index cursor in
  let { visibility; tokens = visibility_tokens; opaque } = parse_visibility cursor in
  let reject_visibility owner = report_misplaced_visibility cursor visibility_tokens owner in
  let finish_definition kind =
    (match (visibility, opaque, kind) with
    | _, None, _
    | Some Public_opaque, Some _, Either.Left (Syntax.Type_definition _, _)
    | _, Some _, Left ((Impl _ | Test _ | Law_proof _), _) ->
        ()
    | _, Some (public, opaque), _ ->
        Cursor.report cursor opaque.span Misplaced_opaque
          ~fixes:
            [
              {
                action = Remove_word "opaque";
                edits = [ Diagnostic.delete (Source.make_span public.span.stop opaque.span.stop) ];
              };
            ]);
    if not (Cursor.is_at_end cursor) then Cursor.fail cursor Line_break_after_definition;
    kind
  in
  let make_failure intended name = Either.Left (Syntax.Definition_error { intended; name }, []) in
  let parse_unnamed parse =
    match finish_definition (parse ()) with
    | kind -> kind
    | exception Cursor.Failed -> make_failure None None
  in
  let parse_named intended ~parse_name ~make_written_name ~parse =
    Cursor.advance cursor;
    match parse_name () with
    | exception Cursor.Failed -> make_failure (Some intended) None
    | parsed -> (
        match finish_definition (parse parsed) with
        | kind -> kind
        | exception Cursor.Failed -> make_failure (Some intended) (Some (make_written_name parsed)))
  in
  let make_plain name = Syntax.Plain_name name in
  let parse_upper expected () = Atoms.parse_upper_name cursor expected in
  let parse_type tuple =
    parse_named Intended_type ~parse_name:(parse_upper Defined_type_name)
      ~make_written_name:make_plain ~parse:(fun name ->
        Either.Left (parse_type_definition cursor ~name ~tuple, []))
  in
  let kind =
    match Cursor.peek_kind cursor with
    | Keyword Fn ->
        parse_named Intended_function
          ~parse_name:(fun () -> parse_definition_name cursor)
          ~make_written_name:Fun.id ~parse:(parse_function cursor)
    | Lower "tuple" when Cursor.peek_ahead cursor 1 = Keyword Type ->
        let word = (Cursor.take cursor).span in
        parse_type (Some (word, Source.make_span word.start (Cursor.peek cursor).span.start))
    | Lower written when Cursor.peek_ahead cursor 1 = Keyword Type ->
        let word = (Cursor.take cursor).span in
        Cursor.report cursor word
          (Misplaced_tuple_word { written })
          ~fixes:
            (if String.edit_distance written "tuple" <= 2 then
               [ { action = Write "tuple"; edits = [ Diagnostic.replace word "tuple" ] } ]
             else
               [
                 {
                   action = Remove_word written;
                   edits =
                     [
                       Diagnostic.delete
                         (Source.make_span word.start (Cursor.peek cursor).span.start);
                     ];
                 };
               ]);
        parse_type None
    | Keyword Type -> parse_type None
    | Keyword Trait ->
        parse_named Intended_trait ~parse_name:(parse_upper Trait_name)
          ~make_written_name:make_plain ~parse:(fun name -> Either.Left (parse_trait cursor ~name))
    | Keyword Impl ->
        report_misplaced_visibility cursor visibility_tokens Impl_owner;
        parse_unnamed (fun () -> Either.Left (parse_impl cursor))
    | Keyword Capability ->
        parse_named Intended_capability ~parse_name:(parse_upper Capability_name)
          ~make_written_name:make_plain ~parse:(fun name ->
            Either.Left (parse_capability cursor ~name))
    | Keyword Let ->
        parse_named Intended_constant
          ~parse_name:(fun () -> parse_definition_name cursor)
          ~make_written_name:Fun.id
          ~parse:(fun name -> Either.Left (parse_constant cursor ~name, []))
    | Reserved ((Const | Static) as reserved) ->
        Habits.report_constant_keyword cursor ~token:(Cursor.peek cursor) ~reserved;
        parse_named Intended_constant
          ~parse_name:(fun () -> parse_definition_name cursor)
          ~make_written_name:Fun.id
          ~parse:(fun name -> Either.Left (parse_constant cursor ~name, []))
    | Keyword Test ->
        reject_visibility Test_owner;
        parse_unnamed (fun () -> Either.Left (test cursor, []))
    | Keyword Theorem ->
        parse_named Intended_theorem
          ~parse_name:(fun () -> Atoms.lower_name cursor Theorem_name)
          ~make_written_name:make_plain
          ~parse:(fun name -> Either.Left (parse_theorem cursor ~name, []))
    | Keyword Proof ->
        reject_visibility Law_proof_owner;
        parse_unnamed (fun () -> Either.Left (parse_law_proof cursor, []))
    | kind when visibility = None && Atoms.begins_statement kind ->
        parse_unnamed (fun () ->
            Cursor.report cursor (Cursor.peek cursor).span Statement_at_top_level;
            raise Cursor.Failed)
    | _ -> parse_unnamed (fun () -> Cursor.fail cursor Definition)
  in
  Either.map
    ~left:(fun (kind, methods) -> (make_definition_node cursor start visibility kind, methods))
    ~right:(fun other -> (visibility, other))
    kind

let parse_definition cursor : Syntax.definition * Split.piece list =
  let parse_function cursor name : (Syntax.definition_kind * Split.piece list, empty) Either.t =
    let signature = parse_function_signature cursor ~name in
    Left (Function { signature; body = parse_body cursor }, [])
  in
  match parse_top_level cursor ~parse_function with
  | Left definition -> definition
  | Right (_, _) -> .

type example =
  | Whole of Syntax.definition * Split.piece list
  | Signature_alone of Syntax.visibility option * Syntax.signature

let parse_example cursor =
  let parse_function cursor name =
    let signature = parse_function_signature cursor ~name in
    match parse_optional_body cursor with
    | Some body -> Either.Left (Syntax.Function { signature; body }, [])
    | None -> Right signature
  in
  match parse_top_level cursor ~parse_function with
  | Left (definition, methods) -> Whole (definition, methods)
  | Right (visibility, signature) -> Signature_alone (visibility, signature)
