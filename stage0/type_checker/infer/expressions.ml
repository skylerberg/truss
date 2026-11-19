let rec check_expression (state : State.state) env ?expected (value : Syntax.expression) : Types.ty
    =
  let type_ =
    if Hashtbl.mem state.lent_tails value.id then check_lent_part state env value
    else check_expression_kind state env ?expected value
  in
  State.record state value type_;
  State.note_compiled_expression state env value;
  type_

and check_lent_part state env (value : Syntax.expression) : Types.ty =
  Hashtbl.remove state.lent_tails value.id;
  match env.output with
  | Some (Lends (mode, part)) ->
      let inner =
        match value.kind with
        | Mode (mode, inner) when Option.is_none (State.find_keyword_operation state inner) ->
            State.note_mode_keyword state value mode inner;
            inner
        | _ -> value
      in
      Hashtbl.replace state.yielded inner.id (match mode with Mut -> Mut | Read | Own -> Read);
      let actual = check_expression state env ~expected:part inner in
      if inner != value then State.alias_expression state value inner;
      if mode = Mut then Modes.mutate state env ~by:Passed_mut inner;
      Name_lookup.coerce state env inner ~actual ~expected:part;
      actual
  | _ -> check_expression_kind state env value

and check state env (value : Syntax.expression) (expected : Types.ty) =
  let actual = check_expression state env ~expected value in
  Name_lookup.coerce state env value ~actual ~expected

and check_expression_kind state env ?expected (value : Syntax.expression) : Types.ty =
  match value.kind with
  | Integer number ->
      state.tables.literals.(value.id) <- Some (Integer_value number);
      State.register_expression state value (fun () -> Form.build_numeric_literal state value.id);
      let type_ = Name_lookup.infer_literal_type state ~expected Integer_literal in
      Pattern_typing.check_literal_fits state value number type_;
      type_
  | Float number ->
      State.register_expression state value (fun () -> Form.build_numeric_literal state value.id);
      let type_ = Name_lookup.infer_literal_type state ~expected Float_literal in
      let significand = number.significand and exponent = number.exponent in
      State.defer state (fun () ->
          match State.resolve state type_ with
          | Types.Literal _ | Types.Variable _ -> false
          | resolved ->
              let rounded =
                if Types.is_builtin Float32 resolved then
                  Literals.round_float32 ~significand ~exponent
                else Literals.round_float64 ~significand ~exponent
              in
              (match rounded with
              | Some rounded_value ->
                  state.tables.literals.(value.id) <- Some (Float_value rounded_value)
              | None ->
                  State.report state Literal_out_of_range (State.read_span state value.id)
                    (Printf.sprintf
                       "This literal is too large for `%s`; it would round to infinity."
                       (Types.show resolved)));
              true);
      type_
  | String literal -> (
      match Pattern_typing.find_character_tag state literal with
      | Some builtin ->
          State.register_expression state value (fun () ->
              Form.build_numeric_literal state value.id);
          Pattern_typing.check_character_literal state value.id literal builtin
      | None -> Values.check_string_literal state env ?expected value literal)
  | True | False ->
      State.register_expression state value (fun () -> Boolean (value.kind = True));
      Types.bool
  | Todo -> (
      State.register_expression state value (fun () -> Todo);
      match expected with Some expected -> expected | None -> Types.Hole)
  | Unreachable ->
      State.reject_in_formula state env (State.read_span state value.id) "`unreachable`";
      State.register_expression state value (fun () -> Unreachable);
      Types.Never
  | Break | Continue ->
      let (kind : Core.kind), word =
        match value.kind with Break -> (Break, "`break`") | _ -> (Continue, "`continue`")
      in
      State.reject_in_formula state env (State.read_span state value.id) word;
      State.register_expression state value (fun () -> kind);
      Types.Never
  | Self_value -> (
      state.locals_read <- state.definition.id :: state.locals_read;
      State.register_expression state value (fun () ->
          Use (Form.build_self_local state env ~origin:value.id));
      match env.self with
      | Some self -> self
      | None ->
          State.make_error_type state Not_a_value (State.read_span state value.id)
            "`self` is a method's receiver, and this is not a method that takes one.")
  | Self_type_value ->
      State.make_error_type state Not_a_value (State.read_span state value.id)
        "`Self` is a type. Build a value of it, or call one of its methods."
  | Name path -> (
      match State.find_head state value with
      | Some resolution -> Name_lookup.check_name state env value resolution
      | None -> State.raise_bug "the name `%s` is not resolved" path.last.text)
  | Member (base, member) -> check_member_value state env value base member
  | Bracket (base, items) -> check_bracket state env ?expected value base items
  | Call (callee, arguments) -> Methods.check_call state env ?expected value callee arguments
  | Try inner -> Operators.try_ state env value inner
  | With (base, updates) -> Calls.check_record_update state env value base updates
  | Prefix (operator, inner) -> Operators.check_prefix state env ?expected value operator inner
  | Mode (mode, inner) ->
      State.note_mode_keyword state value mode inner;
      (match State.find_keyword_operation state inner with
      | Some (call_id, _) ->
          state.keyword_modes <-
            (call_id, match mode with Mut -> Language.Mode.Mut | Own -> Language.Mode.Own)
            :: state.keyword_modes
      | None -> ());
      let type_ = check_expression state env ?expected inner in
      if mode = Mut && Option.is_none (State.find_keyword_operation state inner) then
        Modes.mutate state env ~by:Passed_mut inner;
      State.alias_expression state value inner;
      type_
  | Any inner -> Operators.check_any state env ?expected value inner
  | Binary { operator; left; right; _ } ->
      Operators.check_binary state env ?expected value operator left right
  | Is { value = tested; pattern = written; _ } ->
      let tested_type =
        State.run_in_statement state env (State.read_span state tested.id) (fun () ->
            check_expression state env tested)
      in
      let mode = Modes.classify_scrutinee_mode state tested in
      Pattern_typing.check_pattern state env written tested_type ~mode;
      State.register_expression state value (fun () ->
          Matches
            {
              value = Operands.build mode (State.build_expression state tested);
              pattern = State.build_scrutinee_pattern state written;
            });
      Types.bool
  | Range { start; stop; inclusive; _ } ->
      let element =
        match (start, stop) with
        | Some start, Some stop ->
            let element = check_expression state env start in
            let stop_type = check_expression state env ~expected:element stop in
            Operators.check_literal_operands state ~left:element ~right:stop_type;
            if not (State.unify state element stop_type) then
              State.report_mismatch state (State.read_span state stop.id) ~expected:element
                ~actual:stop_type;
            element
        | Some only, None | None, Some only -> check_expression state env only
        | None, None -> State.make_fresh_type state
      in
      State.register_expression state value (fun () ->
          Form.build_range_record state value start stop ~inclusive);
      Types.Named { path = Well_known.make_path Range; arguments = [ Types.Type element ] }
  | Quantified { quantifier; binder; body } ->
      (match binder with
      | Binder_in (written, collection) ->
          let element = Values.check_collection_element state env ~quantifier:value collection in
          Pattern_typing.check_pattern state env written element ~mode:Language.Mode.Read
      | Binder_type (bound, written) ->
          if not env.specification then
            State.report state Specification_only (State.read_span state value.id)
              "A quantifier over a whole type cannot run, so it is only for specifications and the \
               bodies of functions for specifications only. Quantify over a range or a collection.";
          State.declare state bound
            (Interface.Elaborator.elaborate_type state.context written)
            ~binding:Let ~mode:Language.Mode.Read);
      check state { env with in_quantifier = true } body Types.bool;
      State.register_expression state value (fun () ->
          let make_quantified binder : Core.kind =
            Quantified { quantifier; binder; body = State.build_expression state body }
          in
          match (binder, state.tables.loops.(value.id)) with
          | Binder_type (bound, _), _ ->
              make_quantified
                (Over_type
                   {
                     local = Declared { origin = bound.id; name = bound.text };
                     type_ = Form.read_local_type state bound.id;
                   })
          | Binder_in (written, collection), Some (Elements { count; element; lends }) ->
              let pattern = State.build_pattern state written in
              Form.quantify_over_elements state collection ~count ~element ~lends ~origin:value.id
                (fun elements -> make_quantified (Over_elements { pattern; elements }))
          | ( Binder_in (written, { kind = Range { start = Some start; stop = Some stop; _ }; _ }),
              Some (Integer_range { inclusive; _ }) ) ->
              let pattern = State.build_pattern state written in
              let start = State.build_expression state start in
              make_quantified
                (Over_range { pattern; start; stop = State.build_expression state stop; inclusive })
          | Binder_in _, (None | Some (Integer_range _ | Pulled _)) ->
              State.raise_bug "the checker recorded no iteration for a quantifier over a collection");
      Types.bool
  | Echo inner ->
      let type_ = check_expression state env ?expected inner in
      State.register_expression state value (fun () -> Echo (State.build_expression state inner));
      type_
  | Return inner ->
      State.reject_in_formula state env (State.read_span state value.id) "`return`";
      State.register_expression state value (fun () ->
          match (inner, env.output) with
          | Some inner, Some (Lends (mode, _)) ->
              let returned =
                State.make_synthetic_expression state ~origin:value.id Types.Never (Return None)
              in
              Block
                {
                  statements =
                    Form.lend_statements state mode (State.build_expression state inner)
                    @ [
                        {
                          id = State.allocate_node_id state;
                          origin = value.id;
                          kind = Evaluate returned;
                        };
                      ];
                  value = None;
                }
          | _ -> Return (Option.map (State.build_expression state) inner));
      (match (inner, env.output) with
      | Some inner, Some (Returns output) -> check state env inner output
      | Some inner, Some (Lends (_, part)) ->
          State.mark_lent_tails state inner;
          check state env inner part
      | None, Some (Returns output) ->
          if not (State.unify state output Types.unit) then
            State.report_mismatch state (State.read_span state value.id) ~expected:output
              ~actual:Types.unit
      | Some inner, _ -> ignore (check_expression state env inner)
      | None, _ -> ());
      Types.Never
  | Parenthesized inner ->
      let type_ = check_expression state env ?expected inner in
      State.alias_expression state value inner;
      type_
  | List items -> Values.check_list_literal state env ?expected value items
  | Map entries -> Values.check_map_literal state env ?expected value entries
  | Lambda { parameters; body } -> Values.check_lambda state env ?expected value parameters body
  | If { condition = test; then_; else_ } ->
      Values.check_if state env ?expected value test then_ else_
  | Match { scrutinees; arms } -> Values.match_ state env ?expected value scrutinees arms
  | Provide { implementations; body } ->
      List.iter
        (fun implementation -> ignore (check_expression state env implementation))
        implementations;
      State.register_expression state value (fun () ->
          Form.build_provide state implementations body);
      Statements.check_block_value state env ?expected body
  | Block body ->
      State.register_expression state value (fun () -> Block (State.build_block state body));
      Statements.check_block_value state env ?expected body
  | Expression_error -> Types.Error Diagnostic.reported_elsewhere

and check_member_value state env (value : Syntax.expression) (base : Syntax.expression)
    (member : Syntax.name) =
  match Instantiation.find_static state base with
  | Some (Static_type type_) -> Name_lookup.check_static_member state value type_ member
  | Some (Static_trait _ | Static_capability _) ->
      State.make_error_type state Not_a_value (State.read_span state value.id)
        (Printf.sprintf "`%s` is a method; call it with `(...)`." member.text)
  | None -> (
      let base_type = State.normalize state (check_expression state env base) in
      match base_type with
      | Types.Error _ | Types.Hole -> base_type
      | _ ->
          State.register_expression state value (fun () ->
              Use
                (Field
                   {
                     base = State.make_place (State.build_expression state base);
                     field = member.text;
                     type_ = Form.read_type state value;
                     origin = value.id;
                   }));
          Name_lookup.check_field state value base_type member)

and check_bracket state env ?expected (value : Syntax.expression) (base : Syntax.expression) items =
  match state.resolved.brackets.(value.id) with
  | Some Type_arguments -> (
      match State.find_head state value with
      | Some resolution -> Name_lookup.check_name state env value resolution
      | None -> State.raise_bug "type arguments are written after an expression that is not a name")
  | Some Method_bracket -> (
      match base.kind with
      | Member (inner, member)
        when Option.is_none (Instantiation.find_static state inner)
             && is_field state env inner member ->
          check_index state env ?expected value base items
      | _ ->
          State.make_error_type state Not_a_value (State.read_span state value.id)
            "A method with type arguments is called: write `(...)` after it.")
  | Some Index | None -> check_index state env ?expected value base items

and is_field state env (inner : Syntax.expression) (member : Syntax.name) =
  let base_type =
    match state.tables.types.(inner.id) with
    | Some type_ -> type_
    | None -> check_expression state env inner
  in
  match State.normalize state base_type with
  | Types.Named { path; arguments } -> (
      match Members.find_fields state.lookups path arguments with
      | Some fields ->
          List.exists (fun (field : Types.field) -> field.field_name = member.text) fields
      | None -> false)
  | _ -> false

and check_index state env ?expected:_ (value : Syntax.expression) (base : Syntax.expression) items =
  let base_type =
    State.normalize state
      (match state.tables.types.(base.id) with
      | Some type_ -> type_
      | None -> check_expression state env base)
  in
  match items with
  | [ Item ({ kind = Range { start; stop; _ }; _ } as range) ] -> (
      Option.iter (fun start -> check state env start (Types.make_builtin UInt64)) start;
      Option.iter (fun stop -> check state env stop (Types.make_builtin UInt64)) stop;
      State.record state range
        (Types.Named
           {
             path = Well_known.make_path Range;
             arguments = [ Types.Type (Types.make_builtin UInt64) ];
           });
      State.register_expression state value (fun () ->
          let base = State.make_place (State.build_expression state base) in
          let start = Option.map (State.build_expression state) start in
          let stop = Option.map (State.build_expression state) stop in
          State.make_range state ~origin:value.id base ~start ~stop
            ~inclusive:(match range.kind with Range { inclusive; _ } -> inclusive | _ -> false));
      match (State.find_sequence_element base_type, base_type) with
      | Some element, _ ->
          Types.Named { path = Well_known.make_path Slice; arguments = [ Types.Type element ] }
      | None, Types.Named { path; _ }
        when Well_known.is String path || Well_known.is String_slice path ->
          State.make_error_type state Not_indexable (State.read_span state value.id)
            "Strings cannot be indexed: say which you mean with `bytes()` or `characters()`."
      | None, (Types.Error _ | Types.Hole) -> base_type
      | None, _ ->
          State.make_error_type state Not_indexable (State.read_span state value.id)
            (Printf.sprintf "%s cannot be sliced."
               (String.capitalize_ascii (State.describe state base_type))))
  | [ Item key ] -> (
      if Types.is_well_known String base_type || Types.is_well_known String_slice base_type then begin
        State.make_error_type state Not_indexable (State.read_span state value.id)
          "Strings cannot be indexed: say which you mean with `bytes()` or `characters()`."
      end
      else
        match (State.find_sequence_element base_type, base_type) with
        | _, (Types.Error _ | Types.Hole) ->
            ignore (check_expression state env key);
            base_type
        | Some element, _ ->
            let uint64 = Types.make_builtin UInt64 in
            let actual = check_expression state env ~expected:uint64 key in
            Name_lookup.coerce state env ~argument:Read key ~actual ~expected:uint64;
            State.register_expression state value (fun () ->
                Use
                  (Element
                     {
                       base = State.make_place (State.build_expression state base);
                       index = State.build_expression state key;
                       type_ = State.finalize_type state element;
                       origin = value.id;
                     }));
            element
        | None, _ -> (
            let { Well_known.owner; name; receiver } = Well_known.locate_method Index_at in
            let index_trait =
              State.make_trait_reference ~arguments:[] (Well_known.make_path owner)
            in
            match State.find_evidence state base_type index_trait with
            | Some _ ->
                let resolve_associated associated =
                  State.resolve_associated_type state base_type index_trait associated
                    ~at:(State.read_span state value.id)
                in
                let key_type = resolve_associated Index_key
                and output = resolve_associated Index_output in
                let actual = check_expression state env ~expected:key_type key in
                Name_lookup.coerce state env ~argument:Read ~takes_view_as_owner:true key ~actual
                  ~expected:key_type;
                state.tables.calls.(value.id) <-
                  Some
                    {
                      callee =
                        Trait_method
                          {
                            trait = index_trait;
                            name;
                            receiver;
                            self_type = base_type;
                            instantiation = Types.no_instantiation;
                          };
                      arguments =
                        [
                          { expression = base.id; core_argument_index = 0; mode = Read };
                          { expression = key.id; core_argument_index = 1; mode = Read };
                        ];
                      omitted_defaults = [];
                      callee_result = output;
                    };
                Form.register_index state value;
                output
            | None ->
                ignore (check_expression state env key);
                State.make_error_type state Not_indexable (State.read_span state value.id)
                  (Printf.sprintf "%s cannot be indexed."
                     (String.capitalize_ascii (State.describe state base_type)))))
  | _ ->
      State.make_error_type state Not_indexable (State.read_span state value.id)
        "An index is one value."

let () =
  Hooks.expression_hook := check_expression;
  Hooks.check_hook := check
