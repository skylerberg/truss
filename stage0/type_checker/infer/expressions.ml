let rec check_expression (state : State.state) (env : State.env) ?expected
    (value : Syntax.expression) : Types.ty =
  let env =
    match value.kind with
    | If _ | Match _ | Block _ | Parenthesized _ -> env
    | _ -> if env.binds_view then { env with binds_view = false } else env
  in
  let type_ =
    if Hashtbl.mem state.lent_tails value.id then check_lent_part state env value
    else check_expression_kind state env ?expected value
  in
  State.record state value type_;
  State.note_compiled_expression state env value;
  match State.resolve state type_ with
  | Types.Variable index
    when env.specification
         && (not (Hashtbl.mem state.unifier.specification_unknowns index))
         && State.is_within state type_ Types.integer_types ->
      Conversions.coerce state env value ~actual:type_ ~expected:Types.Integer;
      Types.Integer
  | _ -> type_

and check_lent_part state env (value : Syntax.expression) : Types.ty =
  Hashtbl.remove state.lent_tails value.id;
  match env.output with
  | Some (Lends (mode, part)) ->
      let inner =
        match value.kind with
        | Mode (mode, inner)
          when Option.is_none
                 (Places.find_keyword_operation state.State.resolved state.State.tables inner) ->
            State.note_mode_keyword state value mode inner;
            inner
        | _ -> value
      in
      Hashtbl.replace state.yielded inner.id (match mode with Mut -> Mut | Read | Own -> Read);
      let actual = check_expression state env ~expected:part inner in
      if inner != value then if mode = Mut then Modes.mutate state env ~by:Passed_mut inner;
      Conversions.coerce state env inner ~actual ~expected:part;
      actual
  | _ -> check_expression_kind state env value

and check state env (value : Syntax.expression) (expected : Types.ty) =
  let actual = check_expression state env ~expected value in
  Conversions.coerce state env value ~actual ~expected

and check_expression_kind state env ?expected (value : Syntax.expression) : Types.ty =
  match value.kind with
  | Integer number ->
      State.elaborate state value.id (Literal (Integer_value number));
      Pattern_typing.check_integer_literal state env ?expected value number
  | Float number ->
      let significand = number.significand and exponent = number.exponent in
      let rounded_float32 = Literals.round_float32 ~significand ~exponent
      and rounded_float64 = Literals.round_float64 ~significand ~exponent in
      let report_too_large target =
        State.add_diagnostic state (Float_too_large { at = Written value.id; target })
      in
      let type_ =
        match
          List.filter_map
            (fun (builtin, rounded) -> Option.map (fun _ -> builtin) rounded)
            [ (Language.Builtin_type.Float32, rounded_float32); (Float64, rounded_float64) ]
        with
        | [] -> Types.Error (report_too_large (Exactly (Types.make_builtin Float64)))
        | allowed ->
            State.make_literal_type state value allowed ~report_excluded:(fun excluded ->
                report_too_large (State.make_shown state excluded))
      in
      State.check_when_final state (fun () ->
          Option.iter
            (fun rounded -> State.elaborate state value.id (Literal (Float_value rounded)))
            (if Types.is_builtin Float32 (State.finalize_type state type_) then rounded_float32
             else rounded_float64));
      type_
  | String literal -> (
      match Pattern_typing.find_character_tag state literal with
      | Some builtin -> Pattern_typing.check_character_literal state value.id literal builtin
      | None -> Values.check_string_literal state env ?expected value literal)
  | True | False -> Types.bool
  | Todo -> ( match expected with Some expected -> expected | None -> Types.Hole)
  | Unreachable ->
      State.reject_in_formula state env (Written value.id) Unreachable_expression;
      Types.Never
  | Break | Continue ->
      State.reject_in_formula state env (Written value.id)
        (match value.kind with Break -> Break_expression | _ -> Continue_expression);
      Types.Never
  | Self_value -> (
      state.locals_read <- state.definition.id :: state.locals_read;
      match env.self with
      | Some self -> self
      | None -> State.make_error_type state (Self_outside_method { at = Written value.id }))
  | Self_type_value -> State.make_error_type state (Self_type_as_value { at = Written value.id })
  | Name name -> (
      match State.find_head state value with
      | Some resolution -> Name_lookup.check_name state env value resolution
      | None -> State.raise_bug "the name `%s` is not resolved" name.text)
  | Member (base, member) -> (
      match State.find_head state value with
      | Some resolution -> Name_lookup.check_name state env value resolution
      | None -> check_member_value state env ?expected value base member)
  | Bracket (base, items) -> check_bracket state env ?expected value base items
  | Call (callee, arguments) -> Methods.check_call state env ?expected value callee arguments
  | Try inner -> Operators.try_ state env value inner
  | With (base, updates) -> Calls.check_record_update state env value base updates
  | Prefix (operator, inner) -> Operators.check_prefix state env ?expected value operator inner
  | Mode (mode, inner) ->
      State.note_mode_keyword state value mode inner;
      (match Places.find_keyword_operation state.State.resolved state.State.tables inner with
      | Some (call_id, _) ->
          state.keyword_modes <-
            (call_id, match mode with Mut -> Language.Mode.Mut | Own -> Language.Mode.Own)
            :: state.keyword_modes
      | None -> ());
      let type_ = check_expression state env ?expected inner in
      if
        mode = Mut
        && Option.is_none
             (Places.find_keyword_operation state.State.resolved state.State.tables inner)
      then Modes.mutate state env ~by:Passed_mut inner;
      type_
  | Binary { operator; left; right; _ } ->
      Operators.check_binary state env ?expected value operator left right
  | Is { value = tested; pattern = written; _ } ->
      let tested_type =
        Solver.run_in_statement state env (Written tested.id) (fun () ->
            check_expression state env tested)
      in
      let mode = Places.classify_scrutinee_mode state.State.resolved state.State.tables tested in
      Pattern_typing.check_pattern state env written tested_type ~mode;
      Types.bool
  | Range { start; stop; _ } ->
      let element =
        match (start, stop) with
        | Some start, Some stop ->
            let start_type = check_expression state env start in
            let stop_type = check_expression state env ~expected:start_type stop in
            Operators.check_literal_operands state ~left:start_type ~right:stop_type;
            let is_integer type_ =
              State.is_within state type_ (Types.integer_types @ [ Language.Builtin_type.Integer ])
            in
            if State.unify state start_type stop_type then start_type
            else if env.specification && is_integer start_type && is_integer stop_type then begin
              List.iter
                (fun (bound, actual) ->
                  Conversions.coerce state env bound ~actual ~expected:Types.Integer)
                [ (start, start_type); (stop, stop_type) ];
              Types.Integer
            end
            else begin
              Failures.report_mismatch state (Written stop.id) ~expected:start_type
                ~actual:stop_type;
              start_type
            end
        | Some only, None | None, Some only -> check_expression state env only
        | None, None -> Types.Error Catalog.reported_elsewhere
      in
      Types.Named { path = Well_known.make_path Range; arguments = [ Types.Type element ] }
  | Quantified { quantifier; binder; body } ->
      let type_ =
        match binder with
        | Binder_in (written, collection) ->
            let element = Values.check_collection_element state env ~quantifier:value collection in
            Pattern_typing.check_pattern state env written element ~mode:Language.Mode.Read;
            Types.bool
        | Binder_type (bound, written) ->
            State.declare state bound
              (Interface.Elaborator.elaborate_type (State.read_context state) written)
              ~binding:Let ~mode:Language.Mode.Read;
            if env.specification then Types.bool
            else
              Types.Error
                (State.report_specification_only state
                   (Quantifier_over_type_in_code { at = Written value.id; quantifier }))
      in
      check state { env with in_quantifier = true } body Types.bool;
      type_
  | Echo inner ->
      let type_ = check_expression state env ?expected inner in
      type_
  | Return inner ->
      State.reject_in_formula state env (Written value.id) Return_expression;
      (match (inner, env.output) with
      | Some inner, Some (Returns output) -> check state env inner output
      | Some inner, Some (Lends (_, part)) ->
          State.mark_lent_tails state inner;
          check state env inner part
      | None, Some (Returns output) ->
          if not (State.unify state output Types.unit) then
            Failures.report_mismatch state (Written value.id) ~expected:output ~actual:Types.unit
      | Some inner, _ -> ignore (check_expression state env inner)
      | None, _ -> ());
      Types.Never
  | Parenthesized inner ->
      let type_ = check_expression state env ?expected inner in
      type_
  | List items -> Values.check_list_literal state env ?expected value items
  | Map entries -> Values.check_map_literal state env ?expected value entries
  | Lambda { parameters; body } -> Values.check_lambda state env ?expected value parameters body
  | If { condition = test; then_; else_ } -> Values.check_if state env ?expected test then_ else_
  | Match { scrutinees; arms } -> Values.match_ state env ?expected scrutinees arms
  | Provide { implementations; body } ->
      List.iter
        (fun implementation -> ignore (check_expression state env implementation))
        implementations;
      Statements.check_block_value state env ?expected body
  | Block body -> Values.check_block state env ?expected body
  | Expression_error -> Types.Error Catalog.reported_elsewhere

and check_member_value state env ?expected (value : Syntax.expression) (base : Syntax.expression)
    (member : Syntax.name) =
  match Instantiation.find_static state base with
  | Some (Static_type type_) -> Name_lookup.check_static_member state ?expected value type_ member
  | Some (Static_trait (trait, trait_arguments)) ->
      Name_lookup.check_trait_value_in_full state ?expected value trait ~trait_arguments member
  | Some (Static_capability _) ->
      State.make_error_type state
        (Static_method_as_value { at = Written value.id; name = member.text })
  | None -> (
      let base_type = Conversions.read_checked_head state env base in
      match base_type with
      | Types.Error _ | Types.Hole -> base_type
      | _ -> Name_lookup.check_field state value base_type member)

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
          State.make_error_type state
            (Method_with_type_arguments_as_value { at = Written value.id }))
  | Some Index | None -> check_index state env ?expected value base items

and is_field state env (inner : Syntax.expression) (member : Syntax.name) =
  let base_type =
    match state.tables.types.(inner.id) with
    | Some type_ -> type_
    | None -> check_expression state env inner
  in
  match Conversions.read_actual_head state inner base_type with
  | Types.Named { path; arguments } -> (
      match Members.find_fields state.lookups path arguments with
      | Some fields ->
          List.exists (fun (field : Types.field) -> field.field_name = member.text) fields
      | None -> false)
  | _ -> false

and check_index state env ?expected:_ (value : Syntax.expression) (base : Syntax.expression) items =
  let base_type =
    Conversions.read_actual_head state base
      (match state.tables.types.(base.id) with
      | Some type_ -> type_
      | None -> check_expression state env base)
  in
  match items with
  | [ Item ({ kind = Range { start; stop; _ }; _ } as range) ] -> (
      let model_element = Types.find_specification_sequence_element base_type in
      let bound_type =
        match model_element with Some _ -> Types.Integer | None -> Types.make_builtin UInt64
      in
      Option.iter (fun start -> check state env start bound_type) start;
      Option.iter (fun stop -> check state env stop bound_type) stop;
      State.record state range
        (Types.Named { path = Well_known.make_path Range; arguments = [ Types.Type bound_type ] });
      match (model_element, Types.find_sequence_element base_type, base_type) with
      | Some element, _, _ ->
          Types.Named { path = Well_known.make_path Sequence; arguments = [ Types.Type element ] }
      | None, Some element, _ -> Types.make_named (Well_known.make_path List) [ element ]
      | None, None, _
        when Types.is_well_known String (Types.strip_view base_type)
             && state.package = Path.standard_package ->
          Types.string_type
      | None, None, _ when Types.is_well_known String (Types.strip_view base_type) ->
          State.make_error_type state (String_indexed { at = Written value.id })
      | None, None, (Types.Error _ | Types.Hole) -> base_type
      | None, None, _ ->
          State.make_error_type state
            (Not_sliceable { at = Written value.id; base = State.make_shown state base_type }))
  | [ Item key ] -> (
      if Types.is_well_known String (Types.strip_view base_type) then begin
        State.make_error_type state (String_indexed { at = Written value.id })
      end
      else
        match (Types.find_sequence_element base_type, base_type) with
        | _, (Types.Error _ | Types.Hole) ->
            ignore (check_expression state env key);
            base_type
        | Some element, _ ->
            let uint64 = Types.make_builtin UInt64 in
            let actual = check_expression state env ~expected:uint64 key in
            Conversions.coerce state env ~argument:Read key ~actual ~expected:uint64;
            element
        | None, _ -> (
            let { Well_known.owner; _ } = Well_known.locate_method Index_at in
            let index_trait =
              Types.make_trait_reference ~arguments:[] (Well_known.make_path owner)
            in
            match State.find_evidence state base_type index_trait with
            | Some _ ->
                let resolve_associated associated =
                  Solver.resolve_associated_type state base_type index_trait associated
                    ~at:(Written value.id)
                in
                let key_type = resolve_associated Index_key
                and output = resolve_associated Index_output in
                let actual = check_expression state env ~expected:key_type key in
                Conversions.coerce state env ~argument:Read key ~actual ~expected:key_type;
                State.elaborate state value.id
                  (Call
                     (Tables.make_method_call ~lends:Read index_trait Index_at ~self_type:base_type
                        ~result:output
                        [ (base, Read); (key, Read) ]));
                output
            | None ->
                ignore (check_expression state env key);
                State.make_error_type state
                  (Not_indexable { at = Written value.id; base = State.make_shown state base_type })
            ))
  | _ -> State.make_error_type state (Several_indexes { at = Written value.id })

let () =
  Hooks.expression_hook := check_expression;
  Hooks.check_hook := check
