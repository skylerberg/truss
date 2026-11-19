let check_bit_vector_names state (value : Core.expression) =
  Core_walk.walk_expression
    (Core_walk.make_deep_visitor
       {
         Core_walk.ignore_all with
         place =
           (function
           | Local { type_; origin; _ }
             when not (Types.is_builtin Bool type_ || Types.find_integer_range type_ <> None) ->
               State.report state Not_bit_vector (State.read_span state origin)
                 (Printf.sprintf
                    "An assertion `by bit_vector` can name only integers and booleans, and this is \
                     a `%s`."
                    (Types.show type_))
           | _ -> ());
       })
    value

let record_integer_range state ~(loop : Syntax.id) ~described ~admits_integer
    (range : Syntax.expression) element ~inclusive =
  State.check_when_final state (fun () ->
      let element = State.finalize_type state element in
      if
        State.is_within state element
          (Types.integer_types
          @ Language.Builtin_type.Character
            :: (if admits_integer then [ Language.Builtin_type.Integer ] else []))
      then state.tables.loops.(loop) <- Some (Integer_range { element; inclusive })
      else if not (Types.is_error element) then
        State.report state Not_indexable (State.read_span state range.id)
          (Printf.sprintf "%s range is of integers, not `%s`." described (Types.show element)))

let rec check_block_value state env ?expected (written : Syntax.block) =
  let rec infer_statements_value = function
    | [] -> Types.unit
    | [ (last : Syntax.statement) ] -> (
        match last.kind with
        | Expression value -> Hooks.check_expression state env ?expected value
        | _ ->
            ignore (check_statement state env last ~last:true);
            if State.statement_diverges state last then Types.Never else Types.unit)
    | (first : Syntax.statement) :: rest ->
        ignore
          (State.run_in_statement state env (State.read_span state first.id) (fun () ->
               check_statement state env first ~last:false));
        infer_statements_value rest
  in
  infer_statements_value written.statements

and check_statement state env (written : Syntax.statement) ~last : unit =
  match written.kind with
  | Expression value ->
      State.register_statement state written (fun () ->
          Evaluate (State.build_expression state value));
      let type_ = Hooks.check_expression state env value in
      if not last then
        State.check_when_final state (fun () ->
            let final_type = State.finalize_type state type_ in
            if
              not
                (final_type = Types.unit || final_type = Types.Never || Types.is_error final_type
               || final_type = Types.Hole)
            then
              State.report state Unused_value (State.read_span state value.id)
                ~fixes:
                  [
                    State.fix "Discard it on purpose."
                      [ State.insert (State.read_span state value.id).start "let _ = " ];
                  ]
                (Printf.sprintf
                   "This value of type `%s` is not used. Use it, or discard it with `let _ =`."
                   (Types.show final_type)))
  | Let { is_var; pattern = written_pattern; annotation; value; else_ } ->
      let type_ =
        match annotation with
        | Some annotation ->
            let annotated = Interface.Elaborator.elaborate_type state.context annotation in
            Hooks.check state env value annotated;
            annotated
        | None -> Hooks.check_expression state env value
      in
      if is_var then begin
        State.reject_in_formula state env (State.read_span state written.id) "A `var`";
        Modes.note_owned_value state env value
      end;
      (match else_ with
      | Some block -> (
          let else_type = check_block_value state env block in
          match State.resolve state else_type with
          | Types.Never -> ()
          | _ ->
              State.report state Mismatch (State.read_span state block.id)
                "The `else` of a `let` must leave the block, with `return`, `break`, `continue`, \
                 or `unreachable`.")
      | None -> ());
      let mode =
        if is_var then Language.Mode.Own
        else if Modes.is_borrowed state value then Language.Mode.Read
        else Language.Mode.Own
      in
      State.register_statement state written (fun () ->
          let value = Operands.build mode (State.build_expression state value) in
          let pattern = State.build_scrutinee_pattern state written_pattern in
          Let { pattern; value; else_ = Option.map (State.build_block state) else_ });
      (match (annotation, written_pattern.kind) with
      | None, Binding name -> Hashtbl.replace state.annotatable name.id ()
      | _ -> ());
      Pattern_typing.check_binding_pattern state env written_pattern type_ ~is_var ~mode
  | Assignment { target; operator = Assign; value }
    when assigns_through_index state env written target value ->
      ()
  | Assignment { target = written_target; operator; value } -> (
      let target_type = Hooks.check_expression state env written_target in
      Modes.mutate state env ~by:Assignment written_target;
      match operator with
      | Assign ->
          State.register_statement state written (fun () ->
              let target = State.make_place (State.build_expression state written_target) in
              Assign { target; value = State.build_expression state value });
          Hooks.check state env value target_type;
          Modes.note_owned_value state env value
      | Compound operation -> (
          let right_type = Hooks.check_expression state env ~expected:target_type value in
          Operators.check_literal_operands state ~left:target_type ~right:right_type;
          State.register_statement state written (fun () ->
              Form.build_compound_assign state written written_target value operation);
          match operation with
          | Arithmetic arithmetic ->
              let method_, output = Operators.select_arithmetic_method arithmetic in
              let call_site : Syntax.expression = { kind = Expression_error; id = written.id } in
              let result =
                Operators.check_operator_call
                  ~operands:
                    [
                      {
                        Tables.expression = written_target.id;
                        core_argument_index = 0;
                        mode = Language.Mode.Read;
                      };
                      {
                        Tables.expression = value.id;
                        core_argument_index = 1;
                        mode = Language.Mode.Read;
                      };
                    ]
                  state call_site ~method_ ~output ~left:target_type ~right:(Some right_type)
              in
              if not (State.unify state result target_type) then
                State.report_mismatch state (State.read_span state value.id) ~expected:target_type
                  ~actual:result
          | Shift _ ->
              ignore
                (Operators.infer_shift_result state
                   ~left:(State.read_span state written_target.id, target_type)
                   ~right:(State.read_span state value.id, right_type))
          | Bitwise _ ->
              if not (State.unify state target_type right_type) then
                State.report_mismatch state (State.read_span state value.id) ~expected:target_type
                  ~actual:right_type;
              ignore
                (Operators.infer_bitwise_result state
                   (State.read_span state written_target.id)
                   target_type)))
  | For { mode = running; pattern = written_pattern; annotation; iterable; clauses; body } ->
      State.reject_in_formula state env (State.read_span state written.id) "A `for` loop";
      let mode, inner =
        match iterable.kind with
        | Mode (mode, inner) when Option.is_none (State.find_keyword_operation state inner) ->
            State.note_mode_keyword state iterable mode inner;
            ((match mode with Mut -> Language.Mode.Mut | Own -> Language.Mode.Own), inner)
        | _ -> (Language.Mode.Read, iterable)
      in
      let loop_element = ref None in
      State.run_in_statement state env (State.read_span state iterable.id) (fun () ->
          let element, variable_mode = check_loop_iterable state env written ~mode inner in
          (match annotation with
          | Some written_annotation ->
              let annotated =
                Interface.Elaborator.elaborate_type state.context written_annotation
              in
              if not (State.unify state element annotated) then
                ignore
                  (State.add_mismatch_diagnostic state Mismatch
                     (State.read_span state written_annotation.id)
                     ~sides:[ (element, annotated) ]
                     (Printf.sprintf "Each element of this loop is %s, not %s."
                        (State.describe state element) (State.describe state annotated)))
          | None -> (
              match written_pattern.kind with
              | Binding name -> Hashtbl.replace state.annotatable name.id ()
              | _ -> ()));
          loop_element := Some element;
          (if inner != iterable then
             match state.tables.types.(inner.id) with
             | Some type_ -> State.record state iterable type_
             | None -> ());
          if mode = Language.Mode.Mut then Modes.mutate state env ~by:Passed_mut inner;
          Pattern_typing.check_binding_pattern state env written_pattern element ~is_var:false
            ~mode:variable_mode);
      List.iter
        (check_loop_clause state
           { env with loop_element = Option.map (State.resolve state) !loop_element })
        clauses;
      State.register_statement state written (fun () ->
          let pattern = State.build_pattern state written_pattern in
          let clauses = List.map (Form.build_loop_clause state) clauses in
          Form.build_for_loop state written inner ~pattern ~clauses
            ~body:(State.build_block state body) ~mode:running);
      check_loop_body state env body
  | While { condition = test; clauses; body } ->
      State.reject_in_formula state env (State.read_span state written.id) "A `while` loop";
      State.run_in_statement state env (State.read_span state test.id) (fun () ->
          Hooks.check state env test Types.bool);
      List.iter (check_loop_clause state env) clauses;
      State.register_statement state written (fun () ->
          let condition = State.build_expression state test in
          let clauses = List.map (Form.build_loop_clause state) clauses in
          While
            {
              condition;
              clauses;
              body = State.build_block state body;
              binds_lent_part = Form.binds_lent_part state condition;
            });
      check_loop_body state env body
  | Parallel body | Concurrent body ->
      let concurrent = match written.kind with Concurrent _ -> true | _ -> false in
      State.reject_in_formula state env
        (State.read_span state written.id)
        (if concurrent then "A `concurrent` block" else "A `parallel` block");
      State.register_statement state written (fun () ->
          let branches = List.map (State.build_statement state) body.statements in
          if concurrent then Concurrent branches else Parallel branches);
      List.iter
        (fun (branch : Syntax.statement) ->
          State.run_in_statement state env (State.read_span state branch.id) (fun () ->
              check_statement state env branch ~last:false))
        body.statements
  | Proof body ->
      State.register_statement state written (fun () -> Proof (State.build_block state body));
      check_loop_body state { env with specification = true } body
  | Assert { value; by_bit_vector } ->
      State.register_statement state written (fun () ->
          let value = State.build_expression state value in
          if by_bit_vector then check_bit_vector_names state value;
          Assert
            { condition = { value; executable = Form.is_executable state value }; by_bit_vector });
      Hooks.check state env value Types.bool
  | Statement_error -> ()

and assigns_through_index state env (written : Syntax.statement) (target : Syntax.expression)
    (value : Syntax.expression) =
  match (target.kind, state.resolved.brackets.(target.id)) with
  | Bracket (_, [ Item { kind = Range _; _ } ]), _ -> false
  | Bracket (base, [ Item key ]), (Some Index | None) -> (
      let base_type = State.normalize state (Hooks.check_expression state env base) in
      let { Well_known.owner; name; receiver } = Well_known.locate_method Index_assign_assign in
      let trait = State.make_trait_reference ~arguments:[] (Well_known.make_path owner) in
      match
        ( State.find_evidence state base_type trait,
          Interface.Definition.find_trait_method state.lookups.interface trait.trait ~name ~receiver
        )
      with
      | Some (Interface.Impls.From_impl _ | From_bound | From_any), Some _ ->
          let index = State.make_trait_reference ~arguments:[] (Well_known.make_path Index) in
          let make_parameter parameter_name type_ : Types.parameter_info =
            { name = parameter_name; mode = Own; type_; has_default = false }
          in
          Modes.mutate state env ~by:Assignment base;
          ignore
            (Calls.check_argument state env key
               (make_parameter "key"
                  (State.resolve_associated_type state base_type index Index_key
                     ~at:(State.read_span state key.id)))
               ~has_generic_type:false);
          ignore
            (Calls.check_argument state env value
               (make_parameter "value"
                  (State.resolve_associated_type state base_type index Index_output
                     ~at:(State.read_span state value.id)))
               ~has_generic_type:false);
          let call : Syntax.expression = { kind = Expression_error; id = written.id } in
          State.record state call Types.unit;
          let make_argument (argument_expression : Syntax.expression) position mode :
              Tables.argument =
            { expression = argument_expression.id; core_argument_index = position; mode }
          in
          state.tables.calls.(written.id) <-
            Some
              {
                callee =
                  Trait_method
                    {
                      trait;
                      name;
                      receiver;
                      self_type = base_type;
                      instantiation = Types.no_instantiation;
                    };
                arguments =
                  [ make_argument base 0 Mut; make_argument key 1 Own; make_argument value 2 Own ];
                omitted_defaults = [];
                callee_result = Types.unit;
              };
          Form.register_call state call;
          State.register_statement state written (fun () ->
              Evaluate (State.build_expression state call));
          true
      | _ -> false)
  | _ -> false

and check_loop_body state env (body : Syntax.block) =
  List.iter
    (fun (written : Syntax.statement) ->
      State.run_in_statement state env (State.read_span state written.id) (fun () ->
          check_statement state env written ~last:false))
    body.statements

and check_loop_clause state env (clause : Syntax.loop_clause) =
  let env = { env with specification = true } in
  State.run_in_statement state env (State.read_span state clause.id) (fun () ->
      match clause.kind with
      | Invariant value -> Hooks.check state env value Types.bool
      | Loop_decreases measures ->
          List.iter (fun measure -> ignore (Hooks.check_expression state env measure)) measures
      | Loop_cost cost -> (
          State.check_cost state cost;
          match cost.bound with
          | Big_o value | At_most value | Exactly value ->
              ignore (Hooks.check_expression state env value)))

and check_loop_iterable state env (written : Syntax.statement) ~mode (iterable : Syntax.expression)
    =
  match iterable.kind with
  | Range { start = Some _; stop = Some _; inclusive; _ } -> (
      let range_type = State.normalize state (Hooks.check_expression state env iterable) in
      match range_type with
      | Types.Named { arguments = [ Types.Type element ]; _ } ->
          record_integer_range state ~loop:written.id ~described:"A `for` loop's"
            ~admits_integer:false iterable element ~inclusive;
          (element, mode)
      | _ -> State.raise_bug "a range is not of the range type")
  | _ -> (
      let type_ = State.normalize state (Hooks.check_expression state env iterable) in
      match type_ with
      | Types.Error _ | Types.Hole -> (type_, mode)
      | _ -> (
          let cursor = State.make_trait_reference ~arguments:[] (Well_known.make_path Cursor) in
          let by_position : (Tables.loop * Types.ty * Language.Mode.t) Resolve.Names.lookup =
            if mode = Language.Mode.Own then Absent
            else
              Name_lookup.find_elements_calls state (State.read_span state iterable.id) type_ mode
          and consumed : (Tables.loop * Types.ty) Resolve.Names.lookup =
            if mode = Language.Mode.Own then
              Name_lookup.find_consuming_cursor state (State.read_span state iterable.id) type_
            else Absent
          in
          match (by_position, consumed, State.find_evidence state type_ cursor) with
          | Visible (loop, element, lends), _, _ ->
              State.record_loop state ~loop:written.id ~iterable loop;
              (element, lends)
          | _, Visible (loop, element), _ ->
              State.record_loop state ~loop:written.id ~iterable loop;
              (element, Language.Mode.Own)
          | _, _, Some _ ->
              State.record_loop state ~loop:written.id ~iterable
                (Pulled
                   {
                     cursor = type_;
                     cursor_call = None;
                     remaining =
                       Name_lookup.find_remaining_call state
                         (State.read_span state iterable.id)
                         type_;
                   });
              ( State.resolve_associated_type state type_ cursor Cursor_element
                  ~at:(State.read_span state iterable.id),
                Language.Mode.Own )
          | Hidden hidden, _, None | _, Hidden hidden, None ->
              (Members.make_hidden_error state (State.read_span state iterable.id) hidden, mode)
          | Absent, Absent, None ->
              ( State.make_error_type state Not_indexable
                  (State.read_span state iterable.id)
                  (match mode with
                  | Language.Mode.Read ->
                      Printf.sprintf
                        "A `for` loop cannot go over %s: it is not a `Cursor`, and it has no \
                         `count` and `element` to visit it by position."
                        (State.describe state type_)
                  | Mut ->
                      Printf.sprintf
                        "A `for` loop cannot mutate the elements of `%s`: it has no `element` that \
                         takes `mut self`."
                        (Types.show type_)
                  | Own ->
                      Printf.sprintf
                        "A `for` loop cannot consume `%s`: it has no `cursor` that takes `own \
                         self`."
                        (Types.show type_)),
                mode )))
