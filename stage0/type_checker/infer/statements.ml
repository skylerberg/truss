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

let statement_diverges (state : State.state) =
  State.diverges ~is_never:(fun (value : Syntax.expression) ->
      match state.tables.types.(value.id) with
      | Some type_ -> Conversions.read_expected_head state type_ = Types.Never
      | None -> false)

let rec check_block_value state env ?expected (written : Syntax.block) =
  let rec infer_statements_value = function
    | [] -> Types.unit
    | [ (last : Syntax.statement) ] -> (
        match last.kind with
        | Expression value -> Hooks.check_expression state env ?expected value
        | _ ->
            ignore (check_statement state env last ~last:true);
            if statement_diverges state last then Types.Never else Types.unit)
    | (first : Syntax.statement) :: rest ->
        ignore
          (Solver.run_in_statement state env (State.read_span state first.id) (fun () ->
               check_statement state env first ~last:false));
        infer_statements_value rest
  in
  infer_statements_value written.statements

and check_statement state env (written : Syntax.statement) ~last : unit =
  match written.kind with
  | Expression value ->
      state.tables.discarded.(written.id) <- true;
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
            let annotated =
              Interface.Elaborator.elaborate_type (State.read_context state) annotation
            in
            Hooks.check state env value annotated;
            annotated
        | None -> (
            let type_ = Hooks.check_expression state env value in
            match written_pattern.kind with
            | Variant _ | Record _ | Literal (Literal_string _) ->
                Conversions.read_actual_head state value type_
            | _ -> type_)
      in
      if is_var then begin
        State.reject_in_formula state env (State.read_span state written.id) "A `var`";
        Modes.note_owned_value state env value
      end;
      (match else_ with
      | Some block -> (
          let else_type = check_block_value state env block in
          match Conversions.read_expected_head state else_type with
          | Types.Never -> ()
          | _ ->
              State.report state Mismatch (State.read_span state block.id)
                "The `else` of a `let` must leave the block, with `return`, `break`, `continue`, \
                 or `unreachable`.")
      | None -> ());
      let mode =
        if is_var then Language.Mode.Own
        else if Places.is_borrowed state.State.resolved state.State.tables value then
          Language.Mode.Read
        else Language.Mode.Own
      in
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
          Hooks.check state env value target_type;
          Modes.note_owned_value state env value
      | Compound operation -> (
          let right_type = Hooks.check_expression state env ~expected:target_type value in
          Operators.check_literal_operands state ~left:target_type ~right:right_type;
          match operation with
          | Arithmetic arithmetic ->
              let method_, output = Operators.select_arithmetic_method arithmetic in
              let result =
                Operators.check_operator_call state written.id ~method_ ~output
                  ~left:(written_target, target_type)
                  ~right:(Some (value, right_type))
              in
              if not (State.unify state result target_type) then
                Failures.report_mismatch state (State.read_span state value.id)
                  ~expected:target_type ~actual:result
          | Shift _ ->
              ignore
                (Operators.infer_shift_result state
                   ~left:(State.read_span state written_target.id, target_type)
                   ~right:(State.read_span state value.id, right_type))
          | Bitwise _ ->
              if not (State.unify state target_type right_type) then
                Failures.report_mismatch state (State.read_span state value.id)
                  ~expected:target_type ~actual:right_type;
              ignore
                (Operators.infer_bitwise_result state
                   (State.read_span state written_target.id)
                   target_type)))
  | For { pattern = written_pattern; annotation; iterable; clauses; body; _ } ->
      State.reject_in_formula state env (State.read_span state written.id) "A `for` loop";
      let mode, inner =
        match iterable.kind with
        | Mode (mode, inner)
          when Option.is_none
                 (Places.find_keyword_operation state.State.resolved state.State.tables inner) ->
            State.note_mode_keyword state iterable mode inner;
            ((match mode with Mut -> Language.Mode.Mut | Own -> Language.Mode.Own), inner)
        | _ -> (Language.Mode.Read, iterable)
      in
      let loop_element = ref None in
      Solver.run_in_statement state env (State.read_span state iterable.id) (fun () ->
          let element, variable_mode = check_loop_iterable state env written ~mode inner in
          (match annotation with
          | Some written_annotation ->
              let annotated =
                Interface.Elaborator.elaborate_type (State.read_context state) written_annotation
              in
              if not (State.unify state element annotated) then
                ignore
                  (Failures.add_mismatch_diagnostic state Mismatch
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
      check_loop_body state env body
  | While { condition = test; clauses; body } ->
      State.reject_in_formula state env (State.read_span state written.id) "A `while` loop";
      Solver.run_in_statement state env (State.read_span state test.id) (fun () ->
          Hooks.check state env test Types.bool);
      List.iter (check_loop_clause state env) clauses;
      check_loop_body state env body
  | Parallel body | Concurrent body ->
      let concurrent = match written.kind with Concurrent _ -> true | _ -> false in
      State.reject_in_formula state env
        (State.read_span state written.id)
        (if concurrent then "A `concurrent` block" else "A `parallel` block");
      List.iter
        (fun (branch : Syntax.statement) ->
          Solver.run_in_statement state env (State.read_span state branch.id) (fun () ->
              check_statement state env branch ~last:false))
        body.statements
  | Proof body -> check_loop_body state { env with specification = true } body
  | Assert { value; _ } -> Hooks.check state env value Types.bool
  | Statement_error -> ()

and assigns_through_index state env (written : Syntax.statement) (target : Syntax.expression)
    (value : Syntax.expression) =
  match (target.kind, state.resolved.brackets.(target.id)) with
  | Bracket (_, [ Item { kind = Range _; _ } ]), _ -> false
  | Bracket (base, [ Item key ]), (Some Index | None) -> (
      let base_type = Conversions.read_checked_head state env base in
      let { Well_known.owner; name; receiver } = Well_known.locate_method Index_assign_assign in
      let trait = Types.make_trait_reference ~arguments:[] (Well_known.make_path owner) in
      match
        ( State.find_evidence state base_type trait,
          Interface.Definition.find_trait_method state.lookups.interface trait.trait ~name ~receiver
        )
      with
      | Some (Interface.Impls.From_impl _ | From_bound | From_any), Some _ ->
          let index = Types.make_trait_reference ~arguments:[] (Well_known.make_path Index) in
          let make_parameter parameter_name type_ : Types.parameter_info =
            { name = parameter_name; mode = Own; type_; has_default = false }
          in
          Modes.mutate state env ~by:Assignment base;
          ignore
            (Calls.check_argument state env key
               (make_parameter "key"
                  (Solver.resolve_associated_type state base_type index Index_key
                     ~at:(State.read_span state key.id)))
               ~has_generic_type:false);
          ignore
            (Calls.check_argument state env value
               (make_parameter "value"
                  (Solver.resolve_associated_type state base_type index Index_output
                     ~at:(State.read_span state value.id)))
               ~has_generic_type:false);
          let make_argument (argument_expression : Syntax.expression) position mode :
              Tables.argument =
            { expression = argument_expression; core_argument_index = position; mode }
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
          Solver.require state (Method_call (State.read_span state written.id)) base_type trait;
          true
      | _ -> false)
  | _ -> false

and check_loop_body state env (body : Syntax.block) =
  List.iter
    (fun (written : Syntax.statement) ->
      Solver.run_in_statement state env (State.read_span state written.id) (fun () ->
          check_statement state env written ~last:false))
    body.statements

and check_loop_clause state env (clause : Syntax.loop_clause) =
  Clauses.check_under_condition state ~id:clause.id clause.condition (fun () ->
      match clause.kind with
      | Invariant value -> Clauses.check_condition state env value
      | Loop_decreases measures -> Clauses.check_measures state env measures
      | Loop_cost cost -> Clauses.check_cost state env cost)

and record_loop (state : State.state) (written : Syntax.statement) span (loop : Tables.loop) =
  state.tables.loops.(written.id) <- Some loop;
  match loop with
  | Pulled pulled ->
      State.check_when_final state (fun () ->
          state.tables.loops.(written.id) <-
            Some
              (Pulled
                 {
                   pulled with
                   remaining = Name_lookup.find_remaining_call state span pulled.cursor;
                 }))
  | Integer_range _ | Elements _ -> ()

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
      let span = State.read_span state iterable.id in
      let type_ = Conversions.read_checked_head state env iterable in
      match type_ with
      | Types.Error _ | Types.Hole -> (type_, mode)
      | _ -> (
          let cursor = Types.make_trait_reference ~arguments:[] (Well_known.make_path Cursor) in
          let by_position : (Tables.loop * Types.ty * Language.Mode.t) Resolve.Names.lookup =
            if mode = Language.Mode.Own then Absent
            else Name_lookup.find_elements_calls state iterable type_ mode
          and consumed : (Tables.loop * Types.ty) Resolve.Names.lookup =
            if mode = Language.Mode.Own then Name_lookup.find_consuming_cursor state iterable type_
            else Absent
          in
          match (by_position, consumed, State.find_evidence state type_ cursor) with
          | Visible (loop, element, lends), _, _ ->
              record_loop state written span loop;
              (element, lends)
          | _, Visible (loop, element), _ ->
              record_loop state written span loop;
              (element, Language.Mode.Own)
          | _, _, Some _ ->
              record_loop state written span
                (Pulled { cursor = type_; cursor_call = None; remaining = None });
              ( Solver.resolve_associated_type state type_ cursor Cursor_element ~at:span,
                Language.Mode.Own )
          | Hidden hidden, _, None | _, Hidden hidden, None ->
              (Members.make_hidden_error state span hidden, mode)
          | Absent, Absent, None ->
              ( State.make_error_type state Not_indexable span
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
