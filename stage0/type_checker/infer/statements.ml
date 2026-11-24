let make_trait known = Types.make_trait_reference ~arguments:[] (Well_known.make_path known)

let record_integer_range state ~(loop : Syntax.id) ~owner ~admits_integer
    (range : Syntax.expression) element ~inclusive =
  State.check_when_final state (fun () ->
      let element = State.finalize_type state element in
      if
        State.is_within state element
          (Types.integer_types
          @ Language.Builtin_type.Character
            :: (if admits_integer then [ Language.Builtin_type.Integer ] else []))
      then State.elaborate state loop (Loop (Integer_range { element; inclusive }))
      else if not (Types.is_error element) then
        State.report state (Range_not_integer { at = Written range.id; owner; element }))

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
          (Solver.run_in_statement state env (Written first.id) (fun () ->
               check_statement state env first ~last:false));
        infer_statements_value rest
  in
  infer_statements_value written.statements

and check_statement state env (written : Syntax.statement) ~last : unit =
  match written.kind with
  | Expression value ->
      State.elaborate state written.id Discarded;
      let type_ = Hooks.check_expression state env value in
      if not last then
        State.check_when_final state (fun () ->
            let final_type = State.finalize_type state type_ in
            if
              not
                (final_type = Types.unit || final_type = Types.Never || Types.is_error final_type
               || final_type = Types.Hole)
            then State.report state (Unused_value { at = Written value.id; type_ = final_type }))
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
            | Variant _ | Record _ | Tuple _ | Literal (Literal_string _) ->
                Conversions.read_actual_head state value type_
            | _ -> type_)
      in
      if is_var then begin
        State.reject_in_formula state env (Written written.id) Var_binding;
        Modes.note_owned_value state env value
      end;
      (match else_ with
      | Some block -> (
          let else_type = check_block_value state env block in
          match Conversions.read_expected_head state else_type with
          | Types.Never -> ()
          | _ -> State.report state (Let_else_falls_through { at = Written block.id }))
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
      Pattern_typing.check_binding_pattern state env written_pattern type_ ~is_var
        ~accepts_tuple_pattern:(Option.is_none annotation) ~mode
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
                Failures.report_mismatch state (Written value.id) ~expected:target_type
                  ~actual:result
          | Shift _ ->
              ignore
                (Operators.infer_shift_result state
                   ~left:(Core.Written written_target.id, target_type)
                   ~right:(Core.Written value.id, right_type))
          | Bitwise _ ->
              if not (State.unify state target_type right_type) then
                Failures.report_mismatch state (Written value.id) ~expected:target_type
                  ~actual:right_type;
              ignore (Operators.infer_bitwise_result state (Written written_target.id) target_type))
      )
  | For { pattern = written_pattern; annotation; iterable; clauses; body; _ } ->
      State.reject_in_formula state env (Written written.id) For_statement;
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
      Solver.run_in_statement state env (Written iterable.id) (fun () ->
          let element, variable_mode = check_loop_iterable state env written ~mode inner in
          (match annotation with
          | Some written_annotation ->
              let annotated =
                Interface.Elaborator.elaborate_type (State.read_context state) written_annotation
              in
              if not (State.unify state element annotated) then
                ignore
                  (Failures.add_mismatch_diagnostic state (Written written_annotation.id)
                     ~sides:[ (element, annotated) ]
                     (Loop_element
                        {
                          element = State.make_shown state element;
                          annotated = State.make_shown state annotated;
                        }))
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
            ~accepts_tuple_pattern:(Option.is_none annotation) ~mode:variable_mode);
      List.iter
        (check_loop_clause state
           { env with loop_element = Option.map (State.resolve state) !loop_element })
        clauses;
      check_loop_body state env body
  | While { condition = test; clauses; body } ->
      State.reject_in_formula state env (Written written.id) While_statement;
      Solver.run_in_statement state env (Written test.id) (fun () ->
          Hooks.check state env test Types.bool);
      List.iter (check_loop_clause state env) clauses;
      check_loop_body state env body
  | Parallel body | Concurrent body ->
      let concurrent = match written.kind with Concurrent _ -> true | _ -> false in
      State.reject_in_formula state env (Written written.id)
        (if concurrent then Concurrent_block else Parallel_block);
      List.iter
        (fun (branch : Syntax.statement) ->
          Solver.run_in_statement state env (Written branch.id) (fun () ->
              check_statement state env branch ~last:false))
        body.statements
  | Proof body -> check_loop_body state { env with specification = true } body
  | Assert { value; by = Some Evaluation } ->
      Hooks.check state
        {
          env with
          specification = false;
          compile_time = true;
          in_quantifier = false;
          loop_element = None;
          output = None;
        }
        value Types.bool;
      Constant.check state Evaluated_condition value
  | Assert { value; by = Some Bit_vector | None } -> Hooks.check state env value Types.bool
  | Statement_error -> ()

and assigns_through_index state env (written : Syntax.statement) (target : Syntax.expression)
    (value : Syntax.expression) =
  match (target.kind, state.resolved.brackets.(target.id)) with
  | Bracket (_, [ Item { kind = Range _; _ } ]), _ -> false
  | Bracket (base, [ Item key ]), (Some Index | None) -> (
      let base_type = Conversions.read_checked_head state env base in
      let { Well_known.owner; name; receiver } = Well_known.locate_method Index_assign_assign in
      let trait = make_trait owner in
      match
        ( State.find_evidence state base_type trait,
          Interface.Definition.find_trait_method state.lookups.interface trait.trait ~name ~receiver
        )
      with
      | Some (Interface.Impls.Evidence (Impl _ | Bound)), Some _ ->
          let index = make_trait Index in
          let make_parameter parameter_name type_ : Types.parameter_info =
            { name = parameter_name; mode = Own; type_; has_default = false }
          in
          Modes.mutate state env ~by:Assignment base;
          ignore
            (Calls.check_argument state env key
               (make_parameter "key"
                  (Solver.resolve_associated_type state base_type index Index_key
                     ~at:(Written key.id)))
               ~has_generic_type:false);
          ignore
            (Calls.check_argument state env value
               (make_parameter "value"
                  (Solver.resolve_associated_type state base_type index Index_output
                     ~at:(Written value.id)))
               ~has_generic_type:false);
          State.elaborate state written.id
            (Call
               (Tables.make_method_call trait Index_assign_assign ~self_type:base_type
                  ~result:Types.unit
                  [ (base, Mut); (key, Own); (value, Own) ]));
          Solver.require state (Method_call (Written written.id)) base_type trait;
          true
      | _ -> false)
  | _ -> false

and check_loop_body state env (body : Syntax.block) =
  List.iter
    (fun (written : Syntax.statement) ->
      Solver.run_in_statement state env (Written written.id) (fun () ->
          check_statement state env written ~last:false))
    body.statements

and check_loop_clause state env (clause : Syntax.loop_clause) =
  Clauses.check_under_condition state ~id:clause.id clause.condition (fun () ->
      match clause.kind with
      | Invariant value -> Clauses.check_condition state env value
      | Loop_decreases measures -> Clauses.check_measures state env measures
      | Loop_cost cost -> Clauses.check_cost state env cost)

and record_loop (state : State.state) (written : Syntax.statement) (loop : Tables.loop) =
  State.elaborate state written.id (Loop loop);
  match loop with
  | Pulled pulled ->
      State.check_when_final state (fun () ->
          State.elaborate state written.id
            (Loop (Pulled { pulled with remaining = find_remaining_call state pulled.cursor })))
  | Integer_range _ | Elements _ -> ()

and find_remaining_call state cursor =
  let finite_cursor = make_trait Finite_cursor in
  let call =
    Tables.make_method_call finite_cursor Finite_cursor_remaining ~self_type:cursor
      ~result:(Types.make_builtin UInt64) []
  in
  let is_on_a_parameter (bound : Types.bound_condition) =
    match bound.subject with Types.Parameter _ -> true | _ -> false
  in
  match State.find_evidence state cursor finite_cursor with
  | Some _ -> Some ([], call)
  | None -> (
      match State.reduce_condition state [ { subject = cursor; bound = finite_cursor } ] with
      | Some (_ :: _ as condition) when List.for_all is_on_a_parameter condition ->
          Some (condition, call)
      | Some _ | None -> None)

and check_loop_iterable state env (written : Syntax.statement) ~mode (iterable : Syntax.expression)
    =
  match iterable.kind with
  | Range { start = Some _; stop = Some _; inclusive; _ } -> (
      let range_type = State.normalize state (Hooks.check_expression state env iterable) in
      match range_type with
      | Types.Named { arguments = [ Types.Type element ]; _ } ->
          record_integer_range state ~loop:written.id ~owner:Range_of_loop ~admits_integer:false
            iterable element ~inclusive;
          (element, mode)
      | _ -> State.raise_bug "a range is not of the range type")
  | _ -> (
      let at : Core.origin = Written iterable.id in
      let type_ = Conversions.read_checked_head state env iterable in
      match type_ with
      | Types.Error _ | Types.Hole -> (type_, mode)
      | _ -> (
          let cause : State.cause = Loop at and cursor = make_trait Cursor in
          let by_mode =
            match mode with
            | Language.Mode.Read | Mut -> find_elements_loop state ~cause ~at type_ mode
            | Own -> find_consuming_loop state ~cause ~at type_
          in
          match by_mode with
          | Some (loop, element, lends) ->
              record_loop state written loop;
              (element, lends)
          | None when require_if_implemented state ~cause type_ cursor ->
              record_loop state written
                (Pulled { cursor = type_; cursor_call = None; remaining = None });
              (Solver.resolve_associated_type state type_ cursor Cursor_element ~at, Own)
          | None ->
              ( State.make_error_type state
                  (Not_iterable_loop { at; mode; type_ = State.make_shown state type_ }),
                mode )))

and find_elements_loop state ~cause ~at type_ (lends : Language.Mode.t) =
  let iterable = make_trait Iterable in
  let lending_method =
    match (Types.find_sequence_element type_, lends) with
    | Some _, _ -> None
    | None, Mut -> Some (make_trait Iterable_mut, Well_known.Iterable_mut_element)
    | None, (Read | Own) -> Some (iterable, Iterable_element)
  in
  let required = match lending_method with Some (trait, _) -> trait | None -> iterable in
  if require_if_implemented state ~cause type_ required then
    let element = Solver.resolve_associated_type state type_ iterable Iterable_element_type ~at in
    Some
      ( Tables.Elements
          {
            count =
              Tables.make_method_call iterable Iterable_count ~self_type:type_
                ~result:(Types.make_builtin UInt64) [];
            element =
              (match lending_method with
              | None -> Sequence_element
              | Some (trait, method_) ->
                  Lent_by_call
                    (Tables.make_method_call ~lends trait method_ ~self_type:type_ ~result:element
                       []));
            lends;
          },
        element,
        lends )
  else None

and find_consuming_loop state ~cause ~at type_ =
  let into_cursor = make_trait Into_cursor and cursor_trait = make_trait Cursor in
  if require_if_implemented state ~cause type_ into_cursor then
    let cursor =
      Solver.resolve_associated_type state type_ into_cursor Into_cursor_cursor_type ~at
    in
    Some
      ( Tables.Pulled
          {
            cursor;
            cursor_call =
              Some
                (Tables.make_method_call into_cursor Into_cursor_cursor ~self_type:type_
                   ~result:cursor []);
            remaining = None;
          },
        (match State.find_evidence state cursor cursor_trait with
        | Some _ -> Solver.resolve_associated_type state cursor cursor_trait Cursor_element ~at
        | None -> State.make_error_type state (Cursor_not_cursor { at; type_; cursor })),
        Language.Mode.Own )
  else None

and require_if_implemented state ~cause type_ trait =
  match State.find_evidence state type_ trait with
  | Some _ ->
      Solver.require state cause type_ trait;
      true
  | None -> false
