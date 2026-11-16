open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower
open State
open Modes
open Hooks
open Name_lookup
open Pattern_typing
open Operators

let bit_vector_names state (value : Core.expression) =
  Core_walk.expression
    (Core_walk.deep
       {
         Core_walk.ignore_all with
         place =
           (function
           | Local { type_; origin; _ }
             when not (Types.is_builtin Bool type_ || Types.integer_range type_ <> None) ->
               report state Not_bit_vector (read_span state origin)
                 (Printf.sprintf
                    "An assertion `by bit_vector` can name only integers and booleans, and this is \
                     a `%s`."
                    (Types.show type_))
           | _ -> ());
       })
    value

let rec block_value state env ?expected (written : block) =
  let rec statements_value = function
    | [] -> Types.unit
    | [ (last : statement) ] -> (
        match last.kind with
        | Expression value -> expression state env ?expected value
        | _ ->
            ignore (statement state env last ~last:true);
            if statement_diverges state last then Types.Never else Types.unit)
    | (first : statement) :: rest ->
        ignore
          (in_statement state env (read_span state first.id) (fun () ->
               statement state env first ~last:false));
        statements_value rest
  in
  statements_value written.statements

and statement state env (written : statement) ~last : unit =
  match written.kind with
  | Expression value ->
      register_statement state written (fun () -> Evaluate (build_expression state value));
      let type_ = expression state env value in
      if not last then
        defer state (fun () ->
            match normalize state type_ with
            | Types.Variable _ | Types.Literal _ -> false
            | resolved ->
                if
                  not
                    (resolved = Types.unit || resolved = Types.Never || Types.is_error resolved
                   || resolved = Types.Hole)
                then
                  report state Unused_value (read_span state value.id)
                    ~fixes:
                      [
                        fix "Discard it on purpose."
                          [ insert (read_span state value.id).start "let _ = " ];
                      ]
                    (Printf.sprintf
                       "This value of type `%s` is not used. Use it, or discard it with `let _ =`."
                       (Types.show resolved));
                true)
  | Let { is_var; pattern = written_pattern; annotation; value; else_ } ->
      let type_ =
        match annotation with
        | Some annotation ->
            let annotated = Lower.type_ state.context annotation in
            check state env value annotated;
            annotated
        | None -> expression state env value
      in
      if is_var then begin
        reject_in_formula state env (read_span state written.id) "A `var`";
        check_owned state env value type_
      end;
      (match else_ with
      | Some block -> (
          let else_type = block_value state env block in
          match resolve state else_type with
          | Types.Never -> ()
          | _ ->
              report state Mismatch (read_span state block.id)
                "The `else` of a `let` must leave the block, with `return`, `break`, `continue`, \
                 or `unreachable`.")
      | None -> ());
      let mode =
        if is_var then Types.Own else if borrowed state value then Types.Read else Types.Own
      in
      register_statement state written (fun () ->
          let value = Form.build_operand mode (build_expression state value) in
          let pattern = build_pattern state written_pattern in
          Let { pattern; value; else_ = Option.map (build_block state) else_ });
      (match (annotation, written_pattern.kind) with
      | None, Binding name -> Hashtbl.replace state.annotatable name.id ()
      | _ -> ());
      binding_pattern state env written_pattern type_ ~is_var ~mode
  | Assignment { target; operator = Assign; value }
    when assigns_through_index state env written target value ->
      ()
  | Assignment { target = written_target; operator; value } -> (
      let target_type = expression state env written_target in
      mutate state env ~by:Assignment written_target;
      match operator with
      | Assign ->
          register_statement state written (fun () ->
              let target = place_of (build_expression state written_target) in
              Assign { target; value = build_expression state value });
          check state env value target_type;
          check_owned state env value target_type
      | Compound operation -> (
          let right_type = expression state env ~expected:target_type value in
          literal_operands state ~left:target_type ~right:right_type;
          register_statement state written (fun () ->
              Form.build_compound_assign state written written_target value operation);
          match operation with
          | Arithmetic arithmetic ->
              let trait, method_ = select_arithmetic_trait arithmetic in
              let call_site : expression = { kind = Expression_error; id = written.id } in
              let result =
                operator_call
                  ~operands:
                    [
                      {
                        Tables.expression = written_target.id;
                        core_argument_index = 0;
                        mode = Types.Read;
                        mode_keyword = None;
                      };
                      {
                        Tables.expression = value.id;
                        core_argument_index = 1;
                        mode = Types.Read;
                        mode_keyword = None;
                      };
                    ]
                  state call_site ~trait ~method_ ~left:target_type ~right:(Some right_type)
              in
              if not (unify state result target_type) then
                mismatch state (read_span state value.id) ~expected:target_type ~actual:result
          | Shift _ ->
              check_shift_operands state
                ~left:(read_span state written_target.id, target_type)
                ~right:(read_span state value.id, right_type)
          | Bitwise _ ->
              if not (unify state target_type right_type) then
                mismatch state (read_span state value.id) ~expected:target_type ~actual:right_type;
              check_bitwise_operand state (read_span state written_target.id) target_type))
  | For { mode = running; pattern = written_pattern; annotation; iterable; clauses; body } ->
      reject_in_formula state env (read_span state written.id) "A `for` loop";
      let mode, inner =
        match iterable.kind with
        | Mode (Mut, inner) when Option.is_none (call_with_mode_keyword state inner) ->
            (Types.Mut, inner)
        | Mode (Own, inner) when Option.is_none (call_with_mode_keyword state inner) ->
            (Types.Own, inner)
        | _ -> (Types.Read, iterable)
      in
      let loop_element = ref None in
      in_statement state env (read_span state iterable.id) (fun () ->
          let element, variable_mode = loop_iterable state env written ~mode inner in
          (match annotation with
          | Some written_annotation ->
              let annotated = Lower.type_ state.context written_annotation in
              if not (unify state element annotated) then
                ignore
                  (reported_mismatch state Mismatch
                     (read_span state written_annotation.id)
                     ~sides:[ (element, annotated) ]
                     (Printf.sprintf "The elements of this loop are `%s`, not `%s`."
                        (show state element) (show state annotated)))
          | None -> (
              match written_pattern.kind with
              | Binding name -> Hashtbl.replace state.annotatable name.id ()
              | _ -> ()));
          loop_element := Some element;
          (if inner != iterable then
             match state.tables.types.(inner.id) with
             | Some type_ -> record state iterable type_
             | None -> ());
          if mode = Types.Mut then mutate state env ~by:Passed_mut inner;
          binding_pattern state env written_pattern element ~is_var:false ~mode:variable_mode);
      List.iter
        (loop_clause state { env with loop_element = Option.map (resolve state) !loop_element })
        clauses;
      register_statement state written (fun () ->
          let pattern = build_pattern state written_pattern in
          let clauses = List.map (Form.build_loop_clause state) clauses in
          Form.build_for_loop state written inner ~pattern ~clauses ~body:(build_block state body)
            ~mode:
              (match running with
              | Sequential -> Sequential
              | Parallel_loop -> Parallel_loop
              | Concurrent_loop -> Concurrent_loop));
      loop_body state env body
  | While { condition = test; clauses; body } ->
      reject_in_formula state env (read_span state written.id) "A `while` loop";
      in_statement state env (read_span state test.id) (fun () -> check state env test Types.bool);
      List.iter (loop_clause state env) clauses;
      register_statement state written (fun () ->
          let condition = build_expression state test in
          let clauses = List.map (Form.build_loop_clause state) clauses in
          While
            {
              condition;
              clauses;
              body = build_block state body;
              binds_lent_part = Form.binds_lent_part state condition;
            });
      loop_body state env body
  | Parallel body | Concurrent body ->
      let concurrent = match written.kind with Concurrent _ -> true | _ -> false in
      reject_in_formula state env (read_span state written.id)
        (if concurrent then "A `concurrent` block" else "A `parallel` block");
      register_statement state written (fun () ->
          let branches = List.map (build_statement state) body.statements in
          if concurrent then Concurrent branches else Parallel branches);
      List.iter
        (fun (branch : statement) ->
          in_statement state env (read_span state branch.id) (fun () ->
              statement state env branch ~last:false))
        body.statements
  | Proof body ->
      register_statement state written (fun () -> Proof (build_block state body));
      loop_body state { env with specification = true } body
  | Assert { value; by_bit_vector } ->
      register_statement state written (fun () ->
          let value = build_expression state value in
          if by_bit_vector then bit_vector_names state value;
          Assert
            { condition = { value; executable = Form.is_executable state value }; by_bit_vector });
      check state env value Types.bool
  | Statement_error -> ()

and assigns_through_index state env (written : statement) (target : expression) (value : expression)
    =
  match (target.kind, state.resolved.brackets.(target.id)) with
  | Bracket (_, [ Item { kind = Range _; _ } ]), _ -> false
  | Bracket (base, [ Item key ]), (Some Index | None) -> (
      let base_type = normalize state (expression state env base) in
      let trait = trait_reference (Well_known.path Index_assign) in
      match
        ( implements state base_type trait,
          Members.trait_method state.lookups trait.trait "assign" Mut )
      with
      | Some ((Impls.From_impl _ | From_bound | From_any) as evidence_source), Some method_ ->
          let index = trait_reference (Well_known.path Index) in
          let parameter name type_ : Types.parameter_info =
            { name; mode = Own; type_; has_default = false }
          in
          mutate state env ~by:Assignment base;
          ignore
            (Calls.check_argument state env key
               (parameter "key"
                  (associated state base_type index "Key" ~at:(read_span state key.id))));
          ignore
            (Calls.check_argument state env value
               (parameter "value"
                  (associated state base_type index "Output" ~at:(read_span state value.id))));
          let call : expression = { kind = Expression_error; id = written.id } in
          record state call Types.unit;
          let argument (argument_expression : expression) position mode : Tables.argument =
            {
              expression = argument_expression.id;
              core_argument_index = position;
              mode;
              mode_keyword = None;
            }
          in
          state.tables.calls.(written.id) <-
            Some
              {
                callee =
                  Trait_method
                    {
                      trait;
                      name = "assign";
                      receiver = Mut;
                      self_type = base_type;
                      type_arguments = [];
                      evidence = evidence_of evidence_source;
                    };
                arguments = [ argument base 0 Mut; argument key 1 Own; argument value 2 Own ];
                omitted_defaults = [];
                uses = (Members.method_signature state.lookups trait.trait method_).uses;
                callee_result = Types.unit;
              };
          Form.register_call state call;
          register_statement state written (fun () -> Evaluate (build_expression state call));
          true
      | _ -> false)
  | _ -> false

and loop_body state env (body : block) =
  List.iter
    (fun (written : statement) ->
      in_statement state env (read_span state written.id) (fun () ->
          statement state env written ~last:false))
    body.statements

and loop_clause state env (clause : loop_clause) =
  let env = { env with specification = true } in
  match clause.kind with
  | Invariant value -> check state env value Types.bool
  | Loop_decreases measures ->
      List.iter (fun measure -> ignore (expression state env measure)) measures
  | Loop_cost { resource; bound; _ } -> (
      check_resource state resource;
      match bound with
      | Big_o value | At_most value | Exactly value -> ignore (expression state env value)
      | Finite -> ())

and loop_iterable state env (written : statement) ~mode (iterable : expression) =
  match iterable.kind with
  | Range { start = Some _; stop = Some _; inclusive; _ } -> (
      let range_type = normalize state (expression state env iterable) in
      match range_type with
      | Types.Named { arguments = [ Types.Type element ]; _ } ->
          defer state (fun () ->
              let element = normalize state element in
              if Types.contains_unsolved element then false
              else begin
                if integer_type state element || Types.is_builtin Character element then
                  state.tables.loops.(written.id) <- Some (Integer_range { element; inclusive })
                else if not (Types.is_error element) then
                  report state Not_indexable (read_span state iterable.id)
                    (Printf.sprintf "A `for` loop's range is of integers, not `%s`."
                       (Types.show element));
                true
              end);
          (element, mode)
      | _ -> bug "a range is not of the range type")
  | _ -> (
      let type_ = normalize state (expression state env iterable) in
      match type_ with
      | Types.Error _ | Types.Hole -> (type_, mode)
      | _ -> (
          let cursor = trait_reference (Well_known.path Cursor) in
          let by_position =
            if mode = Types.Own then None
            else elements_calls state (read_span state iterable.id) type_ mode
          and consumed =
            if mode = Types.Own then consuming_cursor state (read_span state iterable.id) type_
            else None
          in
          match (by_position, consumed, implements state type_ cursor) with
          | Some (loop, element, lends), _, _ ->
              state.tables.loops.(written.id) <- Some loop;
              (element, lends)
          | None, Some (loop, element), _ ->
              state.tables.loops.(written.id) <- Some loop;
              (element, Types.Own)
          | None, None, Some _ ->
              state.tables.loops.(written.id) <-
                Some
                  (Pulled
                     {
                       cursor = type_;
                       cursor_call = None;
                       remaining = remaining_call state (read_span state iterable.id) type_;
                     });
              (associated state type_ cursor "Element" ~at:(read_span state iterable.id), Types.Own)
          | None, None, None ->
              ( error state Not_indexable (read_span state iterable.id)
                  (match mode with
                  | Types.Read ->
                      Printf.sprintf
                        "A `for` loop cannot go over `%s`: it is not a `Cursor`, and it has no \
                         `count` and `element` to visit it by position."
                        (Types.show type_)
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
