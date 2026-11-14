(* Checks blocks and statements: [let], assignment, loops and their
   iterations, and the value of a block. *)

open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower
open State
open Modes
open Hooks
open Lookups
open Pattern_typing
open Operators

(* An assertion [by bit_vector] is decided over fixed-width bits, so each
   variable it names is an integer or a boolean. *)
let bit_vector_names state (value : Core.expression) =
  let spans = Syntax_walk.spans state.definition in
  Core_walk.expression
    (Core_walk.deep
       {
         Core_walk.ignore_all with
         place =
           (function
           | Local { type_; origin; _ }
             when not (Types.is_builtin Bool type_ || Types.integer_range type_ <> None) ->
               report state Not_bit_vector spans.(origin)
                 (Printf.sprintf
                    "An assertion `by bit_vector` can name only integers and booleans, and this is \
                     a `%s`."
                    (Types.show type_))
           | _ -> ());
       })
    value

(* A block used as a value. Its last expression is checked against the
   expected type of the block, as part of the enclosing statement. *)
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
        ignore (in_statement state env first.span (fun () -> statement state env first ~last:false));
        statements_value rest
  in
  statements_value written.statements

(* Checks a statement. A statement that is not the last of its block must
   have type [Unit] or [Never]: a value of any other type would be unused. *)
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
                  report state Unused_value value.span
                    ~fixes:[ fix "Discard it on purpose." [ insert value.span.start "let _ = " ] ]
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
        reject_in_formula state env written.span "A `var`";
        check_owned state env value type_
      end;
      (match else_ with
      | Some block -> (
          let else_type = block_value state env block in
          match resolve state else_type with
          | Types.Never -> ()
          | _ ->
              report state Mismatch block.span
                "The `else` of a `let` must leave the block, with `return`, `break`, `continue`, \
                 or `unreachable`.")
      | None -> ());
      let mode =
        if is_var then Types.Own else if borrowed state value then Types.Read else Types.Own
      in
      register_statement state written (fun () ->
          let value = Form.operand mode (build_expression state value) in
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
      | _ -> (
          let right_type = expression state env ~expected:target_type value in
          literal_operands state ~left:target_type ~right:right_type;
          let binary_operator : binary =
            match operator with
            | Add_assign -> Add
            | Subtract_assign -> Subtract
            | Multiply_assign -> Multiply
            | Divide_assign -> Divide
            | Remainder_assign -> Remainder
            | Bit_and_assign -> Bit_and
            | Bit_or_assign -> Bit_or
            | Bit_xor_assign -> Bit_xor
            | Shift_left_assign -> Shift_left
            | Shift_right_assign -> Shift_right
            | Assign -> Add
          in
          register_statement state written (fun () ->
              Form.compound_assign state written written_target value binary_operator);
          match binary_operator with
          | Add | Subtract | Multiply | Divide | Remainder ->
              let trait, method_ =
                match binary_operator with
                | Add -> (Well_known.path Add, "add")
                | Subtract -> (Well_known.path Subtract, "subtract")
                | Multiply -> (Well_known.path Multiply, "multiply")
                | Divide -> (Well_known.path Divide, "divide")
                | _ -> (Well_known.path Remainder, "remainder")
              in
              let fake : expression =
                { kind = Expression_error; span = written.span; id = written.id }
              in
              let result =
                operator_call
                  ~operands:
                    [
                      {
                        Tables.expression = written_target.id;
                        parameter_index = 0;
                        mode = Types.Read;
                        mark = None;
                      };
                      {
                        Tables.expression = value.id;
                        parameter_index = 1;
                        mode = Types.Read;
                        mark = None;
                      };
                    ]
                  state fake ~trait ~method_ ~left:target_type ~right:(Some right_type)
              in
              if not (unify state result target_type) then
                mismatch state value.span ~expected:target_type ~actual:result
          | Shift_left | Shift_right ->
              (match resolve state right_type with
              | Types.Literal (Integer_literal, _) ->
                  ignore (unify state right_type (Types.builtin USize))
              | _ -> ());
              defer state (fun () ->
                  match (normalize state target_type, normalize state right_type) with
                  | (Types.Literal _ | Types.Variable _), _ | _, (Types.Literal _ | Types.Variable _)
                    ->
                      false
                  | left, right ->
                      if not (integer_type state left || Types.is_error left) then
                        report state No_impl written_target.span
                          (Printf.sprintf "Shifts work on built-in integers, not `%s`."
                             (Types.show left));
                      if
                        not
                          ((integer_type state right && not (signed_type state right))
                          || Types.is_error right)
                      then
                        report state Mismatch value.span
                          (Printf.sprintf "A shift amount is an unsigned integer, not `%s`."
                             (Types.show right));
                      true)
          | _ ->
              if not (unify state target_type right_type) then
                mismatch state value.span ~expected:target_type ~actual:right_type;
              defer state (fun () ->
                  match normalize state target_type with
                  | Types.Literal _ | Types.Variable _ -> false
                  | resolved ->
                      if not (integer_type state resolved || Types.is_error resolved) then
                        report state No_impl written_target.span
                          (Printf.sprintf "Bitwise operators work on built-in integers, not `%s`."
                             (Types.show resolved));
                      true)))
  | For { mode = running; pattern = written_pattern; annotation; iterable; clauses; body } ->
      reject_in_formula state env written.span "A `for` loop";
      let mode, inner =
        match iterable.kind with
        | Mode (Mut, inner) when Option.is_none (marked_call state inner) -> (Types.Mut, inner)
        | Mode (Own, inner) when Option.is_none (marked_call state inner) -> (Types.Own, inner)
        | _ -> (Types.Read, iterable)
      in
      (* The types in the loop's header are inferred before the body is
         checked, so the type of the loop variable depends only on the
         header. *)
      let loop_element = ref None in
      in_statement state env iterable.span (fun () ->
          let element, variable_mode = loop_iterable state env written ~mode inner in
          (* The annotation is the element type. The header's statement is
             not settled yet, so in [for index: UInt8 in 0..10] it decides
             the literals of the range. *)
          (match annotation with
          | Some written_annotation ->
              let annotated = Lower.type_ state.context written_annotation in
              if not (unify state element annotated) then
                ignore
                  (reported_mismatch state Mismatch written_annotation.span
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
          if mode = Types.Mut then mutate state env ~by:Mut_mark inner;
          binding_pattern state env written_pattern element ~is_var:false ~mode:variable_mode);
      List.iter
        (loop_clause state { env with loop_element = Option.map (resolve state) !loop_element })
        clauses;
      register_statement state written (fun () ->
          let pattern = build_pattern state written_pattern in
          let clauses = List.map (Form.loop_clause state) clauses in
          Form.for_loop state written inner ~pattern ~clauses ~body:(build_block state body)
            ~mode:
              (match running with
              | Sequential -> Sequential
              | Parallel_loop -> Parallel_loop
              | Concurrent_loop -> Concurrent_loop));
      loop_body state env body
  | While { condition = test; clauses; body } ->
      reject_in_formula state env written.span "A `while` loop";
      in_statement state env test.span (fun () -> check state env test Types.bool);
      List.iter (loop_clause state env) clauses;
      register_statement state written (fun () ->
          let condition = build_expression state test in
          let clauses = List.map (Form.loop_clause state) clauses in
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
      reject_in_formula state env written.span
        (if concurrent then "A `concurrent` block" else "A `parallel` block");
      register_statement state written (fun () ->
          let branches = List.map (build_statement state) body.statements in
          if concurrent then Concurrent branches else Parallel branches);
      List.iter
        (fun (branch : statement) ->
          in_statement state env branch.span (fun () -> statement state env branch ~last:false))
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

(* [collection[key] = value], where the collection's type implements
   [IndexAssign], is a call of its [assign]. The collection keeps the key
   and the value, so a key that is absent is added. Returns false for any
   other assignment, which assigns to the place that the target denotes. *)
and assigns_through_index state env (written : statement) (target : expression) (value : expression)
    =
  match (target.kind, state.resolved.brackets.(target.id)) with
  | Bracket (_, [ Item { kind = Range _; _ } ]), _ -> false
  | Bracket (base, [ Item key ]), (Some Index | None) -> (
      let base_type = normalize state (expression state env base) in
      let trait = trait_reference (Well_known.path Index_assign) in
      match
        ( implements state base_type trait,
          Members.trait_method state.database trait.trait "assign" Mut )
      with
      | Some ((Impls.From_impl _ | From_bound | From_any) as evidence_source), Some method_ ->
          let index = trait_reference (Well_known.path Index) in
          let parameter name type_ : Types.parameter_info =
            { name; mode = Own; type_; has_default = false }
          in
          mutate state env ~by:Assignment base;
          ignore
            (Calls.check_argument state env key
               (parameter "key" (associated state base_type index "Key" ~at:key.span)));
          ignore
            (Calls.check_argument state env value
               (parameter "value" (associated state base_type index "Output" ~at:value.span)));
          (* The call is recorded for the statement, which has no
             expression of its own to record it for. *)
          let call : expression =
            { kind = Expression_error; span = written.span; id = written.id }
          in
          record state call Types.unit;
          let argument (argument_expression : expression) position mode : Tables.argument =
            { expression = argument_expression.id; parameter_index = position; mode; mark = None }
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
                uses = method_.method_signature.uses;
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
      in_statement state env written.span (fun () -> statement state env written ~last:false))
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

(* Checks the iterable of a [for] loop: a range of built-in integers, a
   cursor, or a collection, whose elements the loop visits by position or,
   for a loop that consumes it, pulls from its cursor. Returns the type of
   the loop variable and its mode. *)
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
                  report state Not_indexable iterable.span
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
            if mode = Types.Own then None else elements_calls state iterable.span type_ mode
          and consumed =
            if mode = Types.Own then consuming_cursor state iterable.span type_ else None
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
                       made_by = None;
                       remaining = remaining_call state iterable.span type_;
                     });
              (* A pull gives the loop each value owned. *)
              (associated state type_ cursor "Element" ~at:iterable.span, Types.Own)
          | None, None, None ->
              ( error state Not_indexable iterable.span
                  (match mode with
                  | Types.Read ->
                      Printf.sprintf
                        "A `for` loop cannot go over `%s`: it is not a `Cursor`, and it has no \
                         `count` and `element` to visit it by position."
                        (Types.show type_)
                  | Mut ->
                      Printf.sprintf
                        "A `for` loop cannot change the elements of `%s`: it has no `element` that \
                         takes `mut self`."
                        (Types.show type_)
                  | Own ->
                      Printf.sprintf
                        "A `for` loop cannot consume `%s`: it has no `cursor` that takes `own \
                         self`."
                        (Types.show type_)),
                mode )))
