(* Blocks and statements: [let], assignment, loops and what drives them,
   and what a block's value is. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower
open State
open Hooks
open Lookups
open Pattern_typing
open Operators

(* A block used as a value: its last expression is checked against the
   block's expected type, in the enclosing statement. *)
let rec block_value state env ?expected (written : block) =
  let rec go = function
    | [] -> T.unit
    | [ (last : statement) ] -> (
        match last.kind with
        | Expression value -> expression state env ?expected value
        | _ ->
            ignore (statement state env last ~last:true);
            if statement_never state last then T.Never else T.unit)
    | (first : statement) :: rest ->
        ignore (in_statement state env first.span (fun () -> statement state env first ~last:false));
        go rest
  in
  go written.statements

(* A statement. A statement that is not the last of its block must have
   type [Unit] or [Never]: any other value is unused. *)
and statement state env (written : statement) ~last : unit =
  match written.kind with
  | Expression value ->
      register_statement state written (fun () -> Evaluate (build_expression state value));
      let type_ = expression state env value in
      if not last then
        defer state (fun () ->
            match normalize state type_ with
            | T.Variable _ | T.Literal _ -> false
            | resolved ->
                if
                  not
                    (resolved = T.unit || resolved = T.Never || T.is_error resolved
                   || resolved = T.Hole)
                then
                  report state Unused_value value.span
                    ~fixes:[ fix "Discard it on purpose." [ insert value.span.start "let _ = " ] ]
                    (Printf.sprintf
                       "This value of type `%s` is not used. Use it, or discard it with `let _ =`."
                       (T.show resolved));
                true)
  | Let { mutable_; pattern = written_pattern; annotation; value; else_ } ->
      let type_ =
        match annotation with
        | Some annotation ->
            let annotated = Lower.type_ state.context annotation in
            check state env value annotated;
            annotated
        | None -> expression state env value
      in
      (match else_ with
      | Some block -> (
          let else_type = block_value state env block in
          match resolve state else_type with
          | T.Never -> ()
          | _ ->
              report state Mismatch block.span
                "The `else` of a `let` must leave the block, with `return`, `break`, `continue`, \
                 or `unreachable`.")
      | None -> ());
      let mode = if mutable_ then T.Own else if borrowed state value then T.Read else T.Own in
      register_statement state written (fun () ->
          let value = Form.operand mode (build_expression state value) in
          let pattern = build_pattern state written_pattern in
          Let { pattern; value; else_ = Option.map (build_block state) else_ });
      binding_pattern state env written_pattern type_ ~mutable_ ~mode
  | Assignment { target = written_target; operator; value } -> (
      let target_type = expression state env written_target in
      mutate state env ~by:Assignment written_target;
      match operator with
      | Assign ->
          register_statement state written (fun () ->
              let target = place_of (build_expression state written_target) in
              Assign { target; value = build_expression state value });
          check state env value target_type
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
                | Add -> (core "Add", "add")
                | Subtract -> (core "Subtract", "subtract")
                | Multiply -> (core "Multiply", "multiply")
                | Divide -> (core "Divide", "divide")
                | _ -> (core "Remainder", "remainder")
              in
              let fake : expression =
                { kind = Expression_error; span = written.span; id = written.id }
              in
              let result =
                operator_call
                  ~operands:
                    [
                      {
                        C.expression = written_target.id;
                        parameter = 0;
                        mode = T.Read;
                        conversion = None;
                      };
                      { C.expression = value.id; parameter = 1; mode = T.Read; conversion = None };
                    ]
                  state fake ~trait ~method_ ~left:target_type ~right:(Some right_type)
              in
              if not (unify state result target_type) then
                mismatch state value.span ~expected:target_type ~found:result
          | Shift_left | Shift_right ->
              (match resolve state right_type with
              | T.Literal (Integer_literal, _) -> ignore (unify state right_type (T.builtin USize))
              | _ -> ());
              defer state (fun () ->
                  match (normalize state target_type, normalize state right_type) with
                  | (T.Literal _ | T.Variable _), _ | _, (T.Literal _ | T.Variable _) -> false
                  | left, right ->
                      if not (T.is_integer_type left || T.is_error left) then
                        report state No_impl written_target.span
                          (Printf.sprintf "Shifts work on built-in integers, not `%s`."
                             (T.show left));
                      if
                        not
                          ((T.is_integer_type right && not (T.is_signed right)) || T.is_error right)
                      then
                        report state Mismatch value.span
                          (Printf.sprintf "A shift amount is an unsigned integer, not `%s`."
                             (T.show right));
                      true)
          | _ ->
              if not (unify state target_type right_type) then
                mismatch state value.span ~expected:target_type ~found:right_type;
              defer state (fun () ->
                  match normalize state target_type with
                  | T.Literal _ | T.Variable _ -> false
                  | resolved ->
                      if not (T.is_integer_type resolved || T.is_error resolved) then
                        report state No_impl written_target.span
                          (Printf.sprintf "Bitwise operators work on built-in integers, not `%s`."
                             (T.show resolved));
                      true)))
  | For { pattern = written_pattern; iterable; clauses; body; _ } ->
      let mode, inner =
        match iterable.kind with
        | Mode (Mut, inner) when Option.is_none (marked_call state inner) -> (T.Mut, inner)
        | Mode (Own, inner) when Option.is_none (marked_call state inner) -> (T.Own, inner)
        | _ -> (T.Read, iterable)
      in
      (* The loop's header settles its own types before the body, so the
         loop variable's type comes from the header alone. *)
      let loop_element = ref None in
      in_statement state env iterable.span (fun () ->
          let element, variable_mode = loop_iterable state env written ~mode inner in
          loop_element := Some element;
          (if inner != iterable then
             match state.tables.types.(inner.id) with
             | Some type_ -> record state iterable type_
             | None -> ());
          if mode = T.Mut then mutate state env ~by:Mut_mark inner;
          binding_pattern state env written_pattern element ~mutable_:false ~mode:variable_mode);
      List.iter
        (loop_clause state { env with loop_element = Option.map (resolve state) !loop_element })
        clauses;
      register_statement state written (fun () ->
          let iteration = Form.iteration state written inner in
          let pattern = build_pattern state written_pattern in
          let clauses = List.map (Form.loop_clause state) clauses in
          For
            {
              pattern;
              iteration;
              clauses;
              body = build_block state body;
              parallel = (match written.kind with For { parallel; _ } -> parallel | _ -> false);
            });
      loop_body state env body
  | While { condition = test; clauses; body } ->
      in_statement state env test.span (fun () -> check state env test T.bool);
      List.iter (loop_clause state env) clauses;
      register_statement state written (fun () ->
          let condition = build_expression state test in
          let clauses = List.map (Form.loop_clause state) clauses in
          While { condition; clauses; body = build_block state body });
      loop_body state env body
  | Parallel body ->
      register_statement state written (fun () ->
          Parallel (List.map (build_statement state) body.statements));
      List.iter
        (fun (branch : statement) ->
          in_statement state env branch.span (fun () -> statement state env branch ~last:false))
        body.statements
  | Proof body ->
      register_statement state written (fun () -> Proof (build_block state body));
      loop_body state { env with specification = true } body
  | Assert value ->
      register_statement state written (fun () ->
          let value = build_expression state value in
          Assert { value; executable = Form.is_executable state value });
      check state env value T.bool
  | Yield value -> (
      match env.output with
      | Some (Yields (_, element) | Lends (_, element)) ->
          let inner =
            match value.kind with
            | Mode (_, inner) when Option.is_none (marked_call state inner) -> inner
            | _ -> value
          in
          let found = expression state env ~expected:element inner in
          if inner != value then record state value found;
          (* A part given out to change is reached through the [mut] version
             of each index on the way to it. *)
          (match env.output with
          | Some (Yields (Mut, _) | Lends (Mut, _)) -> mutate state env ~by:Mut_mark inner
          | _ -> ());
          register_statement state written (fun () ->
              let mode =
                match env.output with
                | Some (Yields (mode, _) | Lends (mode, _)) -> mode
                | _ -> T.Read
              in
              Yield { mode; part = Form.operand mode (build_expression state inner) });
          ignore (coerce state env inner ~found ~expected:element)
      | _ ->
          ignore (expression state env value);
          report state Wrong_yield written.span
            "Only a method whose signature `yields` or `lends` can `yield`.")
  | Statement_error -> ()

and loop_body state env (body : block) =
  List.iter
    (fun (written : statement) ->
      in_statement state env written.span (fun () -> statement state env written ~last:false))
    body.statements

and loop_clause state env (clause : loop_clause) =
  let env = { env with specification = true } in
  match clause.kind with
  | Invariant value -> check state env value T.bool
  | Loop_decreases measures ->
      List.iter (fun measure -> ignore (expression state env measure)) measures
  | Loop_cost { resource; bound } -> (
      check_resource state resource;
      match bound with
      | Big_o value | At_most value | Exactly value -> ignore (expression state env value)
      | Finite -> ())

(* What a [for] loop drives: a range of built-in integers, a call to a
   [yields] method, a cursor, or the [each] method of the loop's mode. *)
(* Checks the iterable of a [for] loop. Returns the type of the loop
   variable and its mode. *)
and loop_iterable state env (written : statement) ~mode (iterable : expression) =
  match iterable.kind with
  | Range { start = Some _; stop = Some _; inclusive; _ } -> (
      let range_type = normalize state (expression state env iterable) in
      match range_type with
      | T.Named { arguments = [ T.Type element ]; _ } ->
          defer state (fun () ->
              let element = normalize state element in
              if T.contains_unsolved element then false
              else begin
                if T.is_integer_type element || T.is_builtin Character element then
                  state.tables.loops.(written.id) <- Some (Integer_range { element; inclusive })
                else if not (T.is_error element) then
                  report state Not_indexable iterable.span
                    (Printf.sprintf "A `for` loop's range is of integers, not `%s`."
                       (T.show element));
                true
              end);
          (element, mode)
      | _ -> bug "a range is not of the range type")
  | _ -> (
      let type_ = normalize state (expression state env iterable) in
      let call =
        Option.bind (called iterable) (fun (inner : expression) -> state.tables.calls.(inner.id))
      in
      match (type_, call) with
      | T.Cursor { method_; _ }, Some call ->
          (* The iterable is a call of a yielding method, as in
             [for x in mut items.each()]. The loop iterates over that call.
             The loop variable has the mode that the method yields with. *)
          state.tables.loops.(written.id) <- Some (Yielding { call; mode });
          let yields =
            match function_signature state method_ with
            | Some (Ok { output = Yields (yields, _); _ }) -> yields
            | _ -> mode
          in
          (call.result, yields)
      | T.Error _, _ | T.Hole, _ -> (type_, mode)
      | _ -> (
          match each_call state iterable.span type_ mode with
          | Some (call, element) ->
              state.tables.loops.(written.id) <- Some (Yielding { call; mode });
              (element, mode)
          | None -> (
              let cursor = trait_reference (core "Cursor") in
              match implements state type_ cursor with
              | Some _ ->
                  state.tables.loops.(written.id) <- Some (Pulled { cursor = type_ });
                  (associated state type_ cursor "Element" ~at:iterable.span, mode)
              | None ->
                  ( error state Not_indexable iterable.span
                      (Printf.sprintf
                         "`%s` has no `each` that takes %s, so a `for` loop cannot go over it this \
                          way."
                         (T.show type_)
                         (Path.show_receiver
                            (match mode with T.Read -> Read | Mut -> Mut | Own -> Own))),
                    mode ))))
