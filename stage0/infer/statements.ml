(* Blocks and statements: [let], assignment, loops and what drives them,
   and what a block's value is. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
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

and statement_never state (written : statement) =
  match written.kind with
  | Expression value -> (
      match state.tables.types.(value.id) with
      | Some type_ -> resolve state type_ = T.Never
      | None -> false)
  | While { condition = { kind = True; _ }; body; _ } -> not (contains_break body)
  | _ -> false

and contains_break (written : block) =
  let found = ref false in
  let rec statement (written : statement) =
    match written.kind with
    | For _ | While _ -> ()
    | _ -> Syntax_walk.statement_parts ~expression ~statement written
  and expression (value : expression) =
    match value.kind with
    | Break -> found := true
    | Lambda _ -> ()
    | _ -> Syntax_walk.expression_parts ~expression ~statement value
  in
  List.iter statement written.statements;
  !found

(* A statement. A statement that is not the last of its block must have
   type [Unit] or [Never]: any other value is unused. *)
and statement state env (written : statement) ~last : unit =
  match written.kind with
  | Expression value ->
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
      binding_pattern state env written_pattern type_ ~mutable_ ~mode
  | Assignment { target = written_target; operator; value } -> (
      let target_type = expression state env written_target in
      check_assignable state env written_target;
      mutable_place state written_target;
      match operator with
      | Assign -> check state env value target_type
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
          let element = loop_iterable state env written ~mode inner in
          loop_element := Some element;
          (if inner != iterable then
             match state.tables.types.(inner.id) with
             | Some type_ -> record state iterable type_
             | None -> ());
          binding_pattern state env written_pattern element ~mutable_:false ~mode);
      List.iter
        (loop_clause state { env with loop_element = Option.map (resolve state) !loop_element })
        clauses;
      loop_body state env body
  | While { condition = test; clauses; body } ->
      in_statement state env test.span (fun () -> check state env test T.bool);
      List.iter (loop_clause state env) clauses;
      loop_body state env body
  | Parallel body ->
      List.iter
        (fun (branch : statement) ->
          in_statement state env branch.span (fun () -> statement state env branch ~last:false))
        body.statements
  | Proof body -> loop_body state { env with specification = true } body
  | Assert value -> check state env value T.bool
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
          coerce state inner ~found ~expected:element
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
  | Loop_cost { bound = Big_o value | At_most value | Exactly value; _ } ->
      ignore (expression state env value)
  | Loop_cost { bound = Finite; _ } -> ()

(* What a [for] loop drives: a range of built-in integers, a call to a
   [yields] method, a cursor, or the [each] method of the loop's mode. *)
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
          element
      | _ -> bug "a range is not of the range type")
  | _ -> (
      let type_ = normalize state (expression state env iterable) in
      let call =
        Option.bind (called iterable) (fun (inner : expression) -> state.tables.calls.(inner.id))
      in
      match (type_, call) with
      | T.Cursor _, Some call ->
          (* A call to a [yields] method drives the loop directly, with its
             mark, as in [for x in mut items.each()]. What the call gives is
             what it yields. *)
          state.tables.loops.(written.id) <- Some (Yielding { call; mode });
          call.result
      | T.Error _, _ | T.Hole, _ -> type_
      | _ -> (
          match each_call state type_ mode with
          | Some (call, element) ->
              state.tables.loops.(written.id) <- Some (Yielding { call; mode });
              element
          | None -> (
              let cursor = trait_reference (core "Cursor") in
              match implements state type_ cursor with
              | Some _ ->
                  state.tables.loops.(written.id) <- Some (Pulled { cursor = type_ });
                  associated state type_ cursor "Element" ~at:iterable.span
              | None ->
                  error state Not_indexable iterable.span
                    (Printf.sprintf
                       "`%s` has no `each` that takes %s, so a `for` loop cannot go over it this \
                        way."
                       (T.show type_)
                       (match mode with
                       | T.Read -> "`self`"
                       | Mut -> "`mut self`"
                       | Own -> "`own self`")))))

(* An assignment's left side must be a place that may change. *)
and check_assignable state env (written : expression) =
  let rec root (value : expression) =
    match value.kind with
    | Name path -> (
        match target state path.last with
        | Some (Local id) -> (
            let captured =
              match (state.lambdas, Hashtbl.find_opt state.binding_spans id) with
              | (lambda : span) :: _, Some (binding : span) ->
                  binding.start < lambda.start || binding.start >= lambda.stop
              | _ -> false
            in
            match Hashtbl.find_opt state.locals id with
            | _ when captured -> `Captured path.last.text
            | Some local ->
                if local.mutable_ || local.mode = Mut then `Ok else `Fixed path.last.text
            | None -> `Ok)
        | Some (Definition _) -> `Fixed path.last.text
        | _ -> `Ok)
    | Self_value -> if env.self_mode = T.Mut then `Ok else `Fixed "self"
    | Member (base, _) -> root base
    | Bracket (base, _) -> root base
    | Parenthesized inner -> root inner
    | Mode (Mut, inner) when Option.is_some (marked_call state inner) -> root inner
    | Call _ -> (
        (* A part that is lent [mut] may change; one lent read-only may not. *)
        match lent state value with
        | Some T.Mut -> `Ok
        | Some _ -> `Lent
        | None -> `Not_a_place)
    | _ -> `Not_a_place
  in
  match root written with
  | `Ok -> ()
  | `Captured name ->
      report state Not_assignable written.span
        (Printf.sprintf
           "A lambda cannot change what it captures, and `%s` is from outside it. Return the new \
            value instead, or use a loop."
           name)
  | `Fixed name ->
      report state Not_assignable written.span
        (Printf.sprintf
           "`%s` cannot change here: only a `var`, a `mut` parameter, or `mut self`, and their \
            parts, can be assigned."
           name)
  | `Lent ->
      report state Not_assignable written.span
        ~fixes:[ fix "Mark it `mut`." [ insert written.span.start "mut " ] ]
        "This part is lent read-only, so it cannot change. Mark the place it is lent from \
         `mut`, so that it is lent `mut`."
  | `Not_a_place ->
      report state Not_assignable written.span
        "Only a place, such as a variable, a field, or an element, can be assigned."
