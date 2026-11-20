let select_arithmetic_method : Syntax.arithmetic -> Well_known.method_ * Well_known.associated =
  function
  | Add -> (Add_add, Add_output)
  | Subtract -> (Subtract_subtract, Subtract_output)
  | Multiply -> (Multiply_multiply, Multiply_output)
  | Divide -> (Divide_divide, Divide_output)
  | Remainder -> (Remainder_remainder, Remainder_output)

let infer_integer_result state span type_ ~(describe : string -> string) =
  Solver.require_within state type_ Types.integer_types ~reason:(fun excluded ->
      State.add_diagnostic state No_impl span (describe (State.describe state excluded)))

let infer_bitwise_result state span type_ =
  infer_integer_result state span type_
    ~describe:(Printf.sprintf "Bitwise operators work on built-in integers, not %s.")

let infer_shift_result state ~left:(left_span, left_type) ~right:(right_span, right_type) =
  ignore
    (Solver.require_within state right_type Types.unsigned_integer_types ~reason:(fun excluded ->
         State.add_diagnostic state Mismatch right_span
           (Printf.sprintf "A shift amount is an unsigned integer, not %s."
              (State.describe state excluded))));
  infer_integer_result state left_span left_type
    ~describe:(Printf.sprintf "Shifts work on built-in integers, not %s.")

let is_integer_operand state (operand : Syntax.expression) type_ =
  State.is_within state
    (Conversions.read_actual_head state operand type_)
    (Types.integer_types @ [ Integer ])

let rec try_ state env (value : Syntax.expression) (inner : Syntax.expression) =
  State.reject_in_formula state env (State.read_span state value.id) "`?`";
  let inner_type = Conversions.read_checked_head state env inner in
  let output =
    match env.output with
    | Some (Returns output) -> Some (Conversions.read_expected_head state output)
    | _ -> None
  in
  match (inner_type, output) with
  | ( Types.Named { path; arguments = [ Types.Type ok; Types.Type error ] },
      Some (Types.Named { path = output_path; arguments = [ _; Types.Type output_error ] }) )
    when Well_known.is Result path && Well_known.is Result output_path ->
      if not (State.unify state error output_error) then
        State.report state Wrong_try (State.read_span state value.id)
          (Printf.sprintf
             "`?` returns the error unchanged, so it needs the function's error type `%s`, not \
              `%s`. Convert it first with `map_error`."
             (State.show state output_error) (State.show state error));
      ok
  | ( Types.Named { path; arguments = [ Types.Type some ] },
      Some (Types.Named { path = output_path; _ }) )
    when Well_known.is Option path && Well_known.is Option output_path ->
      some
  | (Types.Error _ | Types.Hole), _ -> inner_type
  | _ ->
      State.make_error_type state Wrong_try (State.read_span state value.id)
        "`?` works on a `Result` in a function that returns a `Result`, and on an `Option` in a \
         function that returns an `Option`. Convert between them with `ok_or` or `ok`."

and check_prefix state env ?expected (value : Syntax.expression) operator
    (inner : Syntax.expression) =
  match operator with
  | Syntax.Not ->
      Hooks.check state env inner Types.bool;
      Types.bool
  | Complement ->
      let type_ = Hooks.check_expression state env ?expected inner in
      infer_integer_result state (State.read_span state value.id) type_
        ~describe:(Printf.sprintf "`~` works on built-in integers, not %s.")
  | Negate -> (
      match inner.kind with
      | Integer number ->
          state.tables.literals.(inner.id) <- Some (Integer_value number);
          state.tables.literals.(value.id) <- Some (Integer_value (Z.neg number));
          let type_ =
            Pattern_typing.check_integer_literal state env ?expected value (Z.neg number)
          in
          State.record state inner type_;
          type_
      | _ -> (
          let type_ = Hooks.check_expression state env ?expected inner in
          let resolved = Conversions.read_actual_head state inner type_ in
          match
            if State.is_within state resolved Types.number_types then
              Solver.require_within state resolved
                (Types.signed_integer_types @ Types.float_types @ [ Integer ])
                ~reason:(Pattern_typing.report_negated_unsigned state value)
            else resolved
          with
          | Types.Hole -> Types.Hole
          | Types.Error _ as error when not (Types.is_error resolved) -> error
          | _ when env.specification && is_integer_operand state inner resolved -> Types.Integer
          | _ ->
              check_operator_call state value.id ~method_:Well_known.Negate_negate
                ~output:Well_known.Negate_output ~left:(inner, type_) ~right:None))

and check_operator_call state call ~method_ ~output ~left:((left : Syntax.expression), left_type)
    ~right =
  let { Well_known.owner; name; receiver } = Well_known.locate_method method_ in
  let reference =
    Types.make_trait_reference
      ~arguments:(List.map (fun (_, right_type) -> Types.Type right_type) (Option.to_list right))
      (Well_known.make_path owner)
  in
  let result = State.make_fresh_type state in
  let make_operand index expression =
    { Tables.expression; core_argument_index = index; mode = Language.Mode.Read }
  in
  state.tables.calls.(call) <-
    Some
      {
        callee =
          Trait_method
            {
              trait = reference;
              name;
              receiver;
              self_type = left_type;
              instantiation = Types.no_instantiation;
            };
        arguments =
          make_operand 0 left
          :: List.map (fun (right, _) -> make_operand 1 right) (Option.to_list right);
        omitted_defaults = [];
        callee_result = result;
      };
  Solver.require state
    (Operator
       {
         at = State.read_span state call;
         operands =
           Option.map
             (fun ((right : Syntax.expression), _) ->
               (State.read_span state left.id, State.read_span state right.id))
             right;
       })
    ~outputs:[ (Well_known.show_associated output, result) ]
    left_type reference;
  result

and check_literal_operands state ~left ~right =
  if State.is_within state left Types.number_types && State.is_within state right Types.number_types
  then ignore (State.unify state left right)

and is_hole state type_ = State.resolve state type_ = Types.Hole

and check_operands state env (left : Syntax.expression) (right : Syntax.expression) =
  let left_type = Hooks.check_expression state env left in
  let right_type = Hooks.check_expression state env ~expected:left_type right in
  if is_hole state left_type || is_hole state right_type then None else Some (left_type, right_type)

and is_string state (operand : Syntax.expression) type_ =
  let type_ = Conversions.read_actual_head state operand type_ in
  Types.is_well_known String type_ || Types.is_well_known String_slice type_

and check_binary state (env : State.env) ?expected (value : Syntax.expression) operator
    (left : Syntax.expression) (right : Syntax.expression) =
  match operator with
  | Syntax.Connective connective ->
      if connective = Implies && not env.specification then
        State.report state Specification_only (State.read_span state value.id)
          "`==>` is only for specifications and the bodies of functions for specifications only; \
           in code, write `!a || b`.";
      Hooks.check state env left Types.bool;
      Hooks.check state env right Types.bool;
      Types.bool
  | Operation (Bitwise _) ->
      let left_type = Hooks.check_expression state env ?expected left in
      let right_type = Hooks.check_expression state env ~expected:left_type right in
      check_literal_operands state ~left:left_type ~right:right_type;
      if not (State.unify state left_type right_type) then
        Failures.report_mismatch state (State.read_span state right.id) ~expected:left_type
          ~actual:right_type;
      infer_bitwise_result state (State.read_span state value.id) left_type
  | Operation (Shift _) ->
      let left_type = Hooks.check_expression state env ?expected left in
      let right_type = Hooks.check_expression state env right in
      infer_shift_result state
        ~left:(State.read_span state left.id, left_type)
        ~right:(State.read_span state right.id, right_type)
  | Comparison comparison -> (
      match check_operands state env left right with
      | None -> Types.bool
      | Some (left_type, right_type) ->
          check_literal_operands state ~left:left_type ~right:right_type;
          if
            env.specification
            && is_integer_operand state left left_type
            && is_integer_operand state right right_type
          then begin
            Types.bool
          end
          else begin
            let left_head = Conversions.read_actual_head state left left_type in
            let right_head = Conversions.read_actual_head state right right_type in
            let compared_type =
              match
                ( Conversions.find_view_as ~owned:right_head ~view:left_head,
                  Conversions.find_view_as ~owned:left_head ~view:right_head )
              with
              | Some _, _ ->
                  Conversions.coerce state env ~argument:Language.Mode.Read right ~actual:right_type
                    ~expected:left_type;
                  left_type
              | None, Some _ ->
                  Conversions.coerce state env ~argument:Language.Mode.Read left ~actual:left_type
                    ~expected:right_type;
                  right_type
              | None, None ->
                  if not (State.unify state left_type right_type) then
                    ignore
                      (Failures.add_operand_mismatch state ~at:(State.read_span state value.id)
                         ~left:(State.read_span state left.id, left_type)
                         ~right:(State.read_span state right.id, right_type));
                  left_type
            in
            let method_, result =
              match comparison with
              | Equal | Not_equal -> (Well_known.Equal_equal, Types.bool)
              | Less | Less_equal | Greater | Greater_equal ->
                  (Ordered_compare, Types.make_named (Well_known.make_path Ordering) [])
            in
            let { Well_known.owner; name; receiver } = Well_known.locate_method method_ in
            let trait = Well_known.make_path owner in
            state.tables.calls.(value.id) <-
              Some
                {
                  callee =
                    Trait_method
                      {
                        trait = Types.make_trait_reference ~arguments:[] trait;
                        name;
                        receiver;
                        self_type = compared_type;
                        instantiation = Types.no_instantiation;
                      };
                  arguments =
                    [
                      { expression = left; core_argument_index = 0; mode = Read };
                      { expression = right; core_argument_index = 1; mode = Read };
                    ];
                  omitted_defaults = [];
                  callee_result = result;
                };
            Solver.require state
              (Method_call (State.read_span state value.id))
              compared_type
              (Types.make_trait_reference ~arguments:[] trait);
            Types.bool
          end)
  | Operation (Arithmetic arithmetic) -> (
      match check_operands state env left right with
      | None -> Types.Hole
      | Some (left_type, right_type) ->
          check_literal_operands state ~left:left_type ~right:right_type;
          if arithmetic = Add && (is_string state left left_type || is_string state right right_type)
          then begin
            let spell_piece (side : Syntax.expression) =
              match side.kind with
              | String { tag = None; form = Ordinary; first; rest = []; _ } ->
                  Some (State.quote_span state (State.read_span state first.id))
              | String _ -> None
              | _ -> Some ("${" ^ State.quote_span state (State.read_span state side.id) ^ "}")
            in
            let fixes =
              match (spell_piece left, spell_piece right) with
              | Some left, Some right ->
                  [
                    State.fix "Join them with interpolation."
                      [
                        State.replace (State.read_span state value.id)
                          (Printf.sprintf "\"%s%s\"" left right);
                      ];
                  ]
              | _ -> []
            in
            State.make_error_type state String_addition (State.read_span state value.id) ~fixes
              "Strings have no `+`. Join them with interpolation, or with methods such as `push`."
          end
          else
            begin if
              env.specification
              && is_integer_operand state left left_type
              && is_integer_operand state right right_type
            then begin
              Types.Integer
            end
            else
              let method_, output = select_arithmetic_method arithmetic in
              check_operator_call state value.id ~method_ ~output ~left:(left, left_type)
                ~right:(Some (right, right_type))
            end)

and check_any state env ?expected (value : Syntax.expression) (inner : Syntax.expression) =
  match Option.map (Conversions.read_expected_head state) expected with
  | Some (Types.Any trait as any_type) ->
      let inner_type = Hooks.check_expression state env inner in
      Solver.require state
        (Any_conversion { at = State.read_span state value.id; any_type })
        inner_type trait;
      Instantiation.check_grants_when_final state (State.read_span state value.id) inner_type trait;
      State.check_when_final state (fun () ->
          let inner_type = State.finalize_type state inner_type in
          if Option.is_some (State.find_evidence state inner_type trait) then
            List.iter
              (fun (bound : Types.trait_reference) ->
                match
                  Interface.Definition.find_trait_interface state.lookups.interface bound.trait
                with
                | Some interface ->
                    List.iter
                      (fun name ->
                        match
                          Types.list_capabilities
                            (Interface.Impls.project_capability_set state.lookups.interface
                               ~list_bounds:(State.lookup_bounds state) inner_type
                               { bound with associated = [] } name)
                        with
                        | [] -> ()
                        | set ->
                            State.report state No_impl (State.read_span state value.id)
                              (Printf.sprintf
                                 "`%s` cannot be an `%s`: its `%s` is %s, and code that holds an \
                                  `any` value has no capability to give to its methods."
                                 (Types.show inner_type) (Types.show any_type) name
                                 (String.concat ", "
                                    (List.map
                                       (fun capability ->
                                         "`" ^ Types.show_capability capability ^ "`")
                                       set))))
                      interface.associated_capabilities
                | None -> ())
              (Interface.Properties.list_bound_closure state.lookups.interface ~self:inner_type
                 trait));
      any_type
  | _ ->
      ignore (Hooks.check_expression state env inner);
      State.make_error_type state Cannot_infer (State.read_span state value.id)
        "`any value` needs an expected type `any Trait`, from an annotation or a parameter."
