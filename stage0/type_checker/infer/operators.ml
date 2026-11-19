let select_arithmetic_method : Syntax.arithmetic -> Well_known.method_ * Well_known.associated =
  function
  | Add -> (Add_add, Add_output)
  | Subtract -> (Subtract_subtract, Subtract_output)
  | Multiply -> (Multiply_multiply, Multiply_output)
  | Divide -> (Divide_divide, Divide_output)
  | Remainder -> (Remainder_remainder, Remainder_output)

let infer_integer_result state span type_ ~(describe : string -> string) =
  let is_integer resolved = State.is_integer_type state resolved || Types.is_error resolved in
  match State.normalize state type_ with
  | Types.Literal _ | Types.Variable _ ->
      State.defer state (fun () ->
          match State.normalize state type_ with
          | Types.Literal _ | Types.Variable _ -> false
          | resolved ->
              if not (is_integer resolved) then
                State.report state No_impl span (describe (Types.show resolved));
              true);
      type_
  | resolved when is_integer resolved -> type_
  | resolved -> State.make_error_type state No_impl span (describe (Types.show resolved))

let infer_bitwise_result state span type_ =
  infer_integer_result state span type_
    ~describe:(Printf.sprintf "Bitwise operators work on built-in integers, not `%s`.")

let infer_shift_result state ~left:(left_span, left_type) ~right:(right_span, right_type) =
  (match State.resolve state right_type with
  | Types.Literal (Integer_literal, _) ->
      ignore (State.unify state right_type (Types.make_builtin UInt64))
  | _ -> ());
  State.defer state (fun () ->
      match State.normalize state right_type with
      | Types.Literal _ | Types.Variable _ -> false
      | right_resolved ->
          if
            not
              (State.is_integer_type state right_resolved
               && not (State.is_signed_type state right_resolved)
              || Types.is_error right_resolved)
          then
            State.report state Mismatch right_span
              (Printf.sprintf "A shift amount is an unsigned integer, not `%s`."
                 (Types.show right_resolved));
          true);
  infer_integer_result state left_span left_type
    ~describe:(Printf.sprintf "Shifts work on built-in integers, not `%s`.")

let is_integer_operand state type_ =
  let type_ = State.normalize state type_ in
  State.is_integer_type state type_ || type_ = Types.Integer
  || match State.resolve state type_ with Types.Literal (Integer_literal, _) -> true | _ -> false

let rec try_ state env (value : Syntax.expression) (inner : Syntax.expression) =
  State.reject_in_formula state env (State.read_span state value.id) "`?`";
  let inner_type = State.normalize state (Hooks.check_expression state env inner) in
  let output =
    match env.output with Some (Returns output) -> Some (State.normalize state output) | _ -> None
  in
  State.register_expression state value (fun () ->
      match output with
      | Some output -> Form.build_try state value inner ~output:(State.finalize_type state output)
      | None -> State.raise_bug "`?` where nothing is returned");
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
      check_built_in_operator state value [ inner ] Types.bool;
      State.register_expression state value (fun () -> Not (State.build_expression state inner));
      Types.bool
  | Complement ->
      let type_ = Hooks.check_expression state env ?expected inner in
      check_built_in_operator state value [ inner ] type_;
      State.register_expression state value (fun () ->
          Form.build_operator state value Complement [ inner ]);
      if
        State.is_integer_type state (State.normalize state type_)
        ||
        match State.resolve state type_ with
        | Types.Literal (Integer_literal, _) -> true
        | _ -> false
      then type_
      else
        State.make_error_type state No_impl (State.read_span state value.id)
          (Printf.sprintf "`~` works on built-in integers, not %s." (State.describe state type_))
  | Negate -> (
      match inner.kind with
      | Integer number ->
          state.tables.literals.(inner.id) <- Some (Integer_value number);
          state.tables.literals.(value.id) <- Some (Integer_value (Z.neg number));
          State.register_expression state value (fun () ->
              Form.build_numeric_literal state value.id);
          let type_ = Name_lookup.infer_literal_type state ~expected Integer_literal in
          State.record state inner type_;
          State.defer state (fun () ->
              match State.resolve state type_ with
              | Types.Literal _ | Types.Variable _ -> false
              | resolved ->
                  if
                    State.is_integer_type state resolved
                    && (not (State.is_signed_type state resolved))
                    && not (Z.equal number Z.zero)
                  then
                    State.report state Negated_unsigned (State.read_span state value.id)
                      (Printf.sprintf "`%s` is unsigned, so it cannot be negated."
                         (Types.show resolved))
                  else Pattern_typing.check_literal_fits state value (Z.neg number) type_;
                  true);
          type_
      | _ ->
          let type_ = Hooks.check_expression state env ?expected inner in
          let resolved = State.normalize state type_ in
          if resolved = Types.Hole then Types.Hole
          else if State.is_integer_type state resolved && not (State.is_signed_type state resolved)
          then
            State.make_error_type state Negated_unsigned (State.read_span state value.id)
              (Printf.sprintf "`%s` is unsigned, so it cannot be negated." (Types.show resolved))
          else if
            env.specification && (State.is_integer_type state resolved || resolved = Types.Integer)
          then begin
            State.register_expression state value (fun () ->
                Form.build_operator state value Negate [ inner ]);
            Types.Integer
          end
          else begin
            Form.register_call state value;
            check_operator_call
              ~operands:
                [
                  {
                    Tables.expression = inner.id;
                    core_argument_index = 0;
                    mode = Language.Mode.Read;
                  };
                ]
              state value ~method_:Well_known.Negate_negate ~output:Well_known.Negate_output
              ~left:type_ ~right:None
          end)

and check_operator_call ~operands state (value : Syntax.expression) ~method_ ~output ~left ~right =
  let { Well_known.owner; name; receiver } = Well_known.locate_method method_ in
  let arguments = match right with Some right -> [ Types.Type right ] | None -> [] in
  let reference = State.make_trait_reference ~arguments (Well_known.make_path owner) in
  let result = State.make_fresh_type state in
  let is_one_built_in_number =
    match (State.resolve state left, Option.map (State.resolve state) right) with
    | Types.Literal (left_kind, _), Some (Types.Literal (right_kind, _)) -> left_kind = right_kind
    | Types.Literal _, None -> true
    | resolved, operand ->
        (State.is_integer_type state resolved || Types.is_float_type resolved)
        && Option.fold ~none:true ~some:(Types.equal resolved) operand
  in
  if is_one_built_in_number then ignore (State.unify state result left);
  state.tables.calls.(value.id) <-
    Some
      {
        callee =
          Trait_method
            {
              trait = reference;
              name;
              receiver;
              self_type = left;
              instantiation = Types.no_instantiation;
            };
        arguments = operands;
        omitted_defaults = [];
        callee_result = result;
      };
  State.defer state (fun () ->
      let left = State.normalize state left in
      let reference = Unify.zonk_trait state.unifier reference in
      if
        Types.contains_unsolved left
        || List.exists
             (function Types.Type type_ -> Types.contains_unsolved type_ | _ -> false)
             reference.trait_arguments
      then false
      else begin
        (match State.find_evidence state left reference with
        | Some _ ->
            let output =
              State.resolve_associated_type state left reference output
                ~at:(State.read_span state value.id)
            in
            let decided = State.zonk state result in
            if not (State.unify state result output) then
              State.report state Mismatch (State.read_span state value.id)
                (Printf.sprintf "This operator gives `%s`, and `%s` is expected."
                   (Types.show (State.zonk state output))
                   (Types.show decided))
        | None ->
            let unknown =
              if Types.is_error left then left
              else
                State.make_error_type state No_impl (State.read_span state value.id)
                  (Printf.sprintf "`%s` does not implement `%s`, so the operator does not apply."
                     (Types.show left) (Types.show_trait reference))
            in
            ignore (State.unify state result unknown));
        true
      end);
  result

and check_literal_operands state ~left ~right =
  match (State.resolve state left, State.resolve state right) with
  | Types.Literal (kind, _), other when Unify.literal_fits state.unifier kind other ->
      ignore (State.unify state left right)
  | other, Types.Literal (kind, _) when Unify.literal_fits state.unifier kind other ->
      ignore (State.unify state left right)
  | Types.Literal (left_kind, _), Types.Literal (right_kind, _) when left_kind = right_kind ->
      ignore (State.unify state left right)
  | _ -> ()

and check_built_in_operator state (value : Syntax.expression) (operands : Syntax.expression list)
    result =
  state.tables.calls.(value.id) <-
    Some
      {
        callee = Built_in_operator;
        arguments =
          List.mapi
            (fun index (operand : Syntax.expression) ->
              { Tables.expression = operand.id; core_argument_index = index; mode = Read })
            operands;
        omitted_defaults = [];
        callee_result = result;
      }

and is_hole state type_ = State.resolve state type_ = Types.Hole

and has_operand_hole state env (left : Syntax.expression) (right : Syntax.expression) =
  let left_type = Hooks.check_expression state env left in
  let right_type = Hooks.check_expression state env ~expected:left_type right in
  is_hole state left_type || is_hole state right_type

and is_string state type_ =
  let type_ = State.normalize state type_ in
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
      check_built_in_operator state value [ left; right ] Types.bool;
      State.register_expression state value (fun () ->
          let left = State.build_expression state left in
          let right = State.build_expression state right in
          Connective { connective; left; right });
      Types.bool
  | Operation (Bitwise _ as operation) ->
      let left_type = Hooks.check_expression state env ?expected left in
      let right_type = Hooks.check_expression state env ~expected:left_type right in
      check_built_in_operator state value [ left; right ] left_type;
      State.register_expression state value (fun () ->
          Form.build_operator state value (Form.convert_to_operation operation) [ left; right ]);
      check_literal_operands state ~left:left_type ~right:right_type;
      if not (State.unify state left_type right_type) then
        State.report_mismatch state (State.read_span state right.id) ~expected:left_type
          ~actual:right_type;
      infer_bitwise_result state (State.read_span state value.id) left_type
  | Operation (Shift _ as operation) ->
      let left_type = Hooks.check_expression state env ?expected left in
      let right_type = Hooks.check_expression state env right in
      check_built_in_operator state value [ left; right ] left_type;
      State.register_expression state value (fun () ->
          Form.build_operator state value (Form.convert_to_operation operation) [ left; right ]);
      infer_shift_result state
        ~left:(State.read_span state left.id, left_type)
        ~right:(State.read_span state right.id, right_type)
  | Comparison comparison when has_operand_hole state env left right ->
      State.register_expression state value (fun () ->
          Form.build_built_in_comparison state comparison left right);
      Types.bool
  | Comparison comparison ->
      let left_type = Option.get state.tables.types.(left.id) in
      let right_type = Option.get state.tables.types.(right.id) in
      check_literal_operands state ~left:left_type ~right:right_type;
      if
        env.specification
        && is_integer_operand state left_type
        && is_integer_operand state right_type
      then begin
        State.register_expression state value (fun () ->
            Form.build_built_in_comparison state comparison left right);
        Types.bool
      end
      else begin
        State.register_expression state value (fun () ->
            Form.build_comparison state value comparison left right);
        let compared_type =
          match
            ( State.find_view_as state ~owned:right_type ~view:left_type,
              State.find_view_as state ~owned:left_type ~view:right_type )
          with
          | Some _, _ ->
              Name_lookup.coerce state env ~argument:Language.Mode.Read right ~actual:right_type
                ~expected:left_type;
              left_type
          | None, Some _ ->
              Name_lookup.coerce state env ~argument:Language.Mode.Read left ~actual:left_type
                ~expected:right_type;
              right_type
          | None, None ->
              if not (State.unify state left_type right_type) then
                ignore (add_operand_mismatch state value left right ~left_type ~right_type);
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
                    trait = State.make_trait_reference ~arguments:[] trait;
                    name;
                    receiver;
                    self_type = compared_type;
                    instantiation = Types.no_instantiation;
                  };
              arguments =
                [
                  { expression = left.id; core_argument_index = 0; mode = Read };
                  { expression = right.id; core_argument_index = 1; mode = Read };
                ];
              omitted_defaults = [];
              callee_result = result;
            };
        Name_lookup.check_implements state value compared_type
          (State.make_trait_reference ~arguments:[] trait);
        Types.bool
      end
  | Operation (Arithmetic _ as operation) when has_operand_hole state env left right ->
      State.register_expression state value (fun () ->
          Form.build_operator state value (Form.convert_to_operation operation) [ left; right ]);
      Types.Hole
  | Operation (Arithmetic arithmetic as operation) ->
      let left_type = Option.get state.tables.types.(left.id) in
      let right_type = Option.get state.tables.types.(right.id) in
      check_literal_operands state ~left:left_type ~right:right_type;
      if arithmetic = Add && (is_string state left_type || is_string state right_type) then begin
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
          && is_integer_operand state left_type
          && is_integer_operand state right_type
        then begin
          ignore
            (match State.resolve state left_type with
            | Types.Literal _ -> State.unify state left_type Types.Integer
            | _ -> true);
          ignore
            (match State.resolve state right_type with
            | Types.Literal _ -> State.unify state right_type Types.Integer
            | _ -> true);
          State.register_expression state value (fun () ->
              Form.build_operator state value (Form.convert_to_operation operation) [ left; right ]);
          Types.Integer
        end
        else
          let method_, output = select_arithmetic_method arithmetic in
          if
            (State.is_integer_type state (State.normalize state left_type)
            && State.is_integer_type state (State.normalize state right_type))
            && not
                 (Types.equal (State.normalize state left_type) (State.normalize state right_type))
          then Types.Error (add_operand_mismatch state value left right ~left_type ~right_type)
          else begin
            Form.register_call state value;
            check_operator_call
              ~operands:
                [
                  {
                    Tables.expression = left.id;
                    core_argument_index = 0;
                    mode = Language.Mode.Read;
                  };
                  {
                    Tables.expression = right.id;
                    core_argument_index = 1;
                    mode = Language.Mode.Read;
                  };
                ]
              state value ~method_ ~output ~left:left_type ~right:(Some right_type)
          end
        end

and add_operand_mismatch state (value : Syntax.expression) (left : Syntax.expression)
    (right : Syntax.expression) ~left_type ~right_type =
  let sides = [ (left_type, right_type); (right_type, left_type) ] in
  let left_type = State.normalize state left_type
  and right_type = State.normalize state right_type in
  if State.is_integer_type state left_type && State.is_integer_type state right_type then begin
    let is_within narrower wider =
      match (Types.find_integer_range narrower, Types.find_integer_range wider) with
      | Some (low, high), Some (wider_low, wider_high) ->
          Z.geq low wider_low && Z.leq high wider_high
      | _ -> false
    in
    let make_widening_fix side (operand : Syntax.expression) target =
      State.fix
        (Printf.sprintf "Convert the %s side to `%s`." side (Types.show target))
        [
          State.replace
            (State.read_span state operand.id)
            (Printf.sprintf "%s.from_integer(%s)" (Types.show target)
               (State.quote_span state (State.read_span state operand.id)));
        ]
    in
    let fixes =
      if is_within right_type left_type then [ make_widening_fix "right" right left_type ]
      else if is_within left_type right_type then [ make_widening_fix "left" left right_type ]
      else []
    in
    State.add_mismatch_diagnostic state Mismatched_integers (State.read_span state value.id) ~sides
      ~fixes
      (Printf.sprintf
         "Integer types never convert implicitly: this compares or combines `%s` with `%s`."
         (Types.show left_type) (Types.show right_type))
  end
  else
    State.add_mismatch state (State.read_span state right.id) ~expected:left_type ~actual:right_type

and check_any state env ?expected (value : Syntax.expression) (inner : Syntax.expression) =
  match Option.map (State.normalize state) expected with
  | Some (Types.Any trait as any_type) ->
      let inner_type = Hooks.check_expression state env inner in
      State.register_expression state value (fun () ->
          let inner = State.build_expression state inner in
          match Form.read_type state value with
          | Types.Any trait ->
              To_any { value = inner; trait; evidence = Form.read_evidence state inner.type_ trait }
          | converted ->
              State.raise_bug "an `any` conversion has the type `%s`" (Types.show converted));
      Instantiation.require state ~at:(State.read_span state value.id) inner_type trait
        ~on_unmet:(fun inner_type other ->
          State.report state No_impl (State.read_span state value.id)
            (match other with
            | None ->
                Printf.sprintf "`%s` does not implement `%s`." (Types.show inner_type)
                  (Types.show_trait trait)
            | Some (name, associated_type) ->
                Printf.sprintf "`%s` is expected, and the `%s` of `%s` is `%s`."
                  (Types.show any_type) name (Types.show inner_type)
                  (State.show state associated_type)));
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
