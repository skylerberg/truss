let select_arithmetic_method : Syntax.arithmetic -> Well_known.method_ * Well_known.associated =
  function
  | Add -> (Add_add, Add_output)
  | Subtract -> (Subtract_subtract, Subtract_output)
  | Multiply -> (Multiply_multiply, Multiply_output)
  | Divide -> (Divide_divide, Divide_output)
  | Remainder -> (Remainder_remainder, Remainder_output)

let infer_integer_result state at type_ ~operator =
  Solver.require_within state type_ Types.integer_types ~reason:(fun excluded ->
      State.add_diagnostic state
        (Not_an_integer_operand { at; operator; excluded = State.make_shown state excluded }))

let infer_bitwise_result state at type_ = infer_integer_result state at type_ ~operator:Bitwise

let infer_shift_result state ~left:(left_at, left_type) ~right:(right_at, right_type) =
  ignore
    (Solver.require_within state right_type Types.unsigned_integer_types ~reason:(fun excluded ->
         State.add_diagnostic state
           (Shift_amount_not_unsigned { at = right_at; excluded = State.make_shown state excluded })));
  infer_integer_result state left_at left_type ~operator:Shift

let is_integer_operand state (operand : Syntax.expression) type_ =
  State.is_within state
    (Conversions.read_actual_head state operand type_)
    (Types.integer_types @ [ Integer ])

let rec try_ state env (value : Syntax.expression) (inner : Syntax.expression) =
  State.reject_in_formula state env (Written value.id) Try_expression;
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
        State.report state
          (Try_error_mismatch
             {
               at = Written value.id;
               output_error = State.normalize_known state output_error;
               error = State.normalize_known state error;
             });
      ok
  | ( Types.Named { path; arguments = [ Types.Type some ] },
      Some (Types.Named { path = output_path; _ }) )
    when Well_known.is Option path && Well_known.is Option output_path ->
      some
  | (Types.Error _ | Types.Hole), _ -> inner_type
  | _ -> State.make_error_type state (Try_misused { at = Written value.id })

and check_prefix state env ?expected (value : Syntax.expression) operator
    (inner : Syntax.expression) =
  match operator with
  | Syntax.Not ->
      Hooks.check state env inner Types.bool;
      Types.bool
  | Complement ->
      let type_ = Hooks.check_expression state env ?expected inner in
      infer_integer_result state (Written value.id) type_ ~operator:Complement
  | Negate -> (
      match inner.kind with
      | Integer number ->
          State.elaborate state inner.id (Literal (Integer_value number));
          State.elaborate state value.id (Literal (Integer_value (Z.neg number)));
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
  let { Well_known.owner; _ } = Well_known.locate_method method_ in
  let reference =
    Types.make_trait_reference
      ~arguments:(List.map (fun (_, right_type) -> Types.Type right_type) (Option.to_list right))
      (Well_known.make_path owner)
  in
  let result = Unify.make_fresh_type state.unifier in
  State.elaborate state call
    (Call
       (Tables.make_method_call reference method_ ~self_type:left_type ~result
          ((left, Read)
          :: List.map (fun (right, _) -> (right, Language.Mode.Read)) (Option.to_list right))));
  Solver.require state
    (Operator
       {
         at = Written call;
         operands =
           Option.map
             (fun ((right : Syntax.expression), _) -> (Core.Written left.id, Core.Written right.id))
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
  Types.is_well_known String (Types.strip_view type_)

and check_binary state (env : State.env) ?expected (value : Syntax.expression) operator
    (left : Syntax.expression) (right : Syntax.expression) =
  match operator with
  | Syntax.Connective _ ->
      Hooks.check state env left Types.bool;
      Hooks.check state env right Types.bool;
      Types.bool
  | Operation (Bitwise _) ->
      let left_type = Hooks.check_expression state env ?expected left in
      let right_type = Hooks.check_expression state env ~expected:left_type right in
      check_literal_operands state ~left:left_type ~right:right_type;
      if not (State.unify state left_type right_type) then
        Failures.report_mismatch state (Written right.id) ~expected:left_type ~actual:right_type;
      infer_bitwise_result state (Written value.id) left_type
  | Operation (Shift _) ->
      let left_type = Hooks.check_expression state env ?expected left in
      let right_type = Hooks.check_expression state env right in
      infer_shift_result state ~left:(Core.Written left.id, left_type)
        ~right:(Core.Written right.id, right_type)
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
            let left_self = Types.strip_view left_head
            and right_self = Types.strip_view right_head in
            let is_array type_ = Option.is_some (Types.find_list_of_array type_) in
            let compared_type =
              if is_array left_self && Types.is_well_known List right_self then right_self
              else if Types.is_view left_head then left_self
              else left_type
            in
            let compares_as_list = Types.is_well_known List (State.normalize state compared_type) in
            let view_as_compared (operand : Syntax.expression) self_type actual =
              if is_array self_type && compares_as_list then begin
                Conversions.coerce state env ~argument:Language.Mode.Read operand ~actual
                  ~expected:compared_type;
                true
              end
              else State.unify ~modulo_views:true state actual compared_type
            in
            let left_fits = view_as_compared left left_self left_type in
            if not (left_fits && view_as_compared right right_self right_type) then
              ignore
                (Failures.add_operand_mismatch state ~at:(Written value.id)
                   ~left:(Core.Written left.id, left_type)
                   ~right:(Core.Written right.id, right_type));
            let method_, result =
              match comparison with
              | Equal | Not_equal -> (Well_known.Equal_equal, Types.bool)
              | Less | Less_equal | Greater | Greater_equal ->
                  (Ordered_compare, Types.make_named (Well_known.make_path Ordering) [])
            in
            let { Well_known.owner; _ } = Well_known.locate_method method_ in
            let trait = Types.make_trait_reference ~arguments:[] (Well_known.make_path owner) in
            State.elaborate state value.id
              (Call
                 (Tables.make_method_call trait method_ ~self_type:compared_type ~result
                    [ (left, Read); (right, Read) ]));
            Solver.require state (Method_call (Written value.id)) compared_type trait;
            Types.bool
          end)
  | Operation (Arithmetic arithmetic) -> (
      match check_operands state env left right with
      | None -> Types.Hole
      | Some (left_type, right_type) ->
          check_literal_operands state ~left:left_type ~right:right_type;
          if arithmetic = Add && (is_string state left left_type || is_string state right right_type)
          then begin
            let list_pieces (side : Syntax.expression) : Catalog.Inference.joined_piece list option
                =
              match side.kind with
              | String { tag = None; form = Ordinary; first = { value = ""; _ }; rest = []; _ } ->
                  Some []
              | String { tag = None; form = Ordinary; first; rest = []; _ } ->
                  Some [ Fragment (Written first.id) ]
              | String _ -> None
              | _ -> Some [ Interpolated (Written side.id) ]
            in
            State.make_error_type state
              (String_addition
                 {
                   at = Written value.id;
                   join =
                     (match (list_pieces left, list_pieces right) with
                     | Some left, Some right -> Some (left @ right)
                     | _ -> None);
                 })
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
