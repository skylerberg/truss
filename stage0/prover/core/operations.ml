let is_nan value = Logic.Operation (Fp_is_nan, [ value ])

let make_float_of_integer (exponent, significand) rounding_mode integer =
  Logic.Operation
    ( To_fp { exponent; significand; rounding_mode = Some rounding_mode },
      [ Logic.Operation (To_real, [ integer ]) ] )

let make_float_literal (exponent, significand) value =
  let bits =
    if exponent = 8 then Z.extract (Z.of_int32 (Int32.bits_of_float value)) 0 32
    else Z.extract (Z.of_int64 (Int64.bits_of_float value)) 0 64
  in
  let fraction = significand - 1 in
  Logic.Operation
    ( Fp,
      [
        Logic.Bits (1, Z.extract bits (exponent + fraction) 1);
        Logic.Bits (exponent, Z.extract bits fraction exponent);
        Logic.Bits (fraction, Z.extract bits 0 fraction);
      ] )

let make_float_equal left right =
  Logic.(Operation (Fp_eq, [ left; right ]) ||| (is_nan left &&& is_nan right))

let make_float_less left right =
  Logic.(not_ (is_nan left) &&& is_nan right ||| Operation (Fp_lt, [ left; right ]))

let compare_terms ty (compared : Language.Comparison.t) left right =
  if Facts.find_float_format ty <> None then
    match compared with
    | Equal -> make_float_equal left right
    | Not_equal -> Logic.not_ (make_float_equal left right)
    | Less -> make_float_less left right
    | Less_equal -> Logic.( ||| ) (make_float_less left right) (make_float_equal left right)
    | Greater -> make_float_less right left
    | Greater_equal -> Logic.( ||| ) (make_float_less right left) (make_float_equal left right)
  else
    match compared with
    | Equal -> Logic.equal left right
    | Not_equal -> Logic.not_ (Logic.equal left right)
    | Less -> Logic.less left right
    | Less_equal -> Logic.less_equal left right
    | Greater -> Logic.greater left right
    | Greater_equal -> Logic.greater_equal left right

let check_widened location ~is_written actual expected =
  match (actual, expected) with
  | Types.Function actual, Types.Function expected
    when (not is_written)
         && not (List.for_all (fun cost -> List.mem cost actual.costs) expected.costs) ->
      Facts.raise_unsupported location Function_value_costs
  | _ -> ()

let find_parameter_code (context : State.context) (frame : State.frame) term =
  if
    Facts.is_home context frame.source
    && (not (Logic.has_quantifier term))
    &&
    match Logic.list_free_constants term with
    | _ :: _ as names -> List.for_all (fun name -> List.mem name context.entry) names
    | [] -> false
  then Facts.find_value_code context term
  else None

let find_integer_limits ty = if Types.is_builtin Character ty then None else Facts.find_bounds ty
let make_limit ty limit = Catalog.Code.Limit { type_ = ty; limit }
let make_comparison left comparison right = Catalog.Code.Compared { left; comparison; right }

let make_range_fix context frame ty term =
  match (find_integer_limits ty, find_parameter_code context frame term) with
  | Some (low, _), Some value ->
      let least = if Z.sign low = 0 then Catalog.Code.Integer Z.zero else make_limit ty Minimum in
      Facts.add_requires context frame
        [
          Clause
            (All
               [
                 make_comparison least Less_equal value;
                 make_comparison value Less_equal (make_limit ty Maximum);
               ]);
        ]
  | _ -> []

let convert_from_integer context frame (site : Invocation.site) term =
  let ty = Facts.substitute_type context frame site.type_ in
  Facts.oblige
    ~fixes:(make_range_fix context frame ty term)
    context frame
    (Facts.locate context frame.source site.origin)
    (Out_of_range { at = Facts.quote frame.source site.origin; type_ = ty })
    (Facts.make_in_range ty term);
  term

let list_impl_packages (context : State.context) (ty : Types.ty) =
  List.sort_uniq compare
    ((match ty with Types.Named { path; _ } -> [ Path.locate_package path ] | _ -> [])
    @ [ Path.locate_package context.current; Path.standard_package ])

let find_written_equal context ty left right =
  let equal = Well_known.locate_method Equal_equal in
  let trait : Types.trait_reference =
    { trait = Well_known.make_path equal.owner; trait_arguments = []; associated = [] }
  in
  match Facts.find_impl context trait ty with
  | Some (((Impl _ : Path.t) as impl), substitution) -> (
      let evidence : Types.evidence = Impl { impl; substitution } in
      match Contracts.find_method_contract context trait equal.name equal.receiver evidence with
      | Some contract when contract.is_logic_function ->
          let symbol =
            Logic.Symbol.Function
              {
                callee = Well_known.make_impl_method_path Equal_equal ~impl;
                type_arguments = [ Types.Type ty ];
              }
          in
          let sort = Facts.declare_sort context ty in
          Facts.declare context (Logic.Function (symbol, [ sort; sort ], Logic.Bool));
          Some (Logic.Apply (symbol, [ left; right ]))
      | _ -> None)
  | _ -> None

let make_derived_equal context (frame : State.frame) (ty : Types.ty) left right =
  let sort = Facts.declare_sort context ty in
  let symbol = Logic.Symbol.Equal ty in
  Facts.declare context (Logic.Function (symbol, [ sort; sort ], Logic.Bool));
  let equal = Logic.Apply (symbol, [ left; right ]) in
  (match (Facts.find_visible_type context ty, Facts.find_constructors context ty) with
  | Some (interface, _), Some shape
    when List.exists Facts.is_standard_equal interface.derives
         && (not (List.mem equal context.equalities))
         && not (Logic.mentions frame.bound equal) ->
      context.equalities <- equal :: context.equalities;
      let fields_equal (variant, fields) =
        Logic.conjunction
          (List.map
             (fun (field, field_type) ->
               let selector = Facts.make_selector_symbol ty variant field in
               let left = Logic.Apply (selector, [ left ])
               and right = Logic.Apply (selector, [ right ]) in
               if Facts.is_equality_identity context field_type then Logic.equal left right
               else if Facts.find_float_format field_type <> None then make_float_equal left right
               else
                 match find_written_equal context field_type left right with
                 | Some equal -> equal
                 | None ->
                     let symbol = Logic.Symbol.Equal field_type in
                     Facts.declare context
                       (Logic.Function
                          ( symbol,
                            [
                              Facts.declare_sort context field_type;
                              Facts.declare_sort context field_type;
                            ],
                            Logic.Bool ));
                     Logic.Apply (symbol, [ left; right ]))
             fields)
      in
      let defined =
        match shape with
        | [ ((None, _) as record) ] -> fields_equal record
        | variants ->
            Logic.disjunction
              (List.map
                 (fun ((variant, _) as one) ->
                   let is_variant term =
                     Logic.Is (Facts.make_constructor_symbol ty variant, term)
                   in
                   Logic.(is_variant left &&& is_variant right &&& fields_equal one))
                 variants)
      in
      Facts.add_frame_fact context frame (Logic.equal equal defined)
  | _ -> ());
  equal

let make_equality context frame (ty : Types.ty) left right =
  if Facts.is_equality_identity context ty then Logic.equal left right
  else if Facts.find_float_format ty <> None then make_float_equal left right
  else
    match find_written_equal context ty left right with
    | Some equal -> equal
    | None -> make_derived_equal context frame ty left right

let find_width (ty : Types.ty) = Option.map fst (Types.find_integer_bits ty)

let declare_opaque_operation context frame ty operation arguments =
  let sorts = List.map (fun _ -> Logic.Int) arguments in
  let integer =
    Option.map
      (fun bits ->
        (bits, match Facts.find_bounds ty with Some (low, _) -> Z.sign low < 0 | None -> false))
      (find_width ty)
  in
  let symbol = Logic.Symbol.Opaque_operation { operation; type_ = ty; integer } in
  Facts.declare context (Logic.Function (symbol, sorts, Facts.declare_sort context ty));
  let term = Logic.Apply (symbol, arguments) in
  Facts.assume context frame (Facts.make_in_range ty term);
  term

let make_overflow_fix context frame ty (operation : Intrinsic.scalar) left right exact =
  match find_integer_limits ty with
  | None -> []
  | Some (low, high) -> (
      let is_unsigned = Z.sign low = 0 in
      let bound_on_left =
        match (right, find_parameter_code context frame left) with
        | Logic.Integer amount, Some value -> (
            let magnitude = Catalog.Code.Integer (Z.abs amount) in
            let bound_by comparison bound written =
              if Z.leq low bound && Z.leq bound high then
                Some (make_comparison value comparison written)
              else None
            in
            match operation with
            | Add when Z.sign amount > 0 ->
                bound_by Less_equal (Z.sub high amount)
                  (Difference (make_limit ty Maximum, magnitude))
            | Add when Z.sign amount < 0 ->
                bound_by Greater_equal (Z.sub low amount) (Sum [ make_limit ty Minimum; magnitude ])
            | Subtract when Z.sign amount > 0 && is_unsigned ->
                bound_by Greater_equal amount magnitude
            | Subtract when Z.sign amount > 0 ->
                bound_by Greater_equal (Z.add low amount) (Sum [ make_limit ty Minimum; magnitude ])
            | Subtract when Z.sign amount < 0 ->
                bound_by Less_equal (Z.add high amount)
                  (Difference (make_limit ty Maximum, magnitude))
            | Multiply when Z.sign amount > 0 && is_unsigned ->
                bound_by Less_equal (Z.div high amount)
                  (Quotient (make_limit ty Maximum, magnitude))
            | _ -> None)
        | _ -> None
      in
      match (bound_on_left, operation) with
      | Some required, _ -> Facts.add_requires context frame [ Clause required ]
      | None, (Add | Multiply) when is_unsigned -> (
          match find_parameter_code context frame exact with
          | Some value ->
              Facts.add_requires context frame
                [ Clause (make_comparison value Less_equal (make_limit ty Maximum)) ]
          | None -> [])
      | None, Subtract when is_unsigned -> []
      | None, _ -> make_range_fix context frame ty exact)

let make_division_overflow_fix context frame ty left right =
  match (find_integer_limits ty, find_parameter_code context frame left) with
  | Some _, Some dividend -> (
      let dividend_not_minimum = make_comparison dividend Not_equal (make_limit ty Minimum) in
      match right with
      | Logic.Integer divisor when Z.equal divisor Z.minus_one ->
          Facts.add_requires context frame [ Clause dividend_not_minimum ]
      | _ -> (
          match find_parameter_code context frame right with
          | Some divisor ->
              Facts.add_requires context frame
                [
                  Clause
                    (Any
                       [
                         dividend_not_minimum;
                         make_comparison divisor Not_equal (Integer Z.minus_one);
                       ]);
                ]
          | None -> []))
  | _ -> []

let make_negation_fix context frame ty inner =
  match (find_integer_limits ty, find_parameter_code context frame inner) with
  | Some _, Some value ->
      Facts.add_requires context frame
        [ Clause (make_comparison value Not_equal (make_limit ty Minimum)) ]
  | _ -> []

let translate_arithmetic context (frame : State.frame) (site : Invocation.site) ty
    (operation : Intrinsic.scalar) left right =
  let source = frame.source in
  let location = Facts.locate context frame.source site.origin in
  let exact, is_division =
    match operation with
    | Add -> (Logic.add left right, false)
    | Subtract -> (Logic.subtract left right, false)
    | Multiply -> (Logic.multiply left right, false)
    | Divide -> (Logic.truncated_divide left right, true)
    | Remainder -> (Logic.truncated_remainder left right, true)
    | _ -> Facts.raise_bug "`%s` is not arithmetic" (Intrinsic.show_operation (Scalar operation))
  in
  if is_division then
    Facts.oblige
      ~fixes:
        (match find_parameter_code context frame right with
        | Some divisor ->
            Facts.add_requires context frame
              [ Clause (make_comparison divisor Not_equal (Integer Z.zero)) ]
        | None -> [])
      context frame location
      (Divisor_may_be_zero { at = Facts.quote source site.origin })
      (Logic.not_ (Logic.equal right (Logic.int 0)));
  (match Facts.find_bounds ty with
  | Some (low, _) when is_division ->
      if Z.sign low < 0 then
        Facts.oblige
          ~fixes:(make_division_overflow_fix context frame ty left right)
          context frame location
          (Division_overflow { at = Facts.quote source site.origin; type_ = ty })
          (Logic.not_ Logic.(equal left (Integer low) &&& equal right (int (-1))))
  | Some (low, high) ->
      let unsigned = Z.sign low = 0 && not (Types.is_builtin Character ty) in
      Facts.oblige
        ~fixes:(make_overflow_fix context frame ty operation left right exact)
        context frame location
        (Overflow { at = Facts.quote source site.origin; type_ = ty })
        (match operation with
        | (Add | Multiply) when unsigned -> Logic.less_equal exact (Integer high)
        | Subtract when unsigned -> Logic.less_equal (Integer low) exact
        | _ -> Facts.make_in_range ty exact)
  | None -> ());
  exact

let make_float_fits source target value =
  match (Facts.find_float_format source, Facts.find_bounds target) with
  | Some format, Some (low, high) ->
      let cut = Logic.Operation (Fp_round_to_integral Toward_zero, [ value ]) in
      Logic.(
        Operation (Fp_leq, [ make_float_of_integer format Toward_positive (Integer low); cut ])
        &&& Operation (Fp_leq, [ cut; make_float_of_integer format Toward_negative (Integer high) ]))
  | _ ->
      Facts.raise_bug "a float check from `%s` to `%s` needs a float source and a bounded target"
        (Types.show source) (Types.show target)

let make_power_facts base exponent =
  let power exponent = Logic.Apply (Logic.Symbol.Integer_power, [ base; exponent ]) in
  let previous = Logic.subtract exponent (Logic.int 1) in
  ( Logic.
      [
        equal exponent (int 0) ==> equal (power exponent) (int 1);
        greater_equal base (int 1)
        &&& greater_equal exponent (int 0)
        ==> greater_equal (power exponent) (int 1);
        greater_equal base (int 2)
        &&& greater_equal exponent (int 0)
        ==> greater (power exponent) exponent;
      ],
    ( Logic.(
        greater_equal exponent (int 1) ==> equal (power exponent) (multiply base (power previous))),
      previous ) )

let make_power_order base left right =
  let power exponent = Logic.Apply (Logic.Symbol.Integer_power, [ base; exponent ]) in
  Logic.(
    greater_equal base (int 1)
    ==> (less_equal left right
        ==> less_equal (power left) (power right)
        &&& (less_equal right left ==> less_equal (power right) (power left))))

let declare_power context frame base exponent =
  Facts.declare context
    (Logic.Function (Logic.Symbol.Integer_power, [ Logic.Int; Logic.Int ], Logic.Int));
  let add exponent =
    if not (List.mem (base, exponent) context.powers) then begin
      List.iter
        (fun (other_base, other) ->
          if other_base = base then
            Facts.add_frame_fact context frame (make_power_order base exponent other))
        context.powers;
      context.powers <- (base, exponent) :: context.powers;
      let facts, step = make_power_facts base exponent in
      List.iter (Facts.add_frame_fact context frame) facts;
      Some step
    end
    else None
  in
  (if not (Logic.mentions frame.bound base || Logic.mentions frame.bound exponent) then
     match add exponent with
     | Some (step, previous) ->
         Facts.add_frame_fact context frame step;
         ignore (add previous)
     | None -> ());
  (match (base, exponent) with
  | Logic.Integer base_value, Logic.Integer exponent_value
    when Z.sign exponent_value >= 0 && Z.leq exponent_value (Z.of_int 256) ->
      Facts.add_frame_fact context frame
        (Logic.equal
           (Logic.Apply (Logic.Symbol.Integer_power, [ base; exponent ]))
           (Logic.Integer (Z.pow base_value (Z.to_int exponent_value))))
  | _ -> ());
  Logic.Apply (Logic.Symbol.Integer_power, [ base; exponent ])

let translate_primitive_operation context (frame : State.frame) ~(site : Invocation.site)
    (operation : Intrinsic.scalar) types operands ~(arguments : Core.origin option list) ~fallback =
  let source = frame.source in
  let location = Facts.locate context frame.source site.origin in
  (match List.find_opt (function Types.Parameter _ | Projection _ -> true | _ -> false) types with
  | Some parameter ->
      Facts.raise_unsupported location
        (Intrinsic_at_parameter { operation = Scalar operation; parameter })
  | None -> ());
  let find_argument index = Option.join (List.nth_opt arguments index) in
  let is_float = match types with ty :: _ -> Facts.find_float_format ty <> None | [] -> false in
  let exact operation left right =
    match (operation : Intrinsic.scalar) with
    | Wrapping_add | Add_overflows -> Logic.add left right
    | Wrapping_subtract | Subtract_overflows -> Logic.subtract left right
    | Wrapping_multiply | Multiply_overflows -> Logic.multiply left right
    | _ ->
        Facts.raise_bug "`%s` has no exact integer result"
          (Intrinsic.show_operation (Scalar operation))
  in
  match (operation, types, operands) with
  | Add, _ :: _, [ left; right ] when is_float ->
      Logic.Operation (Fp_add Nearest_ties_to_even, [ left; right ])
  | Subtract, _ :: _, [ left; right ] when is_float ->
      Logic.Operation (Fp_sub Nearest_ties_to_even, [ left; right ])
  | Multiply, _ :: _, [ left; right ] when is_float ->
      Logic.Operation (Fp_mul Nearest_ties_to_even, [ left; right ])
  | Divide, _ :: _, [ left; right ] when is_float ->
      Logic.Operation (Fp_div Nearest_ties_to_even, [ left; right ])
  | Negate, _ :: _, [ value ] when is_float -> Logic.Operation (Fp_neg, [ value ])
  | (Add | Subtract | Multiply | Divide | Remainder), ty :: _, [ left; right ] when not is_float ->
      let result = translate_arithmetic context frame site ty operation left right in
      if Facts.find_bounds ty <> None then
        Facts.assume context frame (Facts.make_in_range ty result);
      result
  | Negate, ty :: _, [ inner ] when not is_float ->
      let negated = Logic.negate inner in
      if Facts.find_bounds ty <> None then
        Facts.oblige
          ~fixes:(make_negation_fix context frame ty inner)
          context frame location
          (Overflow { at = Facts.quote source site.origin; type_ = ty })
          (Facts.make_in_range ty negated)
      else if ty <> Types.Integer then Facts.raise_unsupported location (Negation_of ty);
      negated
  | Complement, ty :: _, [ inner ] -> declare_opaque_operation context frame ty Complement [ inner ]
  | (Shift_left | Shift_right), ty :: _, [ left; right ] ->
      (match find_width ty with
      | Some bits ->
          let at_amount, (amount, is_operand), fixes =
            match find_argument 1 with
            | Some amount ->
                ( Facts.locate context frame.source amount,
                  (Facts.quote source amount, true),
                  match find_parameter_code context frame right with
                  | Some amount ->
                      Facts.add_requires context frame
                        [ Clause (make_comparison amount Less (Integer (Z.of_int bits))) ]
                  | None -> [] )
            | None -> (location, (Facts.quote source site.origin, false), [])
          in
          Facts.oblige ~fixes context frame at_amount
            (Shift_amount { amount; is_operand; bits })
            Logic.(less right (int bits))
      | None -> Facts.raise_unsupported location (Shift_of ty));
      let shifted = declare_opaque_operation context frame ty operation [ left; right ] in
      (match (Facts.find_bounds ty, find_width ty) with
      | Some (low, high), Some bits
        when Z.equal low Z.zero && not (Logic.mentions frame.bound right) ->
          let scale = declare_power context frame (Logic.int 2) right in
          Facts.assume context frame
            Logic.(
              less_equal (int 0) right
              &&& less right (int bits)
              ==> (less_equal (int 1) scale
                  &&& less_equal scale (Integer (Z.shift_left Z.one (bits - 1)))));
          Facts.assume context frame
            (match operation with
            | Shift_left ->
                Logic.(
                  less_equal (multiply left scale) (Integer high)
                  ==> equal shifted (multiply left scale))
            | _ -> Logic.equal shifted (Logic.truncated_divide left scale))
      | _ -> ());
      shifted
  | (Bit_and | Bit_or | Bit_xor), ty :: _, [ left; right ] ->
      let term = declare_opaque_operation context frame ty operation [ left; right ] in
      (match Facts.find_bounds ty with
      | Some (low, _) when Z.sign low < 0 && operation = Bit_and ->
          let masked_by operand =
            Logic.(
              less_equal (int 0) operand ==> (less_equal (int 0) term &&& less_equal term operand))
          in
          Facts.assume context frame Logic.(masked_by left &&& masked_by right)
      | Some (low, _) when Z.equal low Z.zero -> (
          let at_most bound = Logic.less_equal term bound in
          match operation with
          | Bit_and -> Facts.assume context frame Logic.(at_most left &&& at_most right)
          | _ ->
              let sum = Logic.add left right in
              if operation = Bit_or then
                Facts.assume context frame Logic.(less_equal left term &&& less_equal right term);
              Facts.assume context frame (at_most sum);
              Facts.declare context
                (Logic.Function (Logic.Symbol.Integer_power, [ Logic.Int; Logic.Int ], Logic.Int));
              let exponent = Logic.Symbol (Facts.make_variable "exponent") in
              let below value =
                Logic.less value
                  (Logic.Apply (Logic.Symbol.Integer_power, [ Logic.int 2; exponent ]))
              in
              Facts.assume context frame
                (Logic.forall
                   ( [ (Facts.make_variable "exponent", Logic.Int) ],
                     Logic.(
                       less_equal (int 0) exponent &&& below left &&& below right ==> below term) ))
          )
      | _ -> ());
      term
  | (Wrapping_add | Wrapping_subtract | Wrapping_multiply), ty :: _, [ left; right ]
    when Facts.find_bounds ty <> None ->
      let low, high = Option.get (Facts.find_bounds ty) in
      let modulus = Z.succ (Z.sub high low) in
      Logic.add (Logic.Integer low)
        (Logic.Operation
           ( Mod,
             [
               Logic.subtract (exact operation left right) (Logic.Integer low);
               Logic.Integer modulus;
             ] ))
  | (Add_overflows | Subtract_overflows | Multiply_overflows), ty :: _, [ left; right ]
    when Facts.find_bounds ty <> None ->
      Logic.not_ (Facts.make_in_range ty (exact operation left right))
  | Equal, _ :: _, [ left; right ] when is_float -> make_float_equal left right
  | Less, _ :: _, [ left; right ] when is_float -> make_float_less left right
  | Equal, ty :: _, [ left; right ] when Facts.find_bounds ty <> None -> Logic.equal left right
  | Less, ty :: _, [ left; right ] when Facts.find_bounds ty <> None -> Logic.less left right
  | Fits, [ source; target ], [ value ]
    when Facts.find_bounds source <> None && Facts.find_bounds target <> None ->
      Facts.make_in_range target value
  | Fits, [ source; target ], [ value ]
    when Facts.find_float_format source <> None && Facts.find_bounds target <> None ->
      make_float_fits source target value
  | Convert, [ source; target ], [ value ]
    when Facts.find_bounds source <> None
         && Facts.find_bounds target <> None
         && not (Types.is_builtin Character target) ->
      Logic.ite
        (Facts.make_in_range target value)
        value
        (declare_opaque_operation context frame target Convert [ value ])
  | (Leading_zeros | Trailing_zeros | Count_ones), ty :: _, [ value ]
    when Facts.find_bounds ty <> None -> (
      let low, _ = Option.get (Facts.find_bounds ty) in
      match find_width ty with
      | Some bits ->
          let count counted value =
            let symbol = Logic.Symbol.Bit_count { count = counted; width = bits } in
            Facts.declare context (Logic.Function (symbol, [ Logic.Int ], Logic.Int));
            Logic.Apply (symbol, [ value ])
          in
          let term = count operation value in
          Facts.assume context frame Logic.(less_equal (int 0) term &&& less_equal term (int bits));
          (if Z.equal low Z.zero then
             Contract_axioms.map_each_value context frame value @@ fun frame value ->
             let leading = count Leading_zeros value
             and trailing = count Trailing_zeros value
             and ones = count Count_ones value in
             let power exponent = declare_power context frame (Logic.int 2) exponent in
             let width = Logic.int bits in
             let nonzero = Logic.not_ (Logic.equal value (Logic.int 0)) in
             let below_highest = Logic.subtract width leading in
             List.iter (Facts.assume context frame)
               Logic.
                 [
                   less_equal (int 0) leading
                   &&& less_equal leading width
                   &&& less_equal (int 0) trailing
                   &&& less_equal trailing width
                   &&& less_equal (int 0) ones
                   &&& less_equal ones width;
                   nonzero
                   ==> (less_equal (power (subtract (int (bits - 1)) leading)) value
                       &&& less value (power below_highest));
                   equal (equal ones (int 0)) (equal value (int 0));
                   nonzero ==> less_equal ones below_highest;
                   nonzero
                   &&& equal (add value (int 1)) (power below_highest)
                   ==> equal ones below_highest;
                   nonzero ==> less_equal (add trailing leading) (int (bits - 1));
                   equal value (int 0) ==> (equal trailing width &&& equal leading width);
                 ]);
          term
      | None -> fallback ())
  | _ -> (
      match (operation, types) with
      | (Ieee_equal | Ieee_less), ty :: _ when Facts.find_float_format ty <> None -> (
          match operands with
          | [ left; right ] ->
              Logic.Operation ((if operation = Ieee_equal then Fp_eq else Fp_lt), [ left; right ])
          | _ -> fallback ())
      | (Square_root | Floor | Ceiling | Truncate | Round_to_even), ty :: _
        when Facts.find_float_format ty <> None -> (
          match operands with
          | [ value ] -> (
              match operation with
              | Square_root -> Logic.Operation (Fp_sqrt Nearest_ties_to_even, [ value ])
              | Floor -> Logic.Operation (Fp_round_to_integral Toward_negative, [ value ])
              | Ceiling -> Logic.Operation (Fp_round_to_integral Toward_positive, [ value ])
              | Truncate -> Logic.Operation (Fp_round_to_integral Toward_zero, [ value ])
              | _ -> Logic.Operation (Fp_round_to_integral Nearest_ties_to_even, [ value ]))
          | _ -> fallback ())
      | Fused_multiply_add, ty :: _ when Facts.find_float_format ty <> None -> (
          match operands with
          | [ value; multiplier; addend ] ->
              Logic.Operation (Fp_fma Nearest_ties_to_even, [ value; multiplier; addend ])
          | _ -> fallback ())
      | Is_nan, ty :: _ when Facts.find_float_format ty <> None -> (
          match operands with [ value ] -> is_nan value | _ -> fallback ())
      | From_bits, [ bits; target ] when Facts.find_bounds bits <> None -> (
          match (operands, Facts.find_float_format target, find_width bits) with
          | [ value ], Some (exponent, significand), Some width ->
              Logic.Operation
                ( To_fp { exponent; significand; rounding_mode = None },
                  [ Logic.Operation (Int2bv { width }, [ value ]) ] )
          | _ -> fallback ())
      | To_bits, [ source; bits ] when Facts.find_bounds bits <> None -> (
          match (operands, Facts.find_float_format source, find_width bits) with
          | [ value ], Some (exponent, significand), Some width ->
              let symbol =
                Logic.Symbol.Opaque_operation
                  { operation = To_bits; type_ = bits; integer = Some (width, false) }
              in
              Facts.declare context
                (Logic.Function
                   (symbol, [ Facts.declare_sort context source ], Facts.declare_sort context bits));
              let term = Logic.Apply (symbol, [ value ]) in
              Facts.assume context frame (Facts.make_in_range bits term);
              Facts.assume context frame
                Logic.(
                  not_ (is_nan value)
                  ==> equal
                        (Operation
                           ( To_fp { exponent; significand; rounding_mode = None },
                             [ Operation (Int2bv { width }, [ term ]) ] ))
                        value);
              term
          | _ -> fallback ())
      | Multiply_high, ty :: _ when Facts.find_bounds ty <> None -> (
          match (operands, find_width ty) with
          | [ left; right ], Some bits ->
              Logic.Operation
                (Div, [ Logic.multiply left right; Logic.Integer (Z.shift_left Z.one bits) ])
          | _ -> fallback ())
      | (Rotate_left | Rotate_right | Swap_bytes), ty :: _ when Facts.find_bounds ty <> None ->
          declare_opaque_operation context frame ty operation operands
      | Convert, [ source; target ]
        when Facts.find_float_format source <> None && Facts.find_bounds target <> None -> (
          match operands with
          | [ value ] -> (
              Facts.oblige context frame
                (Facts.locate context frame.source site.origin)
                (Float_conversion { at = Facts.quote frame.source site.origin; target })
                (make_float_fits source target value);
              match (find_width target, Facts.find_bounds target) with
              | Some width, Some (low, _) ->
                  let is_signed = Z.lt low Z.zero in
                  Logic.integer_of_bits ~is_signed ~width
                    (Logic.Operation
                       ( (if is_signed then Fp_to_sbv { width; rounding_mode = Toward_zero }
                          else Fp_to_ubv { width; rounding_mode = Toward_zero }),
                         [ value ] ))
              | _ -> fallback ())
          | _ -> fallback ())
      | Convert, [ source; target ]
        when Facts.find_bounds source <> None && Facts.find_float_format target <> None -> (
          match (operands, Facts.find_float_format target) with
          | [ value ], Some format -> make_float_of_integer format Nearest_ties_to_even value
          | _ -> fallback ())
      | Convert, [ source; target ]
        when Facts.find_float_format source <> None && Facts.find_float_format target <> None -> (
          match (operands, Facts.find_float_format target) with
          | [ value ], Some (exponent, significand) ->
              Logic.Operation
                ( To_fp { exponent; significand; rounding_mode = Some Nearest_ties_to_even },
                  [ value ] )
          | _ -> fallback ())
      | Convert, [ _; target ] when Types.is_builtin Character target -> (
          match operands with
          | [ value ] ->
              Facts.oblige context frame
                (Facts.locate context frame.source site.origin)
                (Not_a_scalar_value { at = Facts.quote frame.source site.origin })
                (Facts.make_in_range target value);
              value
          | _ -> fallback ())
      | _ -> fallback ())
