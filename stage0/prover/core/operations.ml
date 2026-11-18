let make_float_operation name left right =
  Logic.Operation (name, [ Logic.Operation ("RNE", []); left; right ])

let is_nan value = Logic.Operation ("fp.isNaN", [ value ])

let round_toward_zero value =
  Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTZ", []); value ])

let make_float_of_integer (exponent, significand) rounding integer =
  Logic.Operation
    ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
      [ Logic.Operation (rounding, []); Logic.Operation ("to_real", [ integer ]) ] )

let make_float_equal left right =
  Logic.(Operation ("fp.eq", [ left; right ]) ||| (is_nan left &&& is_nan right))

let make_float_less left right =
  Logic.(not_ (is_nan left) &&& is_nan right ||| Operation ("fp.lt", [ left; right ]))

let compare_terms ty (compared : Core.comparison) left right =
  if Facts.find_float_format ty <> None then
    match compared with
    | Equal -> make_float_equal left right
    | Not_equal -> Logic.not_ (make_float_equal left right)
    | Less -> make_float_less left right
    | Less_equal -> Logic.( ||| ) (make_float_less left right) (make_float_equal left right)
    | Greater -> make_float_less right left
    | Greater_equal -> Logic.( ||| ) (make_float_less right left) (make_float_equal left right)
  else
    match Contracts.find_comparison_operator compared with
    | Some _ when compared = Equal -> Logic.equal left right
    | Some symbol -> Logic.Operation (symbol, [ left; right ])
    | None -> Logic.not_ (Logic.equal left right)

let check_widened location ~is_written actual expected =
  match (actual, expected) with
  | Types.Function actual, Types.Function expected
    when (not is_written)
         && not (List.for_all (fun cost -> List.mem cost actual.costs) expected.costs) ->
      Facts.raise_unsupported location "a function value's costs"
  | _ -> ()

let find_parameter_spelling (context : State.context) (frame : State.frame) term =
  if
    frame.source.key = Some context.definition.home
    && (not (Logic.has_quantifier term))
    &&
    match Logic.list_free_constants term with
    | _ :: _ as names -> List.for_all (fun name -> List.mem name context.entry.parameters) names
    | [] -> false
  then Facts.show_truss_value context term
  else None

let find_integer_limits ty =
  if Types.is_builtin Character ty then None
  else Option.map (fun (low, high) -> (Types.show ty, low, high)) (Facts.find_bounds ty)

let make_range_fix context frame ty term =
  match (find_integer_limits ty, find_parameter_spelling context frame term) with
  | Some (name, low, _), Some text ->
      let least = if Z.sign low = 0 then "0" else name ^ ".minimum" in
      Facts.add_requires context frame
        [ Text (Printf.sprintf "%s <= %s && %s <= %s.maximum" least text text name) ]
  | _ -> []

let convert_from_integer context frame (site : Invocation.site) term =
  let ty = Facts.substitute_type context frame site.type_ in
  Facts.oblige context frame Out_of_range
    ~fixes:(make_range_fix context frame ty term)
    (Facts.locate context frame.source site.origin)
    [
      Text "`";
      Facts.quote frame.source site.origin;
      Text (Printf.sprintf "` may not fit in `%s`." (Types.show ty));
    ]
    (Facts.make_in_range ty term);
  term

let spend (context : State.context) (frame : State.frame) (amount_of : Costs.counter -> Logic.term)
    =
  if context.scope.counters = [] then frame
  else
    {
      frame with
      State.spent =
        List.map
          (fun (counter, term) ->
            if List.mem counter context.scope.counters then
              (counter, Costs.plus term (amount_of counter))
            else (counter, term))
          frame.spent;
    }

let declare_unknown_amount context frame (counter : Costs.counter) =
  let amount = Facts.declare_fresh context frame "spent" Logic.Int in
  Facts.assume context frame
    (Logic.Operation ("<=", [ Costs.least_amount counter.resource; amount ]));
  amount

let convert_to_any context frame (site : Invocation.site) =
  let frame =
    spend context frame (fun (counter : Costs.counter) ->
        match (counter.resource, counter.counting) with
        | Metric Allocations, _ -> Logic.int 1
        | Metric Allocated_bytes, Units -> Logic.int 1
        | Metric Allocated_bytes, (At_most | Exactly) ->
            declare_unknown_amount context frame counter
        | (Metric Time | Calls _), _ -> Costs.zero)
  in
  (frame, Facts.arrive context frame "any" (Facts.substitute_type context frame site.type_))

let compute_current_bounds (context : State.context) : Interface.Impls.bounds =
  let list_impl_generics path =
    match Interface.Definition.find_impl_interface context.definition.lookups.interface path with
    | Some interface -> interface.impl_generics
    | None -> []
  in
  let generics =
    match context.definition.current with
    | Method { owner; _ } -> (
        list_impl_generics owner
        @
        match
          Interface.Impls.read_signature context.definition.lookups.interface
            context.definition.current
        with
        | Some signature -> signature.generics
        | None -> [])
    | current -> (
        match Interface.Impls.read_signature context.definition.lookups.interface current with
        | Some signature -> signature.generics
        | None -> list_impl_generics current)
  in
  fun parameter -> Types.list_bounds generics parameter

let find_concrete_impl (context : State.context) (trait : Types.trait_reference) (ty : Types.ty) =
  match ty with
  | Types.Named { path; _ } ->
      let is_own impl =
        Path.equal impl context.definition.current
        ||
        match context.definition.current with
        | Method { owner; _ } -> Path.equal owner impl
        | _ -> false
      in
      let list_bounds = compute_current_bounds context in
      let packages =
        List.sort_uniq compare
          [ Path.locate_package context.definition.current; Path.locate_package path ]
      in
      List.find_map
        (fun package ->
          List.find_map
            (fun impl ->
              let interface =
                Interface.Definition.read_impl_interface context.definition.lookups.interface impl
              in
              let variables =
                List.map (fun (generic : Types.generic) -> generic.generic) interface.impl_generics
              in
              match
                Option.bind
                  (Interface.Impls.match_type ~variables Types.no_substitution interface.for_type ty)
                  (fun arguments ->
                    Interface.Impls.match_arguments ~variables arguments
                      interface.implements.trait_arguments trait.trait_arguments)
              with
              | Some arguments
                when is_own impl
                     || List.for_all
                          (fun (argument, bound) ->
                            Option.is_some
                              (Interface.Impls.find_evidence context.definition.lookups.interface
                                 ~list_bounds argument bound))
                          (Interface.Impls.list_required_bounds interface.impl_generics arguments)
                ->
                  Some (impl, arguments)
              | _ -> None)
            (Interface.Impls.list_impls_of_trait_for_type context.definition.lookups.interface
               ~trait:trait.trait ~type_:path package))
        packages
  | _ -> None

let find_written_equal context ty left right =
  match
    find_concrete_impl context
      { trait = Facts.equal_trait; trait_arguments = []; associated = [] }
      ty
  with
  | Some (((Impl _ : Path.t) as impl), substitution) -> (
      let evidence : Core.evidence = Impl { impl; substitution } in
      match
        Contracts.find_method_contract context.definition.lookups
          { trait = Facts.equal_trait; trait_arguments = []; associated = [] }
          "equal" Read evidence
      with
      | Some contract when contract.is_logic_function ->
          let symbol =
            Logic.Symbol.Function
              {
                callee = Path.Method { owner = impl; name = "equal"; receiver = Read };
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
         && (not (List.mem equal context.assertions.equalities))
         && not (Logic.mentions frame.bound equal) ->
      context.assertions.equalities <- equal :: context.assertions.equalities;
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
  | Some (name, low, high) -> (
      let is_unsigned = Z.sign low = 0 in
      let bound_on_left =
        match (right, find_parameter_spelling context frame left) with
        | Logic.Integer limit, Some text -> (
            let magnitude = Z.to_string (Z.abs limit) in
            let spell_clause relation bound spelled =
              if Z.leq low bound && Z.leq bound high then
                Some (Printf.sprintf "%s %s %s" text relation spelled)
              else None
            in
            match operation with
            | Add when Z.sign limit > 0 ->
                spell_clause "<=" (Z.sub high limit) (name ^ ".maximum - " ^ magnitude)
            | Add when Z.sign limit < 0 ->
                spell_clause ">=" (Z.sub low limit) (name ^ ".minimum + " ^ magnitude)
            | Subtract when Z.sign limit > 0 && is_unsigned -> spell_clause ">=" limit magnitude
            | Subtract when Z.sign limit > 0 ->
                spell_clause ">=" (Z.add low limit) (name ^ ".minimum + " ^ magnitude)
            | Subtract when Z.sign limit < 0 ->
                spell_clause "<=" (Z.add high limit) (name ^ ".maximum - " ^ magnitude)
            | Multiply when Z.sign limit > 0 && is_unsigned ->
                spell_clause "<=" (Z.div high limit) (name ^ ".maximum / " ^ magnitude)
            | _ -> None)
        | _ -> None
      in
      match (bound_on_left, operation) with
      | Some required, _ -> Facts.add_requires context frame [ Text required ]
      | None, (Add | Multiply) when is_unsigned -> (
          match find_parameter_spelling context frame exact with
          | Some text ->
              Facts.add_requires context frame
                [ Text (Printf.sprintf "%s <= %s.maximum" text name) ]
          | None -> [])
      | None, Subtract when is_unsigned -> []
      | None, _ -> make_range_fix context frame ty exact)

let make_division_overflow_fix context frame ty left right =
  match (find_integer_limits ty, find_parameter_spelling context frame left) with
  | Some (name, _, _), Some dividend -> (
      let dividend_not_minimum = Printf.sprintf "%s != %s.minimum" dividend name in
      match right with
      | Logic.Integer divisor when Z.equal divisor Z.minus_one ->
          Facts.add_requires context frame [ Text dividend_not_minimum ]
      | _ -> (
          match find_parameter_spelling context frame right with
          | Some divisor ->
              Facts.add_requires context frame
                [ Text (Printf.sprintf "%s || %s != -1" dividend_not_minimum divisor) ]
          | None -> []))
  | _ -> []

let make_negation_fix context frame ty inner =
  match (find_integer_limits ty, find_parameter_spelling context frame inner) with
  | Some (name, _, _), Some text ->
      Facts.add_requires context frame [ Text (Printf.sprintf "%s != %s.minimum" text name) ]
  | _ -> []

let translate_arithmetic context (frame : State.frame) (site : Invocation.site) ty
    (operation : Intrinsic.scalar) left right =
  let source = frame.source in
  let location = Facts.locate context frame.source site.origin in
  let exact, is_division =
    match operation with
    | Add -> (Logic.Operation ("+", [ left; right ]), false)
    | Subtract -> (Logic.Operation ("-", [ left; right ]), false)
    | Multiply -> (Logic.Operation ("*", [ left; right ]), false)
    | Divide -> (Logic.truncated_divide left right, true)
    | Remainder -> (Logic.truncated_remainder left right, true)
    | _ -> Facts.raise_bug "`%s` is not arithmetic" (Intrinsic.show_operation (Scalar operation))
  in
  if is_division then
    Facts.oblige context frame Division location
      ~fixes:
        (match find_parameter_spelling context frame right with
        | Some text -> Facts.add_requires context frame [ Text (text ^ " != 0") ]
        | None -> [])
      [ Text "The divisor in `"; Facts.quote source site.origin; Text "` may be zero." ]
      (Logic.not_ (Logic.equal right (Logic.int 0)));
  (match Facts.find_bounds ty with
  | Some (low, _) when is_division ->
      if Z.sign low < 0 then
        Facts.oblige context frame Overflow location
          ~fixes:(make_division_overflow_fix context frame ty left right)
          [
            Text "`";
            Facts.quote source site.origin;
            Text (Printf.sprintf "` may overflow `%s`: the least value over -1." (Types.show ty));
          ]
          (Logic.not_ Logic.(equal left (Integer low) &&& equal right (int (-1))))
  | Some (low, high) ->
      let unsigned = Z.sign low = 0 && not (Types.is_builtin Character ty) in
      Facts.oblige context frame Overflow location
        ~fixes:(make_overflow_fix context frame ty operation left right exact)
        [
          Text "`";
          Facts.quote source site.origin;
          Text (Printf.sprintf "` may overflow `%s`." (Types.show ty));
        ]
        (match operation with
        | (Add | Multiply) when unsigned -> Logic.Operation ("<=", [ exact; Integer high ])
        | Subtract when unsigned -> Logic.Operation ("<=", [ Integer low; exact ])
        | _ -> Facts.make_in_range ty exact)
  | None -> ());
  exact

let make_float_fits source target value =
  match (Facts.find_float_format source, Facts.find_bounds target) with
  | Some format, Some (low, high) ->
      let cut = round_toward_zero value in
      Logic.(
        Operation ("fp.leq", [ make_float_of_integer format "RTP" (Integer low); cut ])
        &&& Operation ("fp.leq", [ cut; make_float_of_integer format "RTN" (Integer high) ]))
  | _ ->
      Facts.raise_bug "a float check from `%s` to `%s` needs a float source and a bounded target"
        (Types.show source) (Types.show target)

let find_innermost_axiom (frame : State.frame) term =
  match frame.open_axioms with
  | axiom :: _
    when let named = List.filter (fun name -> Logic.mentions [ name ] term) frame.bound in
         named <> [] && List.for_all (fun name -> List.mem name axiom.parameters) named ->
      Some axiom
  | _ -> None

let rec map_each_value (frame : State.frame) value make =
  if not (Logic.mentions frame.bound value) then make frame value
  else
    match find_innermost_axiom frame value with
    | Some axiom ->
        axiom.at_calls <-
          (fun frame substitute -> map_each_value frame (substitute value) make) :: axiom.at_calls
    | None -> ()

let make_power_facts base exponent =
  let power exponent = Logic.Apply (Logic.Symbol.Cost_power, [ base; exponent ]) in
  let previous = Logic.Operation ("-", [ exponent; Logic.int 1 ]) in
  ( Logic.
      [
        equal exponent (int 0) ==> equal (power exponent) (int 1);
        Operation (">=", [ base; int 1 ])
        &&& Operation (">=", [ exponent; int 0 ])
        ==> Operation (">=", [ power exponent; int 1 ]);
        Operation (">=", [ base; int 2 ])
        &&& Operation (">=", [ exponent; int 0 ])
        ==> Operation (">", [ power exponent; exponent ]);
      ],
    ( Logic.(
        Operation (">=", [ exponent; int 1 ])
        ==> equal (power exponent) (Operation ("*", [ base; power previous ]))),
      previous ) )

let make_power_order base left right =
  let power exponent = Logic.Apply (Logic.Symbol.Cost_power, [ base; exponent ]) in
  Logic.(
    Operation (">=", [ base; int 1 ])
    ==> (Operation ("<=", [ left; right ])
        ==> Operation ("<=", [ power left; power right ])
        &&& (Operation ("<=", [ right; left ]) ==> Operation ("<=", [ power right; power left ]))))

let declare_power context frame base exponent =
  Facts.declare context
    (Logic.Function (Logic.Symbol.Cost_power, [ Logic.Int; Logic.Int ], Logic.Int));
  let add exponent =
    if not (List.mem (base, exponent) context.assertions.powers) then begin
      List.iter
        (fun (other_base, other) ->
          if other_base = base then
            Facts.add_frame_fact context frame (make_power_order base exponent other))
        context.assertions.powers;
      context.assertions.powers <- (base, exponent) :: context.assertions.powers;
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
           (Logic.Apply (Logic.Symbol.Cost_power, [ base; exponent ]))
           (Logic.Integer (Z.pow base_value (Z.to_int exponent_value))))
  | _ -> ());
  Logic.Apply (Logic.Symbol.Cost_power, [ base; exponent ])

let translate_primitive_operation context (frame : State.frame) ~(site : Invocation.site)
    (operation : Intrinsic.scalar) types operands ~(arguments : Core.origin option list) ~fallback =
  let source = frame.source in
  let location = Facts.locate context frame.source site.origin in
  (match List.find_opt (function Types.Parameter _ | Projection _ -> true | _ -> false) types with
  | Some parameter ->
      Facts.raise_unsupported location "`intrinsic::%s` at the type parameter `%s`"
        (Intrinsic.show_operation (Scalar operation))
        (Types.show parameter)
  | None -> ());
  let find_argument index = Option.join (List.nth_opt arguments index) in
  let is_float = match types with ty :: _ -> Facts.find_float_format ty <> None | [] -> false in
  let exact operation left right =
    match (operation : Intrinsic.scalar) with
    | Wrapping_add | Add_overflows -> Logic.Operation ("+", [ left; right ])
    | Wrapping_subtract | Subtract_overflows -> Logic.Operation ("-", [ left; right ])
    | Wrapping_multiply | Multiply_overflows -> Logic.Operation ("*", [ left; right ])
    | _ ->
        Facts.raise_bug "`%s` has no exact integer result"
          (Intrinsic.show_operation (Scalar operation))
  in
  match (operation, types, operands) with
  | Add, _ :: _, [ left; right ] when is_float -> make_float_operation "fp.add" left right
  | Subtract, _ :: _, [ left; right ] when is_float -> make_float_operation "fp.sub" left right
  | Multiply, _ :: _, [ left; right ] when is_float -> make_float_operation "fp.mul" left right
  | Divide, _ :: _, [ left; right ] when is_float -> make_float_operation "fp.div" left right
  | Negate, _ :: _, [ value ] when is_float -> Logic.Operation ("fp.neg", [ value ])
  | (Add | Subtract | Multiply | Divide | Remainder), ty :: _, [ left; right ] when not is_float ->
      let result = translate_arithmetic context frame site ty operation left right in
      if Facts.find_bounds ty <> None then
        Facts.assume context frame (Facts.make_in_range ty result);
      result
  | Negate, ty :: _, [ inner ] when not is_float ->
      let negated = Logic.Operation ("-", [ inner ]) in
      if Facts.find_bounds ty <> None then
        Facts.oblige context frame Overflow location
          ~fixes:(make_negation_fix context frame ty inner)
          [
            Text "`";
            Facts.quote source site.origin;
            Text (Printf.sprintf "` may overflow `%s`." (Types.show ty));
          ]
          (Facts.make_in_range ty negated)
      else if ty <> Types.Integer then
        Facts.raise_unsupported location "negating a value of `%s`" (Types.show ty);
      negated
  | Complement, ty :: _, [ inner ] -> declare_opaque_operation context frame ty Complement [ inner ]
  | (Shift_left | Shift_right), ty :: _, [ left; right ] ->
      (match find_width ty with
      | Some bits ->
          let at_amount, text, fixes =
            match find_argument 1 with
            | Some amount ->
                ( Facts.locate context frame.source amount,
                  [ Obligation.Text "The shift amount `"; Facts.quote source amount; Text "`" ],
                  match find_parameter_spelling context frame right with
                  | Some text ->
                      Facts.add_requires context frame [ Text (Printf.sprintf "%s < %d" text bits) ]
                  | None -> [] )
            | None ->
                ( location,
                  [ Text "The shift amount in `"; Facts.quote source site.origin; Text "`" ],
                  [] )
          in
          Facts.oblige context frame Shift at_amount ~fixes
            (text @ [ Text (Printf.sprintf " may not be less than %d." bits) ])
            Logic.(Operation ("<", [ right; int bits ]))
      | None -> Facts.raise_unsupported location "a shift of `%s`" (Types.show ty));
      let shifted = declare_opaque_operation context frame ty operation [ left; right ] in
      (match (Facts.find_bounds ty, find_width ty) with
      | Some (low, high), Some bits
        when Z.equal low Z.zero && not (Logic.mentions frame.bound right) ->
          let scale = declare_power context frame (Logic.int 2) right in
          Facts.assume context frame
            Logic.(
              Operation ("<=", [ int 0; right ])
              &&& Operation ("<", [ right; int bits ])
              ==> (Operation ("<=", [ int 1; scale ])
                  &&& Operation ("<=", [ scale; Integer (Z.shift_left Z.one (bits - 1)) ])));
          Facts.assume context frame
            (match operation with
            | Shift_left ->
                Logic.(
                  Operation ("<=", [ Operation ("*", [ left; scale ]); Integer high ])
                  ==> equal shifted (Operation ("*", [ left; scale ])))
            | _ -> Logic.equal shifted (Logic.truncated_divide left scale))
      | _ -> ());
      shifted
  | (Bit_and | Bit_or | Bit_xor), ty :: _, [ left; right ] ->
      let term = declare_opaque_operation context frame ty operation [ left; right ] in
      (match Facts.find_bounds ty with
      | Some (low, _) when Z.sign low < 0 && operation = Bit_and ->
          let masked_by operand =
            Logic.(
              Operation ("<=", [ int 0; operand ])
              ==> (Operation ("<=", [ int 0; term ]) &&& Operation ("<=", [ term; operand ])))
          in
          Facts.assume context frame Logic.(masked_by left &&& masked_by right)
      | Some (low, _) when Z.equal low Z.zero -> (
          let at_most bound = Logic.Operation ("<=", [ term; bound ]) in
          match operation with
          | Bit_and -> Facts.assume context frame Logic.(at_most left &&& at_most right)
          | _ ->
              let sum = Logic.Operation ("+", [ left; right ]) in
              if operation = Bit_or then
                Facts.assume context frame
                  Logic.(Operation ("<=", [ left; term ]) &&& Operation ("<=", [ right; term ]));
              Facts.assume context frame (at_most sum);
              Facts.declare context
                (Logic.Function (Logic.Symbol.Cost_power, [ Logic.Int; Logic.Int ], Logic.Int));
              let exponent = Logic.Symbol (Facts.make_variable "exponent") in
              let below value =
                Logic.Operation
                  ("<", [ value; Logic.Apply (Logic.Symbol.Cost_power, [ Logic.int 2; exponent ]) ])
              in
              Facts.assume context frame
                (Logic.forall
                   ( [ (Facts.make_variable "exponent", Logic.Int) ],
                     Logic.(
                       Operation ("<=", [ int 0; exponent ])
                       &&& below left &&& below right ==> below term) )))
      | _ -> ());
      term
  | (Wrapping_add | Wrapping_subtract | Wrapping_multiply), ty :: _, [ left; right ]
    when Facts.find_bounds ty <> None ->
      let low, high = Option.get (Facts.find_bounds ty) in
      let modulus = Z.succ (Z.sub high low) in
      Logic.Operation
        ( "+",
          [
            Logic.Integer low;
            Logic.Operation
              ( "mod",
                [
                  Logic.Operation ("-", [ exact operation left right; Logic.Integer low ]);
                  Logic.Integer modulus;
                ] );
          ] )
  | (Add_overflows | Subtract_overflows | Multiply_overflows), ty :: _, [ left; right ]
    when Facts.find_bounds ty <> None ->
      Logic.not_ (Facts.make_in_range ty (exact operation left right))
  | Equal, _ :: _, [ left; right ] when is_float -> make_float_equal left right
  | Less, _ :: _, [ left; right ] when is_float -> make_float_less left right
  | Equal, ty :: _, [ left; right ] when Facts.find_bounds ty <> None -> Logic.equal left right
  | Less, ty :: _, [ left; right ] when Facts.find_bounds ty <> None ->
      Logic.Operation ("<", [ left; right ])
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
          Facts.assume context frame
            Logic.(Operation ("<=", [ int 0; term ]) &&& Operation ("<=", [ term; int bits ]));
          (if Z.equal low Z.zero then
             map_each_value frame value @@ fun frame value ->
             let leading = count Leading_zeros value
             and trailing = count Trailing_zeros value
             and ones = count Count_ones value in
             let power exponent = declare_power context frame (Logic.int 2) exponent in
             let width = Logic.int bits in
             let nonzero = Logic.not_ (Logic.equal value (Logic.int 0)) in
             let below_highest = Logic.Operation ("-", [ width; leading ]) in
             List.iter (Facts.assume context frame)
               Logic.
                 [
                   Operation ("<=", [ int 0; leading ])
                   &&& Operation ("<=", [ leading; width ])
                   &&& Operation ("<=", [ int 0; trailing ])
                   &&& Operation ("<=", [ trailing; width ])
                   &&& Operation ("<=", [ int 0; ones ])
                   &&& Operation ("<=", [ ones; width ]);
                   nonzero
                   ==> (Operation
                          ("<=", [ power (Operation ("-", [ int (bits - 1); leading ])); value ])
                       &&& Operation ("<", [ value; power below_highest ]));
                   equal (equal ones (int 0)) (equal value (int 0));
                   nonzero ==> Operation ("<=", [ ones; below_highest ]);
                   nonzero
                   &&& equal (Operation ("+", [ value; int 1 ])) (power below_highest)
                   ==> equal ones below_highest;
                   nonzero
                   ==> Operation ("<=", [ Operation ("+", [ trailing; leading ]); int (bits - 1) ]);
                   equal value (int 0) ==> (equal trailing width &&& equal leading width);
                 ]);
          term
      | None -> fallback ())
  | _ -> (
      match (operation, types) with
      | (Ieee_equal | Ieee_less), ty :: _ when Facts.find_float_format ty <> None -> (
          match operands with
          | [ left; right ] ->
              Logic.Operation
                ((if operation = Ieee_equal then "fp.eq" else "fp.lt"), [ left; right ])
          | _ -> fallback ())
      | (Square_root | Floor | Ceiling | Truncate | Round_to_even), ty :: _
        when Facts.find_float_format ty <> None -> (
          match operands with
          | [ value ] -> (
              match operation with
              | Square_root -> Logic.Operation ("fp.sqrt", [ Logic.Operation ("RNE", []); value ])
              | Floor ->
                  Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTN", []); value ])
              | Ceiling ->
                  Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTP", []); value ])
              | Truncate -> round_toward_zero value
              | _ -> Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RNE", []); value ]))
          | _ -> fallback ())
      | Fused_multiply_add, ty :: _ when Facts.find_float_format ty <> None -> (
          match operands with
          | [ value; multiplier; addend ] ->
              Logic.Operation ("fp.fma", [ Logic.Operation ("RNE", []); value; multiplier; addend ])
          | _ -> fallback ())
      | Is_nan, ty :: _ when Facts.find_float_format ty <> None -> (
          match operands with [ value ] -> is_nan value | _ -> fallback ())
      | From_bits, [ bits; target ] when Facts.find_bounds bits <> None -> (
          match (operands, Facts.find_float_format target, find_width bits) with
          | [ value ], Some (exponent, significand), Some width ->
              Logic.Operation
                ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
                  [ Logic.Operation (Printf.sprintf "(_ int2bv %d)" width, [ value ]) ] )
          | _ -> fallback ())
      | To_bits, [ source; bits ] when Facts.find_bounds bits <> None -> (
          match (operands, Facts.find_float_format source, find_width bits) with
          | [ value ], Some (exponent, significand), Some width ->
              Facts.assume context frame
                Logic.(
                  not_ (is_nan value)
                  ==> equal
                        (Operation
                           ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
                             [ Operation (Printf.sprintf "(_ int2bv %d)" width, [ fallback () ]) ]
                           ))
                        value);
              fallback ()
          | _ -> fallback ())
      | Multiply_high, ty :: _ when Facts.find_bounds ty <> None -> (
          match (operands, find_width ty) with
          | [ left; right ], Some bits ->
              Logic.Operation
                ( "div",
                  [
                    Logic.Operation ("*", [ left; right ]); Logic.Integer (Z.shift_left Z.one bits);
                  ] )
          | _ -> fallback ())
      | (Rotate_left | Rotate_right | Swap_bytes), ty :: _ when Facts.find_bounds ty <> None ->
          declare_opaque_operation context frame ty operation operands
      | Convert, [ source; target ]
        when Facts.find_float_format source <> None && Facts.find_bounds target <> None -> (
          match operands with
          | [ value ] -> (
              Facts.oblige context frame Requires
                (Facts.locate context frame.source site.origin)
                [
                  Text "`";
                  Facts.quote frame.source site.origin;
                  Text
                    (Printf.sprintf
                       "` may not fit `%s`: it must be a number that, cut toward zero, is in its \
                        range."
                       (Types.show target));
                ]
                (make_float_fits source target value);
              match (find_width target, Facts.find_bounds target) with
              | Some width, Some (low, _) ->
                  let is_signed = Z.lt low Z.zero in
                  Logic.integer_of_bits ~is_signed ~width
                    (Logic.Operation
                       ( Printf.sprintf "(_ fp.to_%cbv %d)" (if is_signed then 's' else 'u') width,
                         [ Logic.Operation ("RTZ", []); value ] ))
              | _ -> fallback ())
          | _ -> fallback ())
      | Convert, [ source; target ]
        when Facts.find_bounds source <> None && Facts.find_float_format target <> None -> (
          match (operands, Facts.find_float_format target) with
          | [ value ], Some format -> make_float_of_integer format "RNE" value
          | _ -> fallback ())
      | Convert, [ source; target ]
        when Facts.find_float_format source <> None && Facts.find_float_format target <> None -> (
          match (operands, Facts.find_float_format target) with
          | [ value ], Some (exponent, significand) ->
              Logic.Operation
                ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
                  [ Logic.Operation ("RNE", []); value ] )
          | _ -> fallback ())
      | Convert, [ _; target ] when Types.is_builtin Character target -> (
          match operands with
          | [ value ] ->
              Facts.oblige context frame Requires
                (Facts.locate context frame.source site.origin)
                [
                  Text "`";
                  Facts.quote frame.source site.origin;
                  Text "` may not be a Unicode scalar value, which a `Character` must be.";
                ]
                (Facts.make_in_range target value);
              value
          | _ -> fallback ())
      | _ -> fallback ())
