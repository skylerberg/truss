open Core
open State
open Facts
open Contracts

let float_operation name left right =
  Logic.Operation (name, [ Logic.Operation ("RNE", []); left; right ])

let is_nan value = Logic.Operation ("fp.isNaN", [ value ])

let truncated value =
  Logic.Operation
    ( "fp.to_real",
      [ Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTZ", []); value ]) ] )

let float_equal left right =
  Logic.(Operation ("fp.eq", [ left; right ]) ||| (is_nan left &&& is_nan right))

let float_less left right =
  Logic.(not_ (is_nan left) &&& is_nan right ||| Operation ("fp.lt", [ left; right ]))

let compared_terms ty (compared : comparison) left right =
  if float_format ty <> None then
    match compared with
    | Equal -> float_equal left right
    | Not_equal -> Logic.not_ (float_equal left right)
    | Less -> float_less left right
    | Less_equal -> Logic.( ||| ) (float_less left right) (float_equal left right)
    | Greater -> float_less right left
    | Greater_equal -> Logic.( ||| ) (float_less right left) (float_equal left right)
  else
    match comparison compared with
    | Some _ when compared = Equal -> Logic.equal left right
    | Some symbol -> Logic.Operation (symbol, [ left; right ])
    | None -> Logic.not_ (Logic.equal left right)

let check_widened span ~is_written actual expected =
  match (actual, expected) with
  | Types.Function actual, Types.Function expected
    when (not is_written)
         && not (List.for_all (fun cost -> List.mem cost actual.costs) expected.costs) ->
      unsupported span "a function value's costs"
  | _ -> ()

let from_integer context frame (site : Invocation.site) term =
  let ty = substituted context frame site.type_ in
  oblige context frame Out_of_range
    (span_of frame.source site.origin)
    (Printf.sprintf "`%s` may not fit in `%s`." (quote frame.source site.origin) (Types.show ty))
    (in_range ty term);
  term

let spend context frame (amount : Costs.counter -> Logic.term) =
  if context.counters = [] then frame
  else
    {
      frame with
      spent =
        List.map
          (fun (counter, term) ->
            if List.mem counter context.counters then (counter, Costs.plus term (amount counter))
            else (counter, term))
          frame.spent;
    }

let unknown_amount context frame (counter : Costs.counter) =
  let amount = fresh context frame "spent" Logic.Int in
  let least = match counter.resource with Time -> 1 | _ -> 0 in
  assume context frame (Logic.Operation ("<=", [ Logic.int least; amount ]));
  amount

let to_any context frame (site : Invocation.site) =
  let frame =
    spend context frame (fun (counter : Costs.counter) ->
        match (counter.resource, counter.counting) with
        | Allocations, _ -> Logic.int 1
        | Allocated_bytes, Units -> Logic.int 1
        | Allocated_bytes, (At_most | Exactly) -> unknown_amount context frame counter
        | (Time | Calls _), _ -> Costs.zero)
  in
  (frame, arrive context frame "any" (substituted context frame site.type_))

let current_bounds context : Interface.Impls.bounds =
  let impl_generics path =
    match Interface.Impls.impl_interface context.lookups.interface path with
    | Some interface -> interface.impl_generics
    | None -> []
  in
  let generics =
    match context.current with
    | Method { owner; _ } -> (
        impl_generics owner
        @
        match Interface.Impls.signature context.lookups.interface context.current with
        | Some signature -> signature.generics
        | None -> [])
    | current -> (
        match Interface.Impls.signature context.lookups.interface current with
        | Some signature -> signature.generics
        | None -> impl_generics current)
  in
  fun parameter -> Types.bounds_of generics parameter

let concrete_impl context (trait : Types.trait_reference) (ty : Types.ty) =
  match ty with
  | Types.Named { path; _ } ->
      let own impl =
        Path.equal impl context.current
        || match context.current with Method { owner; _ } -> Path.equal owner impl | _ -> false
      in
      let bounds = current_bounds context in
      let packages = List.sort_uniq compare [ Path.package context.current; Path.package path ] in
      List.find_map
        (fun package ->
          List.find_map
            (fun impl ->
              match Interface.Impls.impl_interface context.lookups.interface impl with
              | Some interface -> (
                  let variables =
                    List.map
                      (fun (generic : Types.generic) -> generic.generic)
                      interface.impl_generics
                  in
                  match
                    Option.bind (Interface.Impls.match_type ~variables [] interface.for_type ty)
                      (fun arguments ->
                        Interface.Impls.match_arguments ~variables arguments
                          interface.implements.trait_arguments trait.trait_arguments)
                  with
                  | Some arguments
                    when own impl
                         || List.for_all
                              (fun (argument, bound) ->
                                Option.is_some
                                  (Interface.Impls.implements context.lookups.interface ~bounds
                                     argument bound))
                              (Interface.Impls.required interface.impl_generics arguments) ->
                      Some (impl, arguments)
                  | _ -> None)
              | None -> None)
            (Interface.Impls.impls_in context.lookups.interface ~trait:trait.trait ~type_:path
               package))
        packages
  | _ -> None

let written_equal context ty left right =
  match concrete_impl context { trait = equal_trait; trait_arguments = []; associated = [] } ty with
  | Some (((Impl _ : Path.t) as impl), arguments) -> (
      let evidence : evidence = Impl { impl; arguments } in
      match
        method_contract context.lookups
          { trait = equal_trait; trait_arguments = []; associated = [] }
          "equal" Read evidence
      with
      | Some contract when contract.is_logic_function ->
          let symbol =
            Symbol.Function
              {
                callee = Path.Method { owner = impl; name = "equal"; receiver = Read };
                instance = [ Types.Type ty ];
              }
          in
          let sort = sort_of context ty in
          declare context (Logic.Function (symbol, [ sort; sort ], Logic.Bool));
          Some (Logic.Apply (symbol, [ left; right ]))
      | _ -> None)
  | _ -> None

let derived_equal context frame (ty : Types.ty) left right =
  let sort = sort_of context ty in
  let symbol = Symbol.Equal ty in
  declare context (Logic.Function (symbol, [ sort; sort ], Logic.Bool));
  let equal = Logic.Apply (symbol, [ left; right ]) in
  (match (visible_type context ty, constructors context ty) with
  | Some (interface, _), Some shape
    when List.exists is_standard_equal interface.derives
         && (not (List.mem equal context.equalities))
         && not (Logic.mentions frame.bound equal) ->
      context.equalities <- equal :: context.equalities;
      let fields_equal (variant, fields) =
        Logic.conjunction
          (List.map
             (fun (field, field_type) ->
               let selector = selector_name ty variant field in
               let left = Logic.Apply (selector, [ left ])
               and right = Logic.Apply (selector, [ right ]) in
               if structural context field_type then Logic.equal left right
               else if float_format field_type <> None then float_equal left right
               else
                 match written_equal context field_type left right with
                 | Some equal -> equal
                 | None ->
                     let symbol = Symbol.Equal field_type in
                     declare context
                       (Logic.Function
                          ( symbol,
                            [ sort_of context field_type; sort_of context field_type ],
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
                   let is_variant term = Logic.Is (constructor_name ty variant, term) in
                   Logic.(is_variant left &&& is_variant right &&& fields_equal one))
                 variants)
      in
      fact context frame (Logic.equal equal defined)
  | _ -> ());
  equal

let equal_of context frame (ty : Types.ty) left right =
  if structural context ty then Logic.equal left right
  else if float_format ty <> None then float_equal left right
  else
    match written_equal context ty left right with
    | Some equal -> equal
    | None -> derived_equal context frame ty left right

let width (ty : Types.ty) = Option.map fst (Types.integer_bits ty)

let opaque_operation context frame ty operation arguments =
  let sorts = List.map (fun _ -> Logic.Int) arguments in
  let integer =
    Option.map
      (fun bits -> (bits, match bounds ty with Some (low, _) -> Z.sign low < 0 | None -> false))
      (width ty)
  in
  let symbol = Symbol.Opaque_operation { operation; type_ = ty; integer } in
  declare context (Logic.Function (symbol, sorts, sort_of context ty));
  let term = Logic.Apply (symbol, arguments) in
  assume context frame (in_range ty term);
  term

let parameter_operand context frame (operand : Core.origin) term =
  if
    frame.source.key = Some context.home
    && (not (Logic.has_quantifier term))
    &&
    match Logic.free_constants term with
    | _ :: _ as names -> List.for_all (fun name -> List.mem name context.entry) names
    | [] -> false
  then
    let text = quote frame.source operand in
    let plain =
      String.for_all
        (fun character ->
          character = '_' || character = '.'
          || (character >= 'a' && character <= 'z')
          || (character >= 'A' && character <= 'Z')
          || (character >= '0' && character <= '9'))
        text
    in
    Some (if plain then text else "(" ^ text ^ ")")
  else None

let overflow_fix context frame ty (operation : Intrinsic.operation) (operand : Core.origin) left
    right =
  match (bounds ty, right, parameter_operand context frame operand left) with
  | Some (low, high), Logic.Integer limit, Some text -> (
      let clause relation limit =
        if Z.leq low limit && Z.leq limit high then
          add_requires context frame (Printf.sprintf "%s %s %s" text relation (Z.to_string limit))
        else []
      in
      match operation with
      | Add when Z.sign limit > 0 -> clause "<=" (Z.sub high limit)
      | Add when Z.sign limit < 0 -> clause ">=" (Z.sub low limit)
      | Subtract when Z.sign limit > 0 -> clause ">=" (Z.add low limit)
      | Subtract when Z.sign limit < 0 -> clause "<=" (Z.add high limit)
      | Multiply when Z.sign limit > 0 && Z.sign low = 0 -> clause "<=" (Z.div high limit)
      | _ -> [])
  | _ -> []

let arithmetic ?operand ?divisor context frame (site : Invocation.site) ty
    (operation : Intrinsic.operation) left right =
  let source = frame.source in
  let span = span_of frame.source site.origin in
  let exact =
    match operation with
    | Add -> Logic.Operation ("+", [ left; right ])
    | Subtract -> Logic.Operation ("-", [ left; right ])
    | Multiply -> Logic.Operation ("*", [ left; right ])
    | Divide -> Logic.truncated_divide left right
    | _ -> Logic.truncated_remainder left right
  in
  (match operation with
  | Divide | Remainder ->
      oblige context frame Division span
        ~fixes:
          (match
             Option.bind divisor (fun divisor -> parameter_operand context frame divisor right)
           with
          | Some text -> add_requires context frame (text ^ " != 0")
          | None -> [])
        (Printf.sprintf "The divisor in `%s` may be zero." (quote source site.origin))
        (Logic.not_ (Logic.equal right (Logic.int 0)))
  | _ -> ());
  (match bounds ty with
  | Some (low, _) when operation = Divide || operation = Remainder ->
      if Z.sign low < 0 then
        oblige context frame Overflow span
          (Printf.sprintf "`%s` may overflow `%s`: the least value over -1."
             (quote source site.origin) (Types.show ty))
          (Logic.not_ Logic.(equal left (Integer low) &&& equal right (int (-1))))
  | Some (low, high) ->
      let unsigned = Z.sign low = 0 && not (Types.is_builtin Character ty) in
      oblige context frame Overflow span
        ~fixes:
          (match operand with
          | Some operand -> overflow_fix context frame ty operation operand left right
          | None -> [])
        (Printf.sprintf "`%s` may overflow `%s`." (quote source site.origin) (Types.show ty))
        (match operation with
        | (Add | Multiply) when unsigned -> Logic.Operation ("<=", [ exact; Integer high ])
        | Subtract when unsigned -> Logic.Operation ("<=", [ Integer low; exact ])
        | _ -> in_range ty exact)
  | None -> ());
  exact

let float_fits target value =
  match bounds target with
  | Some (low, high) ->
      let cut = truncated value in
      Logic.(
        not_ (is_nan value)
        &&& not_ (Operation ("fp.isInfinite", [ value ]))
        &&& Operation ("<=", [ Integer low; cut ])
        &&& Operation ("<=", [ cut; Integer high ]))
  | None -> Logic.Boolean false

let innermost_axiom context frame term =
  match context.open_axioms with
  | axiom :: _
    when let named = List.filter (fun name -> Logic.mentions [ name ] term) frame.bound in
         named <> [] && List.for_all (fun name -> List.mem name axiom.parameters) named ->
      Some axiom
  | _ -> None

let rec of_each_value context frame value make =
  if not (Logic.mentions frame.bound value) then make frame value
  else
    match innermost_axiom context frame value with
    | Some axiom ->
        axiom.at_calls <-
          (fun frame substitute -> of_each_value context frame (substitute value) make)
          :: axiom.at_calls
    | None -> ()

let power_facts base exponent =
  let power exponent = Logic.Apply (Symbol.Cost_power, [ base; exponent ]) in
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

let power_order base left right =
  let power exponent = Logic.Apply (Symbol.Cost_power, [ base; exponent ]) in
  Logic.(
    Operation (">=", [ base; int 1 ])
    ==> (Operation ("<=", [ left; right ])
        ==> Operation ("<=", [ power left; power right ])
        &&& (Operation ("<=", [ right; left ]) ==> Operation ("<=", [ power right; power left ]))))

let power_of context frame base exponent =
  declare context (Logic.Function (Symbol.Cost_power, [ Logic.Int; Logic.Int ], Logic.Int));
  let add exponent =
    if not (List.mem (base, exponent) context.powers) then begin
      List.iter
        (fun (other_base, other) ->
          if other_base = base then fact context frame (power_order base exponent other))
        context.powers;
      context.powers <- (base, exponent) :: context.powers;
      let facts, step = power_facts base exponent in
      List.iter (fact context frame) facts;
      Some step
    end
    else None
  in
  (if not (Logic.mentions frame.bound base || Logic.mentions frame.bound exponent) then
     match add exponent with
     | Some (step, previous) ->
         fact context frame step;
         ignore (add previous)
     | None -> ());
  (match (base, exponent) with
  | Logic.Integer base_value, Logic.Integer exponent_value
    when Z.sign exponent_value >= 0 && Z.leq exponent_value (Z.of_int 256) ->
      fact context frame
        (Logic.equal
           (Logic.Apply (Symbol.Cost_power, [ base; exponent ]))
           (Logic.Integer (Z.pow base_value (Z.to_int exponent_value))))
  | _ -> ());
  Logic.Apply (Symbol.Cost_power, [ base; exponent ])

let primitive_operation context frame ~(site : Invocation.site) (operation : Intrinsic.operation)
    types operands ~(arguments : Core.origin option list) ~fallback =
  let source = frame.source in
  let span = span_of frame.source site.origin in
  let argument index = Option.join (List.nth_opt arguments index) in
  let is_float = match types with ty :: _ -> float_format ty <> None | [] -> false in
  let exact operation left right =
    match (operation : Intrinsic.operation) with
    | Add | Wrapping_add | Add_overflows -> Logic.Operation ("+", [ left; right ])
    | Subtract | Wrapping_subtract | Subtract_overflows -> Logic.Operation ("-", [ left; right ])
    | _ -> Logic.Operation ("*", [ left; right ])
  in
  match (operation, types, operands) with
  | Add, _ :: _, [ left; right ] when is_float -> float_operation "fp.add" left right
  | Subtract, _ :: _, [ left; right ] when is_float -> float_operation "fp.sub" left right
  | Multiply, _ :: _, [ left; right ] when is_float -> float_operation "fp.mul" left right
  | Divide, _ :: _, [ left; right ] when is_float -> float_operation "fp.div" left right
  | Negate, _ :: _, [ value ] when is_float -> Logic.Operation ("fp.neg", [ value ])
  | (Add | Subtract | Multiply | Divide | Remainder), ty :: _, [ left; right ] when not is_float ->
      let result =
        arithmetic ?operand:(argument 0) ?divisor:(argument 1) context frame site ty operation left
          right
      in
      if bounds ty <> None then assume context frame (in_range ty result);
      result
  | Negate, ty :: _, [ inner ] when not is_float ->
      let negated = Logic.Operation ("-", [ inner ]) in
      if bounds ty <> None then
        oblige context frame Overflow span
          (Printf.sprintf "`%s` may overflow `%s`." (quote source site.origin) (Types.show ty))
          (in_range ty negated)
      else if ty <> Types.Integer then unsupported span "negating a value of `%s`" (Types.show ty);
      negated
  | Complement, ty :: _, [ inner ] -> opaque_operation context frame ty Complement [ inner ]
  | (Shift_left | Shift_right), ty :: _, [ left; right ] ->
      (match width ty with
      | Some bits ->
          let at_amount, text, fixes =
            match argument 1 with
            | Some amount ->
                ( span_of frame.source amount,
                  Printf.sprintf "The shift amount `%s`" (quote source amount),
                  match parameter_operand context frame amount right with
                  | Some text -> add_requires context frame (Printf.sprintf "%s < %d" text bits)
                  | None -> [] )
            | None ->
                (span, Printf.sprintf "The shift amount in `%s`" (quote source site.origin), [])
          in
          oblige context frame Shift at_amount ~fixes
            (Printf.sprintf "%s may not be less than %d." text bits)
            Logic.(Operation ("<", [ right; int bits ]))
      | None -> unsupported span "a shift of `%s`" (Types.show ty));
      let shifted = opaque_operation context frame ty operation [ left; right ] in
      (match (bounds ty, width ty) with
      | Some (low, high), Some bits
        when Z.equal low Z.zero && not (Logic.mentions frame.bound right) ->
          let scale = power_of context frame (Logic.int 2) right in
          assume context frame
            Logic.(
              Operation ("<=", [ int 0; right ])
              &&& Operation ("<", [ right; int bits ])
              ==> (Operation ("<=", [ int 1; scale ])
                  &&& Operation ("<=", [ scale; Integer (Z.shift_left Z.one (bits - 1)) ])));
          assume context frame
            (match operation with
            | Shift_left ->
                Logic.(
                  Operation ("<=", [ Operation ("*", [ left; scale ]); Integer high ])
                  ==> equal shifted (Operation ("*", [ left; scale ])))
            | _ -> Logic.equal shifted (Logic.truncated_divide left scale))
      | _ -> ());
      shifted
  | (Bit_and | Bit_or | Bit_xor), ty :: _, [ left; right ] ->
      let term = opaque_operation context frame ty operation [ left; right ] in
      (match bounds ty with
      | Some (low, _) when Z.sign low < 0 && operation = Bit_and ->
          let masked_by operand =
            Logic.(
              Operation ("<=", [ int 0; operand ])
              ==> (Operation ("<=", [ int 0; term ]) &&& Operation ("<=", [ term; operand ])))
          in
          assume context frame Logic.(masked_by left &&& masked_by right)
      | Some (low, _) when Z.equal low Z.zero -> (
          let at_most bound = Logic.Operation ("<=", [ term; bound ]) in
          match operation with
          | Bit_and -> assume context frame Logic.(at_most left &&& at_most right)
          | _ ->
              let sum = Logic.Operation ("+", [ left; right ]) in
              if operation = Bit_or then
                assume context frame
                  Logic.(Operation ("<=", [ left; term ]) &&& Operation ("<=", [ right; term ]));
              assume context frame (at_most sum);
              declare context
                (Logic.Function (Symbol.Cost_power, [ Logic.Int; Logic.Int ], Logic.Int));
              let exponent = Logic.Symbol (variable "exponent") in
              let below value =
                Logic.Operation
                  ("<", [ value; Logic.Apply (Symbol.Cost_power, [ Logic.int 2; exponent ]) ])
              in
              assume context frame
                (Logic.forall
                   ( [ (variable "exponent", Logic.Int) ],
                     Logic.(
                       Operation ("<=", [ int 0; exponent ])
                       &&& below left &&& below right ==> below term) )))
      | _ -> ());
      term
  | (Wrapping_add | Wrapping_subtract | Wrapping_multiply), ty :: _, [ left; right ]
    when bounds ty <> None ->
      let low, high = Option.get (bounds ty) in
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
    when bounds ty <> None ->
      Logic.not_ (in_range ty (exact operation left right))
  | Equal, _ :: _, [ left; right ] when is_float -> float_equal left right
  | Less, _ :: _, [ left; right ] when is_float -> float_less left right
  | Equal, ty :: _, [ left; right ] when bounds ty <> None -> Logic.equal left right
  | Less, ty :: _, [ left; right ] when bounds ty <> None -> Logic.Operation ("<", [ left; right ])
  | Fits, [ source; target ], [ value ] when bounds source <> None && bounds target <> None ->
      in_range target value
  | Fits, [ source; target ], [ value ] when float_format source <> None && bounds target <> None ->
      float_fits target value
  | Convert, [ source; target ], [ value ]
    when bounds source <> None && bounds target <> None && not (Types.is_builtin Character target)
    ->
      Logic.ite (in_range target value) value
        (opaque_operation context frame target Convert [ value ])
  | (Leading_zeros | Trailing_zeros | Count_ones), ty :: _, [ value ] when bounds ty <> None -> (
      let low, _ = Option.get (bounds ty) in
      match width ty with
      | Some bits ->
          let count counted value =
            let symbol = Symbol.Bit_count { count = counted; width = bits } in
            declare context (Logic.Function (symbol, [ Logic.Int ], Logic.Int));
            Logic.Apply (symbol, [ value ])
          in
          let term = count operation value in
          assume context frame
            Logic.(Operation ("<=", [ int 0; term ]) &&& Operation ("<=", [ term; int bits ]));
          (if Z.equal low Z.zero then
             of_each_value context frame value @@ fun frame value ->
             let leading = count Leading_zeros value
             and trailing = count Trailing_zeros value
             and ones = count Count_ones value in
             let power exponent = power_of context frame (Logic.int 2) exponent in
             let width = Logic.int bits in
             let nonzero = Logic.not_ (Logic.equal value (Logic.int 0)) in
             let below_highest = Logic.Operation ("-", [ width; leading ]) in
             List.iter (assume context frame)
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
      | (Ieee_equal | Ieee_less), ty :: _ when float_format ty <> None -> (
          match operands with
          | [ left; right ] ->
              Logic.Operation
                ((if operation = Ieee_equal then "fp.eq" else "fp.lt"), [ left; right ])
          | _ -> fallback ())
      | (Square_root | Floor | Ceiling | Truncate | Round_to_even), ty :: _
        when float_format ty <> None -> (
          match operands with
          | [ value ] -> (
              match operation with
              | Square_root -> Logic.Operation ("fp.sqrt", [ Logic.Operation ("RNE", []); value ])
              | Floor ->
                  Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTN", []); value ])
              | Ceiling ->
                  Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTP", []); value ])
              | Truncate ->
                  Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTZ", []); value ])
              | _ -> Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RNE", []); value ]))
          | _ -> fallback ())
      | Fused_multiply_add, ty :: _ when float_format ty <> None -> (
          match operands with
          | [ value; multiplier; addend ] ->
              Logic.Operation ("fp.fma", [ Logic.Operation ("RNE", []); value; multiplier; addend ])
          | _ -> fallback ())
      | Is_nan, ty :: _ when float_format ty <> None -> (
          match operands with [ value ] -> is_nan value | _ -> fallback ())
      | From_bits, [ bits; target ] when bounds bits <> None -> (
          match (operands, float_format target, width bits) with
          | [ value ], Some (exponent, significand), Some width ->
              Logic.Operation
                ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
                  [ Logic.Operation (Printf.sprintf "(_ int2bv %d)" width, [ value ]) ] )
          | _ -> fallback ())
      | To_bits, [ source; bits ] when bounds bits <> None -> (
          match (operands, float_format source, width bits) with
          | [ value ], Some (exponent, significand), Some width ->
              assume context frame
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
      | Multiply_high, ty :: _ when bounds ty <> None -> (
          match (operands, width ty) with
          | [ left; right ], Some bits ->
              Logic.Operation
                ( "div",
                  [
                    Logic.Operation ("*", [ left; right ]); Logic.Integer (Z.shift_left Z.one bits);
                  ] )
          | _ -> fallback ())
      | (Rotate_left | Rotate_right | Swap_bytes), ty :: _ when bounds ty <> None ->
          opaque_operation context frame ty operation operands
      | Convert, [ source; target ] when float_format source <> None && bounds target <> None -> (
          match operands with
          | [ value ] ->
              oblige context frame Requires
                (span_of frame.source site.origin)
                (Printf.sprintf
                   "`%s` may not fit `%s`: it must be a number that, cut toward zero, is in its \
                    range."
                   (quote frame.source site.origin) (Types.show target))
                (float_fits target value);
              Logic.Operation ("to_int", [ truncated value ])
          | _ -> fallback ())
      | Convert, [ source; target ] when bounds source <> None && float_format target <> None -> (
          match (operands, float_format target) with
          | [ value ], Some (exponent, significand) ->
              Logic.Operation
                ( Printf.sprintf "(_ to_fp %d %d)" exponent significand,
                  [ Logic.Operation ("RNE", []); Logic.Operation ("to_real", [ value ]) ] )
          | _ -> fallback ())
      | Convert, [ _; target ] when Types.is_builtin Character target -> (
          match operands with
          | [ value ] ->
              oblige context frame Requires
                (span_of frame.source site.origin)
                (Printf.sprintf
                   "`%s` may not be a Unicode scalar value, which a `Character` must be."
                   (quote frame.source site.origin))
                (in_range target value);
              value
          | _ -> fallback ())
      | _ -> fallback ())
