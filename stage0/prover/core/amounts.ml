let run_code context frame (code : Mir.t) ~type_ =
  match Lambdas.run_lambda_body context frame ~lambdas:code.lambdas code.body ~type_ with
  | Some returned -> returned
  | None -> (frame, Facts.arrive context frame "unfinished" type_)

let holds_specification (formula : Mir.formula) is_one =
  let holds = ref false in
  let visit (statement : Mir.statement) =
    match statement.kind with
    | Basic (Assign { value = Specification value; _ }) when is_one value -> holds := true
    | _ -> ()
  in
  Mir.iter_formula visit formula;
  !holds

let mentions_result (clause : Mir.formula) =
  holds_specification clause (function Result -> true | _ -> false)

let mentions_history (clause : Mir.formula) =
  holds_specification clause (function Yielded -> true | _ -> false)

let assume_typed context (frame : State.frame) term =
  let guarded = Logic.( ==> ) frame.condition term in
  match Operations.find_innermost_axiom context frame guarded with
  | Some axiom -> axiom.hypotheses <- guarded :: axiom.hypotheses
  | None -> Facts.assume context frame term

let rec compare_lexicographically before after =
  match (before, after) with
  | [ right ], [ left ] -> Logic.(less_equal (int 0) right &&& less left right)
  | right :: before, left :: after ->
      Logic.(
        less_equal (int 0) right
        &&& (less left right ||| (equal left right &&& compare_lexicographically before after)))
  | _ -> Logic.Boolean true

let covers ~(clause : Costs.target) ~(counter : Costs.target) =
  match (clause, counter) with
  | Capability path, Capability_method (owner, _) -> Path.equal path owner
  | Through left, Through right -> left = right
  | Capability left, Capability right -> Path.equal left right
  | Capability_method (left, left_method), Capability_method (right, right_method) ->
      Path.equal left right && left_method = right_method
  | _ -> false

let is_same_resource (cost : Mir.cost) ~locals (counter : Costs.counter) =
  match (cost.resource, counter.resource) with
  | Metric bounded, Metric counted -> bounded = counted
  | Calls _, Calls counted -> (
      match Contracts.find_resource cost ~locals with
      | Some (Calls target) -> covers ~clause:target ~counter:counted
      | _ -> false)
  | _ -> false

let declare_bounded_amount context frame bound =
  let amount = Facts.declare_fresh context frame "spent" Logic.Int in
  Facts.assume context frame Logic.(less_equal (int 0) amount &&& less_equal amount bound);
  amount

let compute_amount_within context frame (counter : Costs.counter) bound =
  match counter.counting with
  | Units -> bound
  | At_most | Exactly -> declare_bounded_amount context frame bound

let compute_promised_amount context frame (counter : Costs.counter) (bound : Mir.bound) ~evaluate
    ~is_recursive_call ~exact_target ~change =
  match (bound, counter.counting) with
  | Order_of amount, Units ->
      let amount = evaluate amount in
      let amount =
        if is_recursive_call then
          let hypothesis = Costs.at_least_zero (Costs.bound amount) in
          if counter.resource = Metric Time then Costs.plus hypothesis (Logic.int 1) else hypothesis
        else Costs.units amount
      in
      Costs.minus amount change
  | (At_most amount | Exactly amount), Units ->
      Costs.at_least_zero (Costs.minus (evaluate amount) change)
  | At_most amount, (At_most | Exactly) ->
      declare_bounded_amount context frame (Costs.minus (evaluate amount) change)
  | Exactly amount, (At_most | Exactly) ->
      let amount = Costs.minus (evaluate amount) change in
      if exact_target then amount else declare_bounded_amount context frame amount
  | Order_of _, _ -> Operations.declare_unknown_amount context frame counter

let compute_growth compute_change =
  try Costs.at_least_zero (compute_change ()) with Facts.Unsupported _ -> Costs.zero

let make_may_be_target (context : State.context) frame term ty target =
  if term = target then Logic.Boolean true
  else
    match List.assoc_opt target context.call_targets with
    | Some local -> (
        match (ty, Facts.find_local_type context frame (Core_local local)) with
        | Types.Function _, Some target_type
          when Facts.declare_sort context ty = Facts.declare_sort context target_type ->
            Logic.equal term target
        | _ -> Logic.Boolean false)
    | None -> Logic.Boolean false

let lambda_captures_target (context : State.context) lambda target =
  match
    (List.assoc_opt lambda context.lambda_captures, List.assoc_opt target context.call_targets)
  with
  | Some captured, Some local -> List.mem local captured
  | _ -> false

let make_reach_formula context frame (values : State.passed list) term =
  Logic.disjunction
    (List.map
       (fun (passed : State.passed) ->
         if lambda_captures_target context passed.term term then Logic.Boolean true
         else make_may_be_target context frame passed.term passed.type_ term)
       values)

type capability_reach = Not_reached | Reached_directly | Reached_through_providers

let join_reach first second =
  match (first, second) with
  | Reached_through_providers, _ | _, Reached_through_providers -> Reached_through_providers
  | Reached_directly, _ | _, Reached_directly -> Reached_directly
  | Not_reached, Not_reached -> Not_reached

let list_providers (enclosing : Mir.provided list list) =
  let rec list = function
    | [] -> []
    | block :: outer ->
        List.map
          (fun provider -> (provider, outer))
          (List.concat_map (fun (provided : Mir.provided) -> provided.provides) block)
        @ list outer
  in
  list enclosing

let find_capability_reach (context : State.context) ~(uses : Types.capability_set) capability =
  let rec reach enclosing uses =
    let providers = list_providers enclosing in
    let find_provider used =
      List.find_opt
        (fun ((provider : Core.provided), _) -> Path.equal provider.capability used)
        providers
    in
    let reach_through ((provider : Core.provided), outer) =
      match Interface.Definition.find_impl_interface context.lookups.interface provider.impl with
      | Some impl ->
          if
            reach outer (Types.substitute_capabilities provider.arguments impl.impl_uses)
            = Not_reached
          then Not_reached
          else Reached_through_providers
      | None -> Facts.raise_bug "the provided `%s` has no interface" (Path.show provider.impl)
    in
    List.fold_left
      (fun reached (used : Types.capability) ->
        join_reach reached
          (match used with
          | Built_in _ ->
              if used = Types.make_capability capability then Reached_directly else Not_reached
          | Capability path -> (
              match find_provider path with
              | Some found -> reach_through found
              | None -> if Path.equal path capability then Reached_directly else Not_reached)
          | Capability_parameter _ | Capability_projection _ | Capability_variable _ ->
              List.fold_left
                (fun reached found -> join_reach reached (reach_through found))
                (match find_provider capability with
                | Some _ -> Not_reached
                | None -> Reached_directly)
                providers
          | Capability_error _ -> Facts.raise_bug "the prover reads a capability with an error"
          | Capability_unless _ | Capability_unless_values _ ->
              Facts.raise_bug "a capability's base has a condition"))
      Not_reached
      (List.map Types.find_base (Types.list_capabilities uses))
  in
  reach context.enclosing_provides uses

let compute_capability_amount context frame ~uses capability counter ~direct =
  match find_capability_reach context ~uses capability with
  | Not_reached -> Costs.zero
  | Reached_through_providers -> Operations.declare_unknown_amount context frame counter
  | Reached_directly -> direct ()

let make_conditional_amount condition amount =
  match condition with
  | Logic.Boolean true -> amount
  | Logic.Boolean false -> Costs.zero
  | condition -> Logic.ite condition amount Costs.zero

let compute_callee_amount ?(method_cost : (Language.Metric.t -> Logic.term) option)
    (context : State.context) after ~is_recursive ~clauses:(declared_clauses : State.clauses list)
    ~(bind_frame : State.clauses -> State.frame) ~uses ~(values : State.passed list) ~change
    (counter : Costs.counter) =
  let is_recursive_call =
    is_recursive && counter.counting = Units && List.mem counter context.bounded_counters
  in
  let list_matching_costs (clauses : State.clauses) =
    let frame = bind_frame clauses in
    List.filter_map
      (fun (cost : Mir.cost) ->
        if is_same_resource cost ~locals:frame.locals counter then Some (clauses, frame, cost)
        else None)
      clauses.costs
  in
  let compute_amount (_, (frame : State.frame), (cost : Mir.cost)) =
    let exact_target =
      match (cost.resource, counter.resource) with
      | Calls (Capability _), Calls (Capability_method _) -> false
      | _ -> true
    in
    match (cost.amortized, change) with
    | true, None -> Operations.declare_unknown_amount context after counter
    | _ ->
        compute_promised_amount context after counter cost.bound
          ~evaluate:(fun amount -> snd (Validity.read_specification context frame amount))
          ~is_recursive_call ~exact_target
          ~change:
            (match (cost.amortized, change) with
            | true, Some compute_change -> compute_change ()
            | _ -> Costs.zero)
  in
  let find_first_clauses () =
    let amortized_first = Option.is_some change && counter.amortized in
    List.find_map
      (fun clauses ->
        match list_matching_costs clauses with
        | [] -> None
        | costs ->
            let amortized, plain =
              List.partition (fun (_, _, (cost : Mir.cost)) -> cost.amortized) costs
            in
            Some (if amortized_first then amortized @ plain else plain @ amortized))
      declared_clauses
  in
  match counter.resource with
  | Calls (Capability capability | Capability_method (capability, _)) ->
      compute_capability_amount context after ~uses capability counter ~direct:(fun () ->
          match find_first_clauses () with
          | Some (clause :: _) -> compute_amount clause
          | Some [] | None -> Operations.declare_unknown_amount context after counter)
  | Calls (Through term) when make_reach_formula context after values term = Logic.Boolean false ->
      Costs.zero
  | Calls (Through term) -> (
      let reaches = make_reach_formula context after values term in
      let receiving =
        List.filter_map
          (fun (passed : State.passed) -> if passed.term = term then Some passed.position else None)
          values
      in
      let captured =
        List.exists
          (fun (passed : State.passed) -> lambda_captures_target context passed.term term)
          values
      in
      match find_first_clauses () with
      | Some clauses
        when (not captured) && List.length clauses >= List.length receiving && receiving <> [] ->
          List.fold_left
            (fun total clause -> Costs.plus total (compute_amount clause))
            Costs.zero clauses
      | _ ->
          make_conditional_amount reaches (Operations.declare_unknown_amount context after counter))
  | Metric _ -> (
      let compute_method_amount () =
        match (method_cost, counter.resource, counter.counting) with
        | Some compute_cost, Metric Time, Units ->
            Costs.minus
              (Costs.plus (compute_cost Time) (Logic.int 1))
              (match change with
              | Some compute_change -> compute_growth compute_change
              | None -> Costs.zero)
        | Some compute_cost, Metric ((Allocations | Allocated_bytes) as metric), _ ->
            compute_amount_within context after counter (compute_cost metric)
        | _ -> Operations.declare_unknown_amount context after counter
      in
      match find_first_clauses () with
      | Some (clause :: _) -> compute_amount clause
      | Some [] | None -> compute_method_amount ())

let find_generic_argument context frame (operation : Intrinsic.operation) type_arguments name =
  let generics = (Intrinsic_signatures.make_signature operation).generics in
  List.find_map
    (fun ((generic : Types.generic), argument) ->
      match argument with
      | Types.Value value when generic.generic.name = name ->
          Some (Models.make_value_term context frame value)
      | _ -> None)
    (List.combine generics type_arguments)

let compute_step_amount context frame (invocation : Invocation.t) (values : State.passed list)
    (counter : Costs.counter) =
  match invocation.callee with
  | Intrinsic { operation; type_arguments } -> (
      let cost = Intrinsic_signatures.classify_cost operation in
      match counter.resource with
      | Metric Time -> (
          match (cost.time, counter.counting) with
          | Constant_time, _ -> Costs.zero
          | Linear_in position, Units -> (
              match
                List.find_opt (fun (passed : State.passed) -> passed.position = position) values
              with
              | Some passed -> (
                  match passed.type_ with
                  | Types.Named { path; arguments = [ Types.Type element ] } -> (
                      match Well_known.find_builtin_type path with
                      | Some ((Storage | View) as builtin) ->
                          Models.make_sequence_length context element
                            (Intrinsics.make_buffer_model context builtin element passed.term)
                      | _ -> Operations.declare_unknown_amount context frame counter)
                  | _ -> Operations.declare_unknown_amount context frame counter)
              | None -> Operations.declare_unknown_amount context frame counter)
          | (Linear_in _ | Unbounded_time), _ ->
              Operations.declare_unknown_amount context frame counter)
      | Metric (Allocations | Allocated_bytes) -> (
          match (cost.allocations, counter.resource, counter.counting) with
          | No_allocations, _, _ -> Costs.zero
          | One_if_positive amount, resource, counting -> (
              let amount_term =
                match amount with
                | Argument position ->
                    Option.map
                      (fun (passed : State.passed) -> passed.term)
                      (List.find_opt
                         (fun (passed : State.passed) -> passed.position = position)
                         values)
                | Generic name -> find_generic_argument context frame operation type_arguments name
              in
              match amount_term with
              | Some amount_term when resource = Metric Allocations || counting = Units ->
                  Logic.ite (Logic.greater amount_term (Logic.int 0)) (Logic.int 1) (Logic.int 0)
              | _ -> Operations.declare_unknown_amount context frame counter)
          | Unknown_allocations, _, _ -> Operations.declare_unknown_amount context frame counter)
      | Calls _ -> Costs.zero)
  | Capability_method { capability; name } -> (
      match counter.resource with
      | Calls (Capability counted | Capability_method (counted, _)) ->
          compute_capability_amount context frame ~uses:invocation.uses counted counter
            ~direct:(fun () ->
              match counter.resource with
              | _ when not (Path.equal counted capability) ->
                  Operations.declare_unknown_amount context frame counter
              | Calls (Capability_method (_, method_)) when method_ <> name -> Costs.zero
              | Calls _ | Metric _ -> Logic.int 1)
      | Calls (Through _) -> Costs.zero
      | Metric _ -> (
          match Contracts.find_capability_clauses context capability name with
          | Some capability_clauses ->
              let inside =
                Validity.bind_arguments frame capability_clauses
                  ~arguments:
                    (List.map
                       (fun (passed : State.passed) -> (passed.position, passed.term))
                       values)
                  ~substitution:Types.no_substitution
              in
              compute_callee_amount context frame ~is_recursive:false
                ~clauses:[ capability_clauses ]
                ~bind_frame:(fun _ -> inside)
                ~uses:invocation.uses ~values ~change:None counter
          | None -> Operations.declare_unknown_amount context frame counter))
  | Function _ | Trait_method _ | Indirect () -> (
      match counter.resource with
      | Calls (Capability capability | Capability_method (capability, _)) ->
          compute_capability_amount context frame ~uses:invocation.uses capability counter
            ~direct:(fun () -> Operations.declare_unknown_amount context frame counter)
      | Calls (Through term) ->
          make_conditional_amount
            (make_reach_formula context frame values term)
            (Operations.declare_unknown_amount context frame counter)
      | Metric _ -> Operations.declare_unknown_amount context frame counter)

let declare_held_symbol context ty term =
  let symbol = Logic.Symbol.Potential ty in
  Facts.declare context (Logic.Function (symbol, [ Facts.declare_sort context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let compute_buffer_elements context (ty : Types.ty) =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element; Types.Value _ ] }
    when Well_known.find_builtin_type path = Some Array ->
      Option.map
        (fun model_of -> (element, model_of))
        (Models.find_model_function context ty ~model:(Models.make_sequence_type element))
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Well_known.find_builtin_type path = Some Storage ->
      Some (element, fun term -> Intrinsics.make_buffer_model context Storage element term)
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Well_known.find_builtin_type path = Some View ->
      Some (element, fun term -> Intrinsics.make_buffer_model context View element term)
  | Types.Named { path; arguments } when Types.find_builtin ty = None -> (
      match Interface.Definition.find_interface context.lookups.interface path with
      | Some (Interface.Environment.Type_interface { shape = Record [ field ]; type_generics; _ })
        -> (
          let substitution = Types.make_substitution type_generics arguments in
          match Types.substitute substitution field.field_type with
          | Types.Named { path = field_path; arguments = [ Types.Type element ] }
            when Well_known.find_builtin_type field_path = Some Storage
                 || Well_known.find_builtin_type field_path = Some View ->
              Option.map
                (fun model_of -> (element, model_of))
                (Models.find_model_function context ty ~model:(Models.make_sequence_type element))
          | _ -> None)
      | _ -> None)
  | _ -> None

let find_buffer_elements (context : State.context) (ty : Types.ty) =
  let key = ty in
  match Tables.Type_table.find_opt context.buffers key with
  | Some elements -> elements
  | None ->
      let elements = compute_buffer_elements context ty in
      Tables.Type_table.replace context.buffers key elements;
      elements

let declare_potential_measure context element =
  let symbol = Logic.Symbol.Potential_measure element in
  let measure = Intrinsics.measure_type element in
  Facts.declare context
    (Logic.Constant (symbol, Facts.declare_sort context (Types.Function measure)));
  let term = Logic.Symbol symbol in
  if not (List.mem term context.potentials) then begin
    context.potentials <- term :: context.potentials;
    let each = Logic.Symbol.Variable { label = "potential.element"; numbers = [] } in
    Facts.add_fact context
      (Logic.forall
         ( [ (each, Facts.declare_sort context element) ],
           Logic.equal
             (Lambdas.apply_function context measure term [ Logic.Symbol each ])
             (declare_held_symbol context element (Logic.Symbol each)) ))
  end;
  term

let sum_element_potentials context element sequence =
  Intrinsics.make_sequence_sum context element sequence (declare_potential_measure context element)

let choose_by_variant ty term shape compute_variant =
  match shape with
  | [ (None, fields) ] -> compute_variant (None, fields)
  | variants -> (
      match List.rev variants with
      | last :: earlier ->
          List.fold_left
            (fun otherwise ((variant, _) as one) ->
              Logic.ite
                (Logic.Is (Facts.make_constructor_symbol ty variant, term))
                (compute_variant one) otherwise)
            (compute_variant last) earlier
      | [] -> Costs.zero)

let rec find_potential_clause context (ty : Types.ty) =
  match Validity.find_type_clauses context ty with
  | Some (source, { potential = Some potential; _ }) -> Some (source, potential)
  | _ -> None

and has_potential (context : State.context) ?(seen = []) (ty : Types.ty) =
  if seen <> [] then holds_potential_type context ~seen ty
  else
    let key = ty in
    match Tables.Type_table.find_opt context.holds_potential key with
    | Some holds -> holds
    | None ->
        let holds = holds_potential_type context ~seen ty in
        Tables.Type_table.replace context.holds_potential key holds;
        holds

and holds_potential_type context ~seen (ty : Types.ty) =
  if List.exists (Types.equal ty) seen then false
  else
    match ty with
    | Parameter _ -> true
    | Named _ when Option.is_some (find_buffer_elements context ty) -> true
    | Types.Named { path; arguments } when Types.find_builtin ty = None -> (
        find_potential_clause context ty <> None
        ||
        match Interface.Definition.find_interface context.lookups.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            let substitution = Types.make_substitution interface.type_generics arguments in
            let fields =
              match interface.shape with
              | Record fields -> fields
              | Sum variants ->
                  List.concat_map
                    (fun (variant : Types.variant) -> Option.value variant.fields ~default:[])
                    variants
              | Todo_type | Builtin_type _ -> []
            in
            List.exists
              (fun (field : Types.field) ->
                has_potential context ~seen:(ty :: seen)
                  (Types.substitute substitution field.field_type))
              fields
        | _ -> false)
    | Types.Named { arguments; _ } ->
        if
          List.exists
            (function
              | Types.Type element -> has_potential context ~seen:(ty :: seen) element | _ -> false)
            arguments
        then Facts.raise_unsupported Whole_definition "the potential of a collection's elements"
        else false
    | _ -> false

and compute_potential context (frame : State.frame) ?(seen = []) (ty : Types.ty) term =
  if not (has_potential context ty) then Costs.zero
  else begin
    let held = declare_held_symbol context ty term in
    if (not (List.mem held context.potentials)) && not (Logic.mentions frame.bound term) then begin
      context.potentials <- held :: context.potentials;
      Facts.add_frame_fact context frame
        Logic.(
          Validity.make_validity context frame ~assuming:true ty term ==> less_equal (int 0) held);
      match (find_potential_clause context ty, Facts.find_constructors context ty) with
      | None, None when Option.is_some (find_buffer_elements context ty) -> (
          match find_buffer_elements context ty with
          | Some (element, model_of) ->
              let sequence = model_of term in
              let slack = Intrinsics.declare_buffer_slack context ty term in
              let length = Models.make_sequence_length context element sequence in
              Facts.add_frame_fact context frame
                Logic.(less_equal (int 0) slack &&& less_equal slack (multiply (int 2) length));
              (match ty with
              | Types.Named { path; _ } when Well_known.find_builtin_type path = Some Storage ->
                  let saved =
                    Logic.subtract
                      (Logic.multiply (Logic.int 2) length)
                      (Intrinsics.make_buffer_capacity context element term)
                  in
                  Facts.add_frame_fact context frame
                    (Logic.equal slack
                       (Logic.ite (Logic.greater_equal saved (Logic.int 0)) saved (Logic.int 0)))
              | Types.Named { path; _ }
                when Well_known.find_builtin_type path = Some View
                     || Well_known.find_builtin_type path = Some Array ->
                  Facts.add_frame_fact context frame (Logic.equal slack (Logic.int 0))
              | _ -> ());
              let elements =
                if has_potential context element then
                  sum_element_potentials context element sequence
                else Costs.zero
              in
              Facts.add_frame_fact context frame (Logic.equal held (Costs.plus slack elements))
          | None -> ())
      | clause, Some shape -> (
          try
            let declared_potential =
              match clause with
              | Some (source, written) ->
                  snd
                    (Validity.read_specification context
                       (Validity.make_type_frame context frame source ty ~self:(Some term))
                       written)
              | None -> Costs.zero
            in
            let parts =
              choose_by_variant ty term shape (compute_parts_potential context frame ~seen ty term)
            in
            Facts.add_frame_fact context frame
              (Logic.equal held (Costs.plus declared_potential parts))
          with Facts.Unsupported _ -> ())
      | _ -> ()
    end;
    match (find_potential_clause context ty, Facts.find_constructors context ty) with
    | None, Some [ (None, fields) ] when Option.is_none (find_buffer_elements context ty) -> (
        try compute_parts_potential context frame ~seen ty term (None, fields)
        with Facts.Unsupported _ -> held)
    | _ -> held
  end

and compute_parts_potential context frame ~seen ty term (variant, fields) =
  List.fold_left
    (fun total (field, field_type) ->
      if has_potential context field_type then
        let part = Validity.select_field context ty variant field term in
        Costs.plus total
          (if List.exists (Types.equal field_type) (ty :: seen) then
             declare_held_symbol context field_type part
           else compute_potential context frame ~seen:(ty :: seen) field_type part)
      else total)
    Costs.zero fields

let compute_elements_potential context (ty : Types.ty) term =
  let rec sum_elements ~enclosing (ty : Types.ty) term =
    if not (has_potential context ty) then Costs.zero
    else
      match Facts.find_constructors context ty with
      | Some shape -> (
          let sum_fields (variant, fields) =
            List.fold_left
              (fun total (field, field_type) ->
                if List.exists (Types.equal field_type) (ty :: enclosing) then total
                else
                  Costs.plus total
                    (sum_elements ~enclosing:(ty :: enclosing) field_type
                       (Validity.select_field context ty variant field term)))
              Costs.zero fields
          in
          try choose_by_variant ty term shape sum_fields with Facts.Unsupported _ -> Costs.zero)
      | None -> (
          match (find_potential_clause context ty, find_buffer_elements context ty) with
          | None, Some (element, model_of) when has_potential context element ->
              sum_element_potentials context element (model_of term)
          | _ -> Costs.zero)
  in
  sum_elements ~enclosing:[] ty term

let assume_element_potential_change context frame (sequence : Types.ty) ~before ~after ~replaced
    ~written =
  match find_buffer_elements context sequence with
  | Some (element, model_of) -> (
      try
        if has_potential context element then
          let sum term = sum_element_potentials context element (model_of term) in
          Facts.assume context frame
            (Logic.equal (sum after)
               (Costs.plus
                  (Costs.minus (sum before) (compute_potential context frame element replaced))
                  (compute_potential context frame element written)))
      with Facts.Unsupported _ -> ())
  | None -> ()

let make_static_frame (frame : State.frame) source ~substitution ~self_type =
  {
    frame with
    State.source;
    locals = Locals.empty;
    types = Locals.empty;
    old_locals = Locals.empty;
    self = None;
    old_self = None;
    result = None;
    condition = Logic.Boolean true;
    makes_obligations = false;
    bound = [];
    binders = [];
    substitution;
    self_type = Some self_type;
    yielded = None;
    yielded_so_far = None;
    spent = [];
    aliases = Locals.empty;
    lends = Locals.empty;
  }

let is_static ~has_own_generics (amount : Mir.formula) =
  if has_own_generics then Option.is_some (Contracts.find_integer_literal amount)
  else
    let reads_a_parameter = ref false in
    Mir.iter_formula_places
      (fun _ (place : Mir.place) ->
        match place.root with
        | Local local when List.mem local amount.parameters -> reads_a_parameter := true
        | Local _ | Constant _ | Literal _ -> ())
      amount;
    (not !reads_a_parameter)
    && not
         (holds_specification amount (function
           | Result | Entry _ | Yielded -> true
           | Identical _ | Applied _ | Method_cost _ | Map _ | Quantified _ -> false))

let find_static_bound context frame (metric : Language.Metric.t) (clauses : State.clauses)
    ~has_own_generics ~substitution ~self_type =
  let counter = Costs.make_operand_counter metric in
  let substitution = Types.combine_substitutions substitution clauses.bindings in
  List.find_map
    (fun (cost : Mir.cost) ->
      if
        cost.amortized
        || (not (is_same_resource cost ~locals:Locals.empty counter))
        || not (Conditions.holds_here context ~substitution cost.holds_when)
      then None
      else
        match (counter.counting, cost.bound) with
        | (Units, Order_of amount | (At_most | Exactly), (At_most amount | Exactly amount))
          when is_static ~has_own_generics amount -> (
            try
              Some
                (snd
                   (Validity.read_specification context
                      (make_static_frame frame clauses.callee ~substitution ~self_type)
                      amount))
            with Facts.Unsupported _ -> None)
        | (Units | At_most | Exactly), (Order_of _ | At_most _ | Exactly _) -> None)
    clauses.costs

let find_body_cost (context : State.context) frame (metric : Language.Metric.t) path ~substitution
    ~self_type =
  match (Contracts.find_source context.lookups path, Mir.read_code context.lookups.mir path) with
  | Some (source, _, _), Some { form = code; _ } -> (
      let counter = Costs.make_operand_counter metric in
      let outer_counters = context.counters in
      context.counters <- [ counter ];
      let start =
        {
          (make_static_frame frame source ~substitution ~self_type) with
          spent = [ (counter, Costs.zero) ];
        }
      in
      let find_spent () =
        match
          Lambdas.run_lambda_body context start ~lambdas:code.lambdas code.body ~type_:self_type
        with
        | Some (finished, result) -> (
            match (List.assoc_opt counter finished.spent, metric) with
            | Some spent, Time ->
                Some (Costs.plus spent (compute_potential context finished self_type result))
            | spent, (Allocations | Allocated_bytes) -> spent
            | None, Time -> None)
        | None -> None
      in
      try Fun.protect ~finally:(fun () -> context.counters <- outer_counters) find_spent
      with Facts.Unsupported _ -> None)
  | _ -> None

let find_method_cost_bound context frame (metric : Language.Metric.t) (method_ : Path.t)
    ~trait_arguments self_type =
  let holds ty = try has_potential context ty with Facts.Unsupported _ -> true in
  let includes_potential_made = metric = Time in
  match method_ with
  | Method { owner = trait; name; receiver } -> (
      if Well_known.is Copyable trait then
        if
          Interface.Impls.is_plain context.lookups.interface ~list_bounds:context.bounds self_type
          && not (holds self_type)
        then Some (Costs.least_amount (Metric metric))
        else None
      else
        let reference : Types.trait_reference = { trait; trait_arguments; associated = [] } in
        match Facts.find_impl context reference self_type with
        | Some (impl, substitution) -> (
            let path = Path.Method { owner = impl; name; receiver } in
            match Contracts.read_signature context path with
            | Some (signature : Types.signature) -> (
                let impl_generics =
                  match Interface.Definition.find_impl_interface context.lookups.interface impl with
                  | Some interface -> interface.impl_generics
                  | None -> []
                in
                let has_own_generics =
                  signature.capability_parameters <> []
                  || List.exists
                       (fun (generic : Types.generic) ->
                         not
                           (List.exists
                              (fun (impl_generic : Types.generic) ->
                                impl_generic.generic = generic.generic)
                              impl_generics))
                       signature.generics
                in
                let makes_no_potential =
                  List.for_all
                    (fun (parameter : Types.parameter_info) ->
                      parameter.mode <> Language.Mode.Mut || not (holds parameter.type_))
                    signature.parameters
                  && (match signature.receiver with Some (Mut, ty) -> not (holds ty) | _ -> true)
                  && match signature.output with Returns ty -> not (holds ty) | _ -> false
                in
                let stated_bound =
                  if includes_potential_made && not makes_no_potential then None
                  else
                    Option.bind
                      (Contracts.find_method_contract context reference name receiver
                         (Impl { impl; substitution }))
                      (fun contract ->
                        List.find_map
                          (fun (clauses : State.clauses) ->
                            find_static_bound context frame metric clauses ~has_own_generics
                              ~substitution:
                                (if clauses.inherited then
                                   Contracts.make_trait_substitution context.lookups reference
                                     self_type
                                 else substitution)
                              ~self_type)
                          (Contracts.list_declared_clauses contract))
                in
                match (stated_bound, impl) with
                | Some bound, _ -> Some bound
                | None, Derived _
                  when signature.receiver = None && signature.parameters = []
                       && not has_own_generics ->
                    find_body_cost context frame metric path ~substitution ~self_type
                | None, _ -> None)
            | None -> None)
        | None -> None)
  | _ -> None

let declare_method_cost context frame (metric : Language.Metric.t) (method_ : Path.t)
    ~trait_arguments self_type =
  let symbol = Logic.Symbol.Method_cost { metric; method_; trait_arguments; self_type } in
  Facts.run_once context (Method_cost_bound symbol) (fun () ->
      Facts.declare context (Logic.Constant (symbol, Logic.Int));
      let least = Costs.least_amount (Metric metric) in
      Facts.add_fact context (Logic.less_equal least (Logic.Symbol symbol));
      Option.iter
        (fun bound ->
          Facts.add_fact context (Logic.less_equal (Logic.Symbol symbol) (Costs.larger bound least)))
        (find_method_cost_bound context frame metric method_ ~trait_arguments self_type));
  Logic.Symbol symbol

let compute_method_cost context frame (metric : Language.Metric.t) (callee : Invocation.callee) =
  match callee with
  | Trait_method { trait; name; receiver; self_type; _ } ->
      let substitute_argument : Types.argument -> Types.argument = function
        | Type type_ -> Type (Facts.substitute_type context frame type_)
        | argument -> Types.substitute_argument frame.substitution argument
      in
      declare_method_cost context frame metric
        (Path.Method { owner = trait.trait; name; receiver })
        ~trait_arguments:(List.map substitute_argument trait.trait_arguments)
        (Facts.substitute_type context frame self_type)
  | _ ->
      Facts.raise_unsupported Whole_definition "the %s of a function that is not a trait's method"
        (Language.Metric.show metric)
