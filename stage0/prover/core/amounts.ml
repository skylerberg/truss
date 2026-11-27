type call_amount = {
  call : Catalog.Prover.quoted;
  callee : Path.t;
  states_cost : bool;
  counts_potential : bool;
  counter : Costs.counter;
  amount : Logic.term;
}

type state = { mutable call_amounts : call_amount list }

let state = Private_state.make_key (fun () -> { call_amounts = [] })
let list_call_amounts query = List.rev (Query.read_state query state).call_amounts

let declare_bounded_amount (frame : State.frame) bound =
  let amount = Facts.declare_fresh frame "spent" Logic.Int in
  Facts.assume frame Logic.(less_equal (int 0) amount &&& less_equal amount bound);
  amount

let compute_amount_within (frame : State.frame) (counter : Costs.counter) bound =
  match counter.counting with
  | Units -> bound
  | At_most | Exactly -> declare_bounded_amount frame bound

let compute_promised_amount (frame : State.frame) (counter : Costs.counter) (bound : Mir.bound)
    ~evaluate ~is_recursive_call ~exact_target ~is_converted =
  match (bound, counter.counting) with
  | Order_of amount, Units ->
      let amount = evaluate amount in
      if is_recursive_call then
        let hypothesis = Logic.at_least_zero (Costs.bound amount) in
        if counter.resource = Metric Time then Logic.add hypothesis (Logic.int 1) else hypothesis
      else Costs.units (if is_converted then amount else Costs.reduce_constants amount)
  | (At_most amount | Exactly amount), Units -> Logic.at_least_zero (evaluate amount)
  | At_most amount, (At_most | Exactly) -> declare_bounded_amount frame (evaluate amount)
  | Exactly amount, (At_most | Exactly) ->
      let amount = evaluate amount in
      if exact_target then amount else declare_bounded_amount frame amount
  | Order_of _, _ -> Counters.declare_unknown_amount frame counter

let make_may_be_target (frame : State.frame) term ty target =
  if term = target then Logic.Boolean true
  else
    match Cost_promises.find_call_target frame.query target with
    | Some local -> (
        match (ty, Encoding.find_local_type frame (Core_local local)) with
        | Types.Function _, Some target_type when Encoding.sort_of ty = Encoding.sort_of target_type
          ->
            Logic.equal term target
        | _ -> Logic.Boolean false)
    | None -> Logic.Boolean false

let lambda_captures_target (query : Query.t) lambda target =
  match
    (Counters.find_lambda_captures query lambda, Cost_promises.find_call_target query target)
  with
  | Some captured, Some local -> List.mem local captured
  | _ -> false

let make_reach_formula (frame : State.frame) (values : State.passed list) term =
  Logic.disjunction
    (List.map
       (fun (passed : State.passed) ->
         if lambda_captures_target frame.query passed.term term then Logic.Boolean true
         else make_may_be_target frame passed.term passed.type_ term)
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

let find_capability_reach (frame : State.frame) ~(uses : Types.capability_set) capability =
  let rec reach enclosing uses =
    let providers = list_providers enclosing in
    let find_provider used =
      List.find_opt
        (fun ((provider : Core.provided), _) -> Path.equal provider.capability used)
        providers
    in
    let reach_through ((provider : Core.provided), outer) =
      match
        Interface.Definition.find_impl_interface frame.environment.lookups.interface provider.impl
      with
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
  reach frame.provided uses

let compute_capability_amount (frame : State.frame) ~uses capability counter ~direct =
  match find_capability_reach frame ~uses capability with
  | Not_reached -> Costs.zero
  | Reached_through_providers -> Counters.declare_unknown_amount frame counter
  | Reached_directly -> direct ()

let passes_lambda_assuming_recursive_costs (query : Query.t) (values : State.passed list) =
  List.exists
    (fun (passed : State.passed) -> Counters.assumes_recursive_costs query passed.term)
    values

let compute_callee_amount ?(method_cost : (Language.Metric.t -> Logic.term) option)
    (query : Query.t) after ~is_recursive ~clauses:(declared_clauses : State.clauses list)
    ~(bind_frame : State.clauses -> State.frame) ~uses ~(values : State.passed list)
    ~counts_provider_potential (counter : Costs.counter) =
  if is_recursive && counter.counting = Units then Counters.note_recursive_cost_assumed query;
  let is_recursive_call =
    is_recursive && counter.counting = Units && Cost_promises.is_bounded query counter
  in
  let list_matching_costs (clauses : State.clauses) =
    let frame = bind_frame clauses in
    List.filter_map
      (fun (cost : Mir.cost) ->
        if Costs.is_same_resource cost ~locals:frame.locals counter then Some (frame, cost)
        else None)
      clauses.costs
  in
  let compute_amount ((frame : State.frame), (cost : Mir.cost)) =
    let exact_target =
      match (cost.resource, counter.resource) with
      | Calls (Capability _), Calls (Capability_method _) -> false
      | _ -> true
    in
    let counts_potential =
      cost.amortized
      || (counts_provider_potential && match cost.bound with Order_of _ -> true | _ -> false)
    in
    {
      Costs.amount =
        compute_promised_amount after counter cost.bound
          ~evaluate:(fun amount -> snd (Validity.read_specification frame amount))
          ~is_recursive_call ~exact_target
          ~is_converted:(counts_potential <> counter.amortized);
      counted = (if counts_potential then Potential_change else No_potential);
    }
  in
  let make_counted amount = Costs.make_counted_charge counter amount in
  let find_first_clauses () =
    let amortized_first = counter.amortized in
    List.find_map
      (fun clauses ->
        match list_matching_costs clauses with
        | [] -> None
        | costs ->
            let amortized, plain =
              List.partition (fun (_, (cost : Mir.cost)) -> cost.amortized) costs
            in
            Some (if amortized_first then amortized @ plain else plain @ amortized))
      declared_clauses
  in
  if
    counter.counting = Units && (not is_recursive_call)
    && passes_lambda_assuming_recursive_costs query values
  then make_counted (Counters.declare_unknown_amount after counter)
  else
    match counter.resource with
    | Calls (Capability capability | Capability_method (capability, _)) ->
        make_counted
          (compute_capability_amount after ~uses capability counter ~direct:(fun () ->
               match find_first_clauses () with
               | Some (clause :: _) -> (compute_amount clause).amount
               | Some [] | None -> Counters.declare_unknown_amount after counter))
    | Calls (Through term) when make_reach_formula after values term = Logic.Boolean false ->
        make_counted Costs.zero
    | Calls (Through term) ->
        let reaches = make_reach_formula after values term in
        let receiving =
          List.filter_map
            (fun (passed : State.passed) ->
              if passed.term = term then Some passed.position else None)
            values
        in
        let captured =
          List.exists
            (fun (passed : State.passed) -> lambda_captures_target query passed.term term)
            values
        in
        make_counted
          (match find_first_clauses () with
          | Some clauses
            when (not captured) && List.length clauses >= List.length receiving && receiving <> []
            ->
              List.fold_left
                (fun total clause -> Logic.add total (compute_amount clause).amount)
                Costs.zero clauses
          | _ ->
              Costs.make_conditional_amount reaches (Counters.declare_unknown_amount after counter))
    | Metric _ -> (
        let compute_method_amount () =
          match (method_cost, counter.resource, counter.counting) with
          | Some compute_cost, Metric Time, Units ->
              {
                Costs.amount = Logic.add (compute_cost Time) (Logic.int 1);
                counted = Potential_growth;
              }
          | Some compute_cost, Metric ((Allocations | Allocated_bytes) as metric), _ ->
              {
                Costs.amount = compute_amount_within after counter (compute_cost metric);
                counted = No_potential;
              }
          | _ -> make_counted (Counters.declare_unknown_amount after counter)
        in
        match find_first_clauses () with
        | Some (clause :: _) -> compute_amount clause
        | Some [] | None -> compute_method_amount ())

let compute_step_amount ?result (frame : State.frame) (callee : Callee.t)
    (values : State.passed list) (counter : Costs.counter) =
  let make_counted amount = Costs.make_counted_charge counter amount in
  match callee.target with
  | Intrinsic { operation; _ } -> (
      let cost = Intrinsic_signatures.classify_cost operation in
      let count amount = { Costs.amount; counted = No_potential } in
      let unknown () = make_counted (Counters.declare_unknown_amount frame counter) in
      match counter.resource with
      | Metric Time -> (
          match (cost.time, counter.counting) with
          | Constant_time, _ -> count Costs.zero
          | Linear_in position, Units -> (
              match
                List.find_opt (fun (passed : State.passed) -> passed.position = position) values
              with
              | Some passed -> (
                  match passed.type_ with
                  | Types.Named { path; arguments = [ Types.Type element ] } -> (
                      match Well_known.find_builtin_type path with
                      | Some Storage ->
                          count
                            (Models.make_sequence_length element
                               (Intrinsics.make_buffer_model Storage element passed.term))
                      | _ -> unknown ())
                  | _ -> unknown ())
              | None -> unknown ())
          | Linear_in_result, Units -> (
              match result with Some result -> count result | None -> unknown ())
          | (Linear_in _ | Linear_in_result | Unbounded_time), _ -> unknown ())
      | Metric (Allocations | Allocated_bytes) -> (
          match (cost.allocations, counter.resource, counter.counting) with
          | No_allocations, _, _ -> count Costs.zero
          | Unknown_allocations, _, _ -> unknown ())
      | Calls _ -> make_counted Costs.zero)
  | Definition { capability_method = Some (capability, name); _ } -> (
      match counter.resource with
      | Calls (Capability counted | Capability_method (counted, _)) ->
          make_counted
            (compute_capability_amount frame ~uses:callee.uses counted counter ~direct:(fun () ->
                 match counter.resource with
                 | _ when not (Path.equal counted capability) ->
                     Counters.declare_unknown_amount frame counter
                 | Calls (Capability_method (_, method_)) when method_ <> name -> Costs.zero
                 | Calls _ | Metric _ -> Logic.int 1))
      | Calls (Through _) -> make_counted Costs.zero
      | Metric _ -> make_counted (Counters.declare_unknown_amount frame counter))
  | Definition _ | Function_value ->
      make_counted
        (match counter.resource with
        | Calls (Capability capability | Capability_method (capability, _)) ->
            compute_capability_amount frame ~uses:callee.uses capability counter ~direct:(fun () ->
                Counters.declare_unknown_amount frame counter)
        | Calls (Through term) ->
            Costs.make_conditional_amount
              (make_reach_formula frame values term)
              (Counters.declare_unknown_amount frame counter)
        | Metric _ -> Counters.declare_unknown_amount frame counter)

let make_callback_cost (frame : State.frame) (metric : Language.Metric.t) (ty : Types.ty) term =
  let stated_by_type =
    match ty with
    | Types.Function { costs; _ } -> Costs.find_stated_operand costs metric
    | _ -> None
  in
  match stated_by_type with
  | Some stated -> stated
  | None ->
      let sort = Encoding.sort_of ty in
      let symbol = Logic.Symbol.Callback_cost { metric; sort } in
      let cost = Logic.Apply (symbol, [ term ]) in
      let least = Costs.least_amount (Metric metric) in
      let stated_by_its_signature =
        match term with
        | Logic.Symbol (Function_value { callee; _ }) ->
            Option.bind (Contracts.read_signature frame.environment callee)
              (fun (signature : Types.signature) ->
                Costs.find_stated_operand signature.costs metric)
        | _ -> None
      in
      let shown_of_its_body =
        Option.map
          (fun (bound, showing) ->
            List.iter (Query.add_obligation frame.query) showing;
            bound)
          (Counters.take_lambda_cost frame.query term metric)
      in
      (match Option.to_list stated_by_its_signature @ Option.to_list shown_of_its_body with
      | [] -> Facts.add_theorem frame ~because:(Specifies cost) (Logic.less_equal least cost)
      | values -> List.iter (fun value -> Facts.define frame cost (Logic.larger least value)) values);
      cost

let compute_function_value_amount (frame : State.frame) ~location
    (function_type : Types.function_type) callee_term ~values (counter : Costs.counter) =
  let make_counted amount = Costs.make_counted_charge counter amount in
  let compute_call_amount metric =
    let make_cost () = make_callback_cost frame metric (Types.Function function_type) callee_term in
    let make_plain amount = { Costs.amount; counted = No_potential } in
    match
      ( counter.amortized,
        Costs.list_stated_bounds function_type.costs metric ~amortized:true,
        counter.counting )
    with
    | true, Order_of :: _, Units -> { Costs.amount = Logic.int 1; counted = Potential_change }
    | _ -> (
        match
          (Costs.list_stated_bounds function_type.costs metric ~amortized:false, counter.counting)
        with
        | Order_of :: _, Units -> make_plain (Logic.int 1)
        | Exactly_cost amount :: _, (At_most | Exactly) -> make_plain (Logic.Integer amount)
        | _, (Units | At_most) -> make_plain (compute_amount_within frame counter (make_cost ()))
        | _, Exactly ->
            let cost = make_cost () in
            if cost <> Costs.zero then
              Obligations.oblige
                ~holds_when:(Counters.read_condition frame counter)
                frame location
                (Upper_bound_in_exact_cost { metric; call = { at = location; callee = None } })
                (Logic.equal cost Costs.zero);
            make_plain cost)
  in
  match counter.resource with
  | _ when counter.counting = Units && passes_lambda_assuming_recursive_costs frame.query values ->
      make_counted (Counters.declare_unknown_amount frame counter)
  | Metric metric -> compute_call_amount metric
  | Calls (Through term) ->
      make_counted
        (if lambda_captures_target frame.query callee_term term then
           Counters.declare_unknown_amount frame counter
         else
           Costs.make_conditional_amount
             (make_may_be_target frame callee_term (Types.Function function_type) term)
             (Logic.int 1))
  | Calls (Capability capability | Capability_method (capability, _)) ->
      make_counted
        (compute_capability_amount frame ~uses:function_type.uses capability counter
           ~direct:(fun () -> Counters.declare_unknown_amount frame counter))

let is_indirect (environment : State.environment) (ty : Types.ty) variant =
  match (ty, variant) with
  | Types.Named { path; _ }, Some variant -> (
      match Interface.Definition.find_interface environment.lookups.interface path with
      | Some (Interface.Environment.Type_interface { shape = Sum variants; _ }) ->
          List.exists
            (fun (written : Types.variant) -> written.variant_name = variant && written.indirect)
            variants
      | _ -> false)
  | _ -> false

let compute_construction_amount (environment : State.environment) (ty : Types.ty) variant
    (counter : Costs.counter) =
  match counter.resource with
  | Metric (Allocations | Allocated_bytes) when not (is_indirect environment ty variant) ->
      Costs.zero
  | Metric Allocations -> Logic.int 1
  | Metric Allocated_bytes when counter.counting = Units -> Logic.int 1
  | Metric Allocated_bytes -> Logic.Symbol (Logic.Symbol.Block_bytes { type_ = ty; variant })
  | Metric Time | Calls _ -> Costs.zero

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
    visited = None;
    final_result = None;
    spent = [];
    conditional_counters = [];
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
         (Contracts.mentions_specification amount (function
           | Result | Entry _ | Visited | Final_result -> true
           | Identical _ | Applied _ | Method_cost _ | Map _ | Quantified _ -> false))

let find_static_bound (frame : State.frame) (metric : Language.Metric.t) (clauses : State.clauses)
    ~has_own_generics ~substitution ~self_type =
  let counter = Costs.make_operand_counter metric in
  let substitution = Types.combine_substitutions substitution clauses.bindings in
  List.find_map
    (fun (cost : Mir.cost) ->
      if
        cost.amortized
        || (not (Costs.is_same_resource cost ~locals:Locals.empty counter))
        || not (Conditions.holds_here frame.environment frame.query ~substitution cost.holds_when)
      then None
      else
        match (counter.counting, cost.bound) with
        | (Units, Order_of amount | (At_most | Exactly), (At_most amount | Exactly amount))
          when is_static ~has_own_generics amount -> (
            try
              let bound =
                snd
                  (Validity.read_specification
                     (make_static_frame frame clauses.callee ~substitution ~self_type)
                     amount)
              in
              Some
                (match counter.counting with
                | Units -> Costs.reduce_constants bound
                | At_most | Exactly -> bound)
            with Facts.Unsupported _ -> None)
        | (Units | At_most | Exactly), (Order_of _ | At_most _ | Exactly _) -> None)
    clauses.costs

let find_body_cost (frame : State.frame) (metric : Language.Metric.t) path ~substitution ~self_type
    =
  match
    ( Contracts.find_source frame.environment.lookups path,
      Mir.read_code frame.environment.lookups.mir path )
  with
  | Some (source, _, _), Some { form = code; _ } -> (
      let counter = Costs.make_operand_counter metric in
      let start =
        {
          (make_static_frame frame source ~substitution ~self_type) with
          spent = [ (counter, Costs.zero) ];
        }
      in
      let find_spent () =
        match Lambdas.run_lambda_body start ~lambdas:code.lambdas code.body ~type_:self_type with
        | Some (finished, result) -> (
            match (List.assoc_opt counter finished.spent, metric) with
            | Some spent, Time ->
                Some (Logic.add spent (Potentials.compute_potential finished self_type result))
            | spent, (Allocations | Allocated_bytes) -> spent
            | None, Time -> None)
        | None -> None
      in
      try find_spent () with Facts.Unsupported _ -> None)
  | _ -> None

let find_method_cost_bound (frame : State.frame) (metric : Language.Metric.t) (method_ : Path.t)
    ~trait_arguments self_type =
  let holds ty =
    try Potentials.has_potential frame.environment frame.query ty with Facts.Unsupported _ -> true
  in
  let includes_potential_made = metric = Time in
  match method_ with
  | Method { owner = trait; name; receiver } -> (
      if Well_known.is Copyable trait then
        if
          Interface.Impls.is_plain frame.environment.lookups.interface
            ~list_bounds:frame.environment.bounds self_type
          && not (holds self_type)
        then Some (Costs.least_amount (Metric metric))
        else None
      else
        let reference : Types.trait_reference = { trait; trait_arguments; associated = [] } in
        match Encoding.find_impl frame.environment reference self_type with
        | Some (impl, substitution) -> (
            let path = Path.Method { owner = impl; name; receiver } in
            match Contracts.read_signature frame.environment path with
            | Some (signature : Types.signature) -> (
                let impl_generics =
                  match
                    Interface.Definition.find_impl_interface frame.environment.lookups.interface
                      impl
                  with
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
                  &&
                  match signature.output with
                  | Returns ty -> not (holds ty)
                  | Lends (_, part) -> not (holds (Types.substitute substitution part))
                in
                let stated_bound =
                  if includes_potential_made && not makes_no_potential then None
                  else
                    Option.bind
                      (Contracts.find_method_contract frame.environment reference name receiver
                         (Impl { impl; substitution }))
                      (fun contract ->
                        List.find_map
                          (fun (clauses : State.clauses) ->
                            find_static_bound frame metric clauses ~has_own_generics
                              ~substitution:
                                (if clauses.inherited then
                                   Contracts.make_trait_substitution frame.environment.lookups
                                     reference self_type
                                 else substitution)
                              ~self_type)
                          (Contracts.list_clause_sets contract))
                in
                match (stated_bound, impl) with
                | Some bound, _ -> Some bound
                | None, Derived _
                  when signature.receiver = None && signature.parameters = []
                       && not has_own_generics ->
                    find_body_cost frame metric path ~substitution ~self_type
                | None, _ -> None)
            | None -> None)
        | None -> None)
  | _ -> None

let make_method_cost (frame : State.frame) (metric : Language.Metric.t) (method_ : Path.t)
    ~trait_arguments self_type =
  let symbol = Logic.Symbol.Method_cost { metric; method_; trait_arguments; self_type } in
  Query.run_once frame.query (Method_cost_bound symbol) (fun () ->
      let least = Costs.least_amount (Metric metric) in
      Query.add_theorem frame.query ~because:(Specifies (Logic.Symbol symbol))
        (Logic.less_equal least (Logic.Symbol symbol));
      match find_method_cost_bound frame metric method_ ~trait_arguments self_type with
      | Some bound ->
          Query.add_theorem frame.query ~because:Generalizes_an_execution
            (Logic.less_equal (Logic.Symbol symbol) (Logic.larger bound least))
      | None -> Counters.note_unbounded_method_cost frame.query symbol method_ ~self_type);
  Logic.Symbol symbol

let compute_method_cost (frame : State.frame) (metric : Language.Metric.t) (callee : Callee.t) =
  match callee.target with
  | Definition { trait_method = Some { trait; name; receiver; self_type; _ }; _ } ->
      make_method_cost frame metric
        (Path.Method { owner = trait.trait; name; receiver })
        ~trait_arguments:trait.trait_arguments self_type
  | Definition _ | Function_value | Intrinsic _ ->
      Facts.raise_unsupported Whole_definition (Metric_of_non_trait_method metric)

let has_method_cost (environment : State.environment) (definition : Callee.definition) =
  match definition.trait_method with
  | Some { evidence = Bound; _ } -> true
  | Some { evidence = Impl _ | Derived_for_view _; _ } -> (
      match Contracts.read_signature environment definition.path with
      | Some (signature : Types.signature) -> Types.terminates signature.uses
      | None -> true)
  | None -> false

let list_held_types (environment : State.environment) (query : Query.t) (values : State.passed list)
    ~result_type =
  List.filter
    (fun ty -> try Potentials.has_potential environment query ty with Facts.Unsupported _ -> true)
    (result_type
    :: List.filter_map
         (fun (passed : State.passed) ->
           match passed.mode with
           | Language.Mode.Mut | Own -> Some passed.declared_type
           | Read -> None)
         values)

let spend_copy ?literal (frame : State.frame) ~(declared : Types.ty) term =
  let ty = Types.erase_views declared in
  let literal =
    match (literal, ty) with
    | Some (Language.Literal.Elements _), Types.Named { arguments = [ Types.Type element ]; _ }
      when not
             (Interface.Impls.is_plain frame.environment.lookups.interface
                ~list_bounds:frame.environment.bounds element) ->
        None
    | literal, _ -> literal
  in
  if
    frame.spent = []
    || Interface.Impls.is_plain frame.environment.lookups.interface
         ~list_bounds:frame.environment.bounds ty
       && not
            (try Potentials.has_potential frame.environment frame.query declared
             with Facts.Unsupported _ -> true)
  then frame
  else
    let declare_copy_cost_of metric copied =
      make_method_cost frame metric
        (Well_known.make_method_path Copyable_copy)
        ~trait_arguments:[] copied
    in
    let declare_copy_cost metric = declare_copy_cost_of metric ty in
    let compute_elements_cost metric =
      Option.map
        (fun ({ element; model_of; _ } : Potentials.buffer) ->
          let per_element =
            if
              Interface.Impls.is_plain frame.environment.lookups.interface
                ~list_bounds:frame.environment.bounds
                (Potentials.find_declared_element (Types.strip_view declared) ~erased:element)
            then Costs.least_amount (Metric metric)
            else declare_copy_cost_of metric element
          in
          Logic.multiply (Models.make_sequence_length element (model_of term)) per_element)
        (Potentials.find_buffer frame.environment frame.query ty)
    in
    Counters.spend_operation frame
      ~potential_change:(Some (fun () -> Potentials.compute_potential frame declared term))
      ~held:(fun () -> list_held_types frame.environment frame.query [] ~result_type:declared)
      (fun (counter : Costs.counter) ->
        let make_plain amount = { Costs.amount; counted = No_potential } in
        let make_unknown () =
          Costs.make_counted_charge counter (Counters.declare_unknown_amount frame counter)
        in
        match (literal, counter.resource, counter.counting) with
        | None, Metric Time, Units when Option.is_some (compute_elements_cost Time) ->
            make_plain (Logic.add (Option.get (compute_elements_cost Time)) (Logic.int 1))
        | _, Metric Time, Units ->
            let time = match literal with Some _ -> Costs.zero | None -> declare_copy_cost Time in
            { Costs.amount = Logic.add time (Logic.int 1); counted = Potential_change }
        | Some literal, Metric (Allocations | Allocated_bytes), Units
        | Some literal, Metric Allocations, _ ->
            make_plain
              (Logic.int
                 (match literal with Text "" | Elements [] -> 0 | Text _ | Elements _ -> 1))
        | Some (Text text), Metric Allocated_bytes, (At_most | Exactly) ->
            make_plain (Logic.int (String.length text))
        | Some (Elements _), Metric Allocated_bytes, (At_most | Exactly) -> make_unknown ()
        | Some _, Calls _, _ -> Costs.make_counted_charge counter Costs.zero
        | None, Metric Allocations, _ when Option.is_some (compute_elements_cost Allocations) ->
            make_plain
              (compute_amount_within frame counter
                 (Logic.add (Option.get (compute_elements_cost Allocations)) (Logic.int 1)))
        | None, Metric ((Allocations | Allocated_bytes) as metric), _ ->
            make_plain (compute_amount_within frame counter (declare_copy_cost metric))
        | _, Metric Time, (At_most | Exactly) | None, Calls _, _ -> make_unknown ())

let spend_wait_for_tasks (frame : State.frame) =
  Counters.spend frame (fun (counter : Costs.counter) ->
      match counter.resource with
      | Metric Time -> Counters.declare_unknown_amount frame counter
      | Metric (Allocations | Allocated_bytes) | Calls _ -> Costs.zero)

let spend_contract_call ~(before : State.frame) ~(after : State.frame) (site : Invocation.site)
    (callee : Callee.t) (definition : Callee.definition) (contract : State.contract)
    (values : State.passed list) ~changed ~result ~result_type ~final ~is_recursive ~bind_frame =
  let compute_potential_change () =
    Logic.add
      (Potentials.compute_arguments_potential_change ~before ~after values ~changed)
      (match contract.result_kind with
      | `Lends -> (
          match final with
          | Some final ->
              Logic.subtract
                (Potentials.compute_potential after result_type result)
                (Potentials.compute_potential after result_type final)
          | None -> Costs.zero)
      | `Returns -> Potentials.compute_potential after result_type result)
  in
  let declared_clauses = Contracts.list_clause_sets contract in
  let method_cost =
    lazy
      (if has_method_cost before.environment definition then
         Some (fun metric -> compute_method_cost before metric callee)
       else None)
  in
  let list_metric_costs metric =
    List.concat_map
      (fun (clauses : State.clauses) ->
        List.filter (fun (cost : Mir.cost) -> cost.resource = Metric metric) clauses.costs)
      declared_clauses
  in
  let counts_provider_potential = Option.is_some definition.capability_method in
  let note_amount (counter : Costs.counter) amount =
    match counter.resource with
    | Metric metric when Facts.is_home before ->
        let state = Query.read_state before.query state in
        state.call_amounts <-
          {
            call = Facts.quote before.source site.origin;
            callee = definition.path;
            states_cost = Option.is_some (Lazy.force method_cost) || list_metric_costs metric <> [];
            counts_potential =
              counts_provider_potential
              || (metric = Time && Option.is_some (Lazy.force method_cost))
              || List.exists (fun (cost : Mir.cost) -> cost.amortized) (list_metric_costs metric);
            counter;
            amount;
          }
          :: state.call_amounts
    | Metric _ | Calls _ -> ()
  in
  Counters.spend_operation after ~potential_change:(Some compute_potential_change)
    ~held:(fun () -> list_held_types before.environment before.query values ~result_type)
    ~note:note_amount
    (fun counter ->
      match (definition.capability_method, counter.resource) with
      | Some _, Calls _ -> compute_step_amount after callee values counter
      | _ ->
          compute_callee_amount ?method_cost:(Lazy.force method_cost) before.query after
            ~is_recursive ~clauses:declared_clauses ~bind_frame ~uses:callee.uses ~values
            ~counts_provider_potential counter)

let spend_call_without_a_contract (frame : State.frame) callee values =
  Counters.spend_operation frame ~potential_change:None
    ~held:(fun () -> list_held_types frame.environment frame.query values ~result_type:Types.unit)
    (compute_step_amount frame callee values)

let spend_derived_equality (frame : State.frame) (callee : Callee.t) values ~result_type ~result =
  Counters.spend_operation frame
    ~potential_change:
      (Some
         (fun () ->
           Potentials.compute_call_potential_change ~before:frame ~after:frame values ~changed:[]
             ~result_type ~result))
    ~held:(fun () -> list_held_types frame.environment frame.query values ~result_type)
    (compute_callee_amount
       ~method_cost:(fun metric -> compute_method_cost frame metric callee)
       frame.query frame ~is_recursive:false ~clauses:[]
       ~bind_frame:(fun _ -> frame)
       ~uses:callee.uses ~values ~counts_provider_potential:false)

let spend_indirect_call ~before ~(after : State.frame) ~location function_type called
    (values : State.passed list) ~changed ~result_type ~result =
  Counters.spend_operation after
    ~potential_change:
      (Some
         (fun () ->
           Potentials.compute_call_potential_change ~before ~after values ~changed ~result_type
             ~result))
    ~held:(fun () -> list_held_types after.environment after.query values ~result_type)
    (compute_function_value_amount after ~location function_type called ~values)

let spend_intrinsic (frame : State.frame) callee operation (values : State.passed list) ~changed
    ~result_type ~result =
  Counters.spend_operation frame
    ~potential_change:
      (Some
         (fun () ->
           if Intrinsics.keeps_potential operation then Costs.zero
           else
             Potentials.compute_call_potential_change ~before:frame ~after:frame values
               ~changed:
                 (List.filter_map
                    (fun ((passed : State.passed), later) ->
                      if passed.mode = Language.Mode.Mut then Some (passed.position, later)
                      else None)
                    (List.combine values changed))
               ~result_type ~result))
    ~held:(fun () -> list_held_types frame.environment frame.query values ~result_type)
    (compute_step_amount ~result frame callee values)
