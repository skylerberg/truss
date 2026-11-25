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

let compute_promised_amount (context : State.context) frame (counter : Costs.counter)
    (bound : Mir.bound) ~evaluate ~is_recursive_call ~exact_target ~is_converted =
  match (bound, counter.counting) with
  | Order_of amount, Units ->
      let amount = evaluate amount in
      if is_recursive_call then begin
        context.recursive_costs_assumed <- context.recursive_costs_assumed + 1;
        let hypothesis = Costs.at_least_zero (Costs.bound amount) in
        if counter.resource = Metric Time then Costs.plus hypothesis (Logic.int 1) else hypothesis
      end
      else Costs.units (if is_converted then amount else Costs.reduce_constants amount)
  | (At_most amount | Exactly amount), Units -> Costs.at_least_zero (evaluate amount)
  | At_most amount, (At_most | Exactly) -> declare_bounded_amount context frame (evaluate amount)
  | Exactly amount, (At_most | Exactly) ->
      let amount = evaluate amount in
      if exact_target then amount else declare_bounded_amount context frame amount
  | Order_of _, _ -> Operations.declare_unknown_amount context frame counter

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
    ~(bind_frame : State.clauses -> State.frame) ~uses ~(values : State.passed list)
    ~counts_provider_potential (counter : Costs.counter) =
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
    let counts_potential =
      cost.amortized
      || (counts_provider_potential && match cost.bound with Order_of _ -> true | _ -> false)
    in
    {
      Costs.amount =
        compute_promised_amount context after counter cost.bound
          ~evaluate:(fun amount -> snd (Validity.read_specification context frame amount))
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
              List.partition (fun (_, _, (cost : Mir.cost)) -> cost.amortized) costs
            in
            Some (if amortized_first then amortized @ plain else plain @ amortized))
      declared_clauses
  in
  match counter.resource with
  | Calls (Capability capability | Capability_method (capability, _)) ->
      make_counted
        (compute_capability_amount context after ~uses capability counter ~direct:(fun () ->
             match find_first_clauses () with
             | Some (clause :: _) -> (compute_amount clause).amount
             | Some [] | None -> Operations.declare_unknown_amount context after counter))
  | Calls (Through term) when make_reach_formula context after values term = Logic.Boolean false ->
      make_counted Costs.zero
  | Calls (Through term) ->
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
      make_counted
        (match find_first_clauses () with
        | Some clauses
          when (not captured) && List.length clauses >= List.length receiving && receiving <> [] ->
            List.fold_left
              (fun total clause -> Costs.plus total (compute_amount clause).amount)
              Costs.zero clauses
        | _ ->
            make_conditional_amount reaches
              (Operations.declare_unknown_amount context after counter))
  | Metric _ -> (
      let compute_method_amount () =
        match (method_cost, counter.resource, counter.counting) with
        | Some compute_cost, Metric Time, Units ->
            {
              Costs.amount = Costs.plus (compute_cost Time) (Logic.int 1);
              counted = Potential_growth;
            }
        | Some compute_cost, Metric ((Allocations | Allocated_bytes) as metric), _ ->
            {
              Costs.amount = compute_amount_within context after counter (compute_cost metric);
              counted = No_potential;
            }
        | _ -> make_counted (Operations.declare_unknown_amount context after counter)
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

let compute_step_amount ?result context frame (invocation : Invocation.t)
    (values : State.passed list) (counter : Costs.counter) =
  let make_counted amount = Costs.make_counted_charge counter amount in
  match invocation.callee with
  | Intrinsic { operation; type_arguments } -> (
      let cost = Intrinsic_signatures.classify_cost operation in
      let count amount = { Costs.amount; counted = No_potential } in
      let unknown () = make_counted (Operations.declare_unknown_amount context frame counter) in
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
                            (Models.make_sequence_length context element
                               (Intrinsics.make_buffer_model context Storage element passed.term))
                      | _ -> unknown ())
                  | _ -> unknown ())
              | None -> unknown ())
          | Linear_in_result, Units -> (
              match result with Some result -> count result | None -> unknown ())
          | (Linear_in _ | Linear_in_result | Unbounded_time), _ -> unknown ())
      | Metric (Allocations | Allocated_bytes) -> (
          match (cost.allocations, counter.resource, counter.counting) with
          | No_allocations, _, _ -> count Costs.zero
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
                  count
                    (Logic.ite
                       (Logic.greater amount_term (Logic.int 0))
                       (Logic.int 1) (Logic.int 0))
              | _ -> unknown ())
          | Unknown_allocations, _, _ -> unknown ())
      | Calls _ -> make_counted Costs.zero)
  | Capability_method { capability; name } -> (
      match counter.resource with
      | Calls (Capability counted | Capability_method (counted, _)) ->
          make_counted
            (compute_capability_amount context frame ~uses:invocation.uses counted counter
               ~direct:(fun () ->
                 match counter.resource with
                 | _ when not (Path.equal counted capability) ->
                     Operations.declare_unknown_amount context frame counter
                 | Calls (Capability_method (_, method_)) when method_ <> name -> Costs.zero
                 | Calls _ | Metric _ -> Logic.int 1))
      | Calls (Through _) -> make_counted Costs.zero
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
                ~uses:invocation.uses ~values ~counts_provider_potential:true counter
          | None -> make_counted (Operations.declare_unknown_amount context frame counter)))
  | Function _ | Trait_method _ | Indirect () ->
      make_counted
        (match counter.resource with
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

let compute_buffer context (ty : Types.ty) : State.buffer option =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element; Types.Value _ ] }
    when Well_known.find_builtin_type path = Some Array ->
      Option.map
        (fun model_of -> { State.kind = Array; element; model_of })
        (Models.find_model_function context ty ~model:(Models.make_sequence_type element))
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Well_known.find_builtin_type path = Some Storage ->
      Some
        {
          kind = Storage;
          element;
          model_of = (fun term -> Intrinsics.make_buffer_model context Storage element term);
        }
  | Types.Named { path; arguments } when Types.find_builtin ty = None -> (
      match Interface.Definition.find_interface context.lookups.interface path with
      | Some (Interface.Environment.Type_interface { shape = Record [ field ]; type_generics; _ })
        -> (
          let substitution = Types.make_substitution type_generics arguments in
          match Types.substitute_erased substitution field.field_type with
          | Types.Named { path = field_path; arguments = [ Types.Type element ] } -> (
              match Well_known.find_builtin_type field_path with
              | Some Storage ->
                  Option.map
                    (fun model_of -> { State.kind = Storage; element; model_of })
                    (Models.find_model_function context ty
                       ~model:(Models.make_sequence_type element))
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None

let find_buffer (context : State.context) (ty : Types.ty) =
  let key = ty in
  match Tables.Type_table.find_opt context.buffers key with
  | Some buffer -> buffer
  | None ->
      let buffer = compute_buffer context ty in
      Tables.Type_table.replace context.buffers key buffer;
      buffer

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

let find_declared_element (declared : Types.ty) ~(erased : Types.ty) =
  match declared with
  | Types.Named { arguments = Types.Type element :: _; _ }
    when Types.equal (Types.erase_views element) erased ->
      element
  | _ -> erased

let list_declared_fields (context : State.context) (declared : Types.ty) =
  match declared with
  | Types.Named { path; arguments } when Types.find_builtin declared = None -> (
      match Interface.Definition.find_interface context.lookups.interface path with
      | Some (Interface.Environment.Type_interface interface) ->
          let substitution = Types.make_substitution interface.type_generics arguments in
          let declare variant =
            List.map (fun (field : Types.field) ->
                ((variant, field.field_name), Types.substitute substitution field.field_type))
          in
          Some
            (match interface.shape with
            | Record fields -> declare None fields
            | Sum variants ->
                List.concat_map
                  (fun (variant : Types.variant) ->
                    declare (Some variant.variant_name) (Option.value variant.fields ~default:[]))
                  variants
            | Todo_type | Builtin_type _ -> [])
      | _ -> None)
  | _ -> None

let find_potential_clause context (ty : Types.ty) =
  match Validity.find_type_clauses context ty with
  | Some (source, { potential = Some potential; _ }) -> Some (source, potential)
  | _ -> None

let compute_declared_potential context frame (ty : Types.ty) term =
  match find_potential_clause context ty with
  | Some (source, written) ->
      snd
        (Validity.read_specification context
           (Validity.make_type_frame context frame source ty ~self:(Some term))
           written)
  | None -> Costs.zero

let rec has_potential (context : State.context) ?(seen = []) (declared : Types.ty) =
  if seen <> [] then holds_potential_type context ~seen declared
  else
    match Tables.Type_table.find_opt context.holds_potential declared with
    | Some holds -> holds
    | None ->
        let holds = holds_potential_type context ~seen declared in
        Tables.Type_table.replace context.holds_potential declared holds;
        holds

and holds_potential_type context ~seen (declared : Types.ty) =
  let ty = Types.erase_views declared in
  if Types.is_view declared || List.exists (Types.equal declared) seen then false
  else
    match ty with
    | Parameter _ ->
        not (Interface.Impls.is_plain context.lookups.interface ~list_bounds:context.bounds ty)
    | Named _ when find_potential_clause context ty <> None -> true
    | Named _ when Option.is_some (find_buffer context ty) -> (
        match find_buffer context ty with
        | Some { kind = Storage; _ } -> true
        | Some { element; _ } ->
            has_potential context ~seen:(declared :: seen)
              (find_declared_element declared ~erased:element)
        | None -> false)
    | Types.Named _ when Types.find_builtin ty = None -> (
        match list_declared_fields context declared with
        | Some fields ->
            List.exists
              (fun (_, field_type) -> has_potential context ~seen:(declared :: seen) field_type)
              fields
        | None -> false)
    | Types.Named { arguments; _ } ->
        if
          List.exists
            (function
              | Types.Type element -> has_potential context ~seen:(ty :: seen) element | _ -> false)
            arguments
        then Facts.raise_unsupported Whole_definition Potential_of_elements
        else false
    | _ -> false

and compute_potential context (frame : State.frame) ?(seen = []) (declared : Types.ty) term =
  if not (has_potential context declared) then Costs.zero
  else begin
    let ty = Types.erase_views declared in
    let held = declare_held_symbol context declared term in
    if (not (List.mem held context.potentials)) && not (Logic.mentions frame.bound term) then begin
      context.potentials <- held :: context.potentials;
      Facts.add_frame_fact context frame
        Logic.(
          Validity.make_validity context frame ~assuming:true ty term ==> less_equal (int 0) held);
      match (find_potential_clause context ty, Facts.find_constructors context ty) with
      | None, None when Option.is_some (find_buffer context ty) -> (
          match find_buffer context ty with
          | Some { kind; element; model_of } ->
              let sequence = model_of term in
              let slack = Intrinsics.declare_buffer_slack context ty term in
              let length = Models.make_sequence_length context element sequence in
              Facts.add_frame_fact context frame
                Logic.(less_equal (int 0) slack &&& less_equal slack (multiply (int 2) length));
              (match (ty, kind) with
              | Types.Named { path; _ }, _ when Well_known.find_builtin_type path = Some Storage ->
                  let saved =
                    Logic.subtract
                      (Logic.multiply (Logic.int 2) length)
                      (Intrinsics.make_buffer_capacity context element term)
                  in
                  Facts.add_frame_fact context frame
                    (Logic.equal slack
                       (Logic.ite (Logic.greater_equal saved (Logic.int 0)) saved (Logic.int 0)))
              | _, Array -> Facts.add_frame_fact context frame (Logic.equal slack (Logic.int 0))
              | _ -> ());
              let elements =
                if has_potential context (find_declared_element declared ~erased:element) then
                  sum_element_potentials context element sequence
                else Costs.zero
              in
              Facts.add_frame_fact context frame (Logic.equal held (Costs.plus slack elements))
          | None -> ())
      | _, Some shape -> (
          try
            let declared_potential = compute_declared_potential context frame ty term in
            let parts =
              choose_by_variant ty term shape
                (compute_parts_potential context frame ~seen declared term)
            in
            Facts.add_frame_fact context frame
              (Logic.equal held (Costs.plus declared_potential parts))
          with Facts.Unsupported _ -> ())
      | _ -> ()
    end;
    match (find_potential_clause context ty, Facts.find_constructors context ty) with
    | None, Some [ (None, fields) ] -> (
        try compute_parts_potential context frame ~seen declared term (None, fields)
        with Facts.Unsupported _ -> held)
    | _ -> held
  end

and compute_parts_potential context frame ~seen declared term (variant, fields) =
  let ty = Types.erase_views declared in
  let declared_fields = Option.value ~default:[] (list_declared_fields context declared) in
  List.fold_left
    (fun total (field, erased_field_type) ->
      let field_type =
        Option.value ~default:erased_field_type (List.assoc_opt (variant, field) declared_fields)
      in
      if has_potential context field_type then
        let part = Validity.select_field context ty variant field term in
        Costs.plus total
          (if List.exists (Types.equal field_type) (declared :: seen) then
             declare_held_symbol context field_type part
           else compute_potential context frame ~seen:(declared :: seen) field_type part)
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
          match (find_potential_clause context ty, find_buffer context ty) with
          | None, Some { element; model_of; _ } when has_potential context element ->
              sum_element_potentials context element (model_of term)
          | _ -> Costs.zero)
  in
  sum_elements ~enclosing:[] ty term

let compute_accessible_potential context frame (ty : Types.ty) term =
  if Types.is_view ty then compute_elements_potential context (Types.erase_views ty) term
  else compute_potential context frame ty term

let has_declared_potential context ty = Option.is_some (find_potential_clause context ty)

let compute_arguments_potential_change context ~(before : State.frame) ~(after : State.frame)
    (values : State.passed list) ~changed =
  List.fold_left
    (fun total (passed : State.passed) ->
      match passed.mode with
      | Language.Mode.Mut -> (
          match List.assoc_opt passed.position changed with
          | Some later ->
              Costs.plus total
                (Costs.minus
                   (compute_accessible_potential context after passed.type_ later)
                   (compute_accessible_potential context before passed.type_ passed.term))
          | None -> total)
      | Own -> Costs.minus total (compute_potential context before passed.type_ passed.term)
      | Read -> total)
    Costs.zero values

let compute_call_potential_change context ~before ~after values ~changed ~result_type ~result =
  Costs.plus
    (compute_arguments_potential_change context ~before ~after values ~changed)
    (compute_potential context after result_type result)

let assume_element_potential_change context frame (sequence : Types.ty) ~before ~after ~replaced
    ~written =
  match find_buffer context sequence with
  | Some { element; model_of; _ } -> (
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
              let bound =
                snd
                  (Validity.read_specification context
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
        | argument -> Types.substitute_argument_erased frame.substitution argument
      in
      declare_method_cost context frame metric
        (Path.Method { owner = trait.trait; name; receiver })
        ~trait_arguments:(List.map substitute_argument trait.trait_arguments)
        (Facts.substitute_type context frame self_type)
  | _ -> Facts.raise_unsupported Whole_definition (Metric_of_non_trait_method metric)
