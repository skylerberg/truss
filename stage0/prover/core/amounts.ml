let run_code context frame (code : Mir.t) ~type_ =
  match Lambdas.run_lambda_body context frame ~lambdas:code.lambdas code.body ~type_ with
  | Some returned -> returned
  | None -> (frame, Facts.arrive context frame "unfinished" type_)

let make_empty_parts context frame element =
  let parts =
    Facts.declare_fresh context frame "parts"
      (Facts.declare_sort context (Models.make_sequence_type element))
  in
  Facts.assume context frame
    (Logic.equal (Models.make_sequence_length context element parts) (Logic.int 0));
  parts

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

let assume_typed context frame term =
  match Operations.find_innermost_axiom context frame term with
  | Some axiom -> axiom.hypotheses <- Logic.( ==> ) frame.condition term :: axiom.hypotheses
  | None -> Facts.assume context frame term

let rec compare_lexicographically before after =
  match (before, after) with
  | [ right ], [ left ] ->
      Logic.(Operation ("<=", [ int 0; right ]) &&& Operation ("<", [ left; right ]))
  | right :: before, left :: after ->
      Logic.(
        Operation ("<=", [ int 0; right ])
        &&& (Operation ("<", [ left; right ])
            ||| (equal left right &&& compare_lexicographically before after)))
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
  Facts.assume context frame
    Logic.(Operation ("<=", [ int 0; amount ]) &&& Operation ("<=", [ amount; bound ]));
  amount

let compute_amount_within context frame (counter : Costs.counter) bound =
  match counter.counting with
  | Units -> bound
  | At_most | Exactly -> declare_bounded_amount context frame bound

let declare_amount context frame (counter : Costs.counter) : Costs.amount -> Logic.term = function
  | Exact amount -> amount
  | Within bound when bound = Costs.zero -> Costs.zero
  | Within bound -> declare_bounded_amount context frame bound
  | Unknown -> Operations.declare_unknown_amount context frame counter

let declare_counted_amount (context : State.context) frame ~location ~describe_upper_bound
    (counter : Costs.counter) (amount : Costs.amount) =
  match amount with
  | Within bound
    when counter.counting = Exactly && bound <> Costs.zero
         && List.mem counter context.promised_counters ->
      Facts.oblige context frame Cost location
        [ Text (describe_upper_bound ()) ]
        (Logic.equal bound Costs.zero);
      bound
  | Exact _ | Within _ | Unknown -> declare_amount context frame counter amount

let is_exact_target (cost : Mir.cost) (counter : Costs.counter) =
  match (cost.resource, counter.resource) with
  | Calls (Capability _), Calls (Capability_method _) -> false
  | _ -> true

let compute_promised_amount (counter : Costs.counter) (cost : Mir.cost) ~evaluate ~is_recursive_call
    ~change : Costs.amount =
  match (cost.bound, counter.counting) with
  | Order_of amount, Units ->
      let amount = evaluate amount in
      let amount =
        if is_recursive_call then
          let hypothesis = Costs.at_least_zero (Costs.bound amount) in
          if counter.resource = Metric Time then Costs.plus hypothesis (Logic.int 1) else hypothesis
        else Costs.units amount
      in
      Exact (Costs.minus amount change)
  | (At_most amount | Exactly amount), Units ->
      Exact (Costs.at_least_zero (Costs.minus (evaluate amount) change))
  | Exactly amount, (At_most | Exactly) when is_exact_target cost counter ->
      Exact (Costs.minus (evaluate amount) change)
  | (At_most amount | Exactly amount), (At_most | Exactly) ->
      Within (Costs.minus (evaluate amount) change)
  | (Order_of _ | Finite), _ -> Unknown

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

let make_conditional_amount condition amount =
  match condition with
  | Logic.Boolean true -> amount
  | Logic.Boolean false -> Costs.zero
  | condition -> Logic.ite condition amount Costs.zero

let may_use (uses : Types.capability list) capability =
  List.exists
    (function
      | Types.Capability used -> Path.equal used capability
      | Types.Capability_parameter _ | Types.Capability_projection _ | Types.Capability_variable _
        ->
          true
      | Types.Divergence _ -> false
      | Types.Capability_error _ -> Facts.raise_bug "the prover reads a capability with an error")
    uses

let make_is_zero : Costs.amount -> Logic.term = function
  | Exact amount | Within amount -> Logic.equal amount Costs.zero
  | Unknown -> Logic.Boolean false

let find_lambda_cost (context : State.context) counter term =
  List.assoc_opt (term, Costs.make_one_call_counter counter) context.lambda_costs

let rec rely_on_lambda_costs (context : State.context) counter function_term =
  match function_term with
  | Logic.Operation ("ite", [ _; chosen; otherwise ]) ->
      rely_on_lambda_costs context counter chosen;
      rely_on_lambda_costs context counter otherwise
  | _ ->
      Option.iter
        (fun (cost : State.lambda_cost) ->
          context.obligations <- List.rev_append cost.showing context.obligations;
          cost.showing <- [])
        (find_lambda_cost context counter function_term)

let count_stated_calls (context : State.context) (counter : Costs.counter) callee : Costs.amount =
  let find_literal_amount (cost : Mir.cost) =
    if cost.amortized || not (is_same_resource cost ~locals:Locals.empty counter) then None
    else
      match cost.bound with
      | Order_of amount | At_most amount | Exactly amount ->
          Option.map
            (fun literal ->
              compute_promised_amount counter cost
                ~evaluate:(fun _ -> Logic.Integer literal)
                ~is_recursive_call:false ~change:Costs.zero)
            (Contracts.find_integer_literal amount)
      | Finite -> None
  in
  match Contracts.find_function_contract context.lookups callee with
  | Some contract when not (Facts.is_in_recursion_group context callee) ->
      Option.value ~default:Costs.Unknown
        (List.find_map
           (fun (clauses : State.clauses) -> List.find_map find_literal_amount clauses.costs)
           (Contracts.list_declared_clauses contract))
  | Some _ | None -> Unknown

let rec count_calls_in_one_call (context : State.context) frame (counter : Costs.counter)
    (target : Costs.target) (function_type : Types.function_type) function_term : Costs.amount =
  match function_term with
  | Logic.Operation ("ite", [ condition; chosen; otherwise ]) ->
      Costs.choose condition
        (count_calls_in_one_call context frame counter target function_type chosen)
        (count_calls_in_one_call context frame counter target function_type otherwise)
  | _ -> (
      match (find_lambda_cost context counter function_term, target, function_term) with
      | Some cost, _, _ -> cost.in_one_call
      | None, Through counted, _ ->
          Exact
            (make_conditional_amount
               (make_may_be_target context frame function_term (Types.Function function_type)
                  counted)
               (Logic.int 1))
      | None, (Capability capability | Capability_method (capability, _)), _
        when not (may_use (function_type.uses :> Types.capability list) capability) ->
          Exact Costs.zero
      | None, (Capability _ | Capability_method _), Logic.Symbol (Function_value { callee; _ }) ->
          count_stated_calls context counter callee
      | None, (Capability _ | Capability_method _), _ -> Unknown)

let uses_capability_itself (context : State.context) callee capability =
  match Interface.Impls.read_signature context.lookups.interface callee with
  | Some (signature : Types.signature) ->
      let is_granted_by_callbacks (granted : Types.parameter) =
        let without_granted =
          Types.make_capability_substitution [ granted ] [ (granted.name, Types.no_capabilities) ]
        in
        let names_granted ty = not (Types.equal ty (Types.substitute without_granted ty)) in
        List.for_all
          (fun (ty : Types.ty) ->
            match ty with
            | Function function_type ->
                not (names_granted (Function { function_type with uses = Types.no_capabilities }))
            | ty -> not (names_granted ty))
          (List.map (fun (parameter : Types.parameter_info) -> parameter.type_) signature.parameters
          @ List.map snd (Option.to_list signature.receiver))
      in
      List.exists
        (function
          | Types.Capability used -> Path.equal used capability
          | Types.Capability_parameter granted -> not (is_granted_by_callbacks granted)
          | Types.Capability_projection _ | Types.Capability_variable _ -> true
          | Types.Divergence _ -> false
          | Types.Capability_error _ ->
              Facts.raise_bug "the prover reads a capability with an error")
        (signature.uses :> Types.capability list)
  | None -> true

let find_first_costs (frames : (State.clauses * State.frame Lazy.t) list) ~amortized_first
    is_counted =
  List.find_map
    (fun ((clauses : State.clauses), frame) ->
      match List.filter (is_counted clauses) clauses.costs with
      | [] -> None
      | costs ->
          let amortized, plain = List.partition (fun (cost : Mir.cost) -> cost.amortized) costs in
          Some (Lazy.force frame, if amortized_first then amortized @ plain else plain @ amortized))
    frames

let compute_callee_amount ?(method_cost : (Metric.t -> Logic.term) option) (context : State.context)
    after ~location ~path ~clauses:(declared_clauses : State.clauses list)
    ~(bind_frame : State.clauses -> State.frame) ~uses ~(values : State.passed list) ~change
    (counter : Costs.counter) =
  let frames = List.map (fun clauses -> (clauses, lazy (bind_frame clauses))) declared_clauses in
  let find_first_costs =
    find_first_costs frames ~amortized_first:(Option.is_some change && counter.amortized)
  in
  let compute_cost_amount (frame : State.frame) (cost : Mir.cost) : Costs.amount =
    match (cost.amortized, change) with
    | true, None -> Unknown
    | _ ->
        compute_promised_amount counter cost
          ~evaluate:(fun amount -> snd (Validity.read_specification context frame amount))
          ~is_recursive_call:
            (counter.counting = Units
            && List.mem counter context.promised_counters
            && Facts.is_in_recursion_group context path)
          ~change:
            (match (cost.amortized, change) with
            | true, Some compute_change -> compute_change ()
            | _ -> Costs.zero)
  in
  let find_stated_costs () =
    find_first_costs (fun clauses cost ->
        is_same_resource cost ~locals:(Lazy.force (List.assq clauses frames)).locals counter)
  in
  let count_calls_through position =
    Option.map
      (fun (frame, costs) ->
        let promised = List.map (compute_cost_amount frame) costs in
        let is_exact = function Costs.Exact _ -> true | Within _ | Unknown -> false
        and is_bounded = function Costs.Within _ -> true | Exact _ | Unknown -> false in
        match (List.find_opt is_exact promised, List.find_opt is_bounded promised) with
        | Some tightest, _ | None, Some tightest -> tightest
        | None, None -> Unknown)
      (find_first_costs (fun clauses cost ->
           match (cost.resource, List.nth_opt clauses.parameters position) with
           | Calls (Function_parameter counted), Some parameter -> counted = parameter.local
           | _ -> false))
  in
  let count_calls_through_callback target (passed : State.passed) function_type =
    let in_one_call =
      count_calls_in_one_call context after counter target function_type passed.term
    in
    if in_one_call = Exact Costs.zero then Costs.zero
    else
      let through = count_calls_through passed.position in
      let parameter =
        match List.nth_opt (List.hd declared_clauses).parameters passed.position with
        | Some parameter -> Facts.read_parameter_name parameter
        | None -> Facts.raise_bug "an argument of `%s` with no parameter" (Path.show path)
      in
      match Costs.multiply (Option.value through ~default:Unknown) in_one_call with
      | Unknown ->
          let unbounded =
            make_conditional_amount
              (Logic.not_ (make_is_zero in_one_call))
              (Operations.declare_unknown_amount context after counter)
          in
          if Option.is_none through && List.mem counter context.promised_counters then
            Facts.oblige context after Cost location
              [
                Text
                  (Printf.sprintf
                     "`%s` states no bound on the calls through `%s`, so the %s that this call \
                      makes through the function passed for it have no bound. Give `%s` a `cost \
                      calls(%s)` clause."
                     (Path.show path) parameter
                     (Operations.show_counted_calls context target)
                     (Path.show path) parameter);
              ]
              (Logic.equal unbounded Costs.zero);
          unbounded
      | (Exact _ | Within _) as product ->
          rely_on_lambda_costs context counter passed.term;
          declare_counted_amount context after ~location counter product
            ~describe_upper_bound:(fun () ->
              Printf.sprintf
                "Only an upper bound is known for the %s that this call to `%s` makes through \
                 `%s`, which may be fewer, so no `==` bound can count them. State the cost with \
                 `<=`, or %s."
                (Operations.show_counted_calls context target)
                (Path.show path) parameter
                (match through with
                | Some (Within _) ->
                    Printf.sprintf "give `%s` an `==` bound on `calls(%s)`" (Path.show path)
                      parameter
                | Some (Exact _ | Unknown) | None ->
                    "pass a function that makes the same number of them in every call"))
  in
  let count_calls_through_callbacks target =
    List.fold_left
      (fun total (passed : State.passed) ->
        match passed.type_ with
        | Types.Function function_type ->
            Costs.plus total (count_calls_through_callback target passed function_type)
        | _ -> total)
      Costs.zero values
  in
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
  match counter.resource with
  | Calls (Through _ as target) -> count_calls_through_callbacks target
  | Calls ((Capability capability | Capability_method (capability, _)) as target) ->
      if not (may_use uses capability) then Costs.zero
      else
        Costs.plus
          (match find_stated_costs () with
          | Some (frame, cost :: _) ->
              declare_amount context after counter (compute_cost_amount frame cost)
          | Some (_, []) | None ->
              if uses_capability_itself context path capability then
                Operations.declare_unknown_amount context after counter
              else Costs.zero)
          (count_calls_through_callbacks target)
  | Metric _ -> (
      match (find_stated_costs (), counter.counting) with
      | Some (_, { bound = Finite; _ } :: _), Units
        when counter.resource = Metric Time && Option.is_some method_cost ->
          compute_method_amount ()
      | Some (frame, cost :: _), _ ->
          declare_amount context after counter (compute_cost_amount frame cost)
      | (Some (_, []) | None), _ -> compute_method_amount ())

let find_generic_argument context frame (operation : Intrinsic.operation) type_arguments name =
  let generics = (Intrinsic_signatures.make_signature operation).generics in
  List.find_map
    (fun ((generic : Types.generic), argument) ->
      match argument with
      | Types.Value value when generic.generic.name = name ->
          Some (Models.make_value_term context frame value)
      | _ -> None)
    (List.combine generics type_arguments)

let compute_step_amount context frame ~location (invocation : Invocation.t)
    (values : State.passed list) (counter : Costs.counter) =
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
                      match Intrinsic.find_builtin path with
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
                  Logic.ite
                    (Logic.Operation (">", [ amount_term; Logic.int 0 ]))
                    (Logic.int 1) (Logic.int 0)
              | _ -> Operations.declare_unknown_amount context frame counter)
          | Unknown_allocations, _, _ -> Operations.declare_unknown_amount context frame counter)
      | Calls _ -> Costs.zero)
  | Capability_method { capability; name } -> (
      match counter.resource with
      | Calls (Capability path) when Path.equal path capability -> Logic.int 1
      | Calls (Capability_method (path, method_)) when Path.equal path capability && method_ = name
        ->
          Logic.int 1
      | Calls (Capability _ | Capability_method _ | Through _) -> Costs.zero
      | Metric _ -> (
          match Contracts.find_capability_clauses context.lookups capability name with
          | Some capability_clauses ->
              let inside =
                Validity.bind_arguments frame capability_clauses
                  ~arguments:
                    (List.map
                       (fun (passed : State.passed) -> (passed.position, passed.term))
                       values)
                  ~substitution:Types.no_substitution
              in
              compute_callee_amount context frame ~location
                ~path:(Path.make_capability_method capability name)
                ~clauses:[ capability_clauses ]
                ~bind_frame:(fun _ -> inside)
                ~uses:(invocation.uses :> Types.capability list)
                ~values ~change:None counter
          | None -> Operations.declare_unknown_amount context frame counter))
  | Function _ | Trait_method _ | Indirect () -> (
      match counter.resource with
      | Calls (Through _ as target) ->
          make_conditional_amount
            (Logic.disjunction
               (List.map
                  (fun (passed : State.passed) ->
                    match passed.type_ with
                    | Types.Function function_type ->
                        Logic.not_
                          (make_is_zero
                             (count_calls_in_one_call context frame counter target function_type
                                passed.term))
                    | _ -> Logic.Boolean false)
                  values))
            (Operations.declare_unknown_amount context frame counter)
      | Calls (Capability capability | Capability_method (capability, _))
        when not (may_use (invocation.uses :> Types.capability list) capability) ->
          Costs.zero
      | Calls (Capability _ | Capability_method _) | Metric _ ->
          Operations.declare_unknown_amount context frame counter)

let declare_held_symbol context ty term =
  let symbol = Logic.Symbol.Potential ty in
  Facts.declare context (Logic.Function (symbol, [ Facts.declare_sort context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let compute_buffer_elements context (ty : Types.ty) =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element; Types.Value _ ] }
    when Intrinsic.find_builtin path = Some Array ->
      Option.map
        (fun model_of -> (element, model_of))
        (Models.find_model_function context ty ~model:(Models.make_sequence_type element))
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Intrinsic.find_builtin path = Some Storage ->
      Some (element, fun term -> Intrinsics.make_buffer_model context Storage element term)
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Intrinsic.find_builtin path = Some View ->
      Some (element, fun term -> Intrinsics.make_buffer_model context View element term)
  | Types.Named { path; arguments } when Types.find_builtin ty = None -> (
      match Interface.Definition.find_interface context.lookups.interface path with
      | Some (Interface.Environment.Type_interface { shape = Record [ field ]; type_generics; _ })
        -> (
          let substitution = Types.make_substitution type_generics arguments in
          match Types.substitute substitution field.field_type with
          | Types.Named { path = field_path; arguments = [ Types.Type element ] }
            when Intrinsic.find_builtin field_path = Some Storage
                 || Intrinsic.find_builtin field_path = Some View ->
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

let declare_buffer_slack context (ty : Types.ty) term =
  let symbol = Logic.Symbol.Slack ty in
  Facts.declare context (Logic.Function (symbol, [ Facts.declare_sort context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

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
          Validity.make_validity context frame ~assuming:true ty term
          ==> Operation ("<=", [ int 0; held ]));
      match (find_potential_clause context ty, Facts.find_constructors context ty) with
      | None, None when Option.is_some (find_buffer_elements context ty) -> (
          match find_buffer_elements context ty with
          | Some (element, model_of) ->
              let sequence = model_of term in
              let slack = declare_buffer_slack context ty term in
              let length = Models.make_sequence_length context element sequence in
              Facts.add_frame_fact context frame
                Logic.(
                  Operation ("<=", [ int 0; slack ])
                  &&& Operation ("<=", [ slack; Operation ("*", [ int 2; length ]) ]));
              (match ty with
              | Types.Named { path; _ } when Intrinsic.find_builtin path = Some Storage ->
                  let saved =
                    Logic.Operation
                      ( "-",
                        [
                          Logic.Operation ("*", [ Logic.int 2; length ]);
                          Intrinsics.make_buffer_capacity context element term;
                        ] )
                  in
                  Facts.add_frame_fact context frame
                    (Logic.equal slack
                       (Logic.ite
                          (Logic.Operation (">=", [ saved; Logic.int 0 ]))
                          saved (Logic.int 0)))
              | Types.Named { path; _ }
                when Intrinsic.find_builtin path = Some View
                     || Intrinsic.find_builtin path = Some Array ->
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

let find_literal_bound (metric : Metric.t) (costs : Mir.cost list) =
  let counter = Costs.make_operand_counter metric in
  List.find_map
    (fun (cost : Mir.cost) ->
      if cost.amortized || not (is_same_resource cost ~locals:Locals.empty counter) then None
      else
        match (counter.counting, cost.bound) with
        | Units, Order_of amount | (At_most | Exactly), (At_most amount | Exactly amount) ->
            Contracts.find_integer_literal amount
        | (Units | At_most | Exactly), (Finite | Order_of _ | At_most _ | Exactly _) -> None)
    costs

let find_method_cost_bound context (metric : Metric.t) (method_ : Path.t) ~trait_arguments self_type
    =
  let holds ty = try has_potential context ty with Facts.Unsupported _ -> true in
  let includes_potential_made = metric = Time in
  match method_ with
  | Method { owner = trait; name; receiver } -> (
      if Well_known.is Copyable trait then
        if
          Interface.Impls.is_plain context.lookups.interface
            ~list_bounds:(Operations.compute_current_bounds context)
            self_type
          && not (holds self_type)
        then Some (Costs.least_amount (Metric metric))
        else None
      else
        let reference : Types.trait_reference = { trait; trait_arguments; associated = [] } in
        match Operations.find_concrete_impl context reference self_type with
        | Some (impl, substitution) -> (
            let path = Path.Method { owner = impl; name; receiver } in
            let makes_no_potential =
              match Interface.Impls.read_signature context.lookups.interface path with
              | Some (signature : Types.signature) -> (
                  List.for_all
                    (fun (parameter : Types.parameter_info) ->
                      parameter.mode <> Types.Mut || not (holds parameter.type_))
                    signature.parameters
                  && (match signature.receiver with Some (Mut, ty) -> not (holds ty) | _ -> true)
                  && match signature.output with Returns ty -> not (holds ty) | _ -> false)
              | None -> false
            in
            match
              Contracts.find_method_contract context.lookups reference name receiver
                (Impl { impl; substitution })
            with
            | Some contract when makes_no_potential || not includes_potential_made ->
                Option.map
                  (fun literal -> Logic.Integer literal)
                  (List.find_map
                     (fun (clauses : State.clauses) -> find_literal_bound metric clauses.costs)
                     (Contracts.list_declared_clauses contract))
            | _ -> None)
        | None -> None)
  | _ -> None

let declare_method_cost context frame (metric : Metric.t) (method_ : Path.t) ~trait_arguments
    self_type =
  let symbol = Logic.Symbol.Method_cost { metric; method_; trait_arguments; self_type } in
  Facts.declare context (Logic.Constant (symbol, Logic.Int));
  let least = Costs.least_amount (Metric metric) in
  Facts.add_frame_fact context frame (Logic.Operation ("<=", [ least; Logic.Symbol symbol ]));
  (match find_method_cost_bound context metric method_ ~trait_arguments self_type with
  | Some limit ->
      Facts.add_frame_fact context frame
        (Logic.Operation ("<=", [ Logic.Symbol symbol; Costs.larger limit least ]))
  | None -> ());
  Logic.Symbol symbol

let compute_method_cost context frame (metric : Metric.t) (callee : Invocation.callee) =
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
        (Metric.show metric)
