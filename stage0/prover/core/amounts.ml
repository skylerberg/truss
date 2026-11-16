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
  | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
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

let compute_promised_amount context frame (counter : Costs.counter) (bound : Mir.bound) ~evaluate
    ~is_recursive_call ~exact_target ~change =
  match (bound, counter.counting) with
  | Order_of amount, Units ->
      let amount = evaluate amount in
      let amount =
        if is_recursive_call then
          let hypothesis = Costs.at_least_zero (Costs.bound amount) in
          if counter.resource = Time then Costs.plus hypothesis (Logic.int 1) else hypothesis
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
  | (Order_of _ | Finite), _ -> Operations.declare_unknown_amount context frame counter

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

let make_reach_formula context frame uses (values : State.passed list) (target : Costs.target) =
  match target with
  | Through term ->
      Logic.disjunction
        (List.map
           (fun (passed : State.passed) ->
             if lambda_captures_target context passed.term term then Logic.Boolean true
             else make_may_be_target context frame passed.term passed.type_ term)
           values)
  | Capability path | Capability_method (path, _) ->
      Logic.Boolean
        (List.exists
           (function
             | Types.Capability used -> Path.equal used path
             | Types.Capability_parameter _ | Types.Capability_projection _
             | Types.Capability_variable _ ->
                 true
             | Types.Capability_error _ ->
                 Facts.raise_bug "the prover reads a capability with an error")
           uses)

let make_conditional_amount condition amount =
  match condition with
  | Logic.Boolean true -> amount
  | Logic.Boolean false -> Costs.zero
  | condition -> Logic.ite condition amount Costs.zero

let compute_callee_amount ?ends_in (context : State.context) after ~path ~(parts : State.part list)
    ~(bind_frame : State.part -> State.frame) ~uses ~(values : State.passed list) ~change
    (counter : Costs.counter) =
  let is_recursive_call =
    counter.counting = Units
    && List.mem counter context.bounded_counters
    && Facts.is_in_recursion_group context path
  in
  let list_clauses (part : State.part) =
    let frame = bind_frame part in
    List.filter_map
      (fun (cost : Mir.cost) ->
        if is_same_resource cost ~locals:frame.locals counter then Some (part, frame, cost)
        else None)
      part.costs
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
      (fun part ->
        match list_clauses part with
        | [] -> None
        | clauses ->
            let amortized, plain =
              List.partition (fun (_, _, (cost : Mir.cost)) -> cost.amortized) clauses
            in
            Some (if amortized_first then amortized @ plain else plain @ amortized))
      parts
  in
  match counter.resource with
  | Calls target when make_reach_formula context after uses values target = Logic.Boolean false ->
      Costs.zero
  | Calls (Through term) -> (
      let reaches = make_reach_formula context after uses values (Through term) in
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
  | _ -> (
      let make_time_bound time =
        Costs.minus
          (Costs.plus time (Logic.int 1))
          (match change with
          | Some compute_change -> compute_growth compute_change
          | None -> Costs.zero)
      in
      match (find_first_clauses (), counter.resource, counter.counting, ends_in) with
      | Some ((_, _, { bound = Finite; _ }) :: _), Time, Units, Some time -> make_time_bound time
      | Some (clause :: _), _, _, _ -> compute_amount clause
      | _, Time, Units, Some time -> make_time_bound time
      | _ -> Operations.declare_unknown_amount context after counter)

let find_generic_argument context frame (operation : Intrinsic.operation) type_arguments name =
  let generics = (Intrinsic_signatures.make_signature operation).generics in
  List.find_map
    (fun ((parameter : Types.parameter), argument) ->
      match argument with
      | Types.Value value when parameter.name = name ->
          Some (Models.make_value_term context frame value)
      | _ -> None)
    (Types.make_substitution generics type_arguments)

let compute_step_amount context frame (invocation : Invocation.t) (values : State.passed list)
    (counter : Costs.counter) =
  match invocation.callee with
  | Intrinsic { operation; type_arguments } -> (
      let cost = Intrinsic_signatures.classify_cost operation in
      match counter.resource with
      | Time -> (
          match (cost.time, counter.counting) with
          | Constant_time, _ -> Costs.zero
          | Linear_in position, Units -> (
              match
                List.find_opt (fun (passed : State.passed) -> passed.position = position) values
              with
              | Some passed -> (
                  match passed.type_ with
                  | Types.Named { path; arguments = [ Types.Type element ] } -> (
                      match Intrinsic.builtin_of_path path with
                      | Some ((Storage | View) as builtin) ->
                          Models.make_sequence_length context element
                            (Intrinsics.make_buffer_model context builtin element passed.term)
                      | _ -> Operations.declare_unknown_amount context frame counter)
                  | _ -> Operations.declare_unknown_amount context frame counter)
              | None -> Operations.declare_unknown_amount context frame counter)
          | (Linear_in _ | Unbounded_time), _ ->
              Operations.declare_unknown_amount context frame counter)
      | Allocations | Allocated_bytes -> (
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
              | Some amount_term when resource = Allocations || counting = Units ->
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
      | Time | Allocations | Allocated_bytes -> (
          match Contracts.find_capability_part context.lookups capability name with
          | Some part ->
              let inside =
                Validity.bind_part_arguments frame part
                  ~arguments:
                    (List.map
                       (fun (passed : State.passed) -> (passed.position, passed.term))
                       values)
                  ~substitution:[]
              in
              compute_callee_amount context frame
                ~path:(Path.make_capability_method capability name)
                ~parts:[ part ]
                ~bind_frame:(fun _ -> inside)
                ~uses:(invocation.uses :> Types.capability list)
                ~values ~change:None counter
          | None -> Operations.declare_unknown_amount context frame counter))
  | Function _ | Trait_method _ | Indirect () -> (
      match counter.resource with
      | Calls target ->
          make_conditional_amount
            (make_reach_formula context frame
               (invocation.uses :> Types.capability list)
               values target)
            (Operations.declare_unknown_amount context frame counter)
      | Time | Allocations | Allocated_bytes ->
          Operations.declare_unknown_amount context frame counter)

let declare_held_symbol context ty term =
  let symbol = Logic.Symbol.Potential ty in
  Facts.declare context (Logic.Function (symbol, [ Facts.declare_sort context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let compute_buffer_elements context (ty : Types.ty) =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element; Types.Value _ ] }
    when Intrinsic.builtin_of_path path = Some Array ->
      Option.map
        (fun model_of -> (element, model_of))
        (Models.find_model_function context ty ~model:(Models.make_sequence_type element))
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Intrinsic.builtin_of_path path = Some Storage ->
      Some (element, fun term -> Intrinsics.make_buffer_model context Storage element term)
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Intrinsic.builtin_of_path path = Some View ->
      Some (element, fun term -> Intrinsics.make_buffer_model context View element term)
  | Types.Named { path; arguments } when Types.find_builtin ty = None -> (
      match Interface.Definition.find_interface context.lookups.interface path with
      | Some (Interface.Environment.Type_interface { shape = Record [ field ]; type_generics; _ })
        -> (
          let substitution = Types.make_substitution type_generics arguments in
          match Types.substitute substitution field.field_type with
          | Types.Named { path = field_path; arguments = [ Types.Type element ] }
            when Intrinsic.builtin_of_path field_path = Some Storage
                 || Intrinsic.builtin_of_path field_path = Some View ->
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
              | Types.Named { path; _ } when Intrinsic.builtin_of_path path = Some Storage ->
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
                when Intrinsic.builtin_of_path path = Some View
                     || Intrinsic.builtin_of_path path = Some Array ->
                  Facts.add_frame_fact context frame (Logic.equal slack (Logic.int 0))
              | _ -> ());
              let elements =
                if has_potential context element then
                  Intrinsics.make_sequence_sum context element sequence
                    (declare_potential_measure context element)
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
            let compute_parts = compute_parts_potential context frame ~seen ty term in
            let parts =
              match shape with
              | [ (None, fields) ] -> compute_parts (None, fields)
              | variants -> (
                  match List.rev variants with
                  | last :: earlier ->
                      List.fold_left
                        (fun otherwise ((variant, _) as one) ->
                          Logic.ite
                            (Logic.Is (Facts.make_constructor_symbol ty variant, term))
                            (compute_parts one) otherwise)
                        (compute_parts last) earlier
                  | [] -> Costs.zero)
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

let find_method_time_bound context (method_ : Path.t) ~trait_arguments self_type =
  let holds ty = try has_potential context ty with Facts.Unsupported _ -> true in
  match method_ with
  | Method { owner = trait; name; receiver } -> (
      if Well_known.is Copyable trait then
        if
          Interface.Impls.is_plain context.lookups.interface
            ~list_bounds:(Operations.compute_current_bounds context)
            self_type
          && not (holds self_type)
        then Some Z.one
        else None
      else
        let reference : Types.trait_reference = { trait; trait_arguments; associated = [] } in
        match Operations.find_concrete_impl context reference self_type with
        | Some (impl, arguments) -> (
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
                (Impl { impl; arguments })
            with
            | Some contract when makes_no_potential ->
                List.find_map
                  (fun (part : State.part) ->
                    List.find_map
                      (fun (cost : Mir.cost) ->
                        match cost with
                        | { resource = Time; amortized = false; bound = Order_of amount; _ } ->
                            Contracts.find_integer_literal amount
                        | _ -> None)
                      part.costs)
                  contract.parts
            | _ -> None)
        | None -> None)
  | _ -> None

let declare_trait_method_time context frame (method_ : Path.t) ~trait_arguments self_type =
  let symbol = Logic.Symbol.Method_time { method_; trait_arguments; self_type } in
  Facts.declare context (Logic.Constant (symbol, Logic.Int));
  Facts.add_frame_fact context frame (Logic.Operation ("<=", [ Logic.int 1; Logic.Symbol symbol ]));
  (match find_method_time_bound context method_ ~trait_arguments self_type with
  | Some limit ->
      Facts.add_frame_fact context frame
        (Logic.Operation ("<=", [ Logic.Symbol symbol; Logic.Integer (Z.max limit Z.one) ]))
  | None -> ());
  Logic.Symbol symbol

let compute_method_time context frame (callee : Invocation.callee) =
  match callee with
  | Trait_method { trait; name; receiver; self_type; _ } ->
      let substitute_argument : Types.argument -> Types.argument = function
        | Type type_ -> Type (Facts.substitute_type context frame type_)
        | argument -> Types.substitute_argument frame.substitution argument
      in
      declare_trait_method_time context frame
        (Path.Method { owner = trait.trait; name; receiver })
        ~trait_arguments:(List.map substitute_argument trait.trait_arguments)
        (Facts.substitute_type context frame self_type)
  | _ ->
      Facts.raise_unsupported Whole_definition "the time of a function that is not a trait's method"
