let run_in_specification state (env : State.env) (value : Syntax.expression) check =
  let env = { env with specification = true } in
  Solver.run_in_statement state env (Written value.id) (fun () -> check env)

let check_condition state env value =
  run_in_specification state env value (fun env -> Hooks.check state env value Types.bool)

let require_integer state env (value : Syntax.expression) ~subject =
  ignore
    (Solver.require_within state (Hooks.check_expression state env value)
       (Types.integer_types @ [ Language.Builtin_type.Integer ]) ~reason:(fun excluded ->
         State.add_diagnostic state
           (Not_an_integer
              { at = Written value.id; subject; excluded = State.make_shown state excluded })))

let check_integer state env (value : Syntax.expression) ~subject =
  run_in_specification state env value (fun env -> require_integer state env value ~subject)

let check_measures state env measures =
  List.iter (check_integer state env ~subject:Decreases_measure) measures

let check_resource state (resource : Syntax.resource) =
  let check_capability (path : Syntax.path_type) (method_ : Syntax.name option) =
    let path_text = Interface.Elaborator.show_path path.path in
    match State.find_target state path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_
          when Option.is_none
                 (state.lookups.interface.names.find_key
                    (Path.make_capability_method capability method_.text)) ->
            State.report state
              (No_method
                 {
                   at = Written method_.id;
                   owner = Named_owner path_text;
                   name = method_.text;
                   candidates = [];
                 })
        | _ -> ())
    | Some (Unknown _) -> ()
    | _ ->
        State.report state (Counted_not_a_capability { at = Written path.id; written = path_text })
  in
  match resource with
  | Metric _ -> ()
  | Calls (Call_capability path) -> check_capability path None
  | Calls (Call_method (path, method_)) -> check_capability path (Some method_)
  | Calls (Call_parameter name) -> (
      match (State.find_target state name, State.find_local_type state name) with
      | Some (Local _), (Some (Types.Function _ | Types.Error _ | Types.Hole) | None) -> ()
      | Some (Local _), Some local_type ->
          State.report state
            (Counted_not_a_function { at = Written name.id; name = name.text; type_ = local_type })
      | Some (Unknown _), _ -> ()
      | _ -> State.report state (Counted_neither { at = Written name.id; name = name.text }))

let check_cost_operand state (cost : Syntax.cost) (operand : Interface.Elaborator.cost_operand) =
  let at : Core.origin = Written operand.written.id in
  let described : Catalog.Inference.cost_operand =
    {
      cost_function = operand.metric;
      callee =
        (match operand.callee with
        | Function_parameter name -> Function_parameter name.text
        | Bound_method { type_; method_ } -> (
            match Interface.Elaborator.find_bounded_type (State.read_context state) type_ with
            | Some self_type -> Bound_method { self_type; method_ = method_.text }
            | None -> Unknown_callee)
        | Not_a_callee -> Unknown_callee);
    }
  in
  (match cost.resource with
  | Metric bounded when bounded = operand.metric -> ()
  | Metric bounded ->
      State.report state
        (Cost_of_other_metric
           {
             at;
             operand = described;
             cost_function_name = Written operand.cost_function.id;
             bounded;
           })
  | Calls _ -> State.report state (Cost_of_calls { at; operand = described }));
  match cost.bound with
  | Exactly _ -> State.report state (Upper_bound_in_exact_bound { at; operand = described })
  | Big_o _ | At_most _ -> ()

let check_cost_bound state env (cost : Syntax.cost) =
  match cost.bound with
  | Big_o bound | At_most bound | Exactly bound ->
      List.iter (check_cost_operand state cost)
        (Interface.Elaborator.list_cost_operands (State.read_context state) bound);
      check_integer state env bound ~subject:Cost_bound

let check_cost state env (cost : Syntax.cost) =
  check_resource state cost.resource;
  check_cost_bound state env cost

let check_time_terminates state (clause : Syntax.clause) ~uses =
  match Types.find_unless (Built_in Run_forever) uses with
  | Some unless
    when not
           (Types.has_capability (Built_in Run_forever) uses
           || Interface.Impls.decide_condition state.State.lookups.interface
                ~list_bounds:(State.lookup_bounds state) unless
              = Some []) ->
      State.report state
        (Unbounded_time
           {
             clause = Written clause.id;
             condition = unless;
             has_condition = Option.is_some clause.condition;
           })
  | _ -> ()

let check_under_condition state ~id (written : Syntax.condition option) check =
  match (written, State.record_condition state id written) with
  | _, Some condition -> State.with_added_condition state condition check
  | Some _, None -> State.report state (Clause_never_holds { at = Written id })
  | None, None -> State.raise_bug "a clause without a condition never holds"
