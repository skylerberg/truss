let run_in_specification state (env : State.env) (value : Syntax.expression) check =
  let env = { env with specification = true } in
  Solver.run_in_statement state env (State.read_span state value.id) (fun () -> check env)

let check_condition state env value =
  run_in_specification state env value (fun env -> Hooks.check state env value Types.bool)

let require_integer state env (value : Syntax.expression) ~described =
  ignore
    (Solver.require_within state (Hooks.check_expression state env value)
       (Types.integer_types @ [ Language.Builtin_type.Integer ]) ~reason:(fun excluded ->
         State.add_diagnostic state Mismatch (State.read_span state value.id)
           (Printf.sprintf "%s is an integer, not %s." described (State.describe state excluded))))

let check_integer state env (value : Syntax.expression) ~described =
  run_in_specification state env value (fun env -> require_integer state env value ~described)

let check_measures state env measures =
  List.iter (check_integer state env ~described:"A `decreases` measure") measures

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
            State.report state Unknown_member
              (State.read_span state method_.id)
              (Printf.sprintf "`%s` has no method `%s`." path_text method_.text)
        | _ -> ())
    | Some (Unknown _) -> ()
    | _ ->
        State.report state Not_a_capability (State.read_span state path.id)
          (Printf.sprintf "`calls` counts the calls of a capability, and `%s` is not one." path_text)
  in
  match resource with
  | Metric _ -> ()
  | Calls (Call_capability path) -> check_capability path None
  | Calls (Call_method (path, method_)) -> check_capability path (Some method_)
  | Calls (Call_parameter name) -> (
      match (State.find_target state name, State.find_local_type state name) with
      | Some (Local _), (Some (Types.Function _ | Types.Error _ | Types.Hole) | None) -> ()
      | Some (Local _), Some local_type ->
          State.report state Not_callable (State.read_span state name.id)
            (Printf.sprintf "`calls` counts the calls through a function, and `%s` is a `%s`."
               name.text (Types.show local_type))
      | Some (Unknown _), _ -> ()
      | _ ->
          State.report state Not_callable (State.read_span state name.id)
            (Printf.sprintf
               "`calls` counts the calls of a capability or through a function parameter, and `%s` \
                is neither."
               name.text))

let check_cost_operand state (cost : Syntax.cost) (operand : Interface.Elaborator.cost_operand) =
  let span = State.read_span state operand.written.id in
  let cost_function = operand.cost_function.text in
  let callee =
    match operand.callee with
    | Function_parameter name -> name.text
    | Bound_method { type_; method_ } -> (
        match Interface.Elaborator.find_bounded_type state.context type_ with
        | Some self_type -> Printf.sprintf "%s.%s" (Types.show self_type) method_.text
        | None -> "...")
    | Not_a_callee -> "..."
  in
  let operand_text = Printf.sprintf "%s(%s)" cost_function callee in
  (match cost.resource with
  | Metric bounded when bounded = operand.metric -> ()
  | Metric bounded ->
      let bounded = Language.Metric.show bounded in
      State.report state Cost_of_other_resource span
        ~fixes:
          [
            State.fix
              (Printf.sprintf "Write `%s`." bounded)
              [ State.replace (State.read_span state operand.cost_function.id) bounded ];
          ]
        (Printf.sprintf
           "`%s` bounds the `%s` of one call, not its `%s`, which this clause bounds. Write \
            `%s(%s)`."
           operand_text cost_function bounded bounded callee)
  | Calls _ ->
      State.report state Cost_of_other_resource span
        (Printf.sprintf
           "`%s` bounds the `%s` of one call, not the calls it makes, which this clause counts."
           operand_text cost_function));
  match cost.bound with
  | Exactly _ ->
      State.report state Upper_bound_in_exact_bound span
        (Printf.sprintf
           "`%s` is an upper bound on one call, and a call may spend less, so an exact amount that \
            names it would be false for that call. State this bound with `<=` or `O(...)`."
           operand_text)
  | Big_o _ | At_most _ -> ()

let check_cost state env (cost : Syntax.cost) =
  check_resource state cost.resource;
  match cost.bound with
  | Big_o bound | At_most bound | Exactly bound ->
      List.iter (check_cost_operand state cost)
        (Interface.Elaborator.list_cost_operands state.context bound);
      check_integer state env bound ~described:"A cost bound"

let check_time_terminates state (clause : Syntax.clause) ~uses =
  match Types.find_unless (Built_in Run_forever) uses with
  | Some unless
    when not
           (Types.has_capability (Built_in Run_forever) uses
           || Interface.Impls.decide_condition state.State.lookups.interface
                ~list_bounds:(State.lookup_bounds state) unless
              = Some []) ->
      let shown = Types.show_condition unless in
      let span = State.read_span state clause.id in
      let added = (if Option.is_some clause.condition then "&& " else "when ") ^ shown in
      State.report state Unbounded_time span
        ~fixes:
          [
            Diagnostic.fix
              (Printf.sprintf "Add `%s`." added)
              [ Diagnostic.insert (Source.Definition_span.make_zero_width span.stop) (" " ^ added) ];
          ]
        (Printf.sprintf
           "This function uses `RunForever unless %s`, so it may run forever where the condition \
            does not hold, and a `time` clause bounds it only `when` a condition that implies \
            `%s`."
           shown shown)
  | _ -> ()

let check_under_condition state ~id (written : Syntax.condition option) check =
  match (written, State.record_condition state id written) with
  | _, Some condition -> State.apply_condition_bounds state condition check
  | Some _, None ->
      State.report state Decided_condition (State.read_span state id)
        "This clause's condition never holds where it is written, so the clause would bind \
         nothing. Remove the clause, or name a type parameter in its condition."
  | None, None -> State.raise_bug "a clause without a condition never holds"

let build_under_condition state ~id (written : Syntax.condition option) build :
    'clause Core.conditional option =
  match (State.find_condition state id, written) with
  | Some holds_when, _ ->
      Some { holds_when; clause = State.apply_condition_bounds state holds_when build }
  | None, None -> Some { holds_when = []; clause = build () }
  | None, Some _ -> None
