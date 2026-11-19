let run_in_specification state (env : State.env) (value : Syntax.expression) check =
  let env = { env with specification = true } in
  State.run_in_statement state env (State.read_span state value.id) (fun () -> check env)

let check_condition state env value =
  run_in_specification state env value (fun env -> Hooks.check state env value Types.bool)

let check_integer state env (value : Syntax.expression) ~described =
  run_in_specification state env value (fun env ->
      ignore
        (State.narrow state (Hooks.check_expression state env value)
           (Types.integer_types @ [ Language.Builtin_type.Integer ])
           ~report_excluded:(fun excluded ->
             State.add_diagnostic state Mismatch (State.read_span state value.id)
               (Printf.sprintf "%s is an integer, not %s." described (State.describe state excluded)))))

let check_measures state env measures =
  List.iter (check_integer state env ~described:"A `decreases` measure") measures

let check_cost state env (cost : Syntax.cost) =
  State.check_cost state cost;
  match cost.bound with
  | Big_o bound | At_most bound | Exactly bound ->
      check_integer state env bound ~described:"A cost bound"
