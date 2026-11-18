let run_with ~read ~write value run =
  let outside = read () in
  write value;
  Fun.protect ~finally:(fun () -> write outside) run

let with_counters (scope : State.scope) counters run =
  run_with
    ~read:(fun () -> scope.counters)
    ~write:(fun counters -> scope.counters <- counters)
    counters run

let with_no_costs scope run = with_counters scope [] run

let with_terminates (scope : State.scope) terminates run =
  run_with
    ~read:(fun () -> scope.terminates)
    ~write:(fun terminates -> scope.terminates <- terminates)
    terminates run

let with_reading_callback (scope : State.scope) run =
  run_with
    ~read:(fun () -> scope.is_reading_callback)
    ~write:(fun is_reading_callback -> scope.is_reading_callback <- is_reading_callback)
    true run

let with_validating (scope : State.scope) ty run =
  run_with
    ~read:(fun () -> scope.validating)
    ~write:(fun validating -> scope.validating <- validating)
    (ty :: scope.validating) run

let with_instantiating (scope : State.scope) path run =
  run_with
    ~read:(fun () -> scope.instantiating)
    ~write:(fun instantiating -> scope.instantiating <- instantiating)
    (path :: scope.instantiating) run

let with_axiomatizing (scope : State.scope) symbol run =
  run_with
    ~read:(fun () -> scope.axiomatizing)
    ~write:(fun axiomatizing -> scope.axiomatizing <- axiomatizing)
    (symbol :: scope.axiomatizing) run

let with_ghost_run (scope : State.scope) run =
  let ghost_run = { State.unfinished = [] } in
  run_with
    ~read:(fun () -> scope.proving)
    ~write:(fun proving -> scope.proving <- proving)
    (Running_ghost_code ghost_run) run;
  ghost_run.unfinished
