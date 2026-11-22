let state_value : Lowered.static_value -> Prover.Obligation.value option = function
  | Static_scalar (Bool holds) -> Some (Boolean holds)
  | Static_scalar (Integer (_, number)) -> Some (Integer number)
  | Static_scalar (Character scalar) -> Some (Integer (Z.of_int scalar))
  | Static_scalar _ | Static_record _ | Static_variant _ | Static_array _ | Static_storage _
  | Static_view _ ->
      None

let run_one backend (evaluation : Prover.Obligation.evaluation) :
    (Prover.Obligation.run, string) result =
  match evaluation with
  | Template_check { function_; literals } -> (
      match Backend.evaluate_predicate backend ~function_ ~arguments:[ Literals literals ] with
      | Ok (Ok holds) -> Ok (Evaluated (Some (Boolean holds)))
      | Ok (Error report) -> Ok (Failed report)
      | Error message ->
          Error (Printf.sprintf "The check of a template's text could not be built: %s" message))
  | Constant_value path -> (
      match Backend.evaluate_constant backend path with
      | Ok (Ran value) -> Ok (Evaluated (state_value value))
      | Ok (Reached_todo report) -> Ok (Unfinished report)
      | Ok (Stopped report) | Error report -> Ok (Failed report))

let run backend evaluations =
  List.fold_right
    (fun evaluation runs ->
      Result.bind runs (fun runs ->
          Result.map (fun run -> (evaluation, run) :: runs) (run_one backend evaluation)))
    evaluations (Ok [])
