let rec make_value : Lowered.static_value -> Prover.Obligation.value = function
  | Static_scalar (Bool holds) -> Boolean holds
  | Static_scalar (Integer (_, number)) -> Integer number
  | Static_scalar (Character scalar) -> Integer (Z.of_int scalar)
  | Static_scalar (Float32 bits) -> Float (Int32.float_of_bits bits)
  | Static_scalar (Float64 bits) -> Float (Int64.float_of_bits bits)
  | Static_scalar _ ->
      Compiler_bug.raise_bug ~stage:"Evaluations" "an evaluation gave a scalar that is no value"
  | Static_record fields -> Constructed { variant = None; fields = make_fields fields }
  | Static_variant (variant, fields) ->
      Constructed { variant = Some variant; fields = make_fields fields }
  | Static_array elements | Static_storage { elements; _ } | Static_view { elements; _ } ->
      Elements (List.map make_value elements)

and make_fields fields = List.map (fun (name, value) -> (name, make_value value)) fields

let make_run : (Lowered.static_value Backend.ran, string) result -> Prover.Obligation.run = function
  | Ok (Ran value) -> Evaluated (make_value value)
  | Ok (Reached_todo report) -> Unfinished report
  | Ok (Stopped report) | Error report -> Failed report

let run_one backend (evaluation : Prover.Obligation.evaluation) :
    (Prover.Obligation.run, string) result =
  match evaluation with
  | Template_check { function_; literals } -> (
      match Backend.evaluate_predicate backend ~function_ ~arguments:[ Literals literals ] with
      | Ok (Ok holds) -> Ok (Evaluated (Boolean holds))
      | Ok (Error report) -> Ok (Failed report)
      | Error message ->
          Error (Printf.sprintf "The check of a template's text could not be built: %s" message))
  | Constant_value path -> Ok (make_run (Backend.evaluate_constant backend path))
  | Assertion { definition; condition } ->
      Ok (make_run (Backend.evaluate_assertion backend ~definition ~condition))

let run backend evaluations =
  List.fold_right
    (fun evaluation runs ->
      Result.bind runs (fun runs ->
          Result.map (fun run -> (evaluation, run) :: runs) (run_one backend evaluation)))
    evaluations (Ok [])
