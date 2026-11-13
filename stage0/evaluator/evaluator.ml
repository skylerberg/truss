let root : Prover.run -> Instance.key = function
  | Template_check { from_template; texts; _ } -> Template_check { from_template; texts }
  | Call { function_; arguments; _ } -> Call_evaluation { function_; arguments }

let of_compiler compile : Prover.evaluator =
  {
    code_key = (fun run -> Result.to_option (Compile.run_key (Lazy.force compile) (root run)));
    run =
      (function
      | Template_check evaluation -> (
          match
            Compile.check_template (Lazy.force compile) ~from_template:evaluation.from_template
              ~texts:evaluation.texts
          with
          | Ok (Ran checked) -> (
              match List.assoc_opt evaluation.clause checked with
              | Some holds -> Returned (if holds then Z.one else Z.zero)
              | None -> Not_run)
          | Ok Ran_too_long -> Timed_out
          | Error _ -> Not_run)
      | Call known -> (
          match
            Compile.evaluate_call (Lazy.force compile) ~function_:known.function_
              ~arguments:known.arguments
          with
          | Ok (Ran (Static_scalar (Integer (_, value)))) -> Returned value
          | Ok (Ran (Static_scalar (Bool value))) -> Returned (if value then Z.one else Z.zero)
          | Ok Ran_too_long -> Timed_out
          | Ok (Ran _) | Error _ -> Not_run));
  }
