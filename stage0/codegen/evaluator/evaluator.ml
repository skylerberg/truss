let of_compiler compile : Prover.evaluator =
 fun ({ from_template; texts; clause } : Prover.State.evaluation) ->
  match Compile.check_template (Lazy.force compile) ~from_template ~texts with
  | Ok (Ran checked) -> (
      match List.assoc_opt clause checked with Some holds -> Ran holds | None -> Not_run)
  | Ok Ran_too_long -> Timed_out
  | Error _ -> Not_run
