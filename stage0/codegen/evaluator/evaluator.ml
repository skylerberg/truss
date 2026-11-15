let root ({ from_template; texts; _ } : Prover.State.evaluation) : Instance.key =
  Template_check { from_template; texts }

let of_compiler compile : Prover.evaluator =
  {
    code_key =
      (fun evaluation -> Result.to_option (Compile.run_key (Lazy.force compile) (root evaluation)));
    run =
      (fun evaluation ->
        match
          Compile.check_template (Lazy.force compile) ~from_template:evaluation.from_template
            ~texts:evaluation.texts
        with
        | Ok (Ran checked) -> (
            match List.assoc_opt evaluation.clause checked with
            | Some holds -> Ran holds
            | None -> Not_run)
        | Ok Ran_too_long -> Timed_out
        | Error _ -> Not_run);
  }
