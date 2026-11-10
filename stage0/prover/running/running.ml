let through ?results ?(time_limit = 10_000) compile : Prover.running =
  {
    template =
      (fun evaluation ->
        match
          Compile.check_template ?results (Lazy.force compile) ~time_limit
            ~from_template:evaluation.from_template ~texts:evaluation.texts
        with
        | Ok (Ran found) ->
            Option.map
              (fun holds -> if holds then Prover.Holds else Prover.Fails)
              (List.assoc_opt evaluation.clause found)
        | Ok Ran_too_long -> Some Too_long
        | Error _ -> None);
    call =
      (fun known ->
        match
          Compile.evaluate_call ?results (Lazy.force compile) ~time_limit ~function_:known.function_
            ~arguments:known.arguments
        with
        | Ok (Returned (Static_scalar (Integer (_, value)))) -> Some value
        | Ok (Returned (Static_scalar (Bool value))) -> Some (if value then Z.one else Z.zero)
        | _ -> None);
  }
