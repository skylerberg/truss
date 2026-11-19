let check context (mir : Mir.Graph.t) =
  let rec check_part ~variant (part : Mir.yielded) =
    match (part, variant) with
    | Part (Borrow { mode = Mut; origin; _ }), Some variant ->
        Context.report context Lent_mut_in_variant
          (Context.locate_with_mode_keyword context origin)
          (Printf.sprintf
             "This place is lent `mut` inside the variant `%s`. The caller could replace the \
              variant, and the place would be left without a value. Lend the place itself, and \
              give the caller another method that says whether the place is there."
             variant)
    | Part _, _ -> ()
    | Built { variant = built; fields; _ }, _ ->
        let variant = if Option.is_some built then built else variant in
        List.iter (fun (_, field) -> Option.iter (check_part ~variant) field) fields
  in
  let check_body (body : Mir.Graph.body) =
    Array.iter
      (fun (block : Mir.Graph.basic_block) ->
        match block.terminator with
        | Yield { part; _ } -> check_part ~variant:None part
        | Goto _ | Branch _ | For _ | Fork _ | Join _ | Iteration_end _ | Return _ | Cancel _
        | Resume _ | Unreachable | Written_unreachable | Todo ->
            ())
      body.blocks
  in
  check_body mir.body;
  Array.iter check_body mir.lambdas
