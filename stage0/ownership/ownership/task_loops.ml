let find_collection_type (body : Mir.Graph.body) ~(inside : Mir.Graph.block) part =
  List.find_map
    (fun (statement : Mir.Graph.statement) ->
      match statement.kind with
      | Basic
          (Lend { part = lent; call = { arguments = { value = Borrow { type_; _ }; _ } :: _; _ } })
        when lent = part ->
          Some type_
      | Basic _ | Provide_start _ | Provide_end -> None)
    body.blocks.(inside).statements

let check context (mir : Mir.Graph.t) =
  List.iter
    (fun (body : Mir.Graph.body) ->
      Array.iter
        (fun (block : Mir.Graph.basic_block) ->
          match block.terminator with
          | For
              {
                loop = { schedule = (Parallel | Concurrent) as schedule; origin; _ };
                iteration;
                part;
                elements;
                body = inside;
                _;
              } -> (
              (match elements with
              | Some { element = Lent_by_call lent; _ } when body.locals.(lent).kind = Lent Mut ->
                  Context.report context
                    (Lent_element_race
                       {
                         at = origin;
                         schedule;
                         collection = find_collection_type body ~inside lent;
                       })
              | Some { element = Lent_by_call _ | Sequence_element _; _ } | None -> ());
              match (schedule, iteration) with
              | Concurrent, Pull _ when Context.is_view context body.locals.(part).type_ ->
                  Context.report context
                    (Pulled_view
                       { at = block.terminator_origin; element = body.locals.(part).type_ })
              | _ -> ())
          | _ -> ())
        body.blocks)
    (mir.body :: Array.to_list mir.lambdas)
