let find_collection_type (body : Mir.Graph.body) ~(inside : Mir.Graph.block) part =
  List.find_map
    (fun (statement : Mir.Graph.statement) ->
      match statement.kind with
      | Lend
          { part = lent; call = { arguments = Passed { value = Borrow { type_; _ }; _ } :: _; _ } }
        when lent = part ->
          Some type_
      | _ -> None)
    body.blocks.(inside).statements

let check context (mir : Mir.Graph.t) =
  List.iter
    (fun (body : Mir.Graph.body) ->
      Array.iter
        (fun (block : Mir.Graph.basic_block) ->
          match block.terminator with
          | For
              {
                loop = { schedule = (Parallel_loop | Concurrent_loop) as schedule; origin; _ };
                iteration;
                part;
                elements;
                body = inside;
                _;
              } -> (
              let keyword = if schedule = Parallel_loop then "parallel" else "concurrent" in
              (match elements with
              | Some { element = Lent_by_call lent; _ } when body.locals.(lent).kind = Lent Mut ->
                  Context.report context Data_race
                    (Context.locate_origin context origin)
                    (Printf.sprintf
                       "Data race: the iterations of a `%s for` run at the same time, and each is \
                        lent an element of %s to mutate. Only a `List`, a `Slice`, or an `Array` \
                        lends its elements to iterations that run at the same time: its elements \
                        at different positions are different places. Loop over a `mut Slice` of \
                        the collection's storage, or use a `for` loop."
                       keyword
                       (match find_collection_type body ~inside lent with
                       | Some collection -> Printf.sprintf "`%s`" (Types.show collection)
                       | None -> "the collection"))
              | Some { element = Lent_by_call _ | Sequence_element _; _ } | None -> ());
              match (schedule, iteration) with
              | Concurrent_loop, Pull _ when Context.is_view context body.locals.(part).type_ ->
                  Context.report context Task_outlives_view
                    (Context.locate_origin context block.terminator_origin)
                    (Printf.sprintf
                       "Each iteration of a `concurrent for` runs as a task that outlives the pull \
                        that started it. The element type `%s` is a view, and the next pull could \
                        mutate or drop the value that it views, which would leave the task with a \
                        dangling view. Use a `for` loop, or pull owned values."
                       (Types.show body.locals.(part).type_))
              | _ -> ())
          | _ -> ())
        body.blocks)
    (mir.body :: Array.to_list mir.lambdas)
