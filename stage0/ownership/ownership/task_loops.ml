open Context

let collection_type (body : Mir.Graph.body) ~(inside : Mir.Graph.block) (element : Mir.local) =
  List.find_map
    (fun (statement : Mir.statement) ->
      match statement.kind with
      | Lend { part; call = { arguments = Passed { value = Borrow { type_; _ }; _ } :: _; _ } }
        when part = element ->
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
                lent;
                body = inside;
                _;
              } -> (
              let keyword = if schedule = Parallel_loop then "parallel" else "concurrent" in
              (match lent with
              | Some { element; _ } when body.locals.(element).kind = Lent Mut -> (
                  match collection_type body ~inside element with
                  | Some collection when Place.is_storage_type collection -> ()
                  | collection ->
                      report context Data_race (span context origin)
                        (Printf.sprintf
                           "Data race: the iterations of a `%s for` run at the same time, and each \
                            is lent an element of %s to mutate. Only a `List`, a `Slice`, or an \
                            `Array` lends its elements to iterations that run at the same time: \
                            its elements at different positions are different places. Loop over a \
                            `mut Slice` of the collection's storage, or use a `for` loop."
                           keyword
                           (match collection with
                           | Some collection -> Printf.sprintf "`%s`" (Types.show collection)
                           | None -> "the collection")))
              | _ -> ());
              match (schedule, iteration) with
              | Concurrent_loop, Pull _ when is_view context body.locals.(part).type_ ->
                  report context Task_outlives_view
                    (span context block.terminator_origin)
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
