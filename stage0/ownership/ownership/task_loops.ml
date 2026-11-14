(* The rules on a [parallel for] and a [concurrent for], whose iterations
   run at the same time. An iteration outlives the step of the loop that
   started it, so what it is given stays valid, and distinct from what the
   other iterations are given, until the loop ends. Both rules read the
   loop and the types it names, never the body of a callee. *)
open Context

let is_storage type_ =
  Types.is_well_known List type_ || Types.is_well_known Slice type_ || Types.is_builtin Array type_

(* The type of the collection whose [element] lends a loop's element. *)
let collection_type (body : Mir.body) ~(inside : Mir.block) (element : Mir.local) =
  List.find_map
    (fun (statement : Mir.statement) ->
      match statement.kind with
      | Lend { part; call = { arguments = Passed { value = Borrow { type_; _ }; _ } :: _; _ } }
        when part = element ->
          Some type_
      | _ -> None)
    body.blocks.(inside).statements

let check context (mir : Mir.t) =
  List.iter
    (fun (body : Mir.body) ->
      Array.iter
        (fun (block : Mir.basic_block) ->
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
              (* A data race. Each iteration is lent an element to mutate, so
                 the elements must be different places. An index of a [List],
                 a [Slice], or an [Array] is one for each position. Any other
                 collection's [element] could lend one place to two
                 iterations. *)
              (match lent with
              | Some { element; _ } when body.locals.(element).kind = Lent Mut -> (
                  match collection_type body ~inside element with
                  | Some collection when is_storage collection -> ()
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
              (* A dangling view. A task keeps the value it is given after the
                 loop pulls the cursor again, and a pull may mutate or drop
                 what a view from the cursor views. *)
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
