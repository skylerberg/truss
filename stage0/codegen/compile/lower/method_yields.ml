(* Where the [yield]s of a lending or yielding method's body are. *)

let statement_yields =
  Core_walk.statement_exists ~statement:(fun (inner : Core.statement) ->
      match inner.kind with Yield _ -> true | _ -> false)

let expression_yields (node : Core.expression) =
  statement_yields { id = node.id; origin = node.origin; kind = Evaluate node }

(* How many [yield]s a body has. *)
let count (body : Core.block) =
  let count = ref 0 in
  Core_walk.block
    (Core_walk.deep
       {
         Core_walk.ignore_all with
         statement =
           (fun (node : Core.statement) -> match node.kind with Yield _ -> incr count | _ -> ());
       })
    body;
  !count

(* Whether nothing runs after a [yield] on any path through a body. *)
let each_is_last (body : Core.block) =
  let rec last_in_block (block : Core.block) =
    match (block.value, List.rev block.statements) with
    | Some value, statements ->
        (not (List.exists statement_yields statements)) && last_in_expression value
    | None, [] -> true
    | None, last :: before -> (not (List.exists statement_yields before)) && last_in_statement last
  and last_in_statement (node : Core.statement) =
    match node.kind with
    | Yield _ -> true
    | Evaluate value -> last_in_expression value
    | _ -> not (statement_yields node)
  and last_in_expression (node : Core.expression) =
    match node.kind with
    | Block block -> last_in_block block
    | If { then_; else_; _ } ->
        last_in_block then_ && Option.fold ~none:true ~some:last_in_block else_
    | Match { arms; _ } -> List.for_all (fun (arm : Core.arm) -> last_in_block arm.body) arms
    | _ -> not (expression_yields node)
  in
  last_in_block body
