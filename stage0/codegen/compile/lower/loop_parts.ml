let block_at (blocks : Mir.basic_block Dynarray.t) block = Dynarray.get blocks block
let set_block blocks block basic = Dynarray.set blocks block basic

(* A terminator with each block that it names replaced. *)
let retargeted (target : Mir.block -> Mir.block) (terminator : Mir.terminator) : Mir.terminator =
  match terminator with
  | Goto block -> Goto (target block)
  | Branch branch -> Branch { branch with yes = target branch.yes; no = target branch.no }
  | Switch_variant { place; cases } ->
      Switch_variant
        { place; cases = List.map (fun (variant, block) -> (variant, target block)) cases }
  | For loop ->
      For
        {
          loop with
          body = target loop.body;
          blocks = List.map target loop.blocks;
          after = target loop.after;
        }
  | Fork fork ->
      Fork
        {
          fork with
          branches =
            List.map
              (fun (branch : Mir.branch) ->
                { Mir.entry = target branch.entry; blocks = List.map target branch.blocks })
              fork.branches;
          join = Option.map target fork.join;
        }
  | Join join -> Join { join with next = target join.next }
  | Yield yielded -> Yield { yielded with resume = target yielded.resume }
  | Cancel cancel -> Cancel { cancel with task_end = Option.map target cancel.task_end }
  | Resume resume ->
      Resume
        {
          resume with
          exits =
            List.map
              (fun (exit : Mir.early_exit) -> { exit with resume = target exit.resume })
              resume.exits;
          next = target resume.next;
        }
  | Iteration_end { loop } -> Iteration_end { loop = target loop }
  | (Return _ | Unreachable | Written_unreachable | Todo) as terminator -> terminator

(* The blocks of a loop's body that end its own iterations, not those of a
   loop nested in it. *)
let own_iteration_ends blocks (body : Mir.block list) =
  let nested =
    List.concat_map
      (fun block ->
        match (block_at blocks block).terminator with For { blocks = inner; _ } -> inner | _ -> [])
      body
  in
  List.filter
    (fun block ->
      (not (List.mem block nested))
      && match (block_at blocks block).terminator with Iteration_end _ -> true | _ -> false)
    body

(* The tasks that run in a loop's body: each iteration of a loop there and
   each branch of a fork there. *)
let tasks_in blocks (body : Mir.block list) : Core.task list =
  List.concat_map
    (fun block ->
      match (block_at blocks block).terminator with
      | For { loop; _ } -> [ Core.Iteration { loop = loop.origin } ]
      | Fork { fork; branches; _ } ->
          List.mapi (fun index _ -> Core.Branch { block = fork; index }) branches
      | _ -> [])
    body

(* Ends [part] on each way out of the loop whose body is [body]: where the
   body returns, where an early exit leaves a task around the loop, and
   before each jump to a block outside the body. *)
let end_on_exits blocks ~(body : Mir.block list) ~part ~origin =
  let dead : Mir.statement = { kind = Dead [ part ]; origin } in
  let pads = Hashtbl.create 4 in
  let leave target =
    if List.mem target body then target
    else
      match Hashtbl.find_opt pads target with
      | Some pad -> pad
      | None ->
          Dynarray.add_last blocks
            {
              Mir.statements = [ dead ];
              terminator = Goto target;
              terminator_origin = origin;
              header = None;
            };
          let pad = Dynarray.length blocks - 1 in
          Hashtbl.replace pads target pad;
          pad
  in
  let inside = tasks_in blocks body in
  List.iter
    (fun block ->
      let basic = block_at blocks block in
      set_block blocks block
        (match basic.terminator with
        | Return _ -> { basic with statements = basic.statements @ [ dead ] }
        (* An early exit that leaves a task around the loop leaves the loop,
           once the groups inside it have ended. *)
        | Cancel { task; _ } when not (List.mem task inside) ->
            { basic with statements = basic.statements @ [ dead ] }
        | Cancel _ | Iteration_end _ -> basic
        | terminator -> { basic with terminator = retargeted leave terminator }))
    body

let ended_body (body : Mir.body) : Mir.body =
  let blocks = Dynarray.of_array body.blocks in
  for block = 0 to Array.length body.blocks - 1 do
    match block_at blocks block with
    | { terminator = For { iteration = Pull _; part; blocks = loop_body; loop; _ }; _ } ->
        let dead : Mir.statement = { kind = Dead [ part ]; origin = loop.origin } in
        List.iter
          (fun ending ->
            let basic = block_at blocks ending in
            set_block blocks ending { basic with statements = basic.statements @ [ dead ] })
          (own_iteration_ends blocks loop_body);
        end_on_exits blocks ~body:loop_body ~part ~origin:loop.origin
    | _ -> ()
  done;
  { body with blocks = Mir.canonical (Dynarray.to_array blocks) }

let ended (mir : Mir.t) : Mir.t =
  { body = ended_body mir.body; lambdas = Array.map ended_body mir.lambdas }
