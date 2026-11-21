let lookup_block (blocks : Mir.Graph.basic_block Dynarray.t) (block : Mir.Graph.block) =
  Dynarray.get blocks (block :> int)

let set_block blocks (block : Mir.Graph.block) basic = Dynarray.set blocks (block :> int) basic

let retarget (retarget_block : Mir.Graph.block -> Mir.Graph.block)
    (terminator : Mir.Graph.terminator) : Mir.Graph.terminator =
  match terminator with
  | Goto block -> Goto (retarget_block block)
  | Branch branch ->
      Branch { branch with yes = retarget_block branch.yes; no = retarget_block branch.no }
  | For loop ->
      For
        {
          loop with
          body = retarget_block loop.body;
          blocks = List.map retarget_block loop.blocks;
          after = retarget_block loop.after;
        }
  | Fork fork ->
      Fork
        {
          fork with
          branches =
            List.map
              (fun (branch : Mir.Graph.branch) ->
                {
                  Mir.Graph.entry = retarget_block branch.entry;
                  blocks = List.map retarget_block branch.blocks;
                })
              fork.branches;
          join = Option.map retarget_block fork.join;
        }
  | Join join -> Join { join with next = retarget_block join.next }
  | Yield yielded -> Yield { yielded with resume = retarget_block yielded.resume }
  | Cancel cancel -> Cancel { cancel with task_end = Option.map retarget_block cancel.task_end }
  | Resume resume ->
      Resume
        {
          resume with
          exits =
            List.map
              (fun (exit : Mir.Graph.early_exit) ->
                { exit with resume = retarget_block exit.resume })
              resume.exits;
          next = retarget_block resume.next;
        }
  | Iteration_end { loop } -> Iteration_end { loop = retarget_block loop }
  | (Return _ | Unreachable | Written_unreachable | Todo) as terminator -> terminator

let list_own_iteration_ends blocks (body : Mir.Graph.block list) =
  let nested =
    List.concat_map
      (fun block ->
        match (lookup_block blocks block).terminator with
        | For { blocks = inner; _ } -> inner
        | _ -> [])
      body
  in
  List.filter
    (fun block ->
      (not (List.mem block nested))
      && match (lookup_block blocks block).terminator with Iteration_end _ -> true | _ -> false)
    body

let list_tasks blocks (body : Mir.Graph.block list) : Mir.task list =
  List.concat_map
    (fun block ->
      match (lookup_block blocks block).terminator with
      | For { loop; _ } -> [ Mir.Iteration { loop = loop.node } ]
      | Fork { fork; branches; _ } -> List.mapi (fun index _ -> Mir.Branch { fork; index }) branches
      | Goto _ | Branch _ | Join _ | Iteration_end _ | Yield _ | Return _ | Cancel _ | Resume _
      | Unreachable | Written_unreachable | Todo ->
          [])
    body

let end_on_exits blocks ~(body : Mir.Graph.block list) ~part ~origin =
  let dead : Mir.Graph.statement = { kind = Basic (Dead [ part ]); origin } in
  let pads = Hashtbl.create 4 in
  let leave target =
    if List.mem target body then target
    else
      match Hashtbl.find_opt pads target with
      | Some pad -> pad
      | None ->
          let pad =
            Mir.Graph.add_block blocks
              {
                Mir.Graph.statements = [ dead ];
                terminator = Goto target;
                terminator_origin = origin;
              }
          in
          Hashtbl.replace pads target pad;
          pad
  in
  let inside = list_tasks blocks body in
  List.iter
    (fun block ->
      let basic = lookup_block blocks block in
      set_block blocks block
        (match basic.terminator with
        | Return _ -> { basic with statements = basic.statements @ [ dead ] }
        | Cancel { task; _ } when not (List.mem task inside) ->
            { basic with statements = basic.statements @ [ dead ] }
        | Cancel _ | Iteration_end _ -> basic
        | ( Goto _ | Branch _ | For _ | Fork _ | Join _ | Yield _ | Resume _ | Unreachable
          | Written_unreachable | Todo ) as terminator ->
            { basic with terminator = retarget leave terminator }))
    body

let end_body_parts (body : Mir.Graph.body) : Mir.Graph.body =
  let blocks = Dynarray.of_array body.blocks in
  List.iter
    (fun block ->
      match lookup_block blocks block with
      | { terminator = For { iteration = Pull _; part; blocks = loop_body; loop; _ }; _ } ->
          let dead : Mir.Graph.statement = { kind = Basic (Dead [ part ]); origin = loop.origin } in
          List.iter
            (fun ending ->
              let basic = lookup_block blocks ending in
              set_block blocks ending { basic with statements = basic.statements @ [ dead ] })
            (list_own_iteration_ends blocks loop_body);
          end_on_exits blocks ~body:loop_body ~part ~origin:loop.origin
      | _ -> ())
    (Mir.Graph.list_blocks body.blocks);
  { body with blocks = Mir.Graph.canonicalize (Array.map Option.some (Dynarray.to_array blocks)) }

let end_parts (mir : Mir.Graph.t) : Mir.Graph.t =
  { body = end_body_parts mir.body; lambdas = Array.map end_body_parts mir.lambdas }
