let block_at (blocks : Mir.Graph.basic_block Dynarray.t) block = Dynarray.get blocks block
let set_block blocks block basic = Dynarray.set blocks block basic

let retargeted (target : Mir.Graph.block -> Mir.Graph.block) (terminator : Mir.Graph.terminator) :
    Mir.Graph.terminator =
  match terminator with
  | Goto block -> Goto (target block)
  | Branch branch -> Branch { branch with yes = target branch.yes; no = target branch.no }
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
              (fun (branch : Mir.Graph.branch) ->
                { Mir.Graph.entry = target branch.entry; blocks = List.map target branch.blocks })
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
              (fun (exit : Mir.Graph.early_exit) -> { exit with resume = target exit.resume })
              resume.exits;
          next = target resume.next;
        }
  | Iteration_end { loop } -> Iteration_end { loop = target loop }
  | (Return _ | Unreachable | Written_unreachable | Todo) as terminator -> terminator

let own_iteration_ends blocks (body : Mir.Graph.block list) =
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

let tasks_in blocks (body : Mir.Graph.block list) : Mir.task list =
  List.concat_map
    (fun block ->
      match (block_at blocks block).terminator with
      | For { loop; _ } -> [ Mir.Iteration { loop = loop.origin } ]
      | Fork { fork; branches; _ } ->
          List.mapi (fun index _ -> Mir.Branch { block = fork; index }) branches
      | _ -> [])
    body

let end_on_exits blocks ~(body : Mir.Graph.block list) ~part ~origin =
  let dead : Mir.Graph.statement = { kind = Dead [ part ]; origin } in
  let pads = Hashtbl.create 4 in
  let leave target =
    if List.mem target body then target
    else
      match Hashtbl.find_opt pads target with
      | Some pad -> pad
      | None ->
          Dynarray.add_last blocks
            {
              Mir.Graph.statements = [ dead ];
              terminator = Goto target;
              terminator_origin = origin;
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
        | Cancel { task; _ } when not (List.mem task inside) ->
            { basic with statements = basic.statements @ [ dead ] }
        | Cancel _ | Iteration_end _ -> basic
        | terminator -> { basic with terminator = retargeted leave terminator }))
    body

let ended_body (body : Mir.Graph.body) : Mir.Graph.body =
  let blocks = Dynarray.of_array body.blocks in
  for block = 0 to Array.length body.blocks - 1 do
    match block_at blocks block with
    | { terminator = For { iteration = Pull _; part; blocks = loop_body; loop; _ }; _ } ->
        let dead : Mir.Graph.statement = { kind = Dead [ part ]; origin = loop.origin } in
        List.iter
          (fun ending ->
            let basic = block_at blocks ending in
            set_block blocks ending { basic with statements = basic.statements @ [ dead ] })
          (own_iteration_ends blocks loop_body);
        end_on_exits blocks ~body:loop_body ~part ~origin:loop.origin
    | _ -> ()
  done;
  { body with blocks = Mir.Graph.canonical (Dynarray.to_array blocks) }

let ended (mir : Mir.Graph.t) : Mir.Graph.t =
  { body = ended_body mir.body; lambdas = Array.map ended_body mir.lambdas }
