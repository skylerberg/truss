open Tree

let bug format = Compiler_bug.bug ~stage:"MIR" format

type block = int
type early_exit = { resume : block; returned : local option }
type branch = { entry : block; blocks : block list }
type in_graph = In_graph
type statement = { kind : in_graph statement_kind; origin : Core.origin }

type terminator =
  | Goto of block
  | Branch of { condition : operand; yes : block; no : block; is_if_condition : bool }
  | For of {
      iteration : iteration;
      part : local;
      lent : lent_element option;
      body : block;
      binding_count : int;
      blocks : block list;
      after : block;
      loop : loop;
    }
  | Fork of { fork : Core.origin; concurrent : bool; branches : branch list; join : block option }
  | Join of { fork : Core.origin; next : block }
  | Iteration_end of { loop : block }
  | Yield of { mode : Types.mode; part : yielded; resume : block }
  | Return of operand option
  | Cancel of {
      task : task;
      task_end : block option;
      winner : local;
      number : int;
      returned : (operand * local) option;
    }
  | Resume of { winner : local; exits : early_exit list; next : block }
  | Unreachable
  | Written_unreachable
  | Todo

type basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
}

type body = {
  parameters : local list;
  captures : local list;
  locals : local_info array;
  blocks : basic_block array;
}

type t = { body : body; lambdas : body array }

let successors = function
  | Goto block -> [ block ]
  | Branch { yes; no; _ } -> [ yes; no ]
  | For { body; after; _ } -> [ body; after ]
  | Fork { branches = first :: _; _ } -> [ first.entry ]
  | Fork { branches = []; _ } -> []
  | Join { next; _ } -> [ next ]
  | Yield { resume; _ } -> [ resume ]
  | Cancel { task_end; _ } -> Option.to_list task_end
  | Resume { exits; next; _ } -> List.map (fun exit -> exit.resume) exits @ [ next ]
  | Iteration_end _ | Return _ | Unreachable | Written_unreachable | Todo -> []

let canonical (blocks : basic_block array) =
  let visited = Array.make (Array.length blocks) false and order = ref [] in
  let rec visit block =
    if not visited.(block) then begin
      visited.(block) <- true;
      List.iter visit (successors blocks.(block).terminator);
      order := block :: !order
    end
  in
  visit 0;
  let renumbered = Array.make (Array.length blocks) (-1) in
  List.iteri (fun index block -> renumbered.(block) <- index) !order;
  let target block = renumbered.(block) in
  let reached blocks =
    List.filter_map (fun block -> if visited.(block) then Some (target block) else None) blocks
  in
  let innermost = Hashtbl.create 4 in
  List.iter
    (fun loop ->
      match blocks.(loop).terminator with
      | For { blocks = inside; _ } ->
          let size = List.length inside in
          List.iter
            (fun block ->
              match Hashtbl.find_opt innermost block with
              | Some (_, known) when known <= size -> ()
              | _ -> Hashtbl.replace innermost block (loop, size))
            inside
      | _ -> ())
    !order;
  let loop_of block =
    match Hashtbl.find_opt innermost block with
    | Some (loop, _) -> target loop
    | None -> bug "the end of an iteration outside every loop"
  in
  let renumber at = function
    | Goto block -> Goto (target block)
    | Branch branch -> Branch { branch with yes = target branch.yes; no = target branch.no }
    | For loop ->
        For
          {
            loop with
            body = target loop.body;
            blocks = reached loop.blocks;
            after = target loop.after;
          }
    | Fork fork ->
        Fork
          {
            fork with
            branches =
              List.filter_map
                (fun branch ->
                  if visited.(branch.entry) then
                    Some { entry = target branch.entry; blocks = reached branch.blocks }
                  else None)
                fork.branches;
            join =
              Option.bind fork.join (fun join ->
                  if visited.(join) then Some (target join) else None);
          }
    | Join { fork; next } -> Join { fork; next = target next }
    | Yield yielded -> Yield { yielded with resume = target yielded.resume }
    | Cancel cancel ->
        Cancel
          {
            cancel with
            task_end =
              Option.bind cancel.task_end (fun task_end ->
                  if visited.(task_end) then Some (target task_end) else None);
          }
    | Resume { winner; exits; next } ->
        Resume
          {
            winner;
            exits = List.map (fun exit -> { exit with resume = target exit.resume }) exits;
            next = target next;
          }
    | Iteration_end _ -> Iteration_end { loop = loop_of at }
    | (Return _ | Unreachable | Written_unreachable | Todo) as other -> other
  in
  Array.of_list
    (List.map
       (fun block ->
         { (blocks.(block)) with terminator = renumber block blocks.(block).terminator })
       !order)

let iteration_loop = function Iteration_end { loop } -> Some loop | _ -> None

let block_successors (body : body) block =
  let terminator = body.blocks.(block).terminator in
  (match Option.map (fun loop -> body.blocks.(loop).terminator) (iteration_loop terminator) with
    | Some (For { body = first; after; _ }) -> [ first; after ]
    | _ -> [])
  @ successors terminator
