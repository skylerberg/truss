let raise_bug format = Compiler_bug.raise_bug ~stage:"MIR" format

type block = int
type early_exit = { resume : block; returned : Tree.local option }
type branch = { entry : block; blocks : block list }

type statement_kind =
  | Basic of Tree.basic
  | Provide_start of { provided : Tree.provided list; can_use_tasks : bool }
  | Provide_end

type statement = { kind : statement_kind; origin : Core.origin }

type loop_head = {
  iteration : Tree.iteration;
  part : Tree.local;
  elements : Tree.elements option;
  body : block;
  blocks : block list;
  after : block;
  loop : Tree.loop;
}

type terminator =
  | Goto of block
  | Branch of { condition : Tree.operand; yes : block; no : block }
  | For of loop_head
  | Fork of { fork : Core.origin; concurrent : bool; branches : branch list; join : block option }
  | Join of { fork : Core.origin; next : block }
  | Iteration_end of { loop : block }
  | Yield of { mode : Language.Mode.t; part : Tree.yielded; resume : block }
  | Return of Tree.operand option
  | Cancel of {
      task : Tree.task;
      task_end : block option;
      winner : Tree.local;
      number : int;
      returned : (Tree.operand * Tree.local) option;
    }
  | Resume of { winner : Tree.local; exits : early_exit list; next : block }
  | Unreachable
  | Written_unreachable
  | Todo

type basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
}

type body = {
  parameters : Tree.local list;
  captures : Tree.local list;
  locals : Tree.local_info array;
  blocks : basic_block array;
}

type t = { body : body; lambdas : body array }

let list_successors = function
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

let canonicalize (closed : basic_block option array) =
  let read_block block =
    match closed.(block) with
    | Some basic -> basic
    | None -> raise_bug "block %d is reached and was never closed" block
  in
  let visited = Array.make (Array.length closed) false and order = ref [] in
  let rec visit block =
    if not visited.(block) then begin
      visited.(block) <- true;
      List.iter visit (list_successors (read_block block).terminator);
      order := block :: !order
    end
  in
  visit 0;
  let renumbered = Array.make (Array.length closed) None in
  List.iteri (fun index block -> renumbered.(block) <- Some index) !order;
  let read_target block =
    match renumbered.(block) with
    | Some index -> index
    | None -> raise_bug "a jump to block %d, which is unreachable" block
  in
  let renumber_blocks blocks = List.filter_map (fun block -> renumbered.(block)) blocks in
  let innermost = Hashtbl.create 4 in
  List.iter
    (fun loop ->
      match (read_block loop).terminator with
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
  let renumber_loop block =
    match Hashtbl.find_opt innermost block with
    | Some (loop, _) -> read_target loop
    | None -> raise_bug "the end of an iteration outside every loop"
  in
  let renumber at = function
    | Goto block -> Goto (read_target block)
    | Branch branch ->
        Branch { branch with yes = read_target branch.yes; no = read_target branch.no }
    | For loop ->
        For
          {
            loop with
            body = read_target loop.body;
            blocks = renumber_blocks loop.blocks;
            after = read_target loop.after;
          }
    | Fork fork ->
        Fork
          {
            fork with
            branches =
              List.filter_map
                (fun (branch : branch) ->
                  Option.map
                    (fun entry -> { entry; blocks = renumber_blocks branch.blocks })
                    renumbered.(branch.entry))
                fork.branches;
            join = Option.bind fork.join (fun join -> renumbered.(join));
          }
    | Join { fork; next } -> Join { fork; next = read_target next }
    | Yield yielded -> Yield { yielded with resume = read_target yielded.resume }
    | Cancel cancel ->
        Cancel
          {
            cancel with
            task_end = Option.bind cancel.task_end (fun task_end -> renumbered.(task_end));
          }
    | Resume { winner; exits; next } ->
        Resume
          {
            winner;
            exits = List.map (fun exit -> { exit with resume = read_target exit.resume }) exits;
            next = read_target next;
          }
    | Iteration_end _ -> Iteration_end { loop = renumber_loop at }
    | (Return _ | Unreachable | Written_unreachable | Todo) as other -> other
  in
  Array.of_list
    (List.map
       (fun block ->
         let basic = read_block block in
         { basic with terminator = renumber block basic.terminator })
       !order)

let find_iteration_loop = function Iteration_end { loop } -> Some loop | _ -> None

let read_loop_head (body : body) loop =
  match body.blocks.(loop).terminator with
  | For head -> head
  | _ -> raise_bug "the end of an iteration names block %d, which is no loop" loop

let list_block_successors (body : body) block =
  let terminator = body.blocks.(block).terminator in
  (match find_iteration_loop terminator with
    | Some loop ->
        let head = read_loop_head body loop in
        [ head.body; head.after ]
    | None -> [])
  @ list_successors terminator

module For_testing = struct
  let list_successors = list_successors
end
