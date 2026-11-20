let raise_bug format = Compiler_bug.raise_bug ~stage:"MIR" format

type jump_targets = {
  break_ : Graph.block option;
  continue_ : Graph.terminator option;
  loop_provides : int;
  task_ends : (Tree.task * Graph.block) list;
  task_provides : (Tree.task * int) list;
  provides : int;
}

let expand_body (body : Tree.body) : Graph.body =
  let blocks : Graph.basic_block option Dynarray.t = Dynarray.create () in
  let take_fresh_number () =
    Dynarray.add_last blocks None;
    Dynarray.length blocks - 1
  in
  let list_blocks_since first =
    List.init (Dynarray.length blocks - first) (fun index -> first + index)
  in
  let close (index, emitted) terminator origin =
    Dynarray.set blocks index
      (Some { Graph.statements = List.rev emitted; terminator; terminator_origin = origin })
  in
  let make_assignment target value origin : Graph.statement =
    { kind = Basic (Assign { target; value = Operand value }); origin }
  in
  let find_place_local : Tree.place -> Tree.local option = function
    | { root = Local local; projections = [] } -> Some local
    | _ -> None
  in
  let find_whole_local : Tree.operand -> Tree.local option = function
    | Use { place; _ } -> find_place_local place
    | Borrow _ | Take _ | Immediate _ -> None
  in
  let is_use_of target (value : Tree.operand) =
    Option.is_some (find_whole_local value) && find_place_local target = find_whole_local value
  in
  let branch_on current (value : Tree.operand) ~yes ~no origin =
    match value with
    | Immediate { value = Boolean true; _ } -> close current (Goto yes) origin
    | Immediate { value = Boolean false; _ } -> close current (Goto no) origin
    | _ -> close current (Branch { condition = value; yes; no }) origin
  in
  let rec emit targets current (statements : Tree.statement list) =
    match statements with
    | [] -> Some current
    | statement :: rest -> (
        let origin = statement.origin in
        let emit_rest current = emit targets (current, []) rest in
        match statement.kind with
        | Choose { target; choice = Connective { connective; left; right } } ->
            let evaluated = take_fresh_number ()
            and decided = take_fresh_number ()
            and joined = take_fresh_number () in
            let yes, no =
              match connective with
              | And | Implies -> (evaluated, decided)
              | Or -> (decided, evaluated)
            in
            branch targets current left.statements left.value ~yes ~no origin;
            ignore (expand_arm targets evaluated right ~target ~joined origin);
            close
              ( decided,
                [
                  make_assignment target
                    (Immediate { value = Boolean (connective <> And); type_ = Types.bool })
                    origin;
                ] )
              (Goto joined) origin;
            emit_rest joined
        | Choose { target; choice = Conditional { condition; then_; else_; _ } } ->
            let yes = take_fresh_number ()
            and no = take_fresh_number ()
            and joined = take_fresh_number () in
            branch targets current condition.statements condition.value ~yes ~no origin;
            let reaches_then = expand_arm targets yes then_ ~target ~joined origin in
            let reaches_else = expand_arm targets no else_ ~target ~joined origin in
            if reaches_then || reaches_else then emit_rest joined else None
        | Choose { target; choice = Cases cases } ->
            let joined = take_fresh_number () in
            let unmatched, reaches =
              List.fold_left
                (fun (current, reaches) (case : Tree.case) ->
                  let matched = take_fresh_number () and next = take_fresh_number () in
                  branch targets current case.tests.statements case.tests.value ~yes:matched
                    ~no:next origin;
                  let reaches_value =
                    match case.guard with
                    | None -> expand_arm targets matched case.value ~target ~joined origin
                    | Some guard ->
                        let passed = take_fresh_number () in
                        branch targets (matched, []) guard.statements guard.value ~yes:passed
                          ~no:next origin;
                        expand_arm targets passed case.value ~target ~joined origin
                  in
                  ((next, []), reaches || reaches_value))
                (current, false) cases
            in
            close unmatched Unreachable origin;
            if reaches then emit_rest joined else None
        | Assert_by_bit_vector { condition; code; _ } ->
            let index, emitted = expand_block targets current code.statements in
            emit targets (index, { kind = Basic (Assert condition); origin } :: emitted) rest
        | While { condition; body; failed; _ } ->
            let header = take_fresh_number ()
            and inside = take_fresh_number ()
            and failing = take_fresh_number () in
            let after = take_fresh_number () in
            close current (Goto header) origin;
            branch targets (header, []) condition.statements condition.value ~yes:inside ~no:failing
              origin;
            let in_loop =
              {
                targets with
                break_ = Some after;
                continue_ = Some (Goto header);
                loop_provides = targets.provides;
              }
            in
            (match emit in_loop (inside, []) body.statements with
            | Some ended -> close ended (Goto header) origin
            | None -> ());
            close (expand_block targets (failing, []) failed) (Goto after) origin;
            emit_rest after
        | For { loop; iteration; part; elements; bindings; body } ->
            let index, emitted =
              match elements with
              | Some elements -> expand_block targets current elements.count.statements
              | None -> current
            in
            let after = take_fresh_number () in
            let inside = take_fresh_number () in
            let first = Dynarray.length blocks in
            let in_loop =
              {
                targets with
                break_ = Some after;
                continue_ = Some (Iteration_end { loop = index });
                loop_provides = targets.provides;
                task_provides =
                  (match loop.schedule with
                  | Concurrent ->
                      (Tree.Iteration { loop = loop.node }, targets.provides)
                      :: targets.task_provides
                  | Sequential | Parallel -> targets.task_provides);
              }
            in
            (match emit in_loop (inside, []) (bindings.statements @ body.statements) with
            | Some ended -> (
                match loop.quantified with
                | None -> close ended (Iteration_end { loop = index }) origin
                | Some { quantifier; decides } ->
                    let next_iteration = take_fresh_number () in
                    close (next_iteration, []) (Iteration_end { loop = index }) origin;
                    let decision =
                      Tree.Use
                        {
                          place = { root = Local decides; projections = [] };
                          type_ = Types.bool;
                          origin;
                        }
                    in
                    let yes, no =
                      match quantifier with
                      | Exists -> (after, next_iteration)
                      | Forall -> (next_iteration, after)
                    in
                    branch_on ended decision ~yes ~no origin)
            | None -> ());
            close (index, emitted)
              (For
                 {
                   iteration;
                   part;
                   elements =
                     Option.map
                       (fun (elements : Tree.elements) ->
                         { elements with count = { elements.count with statements = [] } })
                       elements;
                   body = inside;
                   blocks = inside :: list_blocks_since first;
                   after;
                   loop;
                 })
              origin;
            emit_rest after
        | Fork { fork; concurrent; branches } ->
            let join = take_fresh_number () in
            let entries = List.map (fun _ -> take_fresh_number ()) branches in
            let branches =
              List.mapi
                (fun index (branch : Tree.block) ->
                  let entry = List.nth entries index in
                  let next =
                    if index + 1 = List.length entries then join else List.nth entries (index + 1)
                  in
                  let first = Dynarray.length blocks in
                  let branch_end = if concurrent then Some (take_fresh_number ()) else None in
                  let in_branch =
                    match branch_end with
                    | Some branch_end ->
                        {
                          targets with
                          task_ends = (Tree.Branch { fork; index }, branch_end) :: targets.task_ends;
                          task_provides =
                            (Tree.Branch { fork; index }, targets.provides) :: targets.task_provides;
                        }
                    | None -> targets
                  in
                  let ended = emit in_branch (entry, []) branch.statements in
                  (match branch_end with
                  | Some branch_end ->
                      Option.iter (fun ended -> close ended (Goto branch_end) origin) ended;
                      close (branch_end, []) (Join { fork; next }) origin
                  | None ->
                      Option.iter (fun ended -> close ended (Join { fork; next }) origin) ended);
                  { Graph.entry; blocks = entry :: list_blocks_since first })
                branches
            in
            close current (Fork { fork; concurrent; branches; join = Some join }) origin;
            emit_rest join
        | Provide { target; provided; can_use_tasks; body } -> (
            let index, emitted = current in
            let started =
              (index, { Graph.kind = Provide_start { provided; can_use_tasks }; origin } :: emitted)
            in
            match
              ( emit { targets with provides = targets.provides + 1 } started body.statements,
                body.value )
            with
            | Some (index, emitted), Some value ->
                emit targets
                  ( index,
                    { kind = Provide_end; origin } :: make_assignment target value origin :: emitted
                  )
                  rest
            | None, None -> None
            | Some _, None | None, Some _ ->
                raise_bug "a `provide` block whose value and whose end disagree")
        | Resume { winner; exits } ->
            let next = take_fresh_number () in
            let exits =
              List.map
                (fun (exit : Tree.early_exit) ->
                  let entry = take_fresh_number () in
                  (match emit targets (entry, []) exit.resumed.statements with
                  | Some ended -> close ended (Goto next) origin
                  | None -> ());
                  { Graph.resume = entry; returned = exit.returned })
                exits
            in
            close current (Resume { winner; exits; next }) origin;
            emit_rest next
        | Yield { mode; part } ->
            let resume = take_fresh_number () in
            close current (Yield { mode; part; resume }) origin;
            emit_rest resume
        | Jump jump ->
            let terminator, left_provides =
              match jump with
              | Return returned -> (Graph.Return returned, targets.provides)
              | Break -> (
                  match targets.break_ with
                  | Some after -> (Goto after, targets.provides - targets.loop_provides)
                  | None -> raise_bug "a `break` outside a loop")
              | Continue -> (
                  match targets.continue_ with
                  | Some continue_ -> (continue_, targets.provides - targets.loop_provides)
                  | None -> raise_bug "a `continue` outside a loop")
              | Cancel { task; winner; number; returned } -> (
                  match List.assoc_opt task targets.task_provides with
                  | Some task_provides ->
                      ( Cancel
                          {
                            task;
                            task_end = List.assoc_opt task targets.task_ends;
                            winner;
                            number;
                            returned;
                          },
                        targets.provides - task_provides )
                  | None -> raise_bug "a cancellation outside its task")
              | Unreachable -> (Unreachable, 0)
              | Written_unreachable -> (Written_unreachable, 0)
              | Todo -> (Todo, 0)
            in
            let index, emitted = current in
            close
              ( index,
                List.init left_provides (fun _ : Graph.statement -> { kind = Provide_end; origin })
                @ emitted )
              terminator origin;
            None
        | Basic basic ->
            let index, emitted = current in
            emit targets (index, { kind = Basic basic; origin } :: emitted) rest)
  and expand_block targets current (statements : Tree.statement list) =
    match emit targets current statements with
    | Some current -> current
    | None -> raise_bug "statements that control leaves, where it goes on after them"
  and branch targets current (statements : Tree.statement list) (value : Tree.operand option) ~yes
      ~no origin =
    match value with
    | None -> (
        match emit targets current statements with
        | None -> ()
        | Some _ -> raise_bug "statements with no value, whose end control reaches")
    | Some value -> (
        match List.rev statements with
        | { kind = Choose { target; choice = Connective { connective; left; right } }; _ } :: before
          when is_use_of target value ->
            branch_connective targets connective right ~yes ~no origin ~left:(fun ~yes ~no ->
                branch targets current
                  (List.rev_append before left.statements)
                  left.value ~yes ~no origin)
        | { kind = Basic (Assign { target; value = Not negated; _ }); _ } :: before
          when is_use_of target value ->
            branch targets current (List.rev before) (Some negated) ~yes:no ~no:yes origin
        | _ -> branch_on (expand_block targets current statements) value ~yes ~no origin)
  and branch_connective targets connective (right : Tree.block) ~left ~yes ~no origin =
    let evaluated = take_fresh_number () in
    (match connective with
    | And -> left ~yes:evaluated ~no
    | Or -> left ~yes ~no:evaluated
    | Implies -> left ~yes:evaluated ~no:yes);
    branch targets (evaluated, []) right.statements right.value ~yes ~no origin
  and expand_arm targets entry (block : Tree.block) ~target ~joined origin =
    match (emit targets (entry, []) block.statements, block.value) with
    | Some (index, emitted), Some value ->
        close (index, make_assignment target value origin :: emitted) (Goto joined) origin;
        true
    | None, None -> false
    | Some _, None | None, Some _ -> raise_bug "a block whose value and whose end disagree"
  in
  let entry = take_fresh_number () in
  (match
     emit
       {
         break_ = None;
         continue_ = None;
         loop_provides = 0;
         task_ends = [];
         task_provides = [];
         provides = 0;
       }
       (entry, []) body.code.statements
   with
  | None -> ()
  | Some _ -> raise_bug "a body whose end control reaches");
  {
    parameters = body.parameters;
    captures = body.captures;
    locals = body.locals;
    blocks = Graph.canonicalize (Dynarray.to_array blocks);
  }

let expand (code : Tree.t) : Graph.t =
  { body = expand_body code.body; lambdas = Array.map expand_body code.lambdas }

let expand_formula (formula : Tree.formula) : Graph.t =
  expand
    {
      body =
        {
          parameters = formula.parameters;
          captures = [];
          locals = formula.locals;
          is_functional = false;
          value_type = None;
          code =
            {
              statements =
                formula.value.statements
                @ [ { kind = Jump (Return formula.value.value); origin = formula.origin } ];
              value = None;
            };
        };
      lambdas = formula.lambdas;
    }
