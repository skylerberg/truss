let raise_bug format = Compiler_bug.raise_bug ~stage:"MIR" format

type undecided =
  | Undecided_connective of {
      target : Tree.place;
      connective : Tree.connective;
      left : Tree.operand;
      right : Tree.block;
      origin : Core.origin;
    }
  | Undecided_not of { target : Tree.place; negated : Tree.operand; origin : Core.origin }

type jump_targets = {
  break_ : Graph.block option;
  continue_ : Graph.terminator option;
  task_ends : (Tree.task * Graph.block) list;
}

let expand_body (body : Tree.body) : Graph.body =
  let blocks : Graph.basic_block Dynarray.t = Dynarray.create () in
  let fresh () =
    Dynarray.add_last blocks { statements = []; terminator = Unreachable; terminator_origin = 0 };
    Dynarray.length blocks - 1
  in
  let made_since first = List.init (Dynarray.length blocks - first) (fun index -> first + index) in
  let close (index, emitted) terminator origin =
    Dynarray.set blocks index
      { statements = List.rev emitted; terminator; terminator_origin = origin }
  in
  let assigned target value origin : Graph.statement =
    { kind = Assign { target; value = Operand value }; origin }
  in
  let place_local : Tree.place -> Tree.local option = function
    | { root = Local local; projections = [] } -> Some local
    | _ -> None
  in
  let whole_local : Tree.operand -> Tree.local option = function
    | Use { place; _ } -> place_local place
    | Borrow _ | Take _ | Constant _ -> None
  in
  let is_use_of target (value : Tree.operand) =
    Option.is_some (whole_local value) && place_local target = whole_local value
  in
  let branch_on current (value : Tree.operand) ~yes ~no origin =
    match value with
    | Constant { value = Boolean true; _ } -> close current (Goto yes) origin
    | Constant { value = Boolean false; _ } -> close current (Goto no) origin
    | _ -> close current (Branch { condition = value; yes; no; is_if_condition = false }) origin
  in
  let rec emit targets current (undecided : undecided list) (statements : Tree.statement list) =
    let decided () = with_values targets current undecided in
    let reads_undecided (operand : Tree.operand) =
      match List.rev undecided with
      | (Undecided_connective { target; _ } | Undecided_not { target; _ }) :: _ ->
          is_use_of target operand
      | [] -> false
    in
    match statements with
    | [] -> Some (current, undecided)
    | statement :: rest -> (
        let origin = statement.origin in
        let go_on current = emit targets (current, []) [] rest in
        match statement.kind with
        | Choose { target; choice = Connective { connective; left; right } } ->
            let pending = Undecided_connective { target; connective; left; right; origin } in
            if reads_undecided left then emit targets current (undecided @ [ pending ]) rest
            else emit targets (decided ()) [ pending ] rest
        | Basic
            (Assign { target = { root = Local _; projections = [] } as target; value = Not negated })
          when reads_undecided negated ->
            emit targets current (undecided @ [ Undecided_not { target; negated; origin } ]) rest
        | Choose { target; choice = Conditional { condition; then_; else_; _ } } ->
            let yes = fresh () and no = fresh () and joined = fresh () in
            if reads_undecided condition then
              branch_undecided targets current undecided condition ~yes ~no origin
            else branch targets (decided ()) [] (Some condition) ~yes ~no origin;
            let reaches_then = arm targets yes then_ ~target ~joined origin in
            let reaches_else = arm targets no else_ ~target ~joined origin in
            if reaches_then || reaches_else then go_on joined else None
        | Choose { target; choice = Cases cases } ->
            let joined = fresh () in
            let unmatched, reaches =
              List.fold_left
                (fun (current, reaches) (case : Tree.case) ->
                  let matched = fresh () and next = fresh () in
                  branch targets current case.tests.statements case.tests.value ~yes:matched
                    ~no:next origin;
                  let reaches_value =
                    match case.guard with
                    | None -> arm targets matched case.value ~target ~joined origin
                    | Some guard ->
                        let passed = fresh () in
                        branch targets (matched, []) guard.statements guard.value ~yes:passed
                          ~no:next origin;
                        arm targets passed case.value ~target ~joined origin
                  in
                  ((next, []), reaches || reaches_value))
                (decided (), false)
                cases
            in
            close unmatched Unreachable origin;
            if reaches then go_on joined else None
        | Assert_by_bit_vector { condition; code; _ } ->
            let index, emitted = block targets (decided ()) code.statements in
            emit targets (index, { kind = Assert condition; origin } :: emitted) [] rest
        | While { condition; body; failed; _ } ->
            let header = fresh () and inside = fresh () and failing = fresh () in
            let after = fresh () in
            close (decided ()) (Goto header) origin;
            branch targets (header, []) condition.statements condition.value ~yes:inside ~no:failing
              origin;
            let in_loop = { targets with break_ = Some after; continue_ = Some (Goto header) } in
            (match emit in_loop (inside, []) [] body.statements with
            | Some (current, undecided) ->
                close (with_values in_loop current undecided) (Goto header) origin
            | None -> ());
            close (block targets (failing, []) failed) (Goto after) origin;
            go_on after
        | For { loop; iteration; part; lent; binding_count; body } ->
            let index, emitted =
              match lent with
              | Some lent -> block targets (decided ()) lent.count.statements
              | None -> decided ()
            in
            let after = fresh () in
            let inside = fresh () in
            let first = Dynarray.length blocks in
            let in_loop =
              {
                targets with
                break_ = Some after;
                continue_ = Some (Iteration_end { loop = index });
              }
            in
            (match emit in_loop (inside, []) [] body.statements with
            | Some (current, undecided) ->
                close
                  (with_values in_loop current undecided)
                  (Iteration_end { loop = index })
                  origin
            | None -> ());
            close (index, emitted)
              (For
                 {
                   iteration;
                   part;
                   lent =
                     Option.map
                       (fun (lent : Tree.lent_element) ->
                         { lent with count = { lent.count with statements = [] } })
                       lent;
                   body = inside;
                   binding_count;
                   blocks = inside :: made_since first;
                   after;
                   loop;
                 })
              origin;
            go_on after
        | Fork { fork; concurrent; branches } ->
            let current = decided () in
            let join = fresh () in
            let entries = List.map (fun _ -> fresh ()) branches in
            let branches =
              List.mapi
                (fun index (branch : Tree.block) ->
                  let entry = List.nth entries index in
                  let next =
                    if index + 1 = List.length entries then join else List.nth entries (index + 1)
                  in
                  let first = Dynarray.length blocks in
                  let branch_end = if concurrent then Some (fresh ()) else None in
                  let in_branch =
                    match branch_end with
                    | Some branch_end ->
                        {
                          targets with
                          task_ends =
                            (Tree.Branch { block = fork; index }, branch_end) :: targets.task_ends;
                        }
                    | None -> targets
                  in
                  let ended =
                    Option.map
                      (fun (current, undecided) -> with_values in_branch current undecided)
                      (emit in_branch (entry, []) [] branch.statements)
                  in
                  (match branch_end with
                  | Some branch_end ->
                      Option.iter (fun ended -> close ended (Goto branch_end) origin) ended;
                      close (branch_end, []) (Join { fork; next }) origin
                  | None ->
                      Option.iter (fun ended -> close ended (Join { fork; next }) origin) ended);
                  { Graph.entry; blocks = entry :: made_since first })
                branches
            in
            close current (Fork { fork; concurrent; branches; join = Some join }) origin;
            go_on join
        | Resume { winner; exits } ->
            let current = decided () in
            let next = fresh () in
            let exits =
              List.map
                (fun (exit : Tree.early_exit) ->
                  let entry = fresh () in
                  (match emit targets (entry, []) [] exit.resumed.statements with
                  | Some (current, undecided) ->
                      close (with_values targets current undecided) (Goto next) origin
                  | None -> ());
                  { Graph.resume = entry; returned = exit.returned })
                exits
            in
            close current (Resume { winner; exits; next }) origin;
            go_on next
        | Yield { mode; part } ->
            let resume = fresh () in
            close (decided ()) (Yield { mode; part; resume }) origin;
            go_on resume
        | Jump jump ->
            let terminator : Graph.terminator =
              match jump with
              | Return returned -> Return returned
              | Break -> (
                  match targets.break_ with
                  | Some after -> Goto after
                  | None -> raise_bug "a `break` outside a loop")
              | Continue -> (
                  match targets.continue_ with
                  | Some continue_ -> continue_
                  | None -> raise_bug "a `continue` outside a loop")
              | Cancel { task; winner; number; returned } ->
                  Cancel
                    {
                      task;
                      task_end = List.assoc_opt task targets.task_ends;
                      winner;
                      number;
                      returned;
                    }
              | Unreachable -> Unreachable
              | Written_unreachable -> Written_unreachable
              | Todo -> Todo
            in
            close (decided ()) terminator origin;
            None
        | Basic basic ->
            let index, emitted = decided () in
            emit targets (index, { kind = basic; origin } :: emitted) [] rest)
  and block targets current (statements : Tree.statement list) =
    match emit targets current [] statements with
    | Some (current, undecided) -> with_values targets current undecided
    | None -> raise_bug "statements that control leaves, where it goes on after them"
  and branch targets current (statements : Tree.statement list) (value : Tree.operand option) ~yes
      ~no origin =
    match value with
    | None -> (
        match emit targets current [] statements with
        | None -> ()
        | Some _ -> raise_bug "statements with no value, whose end control reaches")
    | Some value -> (
        match List.rev statements with
        | { kind = Choose { target; choice = Connective { connective; left; right } }; _ } :: before
          when is_use_of target value ->
            branch_connective targets connective right ~yes ~no origin ~left:(fun ~yes ~no ->
                branch targets current (List.rev before) (Some left) ~yes ~no origin)
        | { kind = Basic (Assign { target; value = Not negated; _ }); _ } :: before
          when is_use_of target value ->
            branch targets current (List.rev before) (Some negated) ~yes:no ~no:yes origin
        | _ -> branch_on (block targets current statements) value ~yes ~no origin)
  and branch_undecided targets current (undecided : undecided list) (value : Tree.operand) ~yes ~no
      origin =
    match List.rev undecided with
    | Undecided_connective { target; connective; left; right; _ } :: before
      when is_use_of target value ->
        branch_connective targets connective right ~yes ~no origin ~left:(fun ~yes ~no ->
            branch_undecided targets current (List.rev before) left ~yes ~no origin)
    | Undecided_not { target; negated; _ } :: before when is_use_of target value ->
        branch_undecided targets current (List.rev before) negated ~yes:no ~no:yes origin
    | _ -> branch_on (with_values targets current undecided) value ~yes ~no origin
  and branch_connective targets connective (right : Tree.block) ~left ~yes ~no origin =
    let evaluated = fresh () in
    (match connective with
    | And -> left ~yes:evaluated ~no
    | Or -> left ~yes ~no:evaluated
    | Implies -> left ~yes:evaluated ~no:yes);
    branch targets (evaluated, []) right.statements right.value ~yes ~no origin
  and with_values targets current (undecided : undecided list) =
    match List.rev undecided with
    | [] -> current
    | Undecided_connective { target; connective; left; right; origin } :: before ->
        let evaluated = fresh () and decided = fresh () and joined = fresh () in
        let yes, no =
          match connective with And | Implies -> (evaluated, decided) | Or -> (decided, evaluated)
        in
        branch_undecided targets current (List.rev before) left ~yes ~no origin;
        ignore (arm targets evaluated right ~target ~joined origin);
        close
          ( decided,
            [
              assigned target
                (Constant { value = Boolean (connective <> And); type_ = Types.bool })
                origin;
            ] )
          (Goto joined) origin;
        (joined, [])
    | Undecided_not { target; negated; origin } :: before ->
        let index, emitted = with_values targets current (List.rev before) in
        (index, { kind = Assign { target; value = Not negated }; origin } :: emitted)
  and arm targets entry (block : Tree.block) ~target ~joined origin =
    match (emit targets (entry, []) [] block.statements, block.value) with
    | Some (current, undecided), Some value ->
        let index, emitted = with_values targets current undecided in
        close (index, assigned target value origin :: emitted) (Goto joined) origin;
        true
    | None, None -> false
    | Some _, None | None, Some _ -> raise_bug "a block whose value and whose end disagree"
  in
  let entry = fresh () in
  (match
     emit { break_ = None; continue_ = None; task_ends = [] } (entry, []) [] body.code.statements
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
