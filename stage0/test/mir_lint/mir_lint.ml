let rec list_place_locals (place : Mir.place) =
  (match place.root with Local local -> [ local ] | Constant _ | Literal _ -> [])
  @ List.concat_map
      (fun (projection : Mir.projection) ->
        match projection with
        | Element { index; _ } -> list_operand_locals index
        | Range { start; stop; _ } ->
            list_operand_locals start @ Option.fold ~none:[] ~some:list_operand_locals stop
        | Field _ | Variant_field _ -> [])
      place.projections

and list_operand_locals : Mir.operand -> Mir.local list = function
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> list_place_locals place
  | Immediate _ -> []

let list_call_locals (call : Mir.call) =
  (match call.callee.target with Indirect callee -> list_operand_locals callee | _ -> [])
  @ List.concat_map
      (fun (argument : Mir.argument) -> list_operand_locals argument.value)
      call.arguments

let list_written (place : Mir.place) =
  match place with
  | { root = Local local; projections = [] } -> ([], [ local ])
  | _ -> (list_place_locals place, [])

let rec list_rvalue_locals : Mir.rvalue -> Mir.local list = function
  | Operand value | Not value | Convert { value; _ } | Copy value -> list_operand_locals value
  | Operation { operands; _ } | Array operands -> List.concat_map list_operand_locals operands
  | Compare { left; right; _ } -> list_operand_locals left @ list_operand_locals right
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, field) -> Option.fold ~none:[] ~some:list_operand_locals field)
        fields
  | Is_variant { place; _ } -> list_place_locals place
  | Lambda { captures; _ } ->
      List.concat_map (fun (capture : Mir.capture) -> list_place_locals capture.place) captures
  | Function_value _ | Value_parameter _ | Parameter_default _ -> []
  | Specification (Result | Yielded) -> []
  | Specification (Entry local) -> [ local ]
  | Specification (Identical (first, second)) ->
      list_operand_locals first @ list_operand_locals second
  | Specification (Applied { arguments; _ }) -> List.concat_map list_operand_locals arguments
  | Specification (Method_cost { method_; _ }) -> (
      match method_ with Indirect callee -> list_operand_locals callee | _ -> [])
  | Specification (Map entries) ->
      List.concat_map
        (fun (key, value) -> list_operand_locals key @ list_operand_locals value)
        entries
  | Specification (Quantified { range; parameter; matches; body; _ }) ->
      (match range with
        | Over_type _ -> []
        | Over_range { start; stop; _ } -> list_operand_locals start @ list_operand_locals stop)
      @ List.filter
          (fun local -> local <> parameter)
          (list_block_locals
             { statements = matches.statements @ body.statements; value = body.value })

and list_choice_locals : Mir.choice -> Mir.local list = function
  | Conditional { condition; then_; else_; _ } ->
      list_block_locals condition @ list_block_locals then_ @ list_block_locals else_
  | Cases cases ->
      List.concat_map
        (fun (case : Mir.case) ->
          list_block_locals case.tests
          @ Option.fold ~none:[] ~some:list_block_locals case.guard
          @ list_block_locals case.value)
        cases
  | Connective { left; right; _ } -> list_block_locals left @ list_block_locals right

and list_block_locals (block : Mir.block) =
  let read, given =
    List.fold_left
      (fun (read, given) (statement : Mir.statement) ->
        let reads, gives, _ = collect_tree_effects statement.kind in
        (List.filter (fun local -> not (List.mem local given)) reads @ read, gives @ given))
      ([], []) block.statements
  in
  List.filter
    (fun local -> not (List.mem local given))
    (Option.fold ~none:[] ~some:list_operand_locals block.value)
  @ read

and collect_tree_effects : Mir.statement_kind -> Mir.local list * Mir.local list * Mir.local list =
  function
  | Basic basic -> collect_effects basic
  | Choose { target; choice } ->
      let read, given = list_written target in
      (list_choice_locals choice @ read, given, [])
  | Assert_by_bit_vector { condition; _ } -> (list_operand_locals condition, [], [])
  | While _ | For _ | Fork _ | Provide _ | Resume _ | Yield _ | Jump _ ->
      failwith "a statement that holds blocks or jumps, where a formula holds none"

and collect_effects : Mir.basic -> Mir.local list * Mir.local list * Mir.local list = function
  | Assign { target; value; _ } ->
      let read, given = list_written target in
      (list_rvalue_locals value @ read, given, [])
  | Call { destination; call } ->
      let read, given = Option.fold ~none:([], []) ~some:list_written destination in
      (list_call_locals call @ read, given, [])
  | Lend { part; call } -> (list_call_locals call, [ part ], [])
  | Live locals -> ([], locals, [])
  | Dead locals -> ([], [], locals)
  | Assert value | Echo value -> (list_operand_locals value, [], [])
  | Loan_start { borrowed; _ } -> (list_operand_locals borrowed, [], [])
  | Loan_end _ | Ghost_assert _ | Proof _ | Evaluated_assert _ -> ([], [], [])

let collect_graph_effects :
    Mir.Graph.statement_kind -> Mir.local list * Mir.local list * Mir.local list = function
  | Basic basic -> collect_effects basic
  | Provide_start { provided; _ } ->
      ( List.concat_map
          (fun (provided : Mir.provided) -> list_operand_locals provided.value)
          provided,
        [],
        [] )
  | Provide_end -> ([], [], [])

let rec list_yielded_locals : Mir.yielded -> Mir.local list = function
  | Part value -> list_operand_locals value
  | Built { fields; _ } ->
      List.concat_map
        (fun (_, field) -> Option.fold ~none:[] ~some:list_yielded_locals field)
        fields

let list_terminator_reads : Mir.Graph.terminator -> Mir.local list = function
  | Branch { condition; _ } -> list_operand_locals condition
  | For { iteration = Range { start; stop; _ }; _ } ->
      list_operand_locals start @ list_operand_locals stop
  | For { iteration = Pull { cursor; _ }; _ } -> list_place_locals cursor
  | Yield { part; _ } -> list_yielded_locals part
  | Return (Some value) | Cancel { returned = Some (value, _); _ } -> list_operand_locals value
  | Resume { winner; _ } -> [ winner ]
  | Goto _ | Fork _ | Join _ | Iteration_end _
  | Return None
  | Cancel { returned = None; _ }
  | Unreachable | Written_unreachable | Todo ->
      []

let alive = 1
let ended = 2

let check definition (body : Mir.Graph.body) =
  let count = Array.length body.blocks and locals = Array.length body.locals in
  let raise_problem format =
    Printf.ksprintf (fun text -> Harness.fail "%s: %s" definition text) format
  in
  let describe local =
    let kind =
      match body.locals.(local).kind with
      | Source { local; _ } -> "source " ^ Option.value (Mir.find_local_name local) ~default:"?"
      | Temporary -> "temporary"
      | Lent _ -> "lent"
    in
    let origin =
      Array.fold_left
        (fun origin (basic : Mir.Graph.basic_block) ->
          List.fold_left
            (fun origin (statement : Mir.Graph.statement) ->
              match (origin, statement.kind) with
              | ( None,
                  Basic (Assign { target = { root = Local assigned; projections = [] }; value; _ })
                )
                when assigned = local ->
                  Some
                    (match value with
                    | Operand (Use _) -> "use"
                    | Operand (Borrow _) -> "borrow"
                    | Operand _ -> "operand"
                    | Operation _ -> "operation"
                    | Compare _ -> "compare"
                    | Not _ -> "not"
                    | Construct _ -> "construct"
                    | Array _ -> "array"
                    | Is_variant _ -> "is_variant"
                    | Convert _ -> "convert"
                    | Copy _ -> "copy"
                    | Function_value _ -> "function"
                    | Lambda _ -> "lambda"
                    | Value_parameter _ -> "value_parameter"
                    | Parameter_default _ -> "parameter_default"
                    | Specification _ -> "specification")
              | ( None,
                  Basic (Call { destination = Some { root = Local assigned; projections = [] }; _ })
                )
                when assigned = local ->
                  Some "call"
              | None, Basic (Lend { part; _ }) when part = local -> Some "lend"
              | _ -> origin)
            origin basic.statements)
        None body.blocks
    in
    kind ^ " " ^ Option.value origin ~default:"unassigned"
  in
  let check_block index =
    if index < 0 || index >= count then raise_problem "a jump to block %d" index
  in
  let check_local index = if index < 0 || index >= locals then raise_problem "local _%d" index in
  let loans =
    Array.fold_left
      (fun most (basic : Mir.Graph.basic_block) ->
        List.fold_left
          (fun most (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Basic (Loan_start { loan; _ }) -> max most (loan + 1)
            | _ -> most)
          most basic.statements)
      0 body.blocks
  in
  let bindings = Array.make locals 0 in
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      List.iter
        (fun (statement : Mir.Graph.statement) ->
          match statement.kind with
          | Basic
              (Assign
                 {
                   target = { root = Local bound; projections = [] };
                   value = Operand (Borrow _);
                   _;
                 }) -> (
              bindings.(bound) <- bindings.(bound) + 1;
              match body.locals.(bound).kind with
              | Lent _ | Source { mode = Read | Mut; _ } -> ()
              | Temporary | Source { mode = Own; _ } ->
                  raise_problem "_%d (%s) is bound to a place, and is declared to own its value"
                    bound (describe bound))
          | _ -> ())
        basic.statements)
    body.blocks;
  Array.iteri
    (fun bound count ->
      if count > 1 <> body.locals.(bound).has_several_bindings then
        raise_problem "_%d (%s) is bound to a place by %d statements" bound (describe bound) count)
    bindings;
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      List.iter
        (fun (statement : Mir.Graph.statement) ->
          let read, given, ends = collect_graph_effects statement.kind in
          List.iter check_local (read @ given @ ends))
        basic.statements;
      List.iter check_local (list_terminator_reads basic.terminator);
      List.iter check_block (Mir.Graph.For_testing.list_successors basic.terminator);
      match basic.terminator with
      | For { part; body = inside; blocks; after; _ } ->
          check_local part;
          List.iter check_block (inside :: after :: blocks)
      | Fork { branches; join; _ } ->
          List.iter
            (fun (branch : Mir.Graph.branch) ->
              List.iter check_block (branch.entry :: branch.blocks))
            branches;
          Option.iter check_block join
      | _ -> ())
    body.blocks;
  let parts = ref [] in
  Array.iteri
    (fun index (basic : Mir.Graph.basic_block) ->
      (match Mir.Graph.find_iteration_loop basic.terminator with
      | Some loop -> (
          match body.blocks.(loop).terminator with
          | For { blocks; _ } when List.mem index blocks -> ()
          | _ ->
              raise_problem "block %d ends an iteration of %d, which is not a loop around it" index
                loop)
      | None -> ());
      match basic.terminator with
      | For { part; body = inside; blocks; after; _ } ->
          parts := part :: !parts;
          if not (List.mem inside blocks) then
            raise_problem "a loop's body %d is not among its blocks" inside;
          List.iter
            (fun inner ->
              match body.blocks.(inner).terminator with
              | Cancel _ -> ()
              | terminator ->
                  List.iter
                    (fun target ->
                      if target <> after && not (List.mem target blocks) then
                        raise_problem "block %d of the loop at %d jumps out to %d" inner index
                          target)
                    (Mir.Graph.For_testing.list_successors terminator))
            blocks
      | Fork { fork; branches; join; _ } ->
          let entries = List.map (fun (branch : Mir.Graph.branch) -> branch.entry) branches in
          List.iteri
            (fun position (branch : Mir.Graph.branch) ->
              let next =
                match List.nth_opt entries (position + 1) with
                | Some next -> Some next
                | None -> join
              in
              List.iter
                (fun inner ->
                  match body.blocks.(inner).terminator with
                  | Join { fork = joined; next = target } ->
                      if joined <> fork || Some target <> next then
                        raise_problem "branch %d of the block at %d joins to %d" position index
                          target
                  | terminator ->
                      List.iter
                        (fun target ->
                          if not (List.mem target branch.blocks) then
                            raise_problem "branch %d of the block at %d jumps out to %d" position
                              index target)
                        (Mir.Graph.For_testing.list_successors terminator))
                branch.blocks)
            branches
      | _ -> ())
    body.blocks;
  let held_by_exits =
    Array.fold_left
      (fun held (basic : Mir.Graph.basic_block) ->
        match basic.terminator with
        | Cancel { returned = Some (value, _); _ } -> list_operand_locals value @ held
        | _ -> held)
      [] body.blocks
  in
  let locals_in = Array.init (2 * count) (fun _ -> Array.make locals 0)
  and loans_in = Array.init (2 * count) (fun _ -> Array.make loans 0)
  and reached = Array.make (2 * count) false in
  List.iter (fun parameter -> locals_in.(0).(parameter) <- alive) (body.parameters @ body.captures);
  reached.(0) <- true;
  let pending = Queue.create () in
  Queue.add 0 pending;
  let flow target (state, open_loans) =
    let changed = ref (not reached.(target)) in
    reached.(target) <- true;
    Array.iteri
      (fun index value ->
        let merged = locals_in.(target).(index) lor value in
        if merged <> locals_in.(target).(index) then (
          locals_in.(target).(index) <- merged;
          changed := true))
      state;
    Array.iteri
      (fun index value ->
        let merged = loans_in.(target).(index) lor value in
        if merged <> loans_in.(target).(index) then (
          loans_in.(target).(index) <- merged;
          changed := true))
      open_loans;
    if !changed then Queue.add target pending
  in
  let entered = Hashtbl.create 4 in
  let run ~report node =
    let state = Array.copy locals_in.(node) and open_loans = Array.copy loans_in.(node) in
    let read at local =
      if report && state.(local) land ended <> 0 then
        raise_problem "block %d reads _%d where a path has ended it" at local
    in
    let apply at (statement : Mir.Graph.statement) =
      let read_locals, given, ends = collect_graph_effects statement.kind in
      List.iter (read at) read_locals;
      List.iter (fun local -> state.(local) <- alive) given;
      List.iter (fun local -> state.(local) <- ended) ends;
      match statement.kind with
      | Basic (Loan_start { loan; _ }) -> open_loans.(loan) <- alive
      | Basic (Loan_end ended_loans) ->
          List.iter (fun loan -> open_loans.(loan) <- ended) ended_loans
      | _ -> ()
    in
    let list_still_alive ~kept =
      List.filter
        (fun local -> state.(local) land alive <> 0 && not (List.mem local kept))
        (List.init locals Fun.id)
    in
    let list_still_open ~kept =
      List.filter
        (fun loan -> open_loans.(loan) land alive <> 0 && not (List.mem loan kept))
        (List.init loans Fun.id)
    in
    let check_return at value =
      let kept =
        body.parameters @ body.captures @ !parts @ held_by_exits
        @ match value with Some value -> list_operand_locals value | None -> []
      in
      if report then begin
        (match list_still_alive ~kept with
        | [] -> ()
        | local :: _ ->
            raise_problem "block %d returns with _%d alive (%s)" at local (describe local));
        match list_still_open ~kept:[] with
        | [] -> ()
        | loan :: _ -> raise_problem "block %d returns with loan %d open" at loan
      end
    in
    let check_iteration_end at =
      match Mir.Graph.find_iteration_loop body.blocks.(at).terminator with
      | Some loop ->
          (if report then
             match Hashtbl.find_opt entered loop with
             | Some (alive_then, open_then) -> (
                 (match list_still_alive ~kept:(alive_then @ !parts @ held_by_exits) with
                 | [] -> ()
                 | local :: _ -> raise_problem "block %d ends an iteration with _%d alive" at local);
                 match list_still_open ~kept:open_then with
                 | [] -> ()
                 | loan :: _ -> raise_problem "block %d ends an iteration with loan %d open" at loan
                 )
             | None -> ());
          flow (count + loop) (state, open_loans)
      | None -> ()
    in
    if node >= count then begin
      let loop = node - count in
      match body.blocks.(loop).terminator with
      | For { part; body = inside; after; _ } ->
          let iterating = Array.copy state in
          iterating.(part) <- alive;
          flow inside (iterating, open_loans);
          flow after (state, open_loans)
      | _ -> ()
    end
    else
      let basic = body.blocks.(node) in
      List.iter (apply node) basic.statements;
      List.iter (read node) (list_terminator_reads basic.terminator);
      match basic.terminator with
      | For _ ->
          if not (Hashtbl.mem entered node) then
            Hashtbl.replace entered node (list_still_alive ~kept:[], list_still_open ~kept:[]);
          flow (count + node) (state, open_loans)
      | Iteration_end _ -> check_iteration_end node
      | Return value -> check_return node value
      | Cancel { task = Iteration _; _ } -> check_iteration_end node
      | terminator ->
          List.iter
            (fun target -> flow target (state, open_loans))
            (Mir.Graph.For_testing.list_successors terminator)
  in
  while not (Queue.is_empty pending) do
    run ~report:false (Queue.pop pending)
  done;
  Array.iteri (fun node is_reached -> if is_reached then run ~report:true node) reached

let check_file database (file : Path.file) =
  let parts = Database.For_testing.make_mir_lookups database in
  List.iter
    (fun (declaration : Resolve.Names.declaration) ->
      let key = declaration.key in
      let definition = Resolve.Names.show_key key in
      match
        try Mir.find_graph (parts.read_body_part key)
        with Compiler_bug.Bug bug -> Harness.fail "%s: %s" definition bug.message
      with
      | Some mir ->
          check definition mir.body;
          Array.iter (check definition) mir.lambdas
      | None -> ())
    ((Database.make_name_lookups database).list_declarations_in file)
