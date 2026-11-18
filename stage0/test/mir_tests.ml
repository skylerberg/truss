let make_mir_parts packages = Database.For_testing.make_mir_lookups (Support.make_database packages)
let find_graph (parts : Mir.lookups) key = Mir.find_graph (parts.read_body_part key)
let find_code (parts : Mir.lookups) key = Mir.find_code (parts.read_body_part key)

let list_place_locals (place : Mir.place) =
  match place.root with Local local -> [ local ] | Constant _ | Literal _ -> []

let list_operand_locals : Mir.operand -> Mir.local list = function
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> list_place_locals place
  | Immediate _ -> []

let list_call_locals (call : Mir.call) =
  (match call.callee.target with Indirect callee -> list_operand_locals callee | _ -> [])
  @ List.concat_map
      (function Mir.Passed { value; _ } -> list_operand_locals value | Default -> [])
      call.arguments

let list_written (place : Mir.place) =
  match place with
  | { root = Local local; projections = [] } -> ([], [ local ])
  | _ -> (list_place_locals place, [])

let rec list_rvalue_locals : Mir.rvalue -> Mir.local list = function
  | Operand value | Not value | Convert { value; _ } | To_any { value; _ } | Copy value ->
      list_operand_locals value
  | Operation { operands; _ } | Array operands -> List.concat_map list_operand_locals operands
  | Compare { left; right; _ } -> list_operand_locals left @ list_operand_locals right
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, field) -> Option.fold ~none:[] ~some:list_operand_locals field)
        fields
  | Is_variant { place; _ } -> list_place_locals place
  | Lambda { captures; _ } ->
      List.concat_map (fun (capture : Mir.capture) -> list_place_locals capture.place) captures
  | Function_value _ | Value_parameter _ -> []
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
      list_operand_locals condition @ list_block_locals then_ @ list_block_locals else_
  | Cases cases ->
      List.concat_map
        (fun (case : Mir.case) ->
          list_block_locals case.tests
          @ Option.fold ~none:[] ~some:list_block_locals case.guard
          @ list_block_locals case.value)
        cases
  | Connective { left; right; _ } -> list_operand_locals left @ list_block_locals right

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
  | While _ | For _ | Fork _ | Resume _ | Yield _ | Jump _ ->
      failwith "a statement that holds blocks or jumps, where a formula holds none"

and collect_effects : Mir.basic -> Mir.local list * Mir.local list * Mir.local list = function
  | Assign { target; value; _ } ->
      let read, given = list_written target in
      (list_rvalue_locals value @ read, given, [])
  | Call { destination; call } ->
      let read, given = Option.fold ~none:([], []) ~some:list_written destination in
      (list_call_locals call @ read, given, [])
  | Lend { part; call } -> (list_call_locals call, [ part ], [])
  | Slice { destination; base; call; _ } ->
      let read, given = list_written destination in
      (list_call_locals call @ list_place_locals base @ read, given, [])
  | Template { destination; call; _ } ->
      let read, given = list_written destination in
      (list_call_locals call @ read, given, [])
  | Live locals -> ([], locals, [])
  | Dead locals -> ([], [], locals)
  | Assert value | Echo value -> (list_operand_locals value, [], [])
  | Provide { provided; _ } ->
      ( List.concat_map
          (fun (provided : Mir.provided) -> list_operand_locals provided.value)
          provided,
        [],
        [] )
  | Loan_start { borrowed; _ } -> (list_operand_locals borrowed, [], [])
  | Provide_end | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ -> ([], [], [])

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

let validate definition (body : Mir.Graph.body) =
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
    let made =
      Array.fold_left
        (fun found (basic : Mir.Graph.basic_block) ->
          List.fold_left
            (fun found (statement : Mir.Graph.statement) ->
              match (found, statement.kind) with
              | None, Assign { target = { root = Local l; projections = [] }; value; _ }
                when l = local ->
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
                    | To_any _ -> "to_any"
                    | Copy _ -> "copy"
                    | Function_value _ -> "function"
                    | Lambda _ -> "lambda"
                    | Value_parameter _ -> "value_parameter"
                    | Specification _ -> "specification")
              | None, Call { destination = Some { root = Local l; projections = [] }; _ }
                when l = local ->
                  Some "call"
              | None, Lend { part; _ } when part = local -> Some "lend"
              | _ -> found)
            found basic.statements)
        None body.blocks
    in
    kind ^ " " ^ Option.value made ~default:"unassigned"
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
            match statement.kind with Loan_start { loan; _ } -> max most (loan + 1) | _ -> most)
          most basic.statements)
      0 body.blocks
  in
  let bindings = Array.make locals 0 in
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      List.iter
        (fun (statement : Mir.Graph.statement) ->
          match statement.kind with
          | Assign
              { target = { root = Local bound; projections = [] }; value = Operand (Borrow _); _ }
            -> (
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
          let read, given, ends = collect_effects statement.kind in
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
      let read_locals, given, ends = collect_effects statement.kind in
      List.iter (read at) read_locals;
      List.iter (fun local -> state.(local) <- alive) given;
      List.iter (fun local -> state.(local) <- ended) ends;
      match statement.kind with
      | Loan_start { loan; _ } -> open_loans.(loan) <- alive
      | Loan_end ended_loans -> List.iter (fun loan -> open_loans.(loan) <- ended) ended_loans
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

let () =
  let packages = Support.setup [] in
  let parts = lazy (make_mir_parts packages) in
  let built = ref 0 in
  List.iter
    (fun ((file : Path.file), _) ->
      Harness.test
        (Printf.sprintf "%s's MIR keeps the builder's promises" (Path.show_file file))
        (fun () ->
          List.iter
            (fun (declaration : Resolve.Names.declaration) ->
              let key = declaration.key in
              let definition = Resolve.Names.show_key key in
              match
                try find_graph (Lazy.force parts) key
                with Compiler_bug.Bug bug ->
                  Harness.fail "%s: %s" definition bug.message;
                  None
              with
              | Some mir ->
                  incr built;
                  validate definition mir.body;
                  Array.iter (validate definition) mir.lambdas
              | None -> ())
            ((Support.make_names packages).list_declarations_in file)))
    Standard_library.files;
  Harness.test "the standard library has MIR" (fun () ->
      if !built < 500 then Harness.fail "only %d of its definitions have MIR" !built)

let lower_tree_and_graph text =
  let packages = Support.setup [ ("app::main", text) ] in
  match
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = declaration.key in
        if key.path = Path.Top { module_ = Support.parse_module "app::main"; name = "g" } then
          Some key
        else None)
      (Support.list_declarations packages (Support.parse_module "app::main"))
  with
  | Some key -> (
      let parts = make_mir_parts packages in
      match (find_code parts key, find_graph parts key) with
      | Some built, Some graph ->
          validate "g" graph.body;
          Array.iter (validate "g") graph.lambdas;
          (built, graph)
      | _ -> failwith "g has no MIR")
  | None -> failwith "the program has no g"

let lower_graph text = snd (lower_tree_and_graph text)

let locate_named (body : Mir.Graph.body) name =
  let found = ref None in
  Array.iteri
    (fun local (info : Mir.local_info) ->
      match info.kind with
      | Source { local = core; _ } when Mir.find_local_name core = Some name -> found := Some local
      | _ -> ())
    body.locals;
  match !found with Some local -> local | None -> failwith ("no local is named " ^ name)

let compute_reachable (body : Mir.Graph.body) ~from =
  let seen = Array.make (Array.length body.blocks) false in
  let rec visit block =
    if not seen.(block) then begin
      seen.(block) <- true;
      List.iter visit (Mir.Graph.For_testing.list_successors body.blocks.(block).terminator)
    end
  in
  List.iter visit from;
  seen

let list_statements (body : Mir.Graph.body) =
  List.concat_map
    (fun (basic : Mir.Graph.basic_block) -> basic.statements)
    (Array.to_list body.blocks)

let list_terminators (body : Mir.Graph.body) =
  List.mapi
    (fun index (basic : Mir.Graph.basic_block) -> (index, basic.terminator))
    (Array.to_list body.blocks)

let () =
  Harness.test "an assignment evaluates its value, then its target" (fun () ->
      let mir = lower_graph Fixtures.Mir.indexed_assignments_with_calls_on_both_sides in
      let order =
        List.filter_map
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Call
                {
                  call =
                    {
                      callee = { target = Function { path = Top { name = "step"; _ }; _ }; _ };
                      arguments = [ _; Passed { value = Immediate { value = Integer next; _ }; _ } ];
                      _;
                    };
                  _;
                } ->
                Some (Z.to_int next)
            | _ -> None)
          (list_statements mir.body)
      in
      if order <> [ 2; 1; 4; 3 ] then
        Harness.fail "the calls run in the order %s"
          (String.concat ", " (List.map string_of_int order)));
  Harness.test
    "a short-circuit operator evaluates its right operand only where the left does not decide"
    (fun () ->
      let mir = lower_graph Fixtures.Mir.short_circuit_and in
      let body = mir.body in
      let a = locate_named body "a" and b = locate_named body "b" in
      let negates (basic : Mir.Graph.basic_block) =
        List.exists
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Assign { value = Not value; _ } -> List.mem b (list_operand_locals value)
            | _ -> false)
          basic.statements
      in
      match
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.Graph.terminator) with
            | Branch { condition; yes; no; _ } when List.mem a (list_operand_locals condition) ->
                Some (yes, no)
            | _ -> None)
          (list_terminators body)
      with
      | None -> Harness.fail "nothing branches on a"
      | Some (yes, no) ->
          let from_yes = compute_reachable body ~from:[ yes ]
          and from_no = compute_reachable body ~from:[ no ] in
          Array.iteri
            (fun index basic ->
              if negates basic && (from_no.(index) || not from_yes.(index)) then
                Harness.fail "block %d evaluates !b on a path where a is false" index)
            body.blocks);
  Harness.test "a range loop binds a copy of its counter, and a continue ends the iteration"
    (fun () ->
      let mir = lower_graph Fixtures.Mir.range_loop_with_a_continue in
      let body = mir.body in
      let i = locate_named body "i" in
      match
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.Graph.terminator) with
            | For { iteration = Range { inclusive; _ }; part; blocks; _ } ->
                Some (inclusive, part, blocks)
            | _ -> None)
          (list_terminators body)
      with
      | None -> Harness.fail "no range loop"
      | Some (inclusive, part, blocks) ->
          if not inclusive then Harness.fail "the range is not inclusive";
          if body.locals.(i).kind = Temporary || i = part then
            Harness.fail "i is the loop's counter";
          let ends =
            List.filter
              (fun block ->
                match body.blocks.(block).terminator with Iteration_end _ -> true | _ -> false)
              blocks
          in
          if List.length ends < 2 then Harness.fail "the continue does not end the iteration");
  Harness.test "a loop over a collection runs its body for each element, and a break exits it"
    (fun () ->
      let mir = lower_graph Fixtures.Mir.for_loop_with_a_break in
      let body = mir.body in
      match
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.Graph.terminator) with
            | For { iteration = Range _; lent = Some _; blocks; after; _ } -> Some (blocks, after)
            | _ -> None)
          (list_terminators body)
      with
      | None -> Harness.fail "no loop over a collection's positions that lends each element"
      | Some (blocks, after) ->
          if
            not
              (List.exists
                 (fun block ->
                   Mir.Graph.find_iteration_loop body.blocks.(block).terminator = None
                   && List.mem after
                        (Mir.Graph.For_testing.list_successors body.blocks.(block).terminator))
                 blocks)
          then Harness.fail "the break does not leave the loop");
  let check_slice_base_ends body name compare =
    let all = list_statements body in
    let rec read_base_root (local : Mir.local) =
      match
        List.find_map
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Assign
                {
                  target = { root = Local target; projections = [] };
                  value = Operand (Borrow { place = { root = Local borrowed; _ }; _ });
                  _;
                }
              when target = local && body.locals.(local).kind <> Temporary ->
                Some borrowed
            | _ -> None)
          all
      with
      | Some borrowed -> read_base_root borrowed
      | None -> local
    in
    let find_end local =
      List.find_index
        (fun (statement : Mir.Graph.statement) ->
          match statement.kind with Dead locals -> List.mem local locals | _ -> false)
        all
    in
    match
      List.find_map
        (fun (statement : Mir.Graph.statement) ->
          match statement.kind with
          | Slice { base = { root = Local base; _ }; _ } -> Some (read_base_root base)
          | _ -> None)
        all
    with
    | None -> Harness.fail "no slice"
    | Some base -> (
        if body.locals.(base).kind <> Temporary then
          Harness.fail "the slice's base is not a temporary";
        match (find_end base, find_end (locate_named body name)) with
        | Some base_end, Some named_end -> compare base_end named_end
        | _ -> Harness.fail "the base or %s is never ended" name)
  in
  Harness.test "a let keeps the temporary that the slice it binds views until its bindings end"
    (fun () ->
      let mir = lower_graph Fixtures.Mir.let_of_a_slice_of_a_temporary in
      check_slice_base_ends mir.body "middle" (fun base_end middle_end ->
          if base_end < middle_end then Harness.fail "the slice's base ends before middle"));
  Harness.test "a let ends a temporary that its bindings do not view with its statement" (fun () ->
      let mir = lower_graph Fixtures.Mir.let_of_a_temporary_slices_length in
      check_slice_base_ends mir.body "count" (fun base_end count_end ->
          if base_end > count_end then Harness.fail "the slice's base outlives its statement"));
  Harness.test "a let with an else binds its pattern only where it matches" (fun () ->
      let mir = lower_graph Fixtures.Mir.let_else_on_an_option in
      let body = mir.body in
      let x = locate_named body "x" in
      let binds (basic : Mir.Graph.basic_block) =
        List.exists
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with Live locals -> List.mem x locals | _ -> false)
          basic.statements
      in
      let returns_one = function
        | Mir.Graph.Return (Some (Immediate { value = Integer one; _ })) -> Z.equal one Z.one
        | _ -> false
      in
      match
        List.find_opt (fun (_, terminator) -> returns_one terminator) (list_terminators body)
      with
      | None -> Harness.fail "the else does not return 1"
      | Some (else_return, _) ->
          let from_entry = compute_reachable body ~from:[ 0 ] in
          Array.iteri
            (fun index basic ->
              if
                from_entry.(index) && binds basic
                && (compute_reachable body ~from:[ index ]).(else_return)
              then Harness.fail "block %d binds x on the way to the else" index)
            body.blocks;
          if not (Array.exists binds body.blocks) then Harness.fail "x is never bound");
  Harness.test "a match guard that fails ends its arm's bindings before the next arm's test"
    (fun () ->
      let mir = lower_graph Fixtures.Mir.match_with_a_guarded_arm in
      let body = mir.body in
      let x = locate_named body "x" in
      let holding_x =
        x
        :: List.filter_map
             (fun (statement : Mir.Graph.statement) ->
               match statement.kind with
               | Assign
                   { target = { root = Local held; projections = [] }; value = Operand value; _ }
                 when list_operand_locals value = [ x ] ->
                   Some held
               | _ -> None)
             (list_statements body)
      in
      let guard =
        List.find_map
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Assign
                {
                  target = { root = Local result; projections = [] };
                  value = Compare { left; _ };
                  _;
                }
              when List.exists (fun local -> List.mem local holding_x) (list_operand_locals left) ->
                Some result
            | _ -> None)
          (list_statements body)
      in
      let guard_values =
        match guard with
        | Some guard ->
            guard
            :: List.filter_map
                 (fun (statement : Mir.Graph.statement) ->
                   match statement.kind with
                   | Assign
                       {
                         target = { root = Local held; projections = [] };
                         value = Operand value;
                         _;
                       }
                     when list_operand_locals value = [ guard ] ->
                       Some held
                   | _ -> None)
                 (list_statements body)
        | None -> []
      in
      let failed =
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.Graph.terminator) with
            | Branch { condition; no; _ }
              when List.exists (fun guard -> list_operand_locals condition = [ guard ]) guard_values
              ->
                Some no
            | _ -> None)
          (list_terminators body)
      in
      match failed with
      | None -> Harness.fail "nothing branches on the guard"
      | Some failed ->
          let rec walk visited block =
            if not (List.mem block visited) then
              let basic = body.blocks.(block) in
              let rec walk_successors = function
                | [] ->
                    List.iter
                      (walk (block :: visited))
                      (Mir.Graph.For_testing.list_successors basic.terminator)
                | (statement : Mir.Graph.statement) :: rest -> (
                    match statement.kind with
                    | Dead locals when List.mem x locals -> ()
                    | Assign { value = Is_variant _; _ } ->
                        Harness.fail "block %d tests the next arm with x bound" block
                    | _ -> walk_successors rest)
              in
              walk_successors basic.statements
          in
          walk [] failed);
  Harness.test "a functional body's one jump is its return, and its graph branches" (fun () ->
      let built, graph = lower_tree_and_graph Fixtures.Mir.if_else_on_two_comparisons in
      let chosen = ref 0 and jumps = ref [] in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Choose _ -> incr chosen
          | Jump jump -> jumps := jump :: !jumps
          | _ -> ())
        built;
      if !chosen = 0 then Harness.fail "the body holds no value that chooses between blocks";
      (match !jumps with
      | [ Return (Some _) ] -> ()
      | jumps -> Harness.fail "the body holds %d jumps" (List.length jumps));
      if
        not
          (Array.exists
             (fun (block : Mir.Graph.basic_block) ->
               match block.terminator with Branch _ -> true | _ -> false)
             graph.body.blocks)
      then Harness.fail "nothing in the graph branches");
  Harness.test "a loop is one statement that holds its body, and a break is a jump in it" (fun () ->
      let built, graph = lower_tree_and_graph Fixtures.Mir.while_loop_with_a_break in
      let loops =
        List.filter_map
          (fun (statement : Mir.statement) ->
            match statement.kind with While { body; _ } -> Some body | _ -> None)
          built.body.code.statements
      in
      (match loops with
      | [ body ] ->
          let breaks (block : Mir.block) =
            block.value = None
            && List.exists
                 (fun (statement : Mir.statement) -> statement.kind = Jump Break)
                 block.statements
          in
          if
            not
              (List.exists
                 (fun (statement : Mir.statement) ->
                   match statement.kind with
                   | Choose { choice = Conditional { then_; else_; _ }; _ } ->
                       breaks then_ && else_.value <> None
                   | _ -> false)
                 body.statements)
          then Harness.fail "the loop's body holds no `if` that a `break` leaves"
      | loops -> Harness.fail "the body's code holds %d loops" (List.length loops));
      if built.body.code.value <> None then
        Harness.fail "control reaches the end of the body's code";
      if
        not
          (List.exists
             (fun (index, terminator) ->
               List.exists
                 (fun target -> target <= index)
                 (Mir.Graph.For_testing.list_successors terminator))
             (list_terminators graph.body))
      then Harness.fail "no block of the graph jumps back");
  Harness.test "a name that the alternatives of a pattern bind to a part says so" (fun () ->
      let mir = lower_graph Fixtures.Mir.mut_match_whose_alternatives_bind_a_part in
      if not mir.body.locals.(locate_named mir.body "value").has_several_bindings then
        Harness.fail "`value`, which two alternatives bind, does not say so";
      if mir.body.locals.(locate_named mir.body "only").has_several_bindings then
        Harness.fail "`only`, which one pattern binds, says that several statements bind it");
  Harness.test "an argument names the function reference or the lambda expression that it is"
    (fun () ->
      let mir, _ = lower_tree_and_graph Fixtures.Mir.function_and_lambda_passed_to_apply in
      let functions = ref [] in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Basic
              (Call { call = { arguments = Passed { function_ = Some function_; _ } :: _; _ }; _ })
            ->
              functions := function_ :: !functions
          | _ -> ())
        mir;
      match List.rev !functions with
      | [
       Function_reference { path = Top { name = "double"; _ }; _ }; Lambda_expression { body; _ };
      ] ->
          if not mir.lambdas.(body).is_functional then
            Harness.fail "the lambda's body is not functional"
      | _ -> Harness.fail "the calls of `apply` do not name `double` and the lambda");
  Harness.test "a lambda's captures and parameters are locals of its body" (fun () ->
      let mir = lower_graph Fixtures.Mir.lambda_capturing_an_offset in
      match mir.lambdas with
      | [| lambda |] ->
          if lambda.parameters <> [ locate_named lambda "value" ] then
            Harness.fail "the lambda's parameter is not value";
          if lambda.captures <> [ locate_named lambda "offset" ] then
            Harness.fail "the lambda does not capture offset";
          let offset = locate_named mir.body "offset" in
          if
            not
              (List.exists
                 (fun (statement : Mir.Graph.statement) ->
                   match statement.kind with
                   | Assign { value = Lambda { captures = [ capture ]; _ }; _ } ->
                       list_place_locals capture.place = [ offset ]
                   | _ -> false)
                 (list_statements mir.body))
          then Harness.fail "the lambda value does not capture g's offset"
      | lambdas -> Harness.fail "%d lambdas" (Array.length lambdas));
  Harness.test
    "a parameter ends at its body's return, with no `Dead`, in a function and in a lambda, and the \
     bindings of a destructured parameter end with the lambda's scope" (fun () ->
      let is_ended (body : Mir.Graph.body) local =
        List.exists
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with Dead locals -> List.mem local locals | _ -> false)
          (list_statements body)
      in
      let mir = lower_graph Fixtures.Mir.lambda_with_a_destructured_and_a_plain_parameter in
      match mir.lambdas with
      | [| lambda |] ->
          if is_ended mir.body (locate_named mir.body "offset") then
            Harness.fail "a `Dead` ends g's parameter offset";
          List.iter
            (fun parameter ->
              if is_ended lambda parameter then Harness.fail "a `Dead` ends a lambda's parameter")
            lambda.parameters;
          if not (is_ended lambda (locate_named lambda "left")) then
            Harness.fail "no `Dead` ends the binding left"
      | lambdas -> Harness.fail "%d lambdas" (Array.length lambdas));
  Harness.test "a method an impl inherits shares its trait's default method's MIR" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Mir.impls_inheriting_a_default_method) ]
      in
      let module_ = Support.parse_module "app::main" in
      let make_method_path owner name : Path.t = Method { owner; name; receiver = Read } in
      let make_impl_path type_name : Path.t =
        Impl
          {
            module_;
            trait = { path = Top { module_; name = "Shape" }; arguments = []; associated = [] };
            for_type = Top { module_; name = type_name };
          }
      in
      let parts = make_mir_parts packages in
      let read_form path =
        match Mir.read_graph parts path with
        | Some { form; _ } -> form
        | None -> failwith (Path.show path ^ " has no MIR")
      in
      let default_method = make_method_path (Top { module_; name = "Shape" }) "doubled" in
      let default_mir =
        match
          Option.bind ((Support.make_names packages).find_key default_method) (find_graph parts)
        with
        | Some mir -> mir
        | None -> failwith "the default method has no MIR"
      in
      List.iter
        (fun type_name ->
          if read_form (make_method_path (make_impl_path type_name) "doubled") != default_mir then
            Harness.fail "`%s` has a MIR of its own for the method it inherits" type_name)
        [ "Square"; "Cube" ];
      if read_form default_method != default_mir then
        Harness.fail "the default method's MIR by its path is not its definition's";
      if
        read_form (make_method_path (make_impl_path "Square") "side")
        == read_form (make_method_path (make_impl_path "Cube") "side")
      then Harness.fail "two written methods share one MIR");
  Harness.test "defaults have bodies of their own, apart from the MIR of any function's body"
    (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Mir.defaults_of_a_capability_a_type_and_a_method) ]
      in
      let module_ = Support.parse_module "app::main" in
      let make_top_path name : Path.t = Top { module_; name } in
      let parts = make_mir_parts packages in
      let read_defaults path =
        match Mir.read_default_graphs parts path with
        | Some { form; _ } -> form
        | None -> failwith (Path.show path ^ " has no defaults")
      in
      let find_returned (default : Mir.Graph.t) =
        validate "a default" default.body;
        List.find_map
          (fun (_, (terminator : Mir.Graph.terminator)) ->
            match terminator with
            | Return (Some (Immediate { value = Integer value; _ })) -> Some (Z.to_int value)
            | _ -> None)
          (list_terminators default.body)
      in
      let list_positions = function
        | Mir.Parameter_defaults defaults ->
            List.map (fun (position, default) -> (position, find_returned default)) defaults
        | Field_defaults _ -> failwith "a function with field defaults"
      in
      let add : Path.t =
        Method { owner = make_top_path "Tally"; name = "add"; receiver = Static }
      in
      if Mir.read_code parts add <> None then Harness.fail "`Tally.add` has a body's MIR";
      if list_positions (read_defaults add) <> [ (0, Some 5) ] then
        Harness.fail "`Tally.add` does not have its default at position 0";
      let advance : Path.t =
        Method { owner = make_top_path "Counter"; name = "advance"; receiver = Mut }
      in
      if list_positions (read_defaults advance) <> [ (1, Some 3) ] then
        Harness.fail "`Counter.advance` does not have its default at position 1";
      match read_defaults (make_top_path "Counter") with
      | Field_defaults [ { variant = None; field = "step"; value; _ } ] ->
          if find_returned value <> Some 2 then Harness.fail "the default of `step` is not 2"
      | Field_defaults defaults ->
          Harness.fail "`Counter` has %d field defaults" (List.length defaults)
      | Parameter_defaults _ -> Harness.fail "a type with parameter defaults");
  Harness.test "a contract's clauses are formulas that take the function's parameters" (fun () ->
      let packages =
        Support.setup
          [ ("app::main", Fixtures.Mir.contract_with_quantified_and_conditional_clauses) ]
      in
      let g : Path.t = Top { module_ = Support.parse_module "app::main"; name = "g" } in
      let list_parameters (clause : Mir.formula) =
        List.map
          (fun parameter ->
            match clause.locals.(parameter).kind with
            | Source { local; _ } -> Mir.find_local_name local
            | Temporary | Lent _ -> None)
          clause.parameters
      in
      let list_specifications (clause : Mir.formula) =
        let found = ref [] in
        Mir.iter_formula
          (fun (statement : Mir.statement) ->
            match statement.kind with
            | Basic (Assign { value = Specification specification; _ }) ->
                found := specification :: !found
            | _ -> ())
          clause;
        List.rev !found
      in
      let list_choices (clause : Mir.formula) =
        let found = ref [] in
        Mir.iter_formula
          (fun (statement : Mir.statement) ->
            match statement.kind with Choose { choice; _ } -> found := choice :: !found | _ -> ())
          clause;
        List.rev !found
      in
      let computes_a_comparison (block : Mir.block) =
        List.exists
          (fun (statement : Mir.statement) ->
            match statement.kind with Basic (Assign { value = Compare _; _ }) -> true | _ -> false)
          block.statements
      in
      match Mir.read_contract (make_mir_parts packages) g with
      | Some
          { form = { requires = [ quantified; connected; chosen ]; ensures = [ ensured ]; _ }; _ }
        -> (
          List.iter
            (fun clause ->
              if list_parameters clause <> [ Some "count"; Some "items" ] then
                Harness.fail "a clause does not take `count` and `items`")
            [ quantified.clause; connected.clause; chosen.clause; ensured ];
          if quantified.is_executable then Harness.fail "the quantified clause can run";
          if connected.is_executable then
            validate "a clause that runs" (Mir.expand_formula connected.clause).body
          else Harness.fail "the clause of comparisons cannot run";
          (match list_specifications ensured with
          | [ Result; Entry count ] | [ Entry count; Result ] ->
              if not (List.mem count ensured.parameters) then
                Harness.fail "`old` reads no parameter"
          | values ->
              Harness.fail "the `ensures` holds %d specification values" (List.length values));
          (match list_choices connected.clause with
          | [ Connective { connective = And; right; _ } ] ->
              if not (computes_a_comparison right) then
                Harness.fail "the right operand of `&&` is not computed in its block"
          | values -> Harness.fail "the clause of comparisons holds %d values" (List.length values));
          (match list_choices chosen.clause with
          | [ Conditional { then_; else_; if_condition = Some _; _ } ] ->
              if not (computes_a_comparison then_ && computes_a_comparison else_) then
                Harness.fail "a case of the `if` is not computed in its block"
          | values -> Harness.fail "the clause with an `if` holds %d values" (List.length values));
          if quantified.clause.lambdas <> [||] then
            Harness.fail "the quantifier's body is a body of its own";
          match list_specifications quantified.clause with
          | [ Quantified { quantifier = Forall; range = Over_range _; parameter; body; _ } ] ->
              if quantified.clause.locals.(parameter).kind <> Temporary then
                Harness.fail "the quantifier's index is no temporary of the clause";
              if not (computes_a_comparison body) then
                Harness.fail "the quantifier's body is not computed in its block"
          | values -> Harness.fail "the quantified clause holds %d values" (List.length values))
      | Some { form = contract; _ } ->
          Harness.fail "%d `requires` and %d `ensures`" (List.length contract.requires)
            (List.length contract.ensures)
      | None -> Harness.fail "`g` has no contract");
  Harness.test "a clause that quantifies over a range and can run holds the quantifier as a loop"
    (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Mir.contract_with_a_quantified_clause_that_runs) ]
      in
      let f : Path.t = Top { module_ = Support.parse_module "app::main"; name = "f" } in
      match Mir.read_contract (make_mir_parts packages) f with
      | Some { form = { requires = [ quantified ]; _ }; _ } ->
          if not quantified.is_executable then Harness.fail "the quantified clause cannot run";
          let loops = ref 0 in
          Mir.iter_formula
            (fun (statement : Mir.statement) ->
              match statement.kind with
              | For { loop = { quantified = Some _; _ }; _ } -> incr loops
              | _ -> ())
            quantified.clause;
          if !loops <> 1 then Harness.fail "the clause holds %d quantifier loops" !loops
      | Some { form = contract; _ } -> Harness.fail "%d `requires`" (List.length contract.requires)
      | None -> Harness.fail "`f` has no contract");
  Harness.test "a loop holds its clauses as formulas, and a `proof` block's statement its body"
    (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Mir.while_loop_with_an_invariant_and_a_proof_block) ]
      in
      let module_ = Support.parse_module "app::main" in
      let g : Path.t = Top { module_; name = "g" } in
      let key =
        match (Support.make_names packages).find_key g with
        | Some key -> key
        | None -> failwith "the program has no g"
      in
      let mir =
        match find_code (make_mir_parts packages) key with
        | Some mir -> mir
        | None -> failwith "g has no MIR"
      in
      let loops = ref [] and proofs = ref [] in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | While { loop; compared; _ } -> loops := (loop, compared) :: !loops
          | Basic (Proof body) -> proofs := body :: !proofs
          | _ -> ())
        mir;
      (match !loops with
      | [ ({ clauses = [ Invariant invariant ]; _ }, compared) ] -> (
          if List.length invariant.parameters <> 2 then
            Harness.fail "the invariant's formula takes %d locals"
              (List.length invariant.parameters);
          match compared with
          | Some { comparison = Less; _ } -> ()
          | Some _ -> Harness.fail "the loop's condition is another comparison"
          | None -> Harness.fail "the loop's condition is no comparison")
      | loops -> Harness.fail "%d `while` loops with one invariant" (List.length loops));
      match !proofs with
      | [ proof ] -> validate "the proof block" (Mir.For_testing.expand proof).body
      | proofs -> Harness.fail "%d proof blocks" (List.length proofs));
  Harness.test "an early exit from concurrent code ends the tasks it leaves" (fun () ->
      let mir = lower_graph Fixtures.Mir.early_return_from_a_concurrent_loop in
      let blocks = mir.body.blocks in
      let resume winner number =
        Array.to_list blocks
        |> List.find_map (fun (basic : Mir.Graph.basic_block) ->
            match basic.terminator with
            | Resume { winner = resumed; exits; _ } when resumed = winner ->
                Some (List.nth exits (number - 1)).resume
            | _ -> None)
      in
      let rec follow_winner winner number =
        match resume winner number with
        | None -> "lost"
        | Some block -> (
            match blocks.(block).terminator with
            | Cancel { winner; number; _ } -> follow_winner winner number
            | Return _ -> "return"
            | Goto _ -> "jump"
            | Iteration_end _ -> "next"
            | _ -> "other")
      in
      let exits =
        List.filter_map
          (fun (_, terminator) ->
            match (terminator : Mir.Graph.terminator) with
            | Cancel { task; winner; number; _ } ->
                Some
                  ( (match task with Branch _ -> "branch" | Iteration _ -> "iteration"),
                    follow_winner winner number )
            | _ -> None)
          (list_terminators mir.body)
      in
      List.iter
        (fun expected ->
          if not (List.mem expected exits) then
            Harness.fail "no exit from a %s that is a %s" (fst expected) (snd expected))
        [ ("branch", "return"); ("branch", "jump"); ("iteration", "return"); ("iteration", "jump") ];
      Array.iter
        (fun (basic : Mir.Graph.basic_block) ->
          match basic.terminator with
          | Resume { winner; _ } ->
              if
                not
                  (List.exists
                     (fun (statement : Mir.Graph.statement) ->
                       match statement.kind with
                       | Assign { target = { root = Local local; projections = [] }; _ } ->
                           local = winner
                       | _ -> false)
                     (list_statements mir.body))
              then Harness.fail "the winner _%d of a group is never given a value" winner
          | _ -> ())
        blocks)

let analyse_moves text =
  let mir = lower_graph text in
  let body = mir.body in
  let needs_drop (path : Moves.path) =
    path.projections <> []
    ||
    match body.locals.(path.local).type_ with
    | Named { path = Path.Top { name = "Int64" | "Bool" | "UInt64"; _ }; _ } -> false
    | Named { path = Path.Top { module_; _ }; _ } -> not (List.mem "intrinsic" module_.modules)
    | _ -> true
  in
  (body, Moves.analyse ~tracks:needs_drop body)

let find_status_where_ended (body : Mir.Graph.body) moves (path : Moves.path) =
  let found = ref None in
  Array.iteri
    (fun block (basic : Mir.Graph.basic_block) ->
      if !found = None then begin
        let state = Moves.copy_entry_state moves block in
        List.iter
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Dead locals when !found = None && List.mem path.local locals ->
                found := Some (Moves.find_status moves state path)
            | _ -> if !found = None then Moves.apply moves state statement)
          basic.statements
      end)
    body.blocks;
  match !found with Some status -> status | None -> failwith "the local is never ended"

let show_status : Moves.status option -> string = function
  | Some Holds -> "holds"
  | Some Empty -> "empty"
  | Some Maybe -> "maybe"
  | None -> "untracked"

let moves_program =
  {|type Pair(first: String, second: String)

fn text() -> String {
  "text"
}

fn take(value: own String) {
}

fn pair() -> Pair {
  Pair(first: text(), second: text())
}
|}

let () =
  Harness.test "a value moved out on every path holds nothing where its local ends" (fun () ->
      let body, moves =
        analyse_moves (moves_program ^ "fn g() {\n  let kept = text()\n  take(own kept)\n}\n")
      in
      Harness.expect_string ~expected:"empty"
        (show_status
           (find_status_where_ended body moves
              { local = locate_named body "kept"; projections = [] })));
  Harness.test "a value moved out on one path may hold a value where its local ends, under a flag"
    (fun () ->
      let body, moves =
        analyse_moves
          (moves_program
         ^ "fn g(moved: Bool) {\n  let kept = text()\n  if moved {\n    take(own kept)\n  }\n}\n")
      in
      let path : Moves.path = { local = locate_named body "kept"; projections = [] } in
      Harness.expect_string ~expected:"maybe"
        (show_status (find_status_where_ended body moves path));
      if not (List.mem path (Moves.list_flagged moves)) then Harness.fail "the local has no flag");
  Harness.test "a record a field of which was moved out still holds its other fields" (fun () ->
      let body, moves =
        analyse_moves (moves_program ^ "fn g() {\n  let both = pair()\n  take(own both.first)\n}\n")
      in
      let both = locate_named body "both" in
      Harness.expect_string ~expected:"holds"
        (show_status (find_status_where_ended body moves { local = both; projections = [] }));
      Harness.expect_string ~expected:"empty"
        (show_status
           (find_status_where_ended body moves { local = both; projections = [ Field "first" ] })));
  Harness.test "a field given a value again holds one" (fun () ->
      let body, moves =
        analyse_moves
          (moves_program
         ^ "fn g() {\n  var both = pair()\n  take(own both.first)\n  both.first = text()\n}\n")
      in
      Harness.expect_string ~expected:"holds"
        (show_status
           (find_status_where_ended body moves
              { local = locate_named body "both"; projections = [ Field "first" ] })))

let make_call_edge_lookups text : Mir.Call_edges.lookups =
  let database = Support.make_database (Support.setup [ ("app::main", text) ]) in
  let file = Support.parse_file "app::main" in
  (match Support.list_codes (Support.list_fragment_diagnostics database file) with
  | [] -> ()
  | codes -> Harness.fail "the program has diagnostics: %s" (String.concat ", " codes));
  {
    interface = Database.make_interface_lookups database;
    mir = Database.For_testing.make_mir_lookups database;
  }

let make_derived_impl type_name trait : Path.t =
  Derived
    { type_ = Support.make_top_path "app::main" type_name; trait = Well_known.make_path trait }

let expect_paths ~expected paths =
  let actual = List.sort compare (List.map Path.show paths) in
  if actual <> List.sort compare expected then
    Harness.fail "the paths are [%s], not [%s]" (String.concat "; " actual)
      (String.concat "; " expected)

let () =
  let lookups =
    lazy (make_call_edge_lookups Fixtures.Mir.types_deriving_over_written_and_derived_fields)
  in
  let expect_edges path ~expected =
    expect_paths ~expected (Mir.Call_edges.list_path_edges (Lazy.force lookups) path)
  in
  let equal_of type_name : Path.t =
    Method { owner = make_derived_impl type_name Equal; name = "equal"; receiver = Read }
  and default_of type_name : Path.t =
    Method { owner = make_derived_impl type_name Default; name = "default"; receiver = Static }
  in
  let meters_equal = "app::main::impl standard::core::Equal for app::main::Meters.equal" in
  Harness.test "a derived method of a record calls the method of each field's impl" (fun () ->
      expect_edges (equal_of "Span") ~expected:[ meters_equal ]);
  Harness.test "a derived method of a sum type calls the methods of every variant's fields"
    (fun () ->
      expect_edges (equal_of "Shape") ~expected:[ meters_equal ];
      expect_edges
        (Method { owner = make_derived_impl "Shape" Hash; name = "hash"; receiver = Read })
        ~expected:
          [
            "app::main::impl standard::core::Hash for app::main::Meters.hash";
            "standard::core::Hasher.write(mut self)";
          ]);
  Harness.test "a derived method of a type that holds itself calls itself" (fun () ->
      expect_edges (equal_of "Tree")
        ~expected:[ "derived standard::core::Equal for app::main::Tree.equal"; meters_equal ]);
  Harness.test
    "a derived method of a type that holds a list of itself calls the list's method and gives it \
     the type's impl" (fun () ->
      expect_edges (equal_of "Forest")
        ~expected:
          [
            "standard::list::impl standard::core::Equal for standard::list::List.equal";
            "derived standard::core::Equal for app::main::Forest.equal";
            "derived standard::core::Equal for app::main::Forest.not_equal";
          ]);
  Harness.test "a derived method has no call edge for a field of a type parameter's type" (fun () ->
      expect_edges (equal_of "Pair") ~expected:[ meters_equal ]);
  Harness.test "a derived method calls the derived method of a field whose type derives the trait"
    (fun () ->
      expect_edges (equal_of "Outer")
        ~expected:[ "derived standard::core::Equal for app::main::Span.equal" ]);
  Harness.test "a derived default calls the default of each field that has no written default"
    (fun () ->
      expect_edges (default_of "Limits") ~expected:[];
      expect_edges (default_of "Config")
        ~expected:[ "derived standard::core::Default for app::main::Limits.default" ]);
  Harness.test "a call resolved to a derived method is a call edge to that method" (fun () ->
      expect_edges
        (Support.make_top_path "app::main" "make")
        ~expected:[ "derived standard::core::Default for app::main::Config.default" ]);
  Harness.test "a trait's method reaches the derived methods of the trait's impls" (fun () ->
      let implementations =
        List.map Path.show
          (Mir.Call_edges.list_implementations (Lazy.force lookups)
             ~calling_package:(Support.parse_module "app::main").package
             (Method { owner = Well_known.make_path Equal; name = "equal"; receiver = Read }))
      in
      List.iter
        (fun expected ->
          if not (List.mem expected implementations) then
            Harness.fail "the implementations lack %s: [%s]" expected
              (String.concat "; " implementations))
        [ meters_equal; "derived standard::core::Equal for app::main::Span.equal" ])

let () =
  let lookups = lazy (make_call_edge_lookups Fixtures.Mir.impls_inheriting_a_provided_method) in
  let list_edges path = Mir.Call_edges.list_path_edges (Lazy.force lookups) path in
  let level = Support.make_top_path "app::main" "Level" in
  let method_of type_name name =
    "app::main::impl app::main::Level for app::main::" ^ type_name ^ "." ^ name
  in
  let find_edge ~ending edges =
    match List.filter (fun edge -> String.ends_with ~suffix:ending (Path.show edge)) edges with
    | [ edge ] -> edge
    | matching -> failwith (Printf.sprintf "%d edges end with %s" (List.length matching) ending)
  in
  let raised_of_shelf () =
    find_edge ~ending:"Shelf.raised" (list_edges (Support.make_top_path "app::main" "raise"))
  in
  Harness.test "a call of a method that an impl inherits is a call edge to the impl's method"
    (fun () ->
      expect_paths
        ~expected:[ method_of "Shelf" "raised" ]
        (list_edges (Support.make_top_path "app::main" "raise")));
  Harness.test "an inherited method calls its own impl's method where its body calls through Self"
    (fun () ->
      expect_paths
        ~expected:[ method_of "Shelf" "height" ]
        (List.filter
           (fun edge -> Path.locate_package edge <> Path.standard_package)
           (list_edges (raised_of_shelf ()))));
  Harness.test "an integer's inherited `max` calls that integer's `compare` and no other type's"
    (fun () ->
      expect_paths
        ~expected:
          [
            "standard::numbers::signed::impl standard::core::Ordered for \
             standard::intrinsic::Int64.compare";
            "derived standard::core::Equal for standard::core::Ordering.equal";
          ]
        (list_edges (find_edge ~ending:"Int64.max(own self)" (list_edges (raised_of_shelf ())))));
  Harness.test "the body of a provided method calls its trait's method where it calls through Self"
    (fun () ->
      expect_paths ~expected:[ "app::main::Level.height" ]
        (List.filter
           (fun edge -> Path.locate_package edge <> Path.standard_package)
           (list_edges (Method { owner = level; name = "raised"; receiver = Read }))));
  Harness.test "a trait's method reaches the method of every impl, written or inherited" (fun () ->
      expect_paths
        ~expected:
          [ method_of "Shelf" "raised"; method_of "Stair" "raised"; method_of "Pot" "raised" ]
        (Mir.Call_edges.list_implementations (Lazy.force lookups)
           ~calling_package:(Support.parse_module "app::main").package
           (Method { owner = level; name = "raised"; receiver = Read })));
  Harness.test "a call of a generic impl's method has edges to the impl of the type argument"
    (fun () ->
      expect_paths
        ~expected:
          [
            method_of "Pot" "height";
            method_of "Stair" "height";
            method_of "Stair" "raised";
            method_of "Stair" "picked";
          ]
        (list_edges (Support.make_top_path "app::main" "measure")));
  Harness.test "a generic function named as a value has edges to the impl of its type argument"
    (fun () ->
      expect_paths
        ~expected:
          [
            "app::main::pick";
            method_of "Stair" "height";
            method_of "Stair" "raised";
            method_of "Stair" "picked";
          ]
        (list_edges (Support.make_top_path "app::main" "name_pick")));
  Harness.test
    "the body of a provided method that gives its receiver to a bound has edges to its trait's \
     methods" (fun () ->
      expect_paths
        ~expected:
          [
            "app::main::pick";
            "app::main::Level.height";
            "app::main::Level.raised";
            "app::main::Level.picked";
          ]
        (list_edges (Method { owner = level; name = "picked"; receiver = Read })));
  Harness.test
    "an inherited method that gives its receiver to a bound has edges to its own impl's methods"
    (fun () ->
      let picked_of_shelf : Path.t =
        match raised_of_shelf () with
        | Method { owner; receiver; _ } -> Method { owner; name = "picked"; receiver }
        | path -> path
      in
      expect_paths
        ~expected:
          [
            "app::main::pick";
            method_of "Shelf" "height";
            method_of "Shelf" "raised";
            method_of "Shelf" "picked";
          ]
        (list_edges picked_of_shelf))

let () =
  let program = Fixtures.Core.slice_match_on_a_constant_and_loop_over_a_ticking_countdown in
  let show_callee (callee : Mir.callee) =
    Printf.sprintf "%s uses %s"
      (match callee.target with
      | Function { path; _ } -> Path.show path
      | Trait_method { trait; name; _ } -> Path.show trait.trait ^ "." ^ name
      | Capability_method _ | Intrinsic _ | Indirect _ -> "another callee")
      (Types.show_capabilities callee.uses)
  in
  let expect_shown ~expected actual =
    if actual <> expected then
      Harness.fail "expected [%s], found [%s]" (String.concat "; " expected)
        (String.concat "; " actual)
  in
  Harness.test
    "a slice's call, the call of a pattern's `equal`, and a pulled `next` carry the capability set \
     of Core's callee" (fun () ->
      let built, _ = lower_tree_and_graph program in
      let carried = ref [] in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Basic (Slice { call; _ }) ->
              carried := ("a slice carries " ^ show_callee call.callee) :: !carried
          | Basic
              (Call
                 {
                   call = { callee = { target = Trait_method { name = "equal"; _ }; _ }; _ } as call;
                   _;
                 }) ->
              carried := ("a pattern carries " ^ show_callee call.callee) :: !carried
          | For { iteration = Pull { next; _ }; _ } ->
              carried := ("a loop carries " ^ show_callee next) :: !carried
          | _ -> ())
        built;
      expect_shown (List.rev !carried)
        ~expected:
          [
            "a loop carries standard::core::Cursor.next uses {Meter}";
            "a slice carries standard::list::List.slice_from uses {}";
            "a pattern carries standard::core::Equal.equal uses {}";
          ]);
  Harness.test "the callee that a statement invokes is found for a call, a slice, and a pull"
    (fun () ->
      let built, _ = lower_tree_and_graph program in
      let invoked = ref [] in
      Mir.iter_code
        (fun statement ->
          Option.iter
            (fun callee -> invoked := show_callee callee :: !invoked)
            (Mir.find_callee statement))
        built;
      expect_shown (List.rev !invoked)
        ~expected:
          [
            "standard::core::Cursor.next uses {Meter}";
            "standard::list::List.slice_from uses {}";
            "standard::core::Equal.equal uses {}";
            "standard::list::Slice.length uses {}";
          ]);
  Harness.test "a loop over a cursor is a call edge to the cursor's `next`" (fun () ->
      expect_paths
        ~expected:
          [ "app::main::impl standard::core::Cursor for app::main::Countdown.next(mut self)" ]
        (List.filter
           (fun (path : Path.t) ->
             match path with Method { name = "next"; _ } -> true | _ -> false)
           (Mir.Call_edges.list_path_edges (make_call_edge_lookups program)
              (Support.make_top_path "app::main" "g"))));
  Harness.test
    "a `provide` whose body uses `Tasks` only through a pulled `next` can use tasks, so it locks \
     what it provides `mut`" (fun () ->
      let built, _ =
        lower_tree_and_graph
          (Fixtures.Infer.tally ^ Fixtures.Capabilities.spawning_cursor
         ^ Fixtures.Mir.provide_of_a_tally_over_a_loop_pulling_from_a_spawning_cursor)
      in
      let provides = ref [] in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Basic (Provide { can_use_tasks; _ }) -> provides := can_use_tasks :: !provides
          | _ -> ())
        built;
      if !provides <> [ true ] then Harness.fail "the `provide` cannot use tasks")

let () =
  let count_edges operator length =
    let chain = String.concat operator (List.init length (fun _ -> "flag")) in
    let graph = lower_graph (Printf.sprintf "fn g(flag: Bool) -> Bool {\n  %s\n}\n" chain) in
    Array.fold_left
      (fun count (block : Mir.Graph.basic_block) ->
        count + List.length (Mir.Graph.For_testing.list_successors block.terminator))
      0 graph.body.blocks
  in
  List.iter
    (fun operator ->
      Harness.test
        (Printf.sprintf "a chain of `%s` has a graph whose edges grow linearly with its length"
           (String.trim operator))
        (fun () ->
          let short = count_edges operator 40 and long = count_edges operator 80 in
          if long > (2 * short) + 8 then
            Harness.fail "40 operands make %d edges, and 80 make %d" short long))
    [ " && "; " || " ]
