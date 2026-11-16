open Harness
open Support

let mir_parts packages package = Database.For_testing.make_mir_lookups (database packages) package
let app_parts packages = mir_parts packages (module_of "app::main").package
let graph_of (parts : Mir.lookups) key = Mir.graph (parts.body_part key)
let code_of (parts : Mir.lookups) key = Mir.code (parts.body_part key)

let place_locals (place : Mir.place) =
  match place.root with Local local -> [ local ] | Constant _ -> []

let operand_locals : Mir.operand -> Mir.local list = function
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> place_locals place
  | Constant _ -> []

let call_locals (call : Mir.call) =
  (match call.callee with Indirect callee -> operand_locals callee | _ -> [])
  @ List.concat_map
      (function Mir.Passed { value; _ } -> operand_locals value | Default -> [])
      call.arguments

let written (place : Mir.place) =
  match place with
  | { root = Local local; projections = [] } -> ([], [ local ])
  | _ -> (place_locals place, [])

let rec rvalue_locals : Mir.rvalue -> Mir.local list = function
  | Operand value | Not value | Convert { value; _ } | To_any { value; _ } | Copy value ->
      operand_locals value
  | Operation { operands; _ } | Array operands -> List.concat_map operand_locals operands
  | Compare { left; right; _ } -> operand_locals left @ operand_locals right
  | Construct { fields; _ } ->
      List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:operand_locals field) fields
  | Is_variant { place; _ } -> place_locals place
  | Lambda { captures; _ } ->
      List.concat_map (fun (capture : Mir.capture) -> place_locals capture.place) captures
  | Function_value _ | Value_parameter _ -> []
  | Specification (Result | Yielded) -> []
  | Specification (Entry local) -> [ local ]
  | Specification (Identical (first, second)) -> operand_locals first @ operand_locals second
  | Specification (Applied { arguments; _ }) -> List.concat_map operand_locals arguments
  | Specification (Method_time callee) -> (
      match callee with Indirect callee -> operand_locals callee | _ -> [])
  | Specification (Map entries) ->
      List.concat_map (fun (key, value) -> operand_locals key @ operand_locals value) entries
  | Specification (Quantified { range; parameter; matches; body; _ }) ->
      (match range with
        | Over_type _ -> []
        | Over_range { start; stop; _ } -> operand_locals start @ operand_locals stop
        | Over_collection collection -> operand_locals collection)
      @ List.filter
          (fun local -> local <> parameter)
          (block_locals { statements = matches.statements @ body.statements; value = body.value })

and choice_locals : Mir.choice -> Mir.local list = function
  | Conditional { condition; then_; else_; _ } ->
      operand_locals condition @ block_locals then_ @ block_locals else_
  | Cases cases ->
      List.concat_map
        (fun (case : Mir.case) ->
          block_locals case.tests
          @ Option.fold ~none:[] ~some:block_locals case.guard
          @ block_locals case.value)
        cases
  | Connective { left; right; _ } -> operand_locals left @ block_locals right

and block_locals (block : Mir.block) =
  let read, given =
    List.fold_left
      (fun (read, given) (statement : Mir.statement) ->
        let reads, gives, _ = tree_effects statement.kind in
        (List.filter (fun local -> not (List.mem local given)) reads @ read, gives @ given))
      ([], []) block.statements
  in
  List.filter
    (fun local -> not (List.mem local given))
    (Option.fold ~none:[] ~some:operand_locals block.value)
  @ read

and tree_effects : Mir.statement_kind -> Mir.local list * Mir.local list * Mir.local list = function
  | Basic basic -> effects basic
  | Choose { target; choice; _ } ->
      let read, given = written target in
      (choice_locals choice @ read, given, [])
  | While _ | For _ | Fork _ | Resume _ | Yield _ | Jump _ ->
      failwith "a statement that holds blocks or jumps, where a formula holds none"

and effects : Mir.basic -> Mir.local list * Mir.local list * Mir.local list = function
  | Assign { target; value; _ } ->
      let read, given = written target in
      (rvalue_locals value @ read, given, [])
  | Call { destination; call } ->
      let read, given = Option.fold ~none:([], []) ~some:written destination in
      (call_locals call @ read, given, [])
  | Lend { part; call } -> (call_locals call, [ part ], [])
  | Slice { destination; base; call } ->
      let read, given = written destination in
      (call_locals call @ place_locals base @ read, given, [])
  | Template { destination; call; _ } ->
      let read, given = written destination in
      (call_locals call @ read, given, [])
  | Live locals -> ([], locals, [])
  | Dead locals -> ([], [], locals)
  | Assert { condition = value; _ } | Echo value -> (operand_locals value, [], [])
  | Provide { provided; _ } ->
      ( List.concat_map (fun (provided : Mir.provided) -> operand_locals provided.value) provided,
        [],
        [] )
  | Loan_start { borrowed; _ } -> (operand_locals borrowed, [], [])
  | Provide_end | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ -> ([], [], [])

let rec yielded_locals : Mir.yielded -> Mir.local list = function
  | Part value -> operand_locals value
  | Built { fields; _ } ->
      List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:yielded_locals field) fields

let terminator_reads : Mir.Graph.terminator -> Mir.local list = function
  | Branch { condition; _ } -> operand_locals condition
  | For { iteration = Range { start; stop; _ }; _ } -> operand_locals start @ operand_locals stop
  | For { iteration = Pull { cursor; _ }; _ } -> place_locals cursor
  | Yield { part; _ } -> yielded_locals part
  | Return (Some value) | Cancel { returned = Some (value, _); _ } -> operand_locals value
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
  let problem format = Printf.ksprintf (fun text -> fail "%s: %s" definition text) format in
  let describe local =
    let kind =
      match body.locals.(local).kind with
      | Source { name; _ } -> "source " ^ Option.value name ~default:"?"
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
  let block index = if index < 0 || index >= count then problem "a jump to block %d" index in
  let local index = if index < 0 || index >= locals then problem "local _%d" index in
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
                  problem "_%d (%s) is bound to a place, and is declared to own its value" bound
                    (describe bound))
          | _ -> ())
        basic.statements)
    body.blocks;
  Array.iteri
    (fun bound count ->
      if count > 1 <> body.locals.(bound).has_several_bindings then
        problem "_%d (%s) is bound to a place by %d statements" bound (describe bound) count)
    bindings;
  Array.iter
    (fun (basic : Mir.Graph.basic_block) ->
      List.iter
        (fun (statement : Mir.Graph.statement) ->
          let read, given, ends = effects statement.kind in
          List.iter local (read @ given @ ends))
        basic.statements;
      List.iter local (terminator_reads basic.terminator);
      List.iter block (Mir.Graph.For_testing.successors basic.terminator);
      match basic.terminator with
      | For { part; body = inside; blocks; after; _ } ->
          local part;
          List.iter block (inside :: after :: blocks)
      | Fork { branches; join; _ } ->
          List.iter
            (fun (branch : Mir.Graph.branch) -> List.iter block (branch.entry :: branch.blocks))
            branches;
          Option.iter block join
      | _ -> ())
    body.blocks;
  let parts = ref [] in
  Array.iteri
    (fun index (basic : Mir.Graph.basic_block) ->
      (match Mir.Graph.iteration_loop basic.terminator with
      | Some loop -> (
          match body.blocks.(loop).terminator with
          | For { blocks; _ } when List.mem index blocks -> ()
          | _ ->
              problem "block %d ends an iteration of %d, which is not a loop around it" index loop)
      | None -> ());
      match basic.terminator with
      | For { part; body = inside; blocks; after; _ } ->
          parts := part :: !parts;
          if not (List.mem inside blocks) then
            problem "a loop's body %d is not among its blocks" inside;
          List.iter
            (fun inner ->
              match body.blocks.(inner).terminator with
              | Cancel _ -> ()
              | terminator ->
                  List.iter
                    (fun target ->
                      if target <> after && not (List.mem target blocks) then
                        problem "block %d of the loop at %d jumps out to %d" inner index target)
                    (Mir.Graph.For_testing.successors terminator))
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
                        problem "branch %d of the block at %d joins to %d" position index target
                  | terminator ->
                      List.iter
                        (fun target ->
                          if not (List.mem target branch.blocks) then
                            problem "branch %d of the block at %d jumps out to %d" position index
                              target)
                        (Mir.Graph.For_testing.successors terminator))
                branch.blocks)
            branches
      | _ -> ())
    body.blocks;
  let held_by_exits =
    Array.fold_left
      (fun held (basic : Mir.Graph.basic_block) ->
        match basic.terminator with
        | Cancel { returned = Some (value, _); _ } -> operand_locals value @ held
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
        problem "block %d reads _%d where a path has ended it" at local
    in
    let apply at (statement : Mir.Graph.statement) =
      let read_locals, given, ends = effects statement.kind in
      List.iter (read at) read_locals;
      List.iter (fun local -> state.(local) <- alive) given;
      List.iter (fun local -> state.(local) <- ended) ends;
      match statement.kind with
      | Loan_start { loan; _ } -> open_loans.(loan) <- alive
      | Loan_end ended_loans -> List.iter (fun loan -> open_loans.(loan) <- ended) ended_loans
      | _ -> ()
    in
    let still_alive ~kept =
      List.filter
        (fun local -> state.(local) land alive <> 0 && not (List.mem local kept))
        (List.init locals Fun.id)
    in
    let still_open ~kept =
      List.filter
        (fun loan -> open_loans.(loan) land alive <> 0 && not (List.mem loan kept))
        (List.init loans Fun.id)
    in
    let returns at value =
      let kept =
        body.parameters @ body.captures @ !parts @ held_by_exits
        @ match value with Some value -> operand_locals value | None -> []
      in
      if report then begin
        (match still_alive ~kept with
        | [] -> ()
        | local :: _ -> problem "block %d returns with _%d alive (%s)" at local (describe local));
        match still_open ~kept:[] with
        | [] -> ()
        | loan :: _ -> problem "block %d returns with loan %d open" at loan
      end
    in
    let iteration_end at =
      match Mir.Graph.iteration_loop body.blocks.(at).terminator with
      | Some loop ->
          (if report then
             match Hashtbl.find_opt entered loop with
             | Some (alive_then, open_then) -> (
                 (match still_alive ~kept:(alive_then @ !parts @ held_by_exits) with
                 | [] -> ()
                 | local :: _ -> problem "block %d ends an iteration with _%d alive" at local);
                 match still_open ~kept:open_then with
                 | [] -> ()
                 | loan :: _ -> problem "block %d ends an iteration with loan %d open" at loan)
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
      List.iter (read node) (terminator_reads basic.terminator);
      match basic.terminator with
      | For _ ->
          if not (Hashtbl.mem entered node) then
            Hashtbl.replace entered node (still_alive ~kept:[], still_open ~kept:[]);
          flow (count + node) (state, open_loans)
      | Iteration_end _ -> iteration_end node
      | Return value -> returns node value
      | Cancel { task = Iteration _; _ } -> iteration_end node
      | terminator ->
          List.iter
            (fun target -> flow target (state, open_loans))
            (Mir.Graph.For_testing.successors terminator)
  in
  while not (Queue.is_empty pending) do
    run ~report:false (Queue.pop pending)
  done;
  Array.iteri (fun node is_reached -> if is_reached then run ~report:true node) reached

let () =
  let packages = setup [] in
  let parts = lazy (mir_parts packages Path.standard_package) in
  let built = ref 0 in
  List.iter
    (fun ((file : Path.file), _) ->
      test
        (Printf.sprintf "%s's MIR keeps the builder's promises" (Path.show_file file))
        (fun () ->
          List.iter
            (fun (declaration : Resolve.Names.declaration) ->
              let key = Resolve.Names.key_of declaration in
              let definition = Resolve.Names.show_key key in
              match
                try graph_of (Lazy.force parts) key
                with Compiler_bug.Bug bug ->
                  fail "%s: %s" definition bug.message;
                  None
              with
              | Some mir ->
                  incr built;
                  validate definition mir.body;
                  Array.iter (validate definition) mir.lambdas
              | None -> ())
            ((Support.names packages file.module_.package).declarations_in file)))
    Standard_library.files;
  test "the standard library has MIR" (fun () ->
      if !built < 500 then fail "only %d of its definitions have MIR" !built)

let both_of_g text =
  let packages = setup [ ("app::main", text) ] in
  match
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        if key.path = Path.Top { module_ = module_of "app::main"; name = "g" } then Some key
        else None)
      (Support.declarations packages (Support.module_of "app::main"))
  with
  | Some key -> (
      let parts = app_parts packages in
      match (code_of parts key, graph_of parts key) with
      | Some built, Some graph ->
          validate "g" graph.body;
          Array.iter (validate "g") graph.lambdas;
          (built, graph)
      | _ -> failwith "g has no MIR")
  | None -> failwith "the program has no g"

let mir_of_g text = snd (both_of_g text)

let named (body : Mir.Graph.body) name =
  let found = ref None in
  Array.iteri
    (fun local (info : Mir.local_info) ->
      match info.kind with
      | Source { name = Some written; _ } when written = name -> found := Some local
      | _ -> ())
    body.locals;
  match !found with Some local -> local | None -> failwith ("no local is named " ^ name)

let reachable (body : Mir.Graph.body) ~from ?(avoid = []) () =
  let seen = Array.make (Array.length body.blocks) false in
  let rec visit block =
    if (not seen.(block)) && not (List.mem block avoid) then begin
      seen.(block) <- true;
      List.iter visit (Mir.Graph.For_testing.successors body.blocks.(block).terminator)
    end
  in
  List.iter visit from;
  seen

let statements (body : Mir.Graph.body) =
  List.concat_map
    (fun (basic : Mir.Graph.basic_block) -> basic.statements)
    (Array.to_list body.blocks)

let terminators (body : Mir.Graph.body) =
  List.mapi
    (fun index (basic : Mir.Graph.basic_block) -> (index, basic.terminator))
    (Array.to_list body.blocks)

let () =
  test "an assignment evaluates its value, then its target" (fun () ->
      let mir = mir_of_g Fixtures.Mir.assignment_evaluates_its_value_then_its_target_and in
      let order =
        List.filter_map
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Call
                {
                  call =
                    {
                      callee = Function { path = Top { name = "step"; _ }; _ };
                      arguments = [ _; Passed { value = Constant { value = Integer next; _ }; _ } ];
                      _;
                    };
                  _;
                } ->
                Some (Z.to_int next)
            | _ -> None)
          (statements mir.body)
      in
      if order <> [ 2; 1; 4; 3 ] then
        fail "the calls run in the order %s" (String.concat ", " (List.map string_of_int order)));
  test "a short-circuit operator evaluates its right operand only where the left does not decide"
    (fun () ->
      let mir = mir_of_g Fixtures.Mir.short_circuit_operator_jumps_past_its_right in
      let body = mir.body in
      let a = named body "a" and b = named body "b" in
      let negates (basic : Mir.Graph.basic_block) =
        List.exists
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Assign { value = Not value; _ } -> List.mem b (operand_locals value)
            | _ -> false)
          basic.statements
      in
      match
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.Graph.terminator) with
            | Branch { condition; yes; no; _ } when List.mem a (operand_locals condition) ->
                Some (yes, no)
            | _ -> None)
          (terminators body)
      with
      | None -> fail "nothing branches on a"
      | Some (yes, no) ->
          let from_yes = reachable body ~from:[ yes ] ()
          and from_no = reachable body ~from:[ no ] () in
          Array.iteri
            (fun index basic ->
              if negates basic && (from_no.(index) || not from_yes.(index)) then
                fail "block %d evaluates !b on a path where a is false" index)
            body.blocks);
  test "a range loop binds a copy of its counter, and a continue ends the iteration" (fun () ->
      let mir = mir_of_g Fixtures.Mir.range_loop_copies_its_counter_steps_it_at_continue in
      let body = mir.body in
      let i = named body "i" in
      match
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.Graph.terminator) with
            | For { iteration = Range { inclusive; _ }; part; blocks; _ } ->
                Some (inclusive, part, blocks)
            | _ -> None)
          (terminators body)
      with
      | None -> fail "no range loop"
      | Some (inclusive, part, blocks) ->
          if not inclusive then fail "the range is not inclusive";
          if body.locals.(i).kind = Temporary || i = part then fail "i is the loop's counter";
          let ends =
            List.filter
              (fun block ->
                match body.blocks.(block).terminator with Iteration_end _ -> true | _ -> false)
              blocks
          in
          if List.length ends < 2 then fail "the continue does not end the iteration");
  test "a loop over a collection runs its body for each element, and a break exits it" (fun () ->
      let mir = mir_of_g Fixtures.Mir.loop_over_a_collection_runs_its_body_for_each in
      let body = mir.body in
      match
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.Graph.terminator) with
            | For { iteration = Range _; lent = Some _; blocks; after; _ } -> Some (blocks, after)
            | _ -> None)
          (terminators body)
      with
      | None -> fail "no loop over a collection's positions that lends each element"
      | Some (blocks, after) ->
          if
            not
              (List.exists
                 (fun block ->
                   Mir.Graph.iteration_loop body.blocks.(block).terminator = None
                   && List.mem after
                        (Mir.Graph.For_testing.successors body.blocks.(block).terminator))
                 blocks)
          then fail "the break does not leave the loop");
  let slice_base_ends body name compare =
    let all = statements body in
    let rec base_root (local : Mir.local) =
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
      | Some borrowed -> base_root borrowed
      | None -> local
    in
    let ended local =
      List.find_index
        (fun (statement : Mir.Graph.statement) ->
          match statement.kind with Dead locals -> List.mem local locals | _ -> false)
        all
    in
    match
      List.find_map
        (fun (statement : Mir.Graph.statement) ->
          match statement.kind with
          | Slice { base = { root = Local base; _ }; _ } -> Some (base_root base)
          | _ -> None)
        all
    with
    | None -> fail "no slice"
    | Some base -> (
        if body.locals.(base).kind <> Temporary then fail "the slice's base is not a temporary";
        match (ended base, ended (named body name)) with
        | Some base_end, Some named_end -> compare base_end named_end
        | _ -> fail "the base or %s is never ended" name)
  in
  test "a let keeps the temporary that the slice it binds views until its bindings end" (fun () ->
      let mir = mir_of_g Fixtures.Mir.let_keeps_the_base_of_a_slice_it_binds in
      slice_base_ends mir.body "middle" (fun base_end middle_end ->
          if base_end < middle_end then fail "the slice's base ends before middle"));
  test "a let ends a temporary that its bindings do not view with its statement" (fun () ->
      let mir = mir_of_g Fixtures.Mir.let_ends_the_base_of_a_slice_it_does_not_bind in
      slice_base_ends mir.body "count" (fun base_end count_end ->
          if base_end > count_end then fail "the slice's base outlives its statement"));
  test "a let with an else binds its pattern only where it matches" (fun () ->
      let mir = mir_of_g Fixtures.Mir.let_with_an_else_tests_its_pattern_and_the_else in
      let body = mir.body in
      let x = named body "x" in
      let binds (basic : Mir.Graph.basic_block) =
        List.exists
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with Live locals -> List.mem x locals | _ -> false)
          basic.statements
      in
      let returns_one = function
        | Mir.Graph.Return (Some (Constant { value = Integer one; _ })) -> Z.equal one Z.one
        | _ -> false
      in
      match List.find_opt (fun (_, terminator) -> returns_one terminator) (terminators body) with
      | None -> fail "the else does not return 1"
      | Some (else_return, _) ->
          let from_entry = reachable body ~from:[ 0 ] () in
          Array.iteri
            (fun index basic ->
              if
                from_entry.(index) && binds basic
                && (reachable body ~from:[ index ] ()).(else_return)
              then fail "block %d binds x on the way to the else" index)
            body.blocks;
          if not (Array.exists binds body.blocks) then fail "x is never bound");
  test "a match guard that fails ends its arm's bindings before the next arm's test" (fun () ->
      let mir = mir_of_g Fixtures.Mir.match_tests_its_arms_in_order_and_a_guard_that in
      let body = mir.body in
      let x = named body "x" in
      let holding_x =
        x
        :: List.filter_map
             (fun (statement : Mir.Graph.statement) ->
               match statement.kind with
               | Assign
                   { target = { root = Local held; projections = [] }; value = Operand value; _ }
                 when operand_locals value = [ x ] ->
                   Some held
               | _ -> None)
             (statements body)
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
              when List.exists (fun local -> List.mem local holding_x) (operand_locals left) ->
                Some result
            | _ -> None)
          (statements body)
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
                     when operand_locals value = [ guard ] ->
                       Some held
                   | _ -> None)
                 (statements body)
        | None -> []
      in
      let failed =
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.Graph.terminator) with
            | Branch { condition; no; _ }
              when List.exists (fun guard -> operand_locals condition = [ guard ]) guard_values ->
                Some no
            | _ -> None)
          (terminators body)
      in
      match failed with
      | None -> fail "nothing branches on the guard"
      | Some failed ->
          let rec walk visited block =
            if not (List.mem block visited) then
              let basic = body.blocks.(block) in
              let rec go = function
                | [] ->
                    List.iter
                      (walk (block :: visited))
                      (Mir.Graph.For_testing.successors basic.terminator)
                | (statement : Mir.Graph.statement) :: rest -> (
                    match statement.kind with
                    | Dead locals when List.mem x locals -> ()
                    | Assign { value = Is_variant _; _ } ->
                        fail "block %d tests the next arm with x bound" block
                    | _ -> go rest)
              in
              go basic.statements
          in
          walk [] failed);
  test "a functional body's one jump is its return, and its graph branches" (fun () ->
      let built, graph = both_of_g Fixtures.Mir.functional_body_is_one_block_of_values in
      let chosen = ref 0 and jumps = ref [] in
      Mir.iter_code
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Choose _ -> incr chosen
          | Jump jump -> jumps := jump :: !jumps
          | _ -> ())
        built;
      if !chosen = 0 then fail "the body holds no value that chooses between blocks";
      (match !jumps with
      | [ Return (Some _) ] -> ()
      | jumps -> fail "the body holds %d jumps" (List.length jumps));
      if
        not
          (Array.exists
             (fun (block : Mir.Graph.basic_block) ->
               match block.terminator with Branch _ -> true | _ -> false)
             graph.body.blocks)
      then fail "nothing in the graph branches");
  test "a loop is one statement that holds its body, and a break is a jump in it" (fun () ->
      let built, graph = both_of_g Fixtures.Mir.loop_is_one_statement_and_a_break_a_jump in
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
          then fail "the loop's body holds no `if` that a `break` leaves"
      | loops -> fail "the body's code holds %d loops" (List.length loops));
      if built.body.code.value <> None then fail "control reaches the end of the body's code";
      if
        not
          (List.exists
             (fun (index, terminator) ->
               List.exists
                 (fun target -> target <= index)
                 (Mir.Graph.For_testing.successors terminator))
             (terminators graph.body))
      then fail "no block of the graph jumps back");
  test "a name that the alternatives of a pattern bind to a part says so" (fun () ->
      let mir = mir_of_g Fixtures.Mir.name_that_alternatives_bind_says_so in
      if not mir.body.locals.(named mir.body "value").has_several_bindings then
        fail "`value`, which two alternatives bind, does not say so";
      if mir.body.locals.(named mir.body "only").has_several_bindings then
        fail "`only`, which one pattern binds, says that several statements bind it");
  test "an argument names the function reference or the lambda expression that it is" (fun () ->
      let mir, _ = both_of_g Fixtures.Mir.argument_names_the_function_written_as_it in
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
          if not mir.lambdas.(body).is_functional then fail "the lambda's body is not functional"
      | _ -> fail "the calls of `apply` do not name `double` and the lambda");
  test "a lambda's captures and parameters are locals of its body" (fun () ->
      let mir = mir_of_g Fixtures.Mir.lambdas_captures_and_parameters_are_its_own_locals in
      match mir.lambdas with
      | [| lambda |] ->
          if lambda.parameters <> [ named lambda "value" ] then
            fail "the lambda's parameter is not value";
          if lambda.captures <> [ named lambda "offset" ] then
            fail "the lambda does not capture offset";
          let offset = named mir.body "offset" in
          if
            not
              (List.exists
                 (fun (statement : Mir.Graph.statement) ->
                   match statement.kind with
                   | Assign { value = Lambda { captures = [ capture ]; _ }; _ } ->
                       place_locals capture.place = [ offset ]
                   | _ -> false)
                 (statements mir.body))
          then fail "the lambda value does not capture g's offset"
      | lambdas -> fail "%d lambdas" (Array.length lambdas));
  test "a method an impl inherits shares its trait's default method's MIR" (fun () ->
      let packages =
        setup [ ("app::main", Fixtures.Mir.method_an_impl_inherits_shares_its_traits_default) ]
      in
      let module_ = module_of "app::main" in
      let method_of owner name : Path.t = Method { owner; name; receiver = Read } in
      let impl_for type_name : Path.t =
        Impl
          {
            module_;
            trait = { path = Top { module_; name = "Shape" }; arguments = []; associated = [] };
            for_type = Top { module_; name = type_name };
          }
      in
      let parts = app_parts packages in
      let by_path path =
        match Mir.graph_of_path parts path with
        | Some mir -> mir
        | None -> failwith (Path.show path ^ " has no MIR")
      in
      let default_method = method_of (Top { module_; name = "Shape" }) "doubled" in
      let default_mir =
        match
          Option.bind
            ((Support.names packages (Path.package default_method)).key default_method)
            (graph_of parts)
        with
        | Some mir -> mir
        | None -> failwith "the default method has no MIR"
      in
      List.iter
        (fun type_name ->
          if by_path (method_of (impl_for type_name) "doubled") != default_mir then
            fail "`%s` has a MIR of its own for the method it inherits" type_name)
        [ "Square"; "Cube" ];
      if by_path default_method != default_mir then
        fail "the default method's MIR by its path is not its definition's";
      if
        by_path (method_of (impl_for "Square") "side")
        == by_path (method_of (impl_for "Cube") "side")
      then fail "two written methods share one MIR");
  test "defaults have bodies of their own, apart from the MIR of any function's body" (fun () ->
      let packages = setup [ ("app::main", Fixtures.Mir.defaults_have_bodies_of_their_own) ] in
      let module_ = module_of "app::main" in
      let top name : Path.t = Top { module_; name } in
      let parts = app_parts packages in
      let defaults_of path =
        match Mir.default_graphs_of_path parts path with
        | Some defaults -> defaults
        | None -> failwith (Path.show path ^ " has no defaults")
      in
      let returned (default : Mir.Graph.t) =
        validate "a default" default.body;
        List.find_map
          (fun (_, (terminator : Mir.Graph.terminator)) ->
            match terminator with
            | Return (Some (Constant { value = Integer value; _ })) -> Some (Z.to_int value)
            | _ -> None)
          (terminators default.body)
      in
      let positions = function
        | Mir.Parameter_defaults defaults ->
            List.map (fun (position, default) -> (position, returned default)) defaults
        | Field_defaults _ -> failwith "a function with field defaults"
      in
      let add : Path.t = Method { owner = top "Tally"; name = "add"; receiver = Static } in
      if Mir.code_of_path parts add <> None then fail "`Tally.add` has a body's MIR";
      if positions (defaults_of add) <> [ (0, Some 5) ] then
        fail "`Tally.add` does not have its default at position 0";
      let advance : Path.t = Method { owner = top "Counter"; name = "advance"; receiver = Mut } in
      if positions (defaults_of advance) <> [ (1, Some 3) ] then
        fail "`Counter.advance` does not have its default at position 1";
      match defaults_of (top "Counter") with
      | Field_defaults [ { variant = None; field = "step"; value; _ } ] ->
          if returned value <> Some 2 then fail "the default of `step` is not 2"
      | Field_defaults defaults -> fail "`Counter` has %d field defaults" (List.length defaults)
      | Parameter_defaults _ -> fail "a type with parameter defaults");
  test "a contract's clauses are formulas that take the function's parameters" (fun () ->
      let packages = setup [ ("app::main", Fixtures.Mir.contracts_clauses_are_formulas) ] in
      let g : Path.t = Top { module_ = module_of "app::main"; name = "g" } in
      let parameters (clause : Mir.formula) =
        List.map
          (fun parameter ->
            match clause.locals.(parameter).kind with
            | Source { name; _ } -> name
            | Temporary | Lent _ -> None)
          clause.parameters
      in
      let specifications (clause : Mir.formula) =
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
      let choosing (clause : Mir.formula) =
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
      match Mir.contract_of_path (app_parts packages) g with
      | Some { requires = [ quantified; connected; chosen ]; ensures = [ ensured ]; _ } -> (
          List.iter
            (fun clause ->
              if parameters clause <> [ Some "count"; Some "items" ] then
                fail "a clause does not take `count` and `items`")
            [ quantified.clause; connected.clause; chosen.clause; ensured ];
          if quantified.is_executable then fail "the quantified clause can run";
          if connected.is_executable then
            validate "a clause that runs" (Mir.code_of_formula connected.clause).body
          else fail "the clause of comparisons cannot run";
          (match specifications ensured with
          | [ Result; Entry count ] | [ Entry count; Result ] ->
              if not (List.mem count ensured.parameters) then fail "`old` reads no parameter"
          | values -> fail "the `ensures` holds %d specification values" (List.length values));
          (match choosing connected.clause with
          | [ Connective { connective = And; right; _ } ] ->
              if not (computes_a_comparison right) then
                fail "the right operand of `&&` is not computed in its block"
          | values -> fail "the clause of comparisons holds %d values" (List.length values));
          (match choosing chosen.clause with
          | [ Conditional { then_; else_; if_condition = Some _; _ } ] ->
              if not (computes_a_comparison then_ && computes_a_comparison else_) then
                fail "a case of the `if` is not computed in its block"
          | values -> fail "the clause with an `if` holds %d values" (List.length values));
          if quantified.clause.lambdas <> [||] then
            fail "the quantifier's body is a body of its own";
          match specifications quantified.clause with
          | [ Quantified { quantifier = Forall; range = Over_range _; parameter; body; _ } ] ->
              if quantified.clause.locals.(parameter).kind <> Temporary then
                fail "the quantifier's index is no temporary of the clause";
              if not (computes_a_comparison body) then
                fail "the quantifier's body is not computed in its block"
          | values -> fail "the quantified clause holds %d values" (List.length values))
      | Some contract ->
          fail "%d `requires` and %d `ensures`" (List.length contract.requires)
            (List.length contract.ensures)
      | None -> fail "`g` has no contract");
  test "a loop holds its clauses as formulas, and a `proof` block's statement its body" (fun () ->
      let packages = setup [ ("app::main", Fixtures.Mir.loop_holds_its_clauses_as_formulas) ] in
      let module_ = module_of "app::main" in
      let g : Path.t = Top { module_; name = "g" } in
      let key =
        match (Support.names packages (Path.package g)).key g with
        | Some key -> key
        | None -> failwith "the program has no g"
      in
      let mir =
        match code_of (app_parts packages) key with
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
            fail "the invariant's formula takes %d locals" (List.length invariant.parameters);
          match compared with
          | Some { comparison = Less; _ } -> ()
          | Some _ -> fail "the loop's condition is another comparison"
          | None -> fail "the loop's condition is no comparison")
      | loops -> fail "%d `while` loops with one invariant" (List.length loops));
      match !proofs with
      | [ proof ] -> validate "the proof block" (Mir.For_testing.expanded proof).body
      | proofs -> fail "%d proof blocks" (List.length proofs));
  test "an early exit from concurrent code ends the tasks it leaves" (fun () ->
      let mir = mir_of_g Fixtures.Mir.early_exit_from_concurrent_code_ends_the_tasks_it_leaves in
      let blocks = mir.body.blocks in
      let resume winner number =
        Array.to_list blocks
        |> List.find_map (fun (basic : Mir.Graph.basic_block) ->
            match basic.terminator with
            | Resume { winner = resumed; exits; _ } when resumed = winner ->
                Some (List.nth exits (number - 1)).resume
            | _ -> None)
      in
      let rec taken winner number =
        match resume winner number with
        | None -> "lost"
        | Some block -> (
            match blocks.(block).terminator with
            | Cancel { winner; number; _ } -> taken winner number
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
                    taken winner number )
            | _ -> None)
          (terminators mir.body)
      in
      List.iter
        (fun expected ->
          if not (List.mem expected exits) then
            fail "no exit from a %s that is a %s" (fst expected) (snd expected))
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
                     (statements mir.body))
              then fail "the winner _%d of a group is never given a value" winner
          | _ -> ())
        blocks)

let moves_of_g text =
  let mir = mir_of_g text in
  let body = mir.body in
  let needs_drop (path : Moves.path) =
    path.steps <> []
    ||
    match body.locals.(path.local).type_ with
    | Named { path = Path.Top { name = "Int64" | "Bool" | "UInt64"; _ }; _ } -> false
    | Named { path = Path.Top { module_; _ }; _ } -> not (List.mem "intrinsic" module_.modules)
    | _ -> true
  in
  (body, Moves.analyse ~tracks:needs_drop body)

let status_where_ended (body : Mir.Graph.body) moves (path : Moves.path) =
  let found = ref None in
  Array.iteri
    (fun block (basic : Mir.Graph.basic_block) ->
      if !found = None then begin
        let state = Moves.entry moves block in
        List.iter
          (fun (statement : Mir.Graph.statement) ->
            match statement.kind with
            | Dead locals when !found = None && List.mem path.local locals ->
                found := Some (Moves.status moves state path)
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
  test "a value moved out on every path holds nothing where its local ends" (fun () ->
      let body, moves =
        moves_of_g (moves_program ^ "fn g() {\n  let kept = text()\n  take(own kept)\n}\n")
      in
      expect_string ~expected:"empty"
        (show_status (status_where_ended body moves { local = named body "kept"; steps = [] })));
  test "a value moved out on one path may hold a value where its local ends, under a flag"
    (fun () ->
      let body, moves =
        moves_of_g
          (moves_program
         ^ "fn g(moved: Bool) {\n  let kept = text()\n  if moved {\n    take(own kept)\n  }\n}\n")
      in
      let path : Moves.path = { local = named body "kept"; steps = [] } in
      expect_string ~expected:"maybe" (show_status (status_where_ended body moves path));
      if not (List.mem path (Moves.flagged moves)) then fail "the local has no flag");
  test "a record a field of which was moved out still holds its other fields" (fun () ->
      let body, moves =
        moves_of_g (moves_program ^ "fn g() {\n  let both = pair()\n  take(own both.first)\n}\n")
      in
      let both = named body "both" in
      expect_string ~expected:"holds"
        (show_status (status_where_ended body moves { local = both; steps = [] }));
      expect_string ~expected:"empty"
        (show_status (status_where_ended body moves { local = both; steps = [ Field "first" ] })));
  test "a field given a value again holds one" (fun () ->
      let body, moves =
        moves_of_g
          (moves_program
         ^ "fn g() {\n  var both = pair()\n  take(own both.first)\n  both.first = text()\n}\n")
      in
      expect_string ~expected:"holds"
        (show_status
           (status_where_ended body moves { local = named body "both"; steps = [ Field "first" ] })))
