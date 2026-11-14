(* Tests of the MIR. Every definition of the standard library has MIR that
   keeps the builder's promises, which a validator checks, and the MIR of
   small programs has each construct's structure. The tests read properties
   of the MIR, never its text, so renumbering blocks or locals breaks none. *)

open Harness
open Support

let mir_of database key = Query.demand database Mir.mir key

(* What code reads *)

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

let rvalue_locals : Mir.rvalue -> Mir.local list = function
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

let rec yielded_locals : Mir.yielded -> Mir.local list = function
  | Part value -> operand_locals value
  | Built { fields; _ } ->
      List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:yielded_locals field) fields

(* A write to a whole local gives it a value; a write to a part of one reads
   the local. *)
let written (place : Mir.place) =
  match place with
  | { root = Local local; projections = [] } -> ([], [ local ])
  | _ -> (place_locals place, [])

(* The locals a statement reads, the locals it gives values, and the locals
   it ends. *)
let effects (statement : Mir.statement) =
  match statement.kind with
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

let terminator_reads : Mir.terminator -> Mir.local list = function
  | Branch { condition; _ } -> operand_locals condition
  | Switch_variant { place; _ } -> place_locals place
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

(* The validator *)

let alive = 1
let ended = 2

(* Checks a body against the builder's promises. Jumps reach blocks of the
   body, and locals and loans exist. A local is never read where some path
   has ended it. Leaving scopes ends what they hold: where a function
   returns, every local is ended but its parameters, captures, loop parts,
   and returned value, and every loan is ended; where an iteration ends,
   only what was alive or open when the loop started still is. A loop's
   blocks and a branch's blocks are closed: control leaves them only by the
   loop's end, a [Join], or an exit from tasks. *)
let validate definition (body : Mir.body) =
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
        (fun found (basic : Mir.basic_block) ->
          List.fold_left
            (fun found (statement : Mir.statement) ->
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
                    | Value_parameter _ -> "value_parameter")
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
      (fun most (basic : Mir.basic_block) ->
        List.fold_left
          (fun most (statement : Mir.statement) ->
            match statement.kind with Loan_start { loan; _ } -> max most (loan + 1) | _ -> most)
          most basic.statements)
      0 body.blocks
  in
  Array.iter
    (fun (basic : Mir.basic_block) ->
      List.iter
        (fun statement ->
          let read, given, ends = effects statement in
          List.iter local (read @ given @ ends))
        basic.statements;
      List.iter local (terminator_reads basic.terminator);
      List.iter block (Mir.successors basic.terminator);
      match basic.terminator with
      | For { part; body = inside; blocks; after; _ } ->
          local part;
          List.iter block (inside :: after :: blocks)
      | Fork { branches; join; _ } ->
          List.iter
            (fun (branch : Mir.branch) -> List.iter block (branch.entry :: branch.blocks))
            branches;
          Option.iter block join
      | _ -> ())
    body.blocks;
  (* Closed loops and branches *)
  let parts = ref [] in
  Array.iteri
    (fun index (basic : Mir.basic_block) ->
      (match Mir.iteration_loop basic.terminator with
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
              (* An early exit from a task around the loop ends that task. *)
              | Cancel _ -> ()
              | terminator ->
                  List.iter
                    (fun target ->
                      if target <> after && not (List.mem target blocks) then
                        problem "block %d of the loop at %d jumps out to %d" inner index target)
                    (Mir.successors terminator))
            blocks
      | Fork { fork; branches; join; _ } ->
          let entries = List.map (fun (branch : Mir.branch) -> branch.entry) branches in
          List.iteri
            (fun position (branch : Mir.branch) ->
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
                        (Mir.successors terminator))
                branch.blocks)
            branches
      | _ -> ())
    body.blocks;
  let held_by_exits =
    Array.fold_left
      (fun held (basic : Mir.basic_block) ->
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
  (* Runs a block from the state that reaches it, and reports what it
     breaks where [report] holds. *)
  let run ~report node =
    let state = Array.copy locals_in.(node) and open_loans = Array.copy loans_in.(node) in
    let read at local =
      if report && state.(local) land ended <> 0 then
        problem "block %d reads _%d where a path has ended it" at local
    in
    let apply at (statement : Mir.statement) =
      let read_locals, given, ends = effects statement in
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
      match Mir.iteration_loop body.blocks.(at).terminator with
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
      (* A loop's head: an iteration of its body, or its end. *)
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
          List.iter (fun target -> flow target (state, open_loans)) (Mir.successors terminator)
  in
  while not (Queue.is_empty pending) do
    run ~report:false (Queue.pop pending)
  done;
  Array.iteri (fun node is_reached -> if is_reached then run ~report:true node) reached

let () =
  let database = setup [] in
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
                try mir_of database key
                with Compiler_bug.Bug bug ->
                  fail "%s: %s" definition bug.message;
                  None
              with
              | Some mir ->
                  incr built;
                  validate definition mir.body;
                  Array.iter (validate definition) mir.lambdas
              | None -> ())
            (Query.demand database Resolve.Names.declarations_in file)))
    Standard_library.files;
  test "the standard library has MIR" (fun () ->
      if !built < 500 then fail "only %d of its definitions have MIR" !built)

(* The structure of constructs *)

(* The MIR of the function [g] of a program, validated. *)
let mir_of_g text =
  let database = setup [ ("app::main", text) ] in
  match
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        if key.path = Path.Top { module_ = module_of "app::main"; name = "g" } then Some key
        else None)
      (Query.demand database Resolve.Names.declarations (module_of "app::main"))
  with
  | Some key -> (
      match mir_of database key with
      | Some mir ->
          validate "g" mir.body;
          Array.iter (validate "g") mir.lambdas;
          mir
      | None -> failwith "g has no MIR")
  | None -> failwith "the program has no g"

(* The local a name is bound to. *)
let named (body : Mir.body) name =
  let found = ref None in
  Array.iteri
    (fun local (info : Mir.local_info) ->
      match info.kind with
      | Source { name = Some written; _ } when written = name -> found := Some local
      | _ -> ())
    body.locals;
  match !found with Some local -> local | None -> failwith ("no local is named " ^ name)

(* The blocks reachable from [from], without passing a block in [avoid]. *)
let reachable (body : Mir.body) ~from ?(avoid = []) () =
  let seen = Array.make (Array.length body.blocks) false in
  let rec visit block =
    if (not seen.(block)) && not (List.mem block avoid) then begin
      seen.(block) <- true;
      List.iter visit (Mir.successors body.blocks.(block).terminator)
    end
  in
  List.iter visit from;
  seen

let statements (body : Mir.body) =
  List.concat_map (fun (basic : Mir.basic_block) -> basic.statements) (Array.to_list body.blocks)

let terminators (body : Mir.body) =
  List.mapi
    (fun index (basic : Mir.basic_block) -> (index, basic.terminator))
    (Array.to_list body.blocks)

let () =
  test "an assignment evaluates its value, then its target" (fun () ->
      let mir = mir_of_g Fixtures.Mir.assignment_evaluates_its_value_then_its_target_and in
      let order =
        List.filter_map
          (fun (statement : Mir.statement) ->
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
      let negates (basic : Mir.basic_block) =
        List.exists
          (fun (statement : Mir.statement) ->
            match statement.kind with
            | Assign { value = Not value; _ } -> List.mem b (operand_locals value)
            | _ -> false)
          basic.statements
      in
      match
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.terminator) with
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
            match (terminator : Mir.terminator) with
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
  test "a loop over a collection runs its body for each element, and a break leaves it" (fun () ->
      let mir = mir_of_g Fixtures.Mir.loop_over_a_collection_runs_its_body_for_each in
      let body = mir.body in
      match
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.terminator) with
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
                   Mir.iteration_loop body.blocks.(block).terminator = None
                   && List.mem after (Mir.successors body.blocks.(block).terminator))
                 blocks)
          then fail "the break does not leave the loop");
  (* The local that a slice's base is, through the alias that holds the
     base's borrow while the slice's bounds are evaluated. [compare] is
     given where in the body's statements the base and a named local end. *)
  let slice_base_ends body name compare =
    let all = statements body in
    let rec base_root (local : Mir.local) =
      match
        List.find_map
          (fun (statement : Mir.statement) ->
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
        (fun (statement : Mir.statement) ->
          match statement.kind with Dead locals -> List.mem local locals | _ -> false)
        all
    in
    match
      List.find_map
        (fun (statement : Mir.statement) ->
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
      let binds (basic : Mir.basic_block) =
        List.exists
          (fun (statement : Mir.statement) ->
            match statement.kind with Live locals -> List.mem x locals | _ -> false)
          basic.statements
      in
      let returns_one = function
        | Mir.Return (Some (Constant { value = Integer one; _ })) -> Z.equal one Z.one
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
      (* x, and the temporaries that hold its value. *)
      let holding_x =
        x
        :: List.filter_map
             (fun (statement : Mir.statement) ->
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
          (fun (statement : Mir.statement) ->
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
      let failed =
        List.find_map
          (fun (_, terminator) ->
            match (terminator : Mir.terminator) with
            | Branch { condition; no; _ }
              when Some (operand_locals condition) = Option.map (fun g -> [ g ]) guard ->
                Some no
            | _ -> None)
          (terminators body)
      in
      match failed with
      | None -> fail "nothing branches on the guard"
      | Some failed ->
          (* Each path from the failed guard ends x before it tests a
             pattern again. *)
          let rec walk visited block =
            if not (List.mem block visited) then
              let basic = body.blocks.(block) in
              let rec go = function
                | [] -> (
                    match basic.terminator with
                    | Switch_variant _ -> fail "block %d tests the next arm with x bound" block
                    | terminator -> List.iter (walk (block :: visited)) (Mir.successors terminator))
                | (statement : Mir.statement) :: rest -> (
                    match statement.kind with
                    | Dead locals when List.mem x locals -> ()
                    | Assign { value = Is_variant _; _ } ->
                        fail "block %d tests the next arm with x bound" block
                    | _ -> go rest)
              in
              go basic.statements
          in
          walk [] failed);
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
                 (fun (statement : Mir.statement) ->
                   match statement.kind with
                   | Assign { value = Lambda { captures = [ capture ]; _ }; _ } ->
                       place_locals capture.place = [ offset ]
                   | _ -> false)
                 (statements mir.body))
          then fail "the lambda value does not capture g's offset"
      | lambdas -> fail "%d lambdas" (Array.length lambdas));
  test "a method an impl inherits shares its trait's default method's MIR" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Mir.method_an_impl_inherits_shares_its_traits_default) ]
      in
      let module_ = module_of "app::main" in
      let method_of owner name : Path.t = Method { owner; name; receiver = Read } in
      let impl_for type_name : Path.t =
        Impl { module_; trait = "Shape"; for_type = { type_name; generics = [] } }
      in
      let by_path path =
        match Query.demand database Mir.of_path path with
        | Some mir -> mir
        | None -> failwith (Path.show path ^ " has no MIR")
      in
      let default_method = method_of (Top { module_; name = "Shape" }) "doubled" in
      let default_mir =
        match
          Option.bind (Query.demand database Interface.Summary.key default_method) (mir_of database)
        with
        | Some mir -> mir
        | None -> failwith "the default method has no MIR"
      in
      (* Physical equality: the inherited methods hold the default method's MIR itself, not a
         MIR built again for each [impl]. *)
      List.iter
        (fun type_name ->
          if by_path (method_of (impl_for type_name) "doubled") != default_mir then
            fail "`%s` has a MIR of its own for the method it inherits" type_name)
        [ "Square"; "Cube" ];
      if by_path default_method != default_mir then
        fail "the default method's MIR by its path is not its definition's";
      (* A method an [impl] writes has its own definition's MIR. *)
      if
        by_path (method_of (impl_for "Square") "side")
        == by_path (method_of (impl_for "Cube") "side")
      then fail "two written methods share one MIR");
  test "defaults have bodies of their own, apart from the MIR of any function's body" (fun () ->
      let database = setup [ ("app::main", Fixtures.Mir.defaults_have_bodies_of_their_own) ] in
      let module_ = module_of "app::main" in
      let top name : Path.t = Top { module_; name } in
      let defaults_of path =
        match Query.demand database Mir.defaults_of_path path with
        | Some defaults -> defaults
        | None -> failwith (Path.show path ^ " has no defaults")
      in
      (* The value a default's body returns, where it is a literal. *)
      let returned (default : Mir.t) =
        validate "a default" default.body;
        List.find_map
          (fun (_, (terminator : Mir.terminator)) ->
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
      (* A capability's method has no body, and its callers evaluate its default. *)
      let add : Path.t = Method { owner = top "Tally"; name = "add"; receiver = Static } in
      if Query.demand database Mir.of_path add <> None then fail "`Tally.add` has a body's MIR";
      if positions (defaults_of add) <> [ (0, Some 5) ] then
        fail "`Tally.add` does not have its default at position 0";
      (* A method's positions count [self] first, as a call's arguments do. *)
      let advance : Path.t = Method { owner = top "Counter"; name = "advance"; receiver = Mut } in
      if positions (defaults_of advance) <> [ (1, Some 3) ] then
        fail "`Counter.advance` does not have its default at position 1";
      match defaults_of (top "Counter") with
      | Field_defaults [ { variant = None; field = "step"; value; _ } ] ->
          if returned value <> Some 2 then fail "the default of `step` is not 2"
      | Field_defaults defaults -> fail "`Counter` has %d field defaults" (List.length defaults)
      | Parameter_defaults _ -> fail "a type with parameter defaults");
  test "an early exit from concurrent code ends the tasks it leaves" (fun () ->
      let mir = mir_of_g Fixtures.Mir.early_exit_from_concurrent_code_ends_the_tasks_it_leaves in
      let blocks = mir.body.blocks in
      (* Where the exit that cancels with [number] goes on once its group of
         tasks has ended. *)
      let resume winner number =
        Array.to_list blocks
        |> List.find_map (fun (basic : Mir.basic_block) ->
            match basic.terminator with
            | Resume { winner = resumed; exits; _ } when resumed = winner ->
                Some (List.nth exits (number - 1)).resume
            | _ -> None)
      in
      (* What an exit does once every task it leaves has ended. *)
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
            match (terminator : Mir.terminator) with
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
      (* Before a group's tasks start, its winner is given a value. *)
      Array.iter
        (fun (basic : Mir.basic_block) ->
          match basic.terminator with
          | Resume { winner; _ } ->
              if
                not
                  (List.exists
                     (fun (statement : Mir.statement) ->
                       match statement.kind with
                       | Assign { target = { root = Local local; projections = [] }; _ } ->
                           local = winner
                       | _ -> false)
                     (statements mir.body))
              then fail "the winner _%d of a group is never given a value" winner
          | _ -> ())
        blocks)

(* The move analysis *)

(* The analysis of [g]'s MIR, with each value that is not a number or a
   [Bool] having something to drop. *)
let moves_of_g text =
  let mir = mir_of_g text in
  let body = mir.body in
  let needs_drop (path : Moves.path) =
    path.steps <> []
    ||
    match body.locals.(path.local).type_ with
    | Named { path = Path.Top { name = "Int64" | "Bool" | "USize"; _ }; _ } -> false
    | Named { path = Path.Top { module_; _ }; _ } -> not (List.mem "intrinsic" module_.modules)
    | _ -> true
  in
  (body, Moves.analyse ~tracks:needs_drop body)

(* What a path holds where its local is first ended. *)
let status_where_ended (body : Mir.body) moves (path : Moves.path) =
  let found = ref None in
  Array.iteri
    (fun block (basic : Mir.basic_block) ->
      if !found = None then begin
        let state = Moves.entry moves block in
        List.iter
          (fun (statement : Mir.statement) ->
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
