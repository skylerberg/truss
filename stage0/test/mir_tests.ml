(* Tests of the MIR: the MIR of a program's functions as text, and the MIR of
   every definition of the standard library, which must be well formed. *)

open Harness
open Support

let mir_of database key = Query.demand database Mir.mir key

(* Fails unless every jump of a body reaches one of its blocks and every
   local it names is one of its locals. *)
let check_body definition (body : Mir.body) =
  let blocks = Array.length body.blocks and locals = Array.length body.locals in
  let block index =
    if index < 0 || index >= blocks then fail "%s: a jump to block %d" definition index
  in
  let local index = if index < 0 || index >= locals then fail "%s: local _%d" definition index in
  let place (place : Mir.place) =
    match place.root with Local found -> local found | Constant _ -> ()
  in
  let operand : Mir.operand -> unit = function
    | Use { place = found; _ } | Borrow { place = found; _ } | Take { place = found; _ } ->
        place found
    | Constant _ -> ()
  in
  Array.iter
    (fun (basic : Mir.basic_block) ->
      List.iter
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Assign { target; _ } -> place target
          | Live found | Dead found -> List.iter local found
          | Lend { part; _ } -> local part
          | Assert value | Echo value -> operand value
          | _ -> ())
        basic.statements;
      match basic.terminator with
      | Goto target -> block target
      | Branch { condition; yes; no } ->
          operand condition;
          block yes;
          block no
      | Switch_variant { place = found; cases } ->
          place found;
          List.iter (fun (_, target) -> block target) cases
      | For { part; body = inside; after; _ } ->
          local part;
          block inside;
          block after
      | Yield { part; resume; _ } ->
          operand part;
          block resume
      | Exit_tasks { exit = Exit_to target; _ } -> block target
      | Return (Some value) -> operand value
      | Iteration_end | Return None | Exit_tasks _ | Unreachable | Todo -> ())
    body.blocks

let () =
  let database = setup [] in
  let built = ref 0 in
  List.iter
    (fun ((file : Path.file), _) ->
      test
        (Printf.sprintf "%s's MIR is well formed" (Path.show_file file))
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
                  check_body definition mir.body;
                  Array.iter (check_body definition) mir.lambdas
              | None -> ())
            (Query.demand database Resolve.Names.declarations_in file)))
    Standard_library.files;
  test "the standard library has MIR" (fun () ->
      if !built < 500 then fail "only %d of its definitions have MIR" !built)

(* The printed MIR of the function [g] of a program. *)
let printed text =
  let database = setup [ ("app::main", text) ] in
  match
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        if key.path = Path.Top { module_ = module_of "app::main"; name = "g" } then Some key
        else None)
      (Query.demand database Resolve.Names.declarations (module_of "app::main"))
  with
  | Some key -> ( match mir_of database key with Some mir -> Mir.show mir | None -> "no MIR")
  | None -> "no g"

let expect name text expected =
  test name (fun () ->
      let actual = printed text in
      if actual <> expected then fail "found:\n%s" actual)

let () =
  expect
    "an assignment evaluates its value, then its target, and a compound assignment its operand \
     first"
    Fixtures.Mir.assignment_evaluates_its_value_then_its_target_and
    "0:\n\
    \  loan 0: read mut _1 for the operation\n\
    \  end loans 0\n\
    \  _2 = app::main::step(mut _1, 2)\n\
    \  loan 1: read _2 for the operation\n\
    \  loan 2: read mut _0 for the operation\n\
    \  loan 3: read mut _1 for the operation\n\
    \  end loans 3\n\
    \  _3 = app::main::step(mut _1, 1)\n\
    \  end loans 2\n\
    \  _4 = lend standard::core::Index.at(mut _0, _3)\n\
    \  loan 4: mut mut _0 for the statement\n\
    \  end loans 1\n\
    \  _4 = _2\n\
    \  end loans 4\n\
    \  dead _2, _3, _4\n\
    \  loan 5: read mut _1 for the operation\n\
    \  end loans 5\n\
    \  _5 = app::main::step(mut _1, 4)\n\
    \  live _6\n\
    \  _6 = _5\n\
    \  loan 6: read _6 for the operation\n\
    \  loan 7: read mut _0 for the operation\n\
    \  loan 8: read mut _1 for the operation\n\
    \  end loans 8\n\
    \  _7 = app::main::step(mut _1, 3)\n\
    \  end loans 7\n\
    \  _8 = lend standard::core::Index.at(mut _0, _7)\n\
    \  loan 9: mut mut _0 for the statement\n\
    \  end loans 6\n\
    \  _9 = _6\n\
    \  _10 = add(take _8, _9)\n\
    \  _8 = _10\n\
    \  end loans 9\n\
    \  dead _5, _6, _7, _8, _9, _10\n\
    \  return ()";
  expect "a match tests its arms in order, and a guard that fails ends the arm's bindings"
    Fixtures.Mir.match_tests_its_arms_in_order_and_a_guard_that
    "0:\n\
    \  _2 = _0 is Some\n\
    \  branch _2 1 5\n\
     1:\n\
    \  live _3\n\
    \  _3 = read _0.(Some).value\n\
    \  goto 2\n\
     2:\n\
    \  matched\n\
    \  loan 0: read read _0 for the operation\n\
    \  _4 = _3\n\
    \  loan 1: read _4 for the operation\n\
    \  end loans 1\n\
    \  _5 = _4 > 0\n\
    \  branch _5 11 3\n\
     3:\n\
    \  dead _4, _5\n\
    \  goto 4\n\
     4:\n\
    \  end loans 0\n\
    \  dead _3\n\
    \  goto 5\n\
     5:\n\
    \  _6 = _0 is Some\n\
    \  branch _6 9 6\n\
     6:\n\
    \  _7 = _0 is None\n\
    \  branch _7 8 7\n\
     7:\n\
    \  unreachable\n\
     8:\n\
    \  goto 10\n\
     9:\n\
    \  goto 10\n\
     10:\n\
    \  matched\n\
    \  _1 = 0\n\
    \  dead _6, _7\n\
    \  goto 13\n\
     11:\n\
    \  dead _4, _5\n\
    \  goto 12\n\
     12:\n\
    \  end loans 0\n\
    \  _1 = _3\n\
    \  dead _3\n\
    \  dead _2\n\
    \  goto 13\n\
     13:\n\
    \  _8 = _1\n\
    \  dead _1\n\
    \  return _8";
  expect "a let with an else tests its pattern, and the else leaves the block"
    Fixtures.Mir.let_with_an_else_tests_its_pattern_and_the_else
    "0:\n\
    \  _1 = _0 is Some\n\
    \  branch _1 2 1\n\
     1:\n\
    \  dead _1\n\
    \  return 1\n\
     2:\n\
    \  live _2\n\
    \  _2 = read _0.(Some).value\n\
    \  goto 3\n\
     3:\n\
    \  dead _1\n\
    \  _3 = _2\n\
    \  dead _2\n\
    \  return _3";
  expect "a short-circuit operator jumps past its right operand"
    Fixtures.Mir.short_circuit_operator_jumps_past_its_right
    "0:\n\
    \  branch _0 1 3\n\
     1:\n\
    \  branch _1 3 2\n\
     2:\n\
    \  _2 = true\n\
    \  goto 4\n\
     3:\n\
    \  _2 = false\n\
    \  goto 4\n\
     4:\n\
    \  _3 = _2\n\
    \  dead _2\n\
    \  return _3";
  expect "a range loop copies its counter, steps it at continue, and ends at an inclusive stop"
    Fixtures.Mir.range_loop_copies_its_counter_steps_it_at_continue
    "0:\n\
    \  _1 = 0\n\
    \  live _2\n\
    \  _2 = _1\n\
    \  goto 1\n\
     1:\n\
    \  dead _1\n\
    \  _3 = _0\n\
    \  for _4 in 0..=_3 3 after 2\n\
     2:\n\
    \  dead _3\n\
    \  _11 = _2\n\
    \  dead _2\n\
    \  return _11\n\
     3:\n\
    \  live _5\n\
    \  _5 = _4\n\
    \  _6 = _5\n\
    \  loan 0: read _6 for the operation\n\
    \  end loans 0\n\
    \  _7 = _6 == 3\n\
    \  branch _7 7 4\n\
     4:\n\
    \  dead _6, _7\n\
    \  goto 5\n\
     5:\n\
    \  goto 6\n\
     6:\n\
    \  live _8\n\
    \  _8 = _5\n\
    \  loan 1: read _8 for the operation\n\
    \  end loans 1\n\
    \  _9 = _8\n\
    \  _10 = add(take _2, _9)\n\
    \  _2 = _10\n\
    \  dead _8, _9, _10\n\
    \  dead _5\n\
    \  next\n\
     7:\n\
    \  dead _6, _7\n\
    \  goto 8\n\
     8:\n\
    \  dead _5\n\
    \  next";
  expect "a loop over a yielding call runs its body for each part"
    Fixtures.Mir.loop_over_a_yielding_call_runs_its_body_for_each
    "0:\n\
    \  _1 = 0\n\
    \  live _2\n\
    \  _2 = _1\n\
    \  goto 1\n\
     1:\n\
    \  dead _1\n\
    \  for _3 in standard::list::impl Iterable for List[Element].each(read _0) 2 after 8\n\
     2:\n\
    \  loan 0: read read _0 for the loop\n\
    \  live _4\n\
    \  _4 = read _3\n\
    \  _5 = _4\n\
    \  loan 1: read _5 for the operation\n\
    \  end loans 1\n\
    \  _6 = _5 < 0\n\
    \  branch _6 6 3\n\
     3:\n\
    \  dead _5, _6\n\
    \  goto 4\n\
     4:\n\
    \  goto 5\n\
     5:\n\
    \  live _7\n\
    \  _7 = _4\n\
    \  loan 2: read _7 for the operation\n\
    \  end loans 2\n\
    \  _8 = _7\n\
    \  _9 = add(take _2, _8)\n\
    \  _2 = _9\n\
    \  dead _7, _8, _9\n\
    \  end loans 0\n\
    \  dead _4\n\
    \  next\n\
     6:\n\
    \  dead _5, _6\n\
    \  goto 7\n\
     7:\n\
    \  end loans 0\n\
    \  dead _4\n\
    \  goto 8\n\
     8:\n\
    \  _10 = _2\n\
    \  dead _2\n\
    \  return _10";
  expect "a lambda's captures and parameters are its own locals"
    Fixtures.Mir.lambdas_captures_and_parameters_are_its_own_locals
    "0:\n\
    \  _1 = lambda 0\n\
    \  _2 = app::main::apply(_1)\n\
    \  _3 = _2\n\
    \  dead _1, _2\n\
    \  return _3\n\n\
     lambda 0\n\
     0:\n\
    \  _2 = _1\n\
    \  loan 0: read _2 for the operation\n\
    \  _3 = _0\n\
    \  end loans 0\n\
    \  _4 = add(_2, _3)\n\
    \  _5 = _4\n\
    \  dead _1\n\
    \  dead _2, _3, _4\n\
    \  return _5"
