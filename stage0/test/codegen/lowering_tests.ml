let () =
  Codegen_support.test "an index of a list out of bounds is reported where the index is written"
    (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.grid_cell_index_out_of_bounds
        "test 0 panicked\nmessage 47\nindex out of bounds\n  at example/main.truss:4:3\n");
  Codegen_support.test
    "a check in a called lending method of the standard library reports the program's call site"
    (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.map_index_by_a_missing_key
        "test 0 panicked\nmessage 48\nindex out of bounds\n  at example/main.truss:3:11\n");
  Codegen_support.test
    "a lending method of the standard library is forwarded through a call whose capability \
     parameter it instantiates with no capability" (fun () ->
      let probe_module : Path.module_ =
        { package = Path.standard_package; modules = [ "forwarding_probe" ] }
      in
      let shelf : Path.t = Top { module_ = probe_module; name = "Shelf" } in
      let read : Lowered.Item.t =
        Code
          {
            path = Top { module_ = probe_module; name = "read_first_book" };
            instantiation = Ground.no_instantiation;
            assumes_condition = false;
          }
      in
      let _, backend =
        Codegen_support.load_standard_probe ~roots:[ read ]
          { module_ = probe_module; name = "probe" }
          Fixtures.Lowering.shelf_lending_through_a_capability_parameter
      in
      match
        List.filter_map
          (function
            | Lowered.Item.Code { path = Method { owner; name; _ }; _ } when Path.equal owner shelf
              ->
                Some name
            | _ -> None)
          (Emit_c.references (Backend.For_testing.compile_fragment backend read))
      with
      | [] -> ()
      | called ->
          Codegen_support.fail "read_first_book calls Shelf.%s" (String.concat ", Shelf." called));
  Codegen_support.test
    "a check on the first line of an indented method reports its column in the file" (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.panic_on_the_first_line_of_a_method_in_an_impl
        "test 0 panicked\nmessage 48\narithmetic overflow\n  at example/main.truss:8:28\n");
  Codegen_support.test
    "a column after a letter of two bytes counts Unicode scalar values, as a diagnostic's does"
    (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.index_past_the_end_after_an_accented_letter
        "test 0 panicked\nmessage 48\nindex out of bounds\n  at example/main.truss:3:29\n")

let () =
  Codegen_support.test
    "a call of a lending method that never lends compiles, and the code after it is unreachable"
    (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.call_of_a_lending_method_that_never_lends
        "test 0 panicked\n\
         message 108\n\
         no cell\n\
        \  at example/main.truss:6:3\n\
        \  called at example/main.truss:12:3\n\
        \  called at example/main.truss:17:10\n")

let expect_fold name ~folded ~run source =
  Codegen_support.test name (fun () ->
      let database, backend =
        Codegen_support.load
          ~roots:
            (List.map
               (fun name ->
                 Lowered.Item.make_constant (Top { module_ = Codegen_support.example; name }))
               (folded @ run))
          source
      in
      let is_folded name =
        Backend.For_testing.is_folded backend (Top { module_ = Codegen_support.example; name })
      in
      List.iter
        (fun name ->
          if not (is_folded name) then Codegen_support.fail "%s is run, and should fold" name)
        folded;
      List.iter
        (fun name -> if is_folded name then Codegen_support.fail "%s folds, and should be run" name)
        run;
      Codegen_support.expect_string ~expected:"test 0 passed\n"
        (Codegen_support.run_example_tests database backend))

let () =
  expect_fold "constants fold from their MIR, except a set, which is built by running"
    ~folded:[ "small"; "flag"; "names"; "rows"; "corner"; "primes" ]
    ~run:[ "colors" ] Fixtures.Lowering.folded_constants_and_a_set;
  expect_fold "a chain of ten constants, each naming the one before, folds" ~folded:[ "tenth" ]
    ~run:[] Fixtures.Lowering.chain_of_ten_constants

let () =
  expect_fold "a constant computed by a call folds where its code does, and is run otherwise"
    ~folded:[ "nine" ]
    ~run:[ "squares"; "last"; "word"; "report" ]
    Fixtures.Lowering.constants_computed_by_calls;
  expect_fold "a constant keeps the capacity of its lists, whether it folds or is run"
    ~folded:[ "folded"; "literal" ] ~run:[ "roomy" ]
    Fixtures.Lowering.constants_keeping_their_capacity;
  Codegen_support.test
    "a test that reaches a constant whose evaluation reaches a todo is incomplete, and the others \
     run" (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.tests_reading_an_unfinished_constant
        "test 0 passed\n\
         test 1 incomplete\n\
         message 84\n\
         the constant example.table is not computed: todo reached\n\
        \  at example/main.truss:2:3\n");
  Codegen_support.test "a constant whose evaluation uses too much CPU time cannot be built"
    (fun () ->
      let database, _ = Codegen_support.load Fixtures.Lowering.constant_computed_by_a_long_loop in
      match
        Backend.run_tests
          (Codegen_support.make_backend ~evaluation_cpu_time_limit_ms:5 database)
          ~time_limit_ms:2000
          (Codegen_support.list_tests database)
      with
      | Error message ->
          Codegen_support.expect_string
            ~expected:"Evaluating example.spun stopped: it used more than 5 ms of CPU time" message
      | Ok _ -> Codegen_support.fail "the tests ran")
