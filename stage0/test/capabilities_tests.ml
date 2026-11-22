let check packages =
  Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
    (Support.make_database packages)

let expect_one_diagnostic = Support.expect_one_diagnostic ~check
let expect_fine text = Support.expect_no_diagnostics ~check [ ("app.main", text) ]

let list_core_expressions text ~of_function =
  let module_ = Support.parse_module "app.main" in
  (Support.collect_core_nodes
     (Support.setup [ ("app.main", text) ])
     { module_; path = Top { module_; name = of_function }; ordinal = 0 })
    .expressions

let expect_not_available text ~message =
  match check (Support.setup [ ("app.main", text) ]) (Support.parse_file "app.main") with
  | [ diagnostic ]
    when Diagnostic.Code.name diagnostic.code = "capabilities.not_available"
         && diagnostic.message = message ->
      ()
  | reported ->
      Harness.fail "expected %S, got [%s]" message
        (String.concat "; "
           (List.map
              (fun (diagnostic : Diagnostic.t) ->
                Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
              reported))

let () =
  Harness.test "a call in a capability's impl declares the capability on the impl" (fun () ->
      expect_not_available Fixtures.Capabilities.greeter_impl_calling_panic
        ~message:
          "This call uses `Panic`, which is not available here. Declare it with `uses Panic` on \
           the `impl`.");
  Harness.test "a call in an impl declares the capability in the set its trait's method uses"
    (fun () ->
      expect_not_available Fixtures.Capabilities.countdown_cursor_calling_panic
        ~message:
          "This call uses `Panic`, which is not available here. Declare it with `capability Uses = \
           Panic` in the `impl`.";
      expect_not_available Fixtures.Capabilities.countdown_cursor_using_random_calling_panic
        ~message:
          "This call uses `Panic`, which is not available here. Declare it with `Panic` in the \
           `impl`'s `capability Uses`.");
  Harness.test "a call in an impl declares a capability its trait's method allows on the method"
    (fun () ->
      expect_not_available Fixtures.Capabilities.describe_impl_omitting_the_clock_its_trait_declares
        ~message:
          "This call uses `Clock`, which is not available here. Declare it with `uses Clock`, or \
           `provide` an implementation.";
      expect_not_available Fixtures.Capabilities.countdown_cursor_using_panic_without_naming_its_set
        ~message:
          "This call uses `Panic`, which is not available here. Declare it with `uses Panic`.");
  Harness.test "a call in an impl adds the capability to its set and names the set on the method"
    (fun () ->
      expect_not_available
        Fixtures.Capabilities.countdown_cursor_calling_panic_without_naming_its_set
        ~message:
          "This call uses `Panic`, which is not available here. Declare it with `capability Uses = \
           Panic` in the `impl` and `uses Self.Uses` on the method.");
  Harness.test "a call in an impl of a trait that fixes its method's capabilities can only provide"
    (fun () ->
      expect_not_available Fixtures.Capabilities.describe_impl_calling_clock
        ~message:
          "This call uses `Clock`, but `describe` can use only the capabilities `Describe` \
           declares for it. Provide an implementation with `provide`.";
      expect_not_available Fixtures.Capabilities.describe_impl_calling_panic
        ~message:
          "This call uses `Panic`, but `describe` can use only the capabilities `Describe` \
           declares for it.");
  Harness.test "a provided implementation's capabilities are declared as a call's are" (fun () ->
      expect_not_available Fixtures.Capabilities.provide_of_a_greeter_using_clock
        ~message:
          "This implementation uses `Clock`, which is not available here. Declare it with `uses \
           Clock`, or `provide` an implementation.")

let () =
  Harness.test "a capability call needs its capability, which it may declare or provide" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.clock_call_without_uses
        "capabilities.not_available"
        ~says:
          "This call uses `Clock`, which is not available here. Declare it with `uses Clock`, or \
           `provide` an implementation.");
  Harness.test "a call that uses Panic can only declare it, since nothing can provide Panic"
    (fun () ->
      expect_one_diagnostic "fn f() {\n  Panic.crash(\"no\")\n}\n" "capabilities.not_available"
        ~says:"This call uses `Panic`, which is not available here. Declare it with `uses Panic`.");
  Harness.test "a call that a `for` loop makes is named by the loop" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.panicking_bag_in_a_for_loop
        "capabilities.not_available" ~at:("bag", 2)
        ~says:"The call that this `for` loop makes uses `Panic`, which is not available here.");
  Harness.test "a `concurrent` block needs `Tasks`" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.concurrent_block_without_tasks
        "capabilities.not_available"
        ~says:"This `concurrent` block uses `Tasks`, which is not available here.");
  Harness.test "a function that declares a capability may call it" (fun () ->
      expect_fine Fixtures.Capabilities.clock_call_using_clock);
  Harness.test "a call to a function with uses needs its capabilities" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.call_of_stamp "capabilities.not_available");
  Harness.test "provide makes a capability available in its block" (fun () ->
      expect_fine Fixtures.Capabilities.provide_of_a_fixed_clock);
  Harness.test "provide records each capability's impl with its generic arguments" (fun () ->
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with
            | Provide { implementations; _ } ->
                Some
                  (List.map
                     (fun (implementation : Core.implementation) -> implementation.provides)
                     implementations)
            | _ -> None)
          (list_core_expressions Fixtures.Capabilities.provide_of_a_generic_fixed_clock
             ~of_function:"f")
      with
      | [ [ [ { capability; impl = Impl _; arguments } ] ] ]
        when Path.equal capability (Support.make_top_path "standard.capabilities" "Clock")
             &&
             match Types.For_testing.list_arguments arguments with
             | [ (_, Type tag) ] -> Types.show tag = "Bool"
             | _ -> false ->
          ()
      | _ -> Harness.fail "not recorded");
  Harness.test "a specification may not use Panic" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.ensures_calling_checked_using_panic
        "capabilities.not_available");
  Harness.test "a specification cannot use the function's capabilities" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.ensures_calling_stamp "capabilities.not_available");
  Harness.test "a loop invariant cannot use the function's capabilities" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.loop_invariant_calling_stamp
        "capabilities.not_available");
  Harness.test "a type's invariant may use no capability" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.invariant_calling_stamp
        "capabilities.not_available");
  Harness.test "a law may use no capability" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.law_calling_stamp "capabilities.not_available");
  Harness.test "a constant's value may use no capability" (fun () ->
      expect_not_available Fixtures.Capabilities.constant_calling_the_clock
        ~message:
          "This call uses `Clock`, but the value of a constant may use no capability. A constant \
           is computed when the program is compiled, and a build has no capabilities.");
  Harness.test "a constant's value cannot call a function that may panic" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.constant_calling_a_function_that_panics
        "capabilities.not_available" ~says:"uses `Panic`, but the value of a constant");
  Harness.test "a constant's value must terminate" (fun () ->
      expect_not_available Fixtures.Capabilities.constant_calling_a_function_that_may_run_forever
        ~message:"This call uses `RunForever`, but the value of a constant must terminate.");
  Harness.test "a lambda's uses must fit the function type it is passed as" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.lambda_using_clock_passed_as_plain
        "capabilities.lambda_uses");
  Harness.test "a loop over a value needs the capabilities that its `element` uses" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.loop_over_a_ticker_without_uses
        "capabilities.not_available");
  Harness.test "a loop over a value can use the function's capabilities" (fun () ->
      expect_fine Fixtures.Capabilities.loop_over_a_ticker_using_clock);
  Harness.test
    "a capability parameter is instantiated with the capabilities of the lambdas passed for it"
    (fun () -> expect_fine Fixtures.Capabilities.for_each_of_lambdas);
  Harness.test "a trait's method solves its capability parameter as a function does" (fun () ->
      let visitor = Fixtures.Capabilities.visitor in
      let call =
        "{\n  numbers.visit_all(fn(value) {\n    let _ = Clock.now()\n    let _ = value\n  })\n}\n"
      in
      expect_fine (visitor ^ "fn f(numbers: Numbers)\n  uses Clock\n" ^ call);
      expect_one_diagnostic
        (visitor ^ "fn f(numbers: Numbers)\n" ^ call)
        "capabilities.not_available");
  Harness.test "a capability parameter's set must be available at the call" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.for_each_of_a_lambda_using_clock
        "capabilities.not_available");
  Harness.test "a test that crashes declares Panic, as a function does" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.test_calling_panic "capabilities.not_available";
      expect_fine Fixtures.Capabilities.test_declaring_panic);
  Harness.test "a test that runs a loop without a measure declares RunForever, as a function does"
    (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.test_running_a_loop_without_a_measure
        "capabilities.not_available";
      expect_fine Fixtures.Capabilities.test_declaring_run_forever);
  Harness.test "a place whose implementation mutates state is provided mut" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.counter_provided_as_tally
        "capabilities.provide_mode")

let first_or_crash = Fixtures.Capabilities.first_or_crash
let run = first_or_crash ^ Fixtures.Capabilities.run

let () =
  let declare_panic =
    "This call uses `Panic`, which is not available here. Declare it with `uses Panic`."
  in
  let only_panic description =
    Printf.sprintf
      "This call uses `Clock`, but %s may use no capability except `Panic` and `RunForever`, even \
       one that is available outside it. Parallel calls of one implementation could race."
      description
  in
  Harness.test "a call in a parallel branch needs Panic as the same call outside the branch does"
    (fun () ->
      expect_one_diagnostic
        (first_or_crash ^ Fixtures.Capabilities.first_or_crash_in_a_parallel_branch_without_uses)
        "capabilities.not_available" ~says:declare_panic ~at:("first_or_crash(left)", 1);
      expect_fine
        (first_or_crash ^ Fixtures.Capabilities.first_or_crash_in_a_parallel_branch_using_panic));
  Harness.test "a call in a nested parallel branch needs the function's Panic" (fun () ->
      expect_one_diagnostic
        (first_or_crash
       ^ Fixtures.Capabilities.first_or_crash_in_a_nested_parallel_branch_without_uses)
        "capabilities.not_available" ~says:declare_panic ~at:("first_or_crash(left)", 1));
  Harness.test "a call in a parallel for needs Panic as the same call outside the loop does"
    (fun () ->
      expect_one_diagnostic
        (first_or_crash ^ Fixtures.Capabilities.first_or_crash_in_a_parallel_for_without_uses)
        "capabilities.not_available" ~says:declare_panic ~at:("first_or_crash(row)", 1);
      expect_fine
        (first_or_crash ^ Fixtures.Capabilities.first_or_crash_in_a_parallel_for_using_panic));
  Harness.test "a parallel branch may use no capability but Panic, even one its function declares"
    (fun () ->
      expect_not_available Fixtures.Capabilities.clock_call_in_a_parallel_branch
        ~message:(only_panic "a `parallel` branch");
      expect_not_available Fixtures.Capabilities.clock_call_in_a_parallel_for
        ~message:(only_panic "a `parallel for`"));
  Harness.test "a capability that a parallel branch may not use is reported once, by the branch"
    (fun () ->
      expect_not_available Fixtures.Capabilities.clock_call_in_a_parallel_branch_without_uses
        ~message:(only_panic "a `parallel` branch"));
  Harness.test "a parallel branch may use a capability that it provides" (fun () ->
      expect_fine Fixtures.Capabilities.provide_of_a_fixed_clock_in_a_parallel_branch);
  Harness.test "a parallel branch in a lambda uses Panic only where the lambda's type allows it"
    (fun () ->
      expect_one_diagnostic
        (first_or_crash
       ^ Fixtures.Capabilities.lambda_with_a_crashing_parallel_branch_passed_as_plain)
        "capabilities.lambda_uses"
        ~says:"This lambda uses `Panic`, which the function type it is passed as does not allow."
        ~at:("fn() {", 1));
  Harness.test "a parallel branch in a lambda adds Panic to the lambda's inferred uses" (fun () ->
      expect_one_diagnostic
        (run ^ Fixtures.Capabilities.run_of_a_lambda_with_a_crashing_parallel_branch_without_uses)
        "capabilities.not_available" ~says:declare_panic ~at:("run(fn", 1);
      let text =
        run ^ Fixtures.Capabilities.run_of_a_lambda_with_a_crashing_parallel_branch_using_panic
      in
      expect_fine text;
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match (node.kind, node.type_) with
            | Lambda _, Function { uses; _ } -> Some (Types.has_capability (Built_in Panic) uses)
            | _ -> None)
          (list_core_expressions text ~of_function:"f")
      with
      | [ true ] -> ()
      | _ -> Harness.fail "the lambda's inferred uses leave out Panic");
  Harness.test "a call in a parallel branch needs the Panic of a lambda passed to it" (fun () ->
      expect_one_diagnostic
        (run ^ Fixtures.Capabilities.run_of_a_crashing_lambda_in_a_parallel_branch_without_uses)
        "capabilities.not_available" ~says:declare_panic ~at:("run(fn", 1))

let () =
  Harness.test "a dependency can use only the capabilities that it is granted" (fun () ->
      let packages =
        Support.setup
          [
            ("app.main", Fixtures.Capabilities.call_of_a_dependencys_stamp);
            ("clock_library.time", Fixtures.Capabilities.time_stamp_using_clock);
          ]
      in
      let packages =
        Support.with_dependencies packages { owner = None; name = "app" }
          [ { package = { owner = None; name = "clock_library" }; capabilities = [] } ]
      in
      match Support.list_codes (check packages (Support.parse_file "app.main")) with
      | [ "capabilities.not_granted" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual))

let () =
  let with_grant files granted =
    let packages =
      Support.with_dependencies (Support.setup files) { owner = None; name = "app" }
        [ { package = { owner = None; name = "clock_library" }; capabilities = granted } ]
    in
    Support.list_codes (check packages (Support.parse_file "app.main"))
  in
  let library = ("clock_library.time", Fixtures.Capabilities.library_time) in
  Harness.test "a dependency's trait method can use only the granted capabilities" (fun () ->
      match with_grant [ ("app.main", Fixtures.Capabilities.wall_stamp_call); library ] [] with
      | "capabilities.not_granted" :: _ -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "a dependency's trait method can use a granted capability" (fun () ->
      match
        with_grant
          [ ("app.main", Fixtures.Capabilities.wall_stamp_call); library ]
          [ Grant.Prelude "Clock" ]
      with
      | [] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "providing a dependency's type checks the grants for the capabilities of its impls"
    (fun () ->
      match
        with_grant
          [ ("app.main", Fixtures.Capabilities.provide_of_a_dependencys_fixed_clock); library ]
          []
      with
      | [ "capabilities.not_granted" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual))

let () =
  Harness.test "an implementation of a capability may not call the capability directly" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.notes_impl_calling_notes
        "capabilities.not_available");
  Harness.test "an implementation of a capability may hand the capability to a function value"
    (fun () -> expect_fine Fixtures.Capabilities.notes_impl_handing_notes_to_a_function)

let list_codes_with_grants files grants =
  let packages =
    Support.with_dependencies
      (Support.setup ~dependencies:[ ("plugins", "framework") ] files)
      { owner = None; name = "app" }
      (List.map (fun (package, capabilities) -> { Manifest.package; capabilities }) grants)
  in
  (packages, Support.list_codes (check packages (Support.parse_file "app.main")))

let expect_codes ~expected (_, actual) =
  if actual <> expected then
    Harness.fail "found [%s], expected [%s]" (String.concat "; " actual)
      (String.concat "; " expected)

let time = ("clock_library.time", Fixtures.Capabilities.time_stamp_using_clock)
let sources = ("framework.sources", Fixtures.Capabilities.sources_sources)
let timers = ("plugins.timers", Fixtures.Capabilities.timers_timers)

let () =
  let value = ("app.main", Fixtures.Capabilities.dependencys_function_as_a_value) in
  Harness.test "a function value of a dependency's function can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (list_codes_with_grants [ value; time ] [ ({ owner = None; name = "clock_library" }, []) ]));
  Harness.test "a function value of a dependency's function can use a granted capability" (fun () ->
      expect_codes ~expected:[]
        (list_codes_with_grants [ value; time ]
           [ ({ owner = None; name = "clock_library" }, [ Grant.Prelude "Clock" ]) ]));
  let bound = ("app.main", Fixtures.Capabilities.bound) in
  Harness.test
    "an impl of a dependency that satisfies a bound can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (list_codes_with_grants [ bound; sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ Grant.Prelude "Clock" ]);
             ({ owner = None; name = "plugins" }, []);
           ]));
  Harness.test "an impl of a dependency that satisfies a bound can use a granted capability"
    (fun () ->
      expect_codes ~expected:[]
        (list_codes_with_grants [ bound; sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ Grant.Prelude "Clock" ]);
             ({ owner = None; name = "plugins" }, [ Grant.Prelude "Clock" ]);
           ]));
  Harness.test "an impl of a dependency behind an `any` value can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (list_codes_with_grants
           [ ("app.main", Fixtures.Capabilities.any_timer_from_plugins); sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ Grant.Prelude "Clock" ]);
             ({ owner = None; name = "plugins" }, []);
           ]))

let ledger = ("store.ledger", Fixtures.Capabilities.ledger_ledger)
let pays = ("app.main", Fixtures.Capabilities.pays)

let list_problems packages =
  let app : Path.package = { owner = None; name = "app" } in
  let database = Support.make_database packages in
  Database.list_manifest_problems database app

let () =
  Harness.test "a grant names a capability outside the prelude by its full path" (fun () ->
      expect_codes ~expected:[]
        (list_codes_with_grants [ pays; ledger ]
           [
             ( { owner = None; name = "store" },
               [ Grant.Full_path { module_names = [ "store"; "ledger" ]; name = "Ledger" } ] );
           ]));
  Harness.test "a capability's name alone grants only one of the prelude" (fun () ->
      let packages, actual =
        list_codes_with_grants [ pays; ledger ]
          [ ({ owner = None; name = "store" }, [ Grant.Prelude "Ledger" ]) ]
      in
      expect_codes ~expected:[ "capabilities.not_granted" ] (packages, actual);
      match list_problems packages with
      | [
       Not_a_capability
         { dependency = { Path.owner = None; name = "store" }; capability = Prelude "Ledger" };
      ] ->
          ()
      | _ -> Harness.fail "the grant is not reported");
  Harness.test "a grant covers only the capabilities it names" (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (list_codes_with_grants [ pays; ledger ]
           [ ({ Path.owner = None; name = "store" }, [ Grant.Prelude "Clock" ]) ]))

let () =
  Harness.test "a dependency that nothing in the package names is reported" (fun () ->
      let packages, _ =
        list_codes_with_grants
          [ ("app.main", Fixtures.Capabilities.function_returning_one); time ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      match list_problems packages with
      | [ Unused_dependency { Path.owner = None; name = "clock_library" } ] -> ()
      | _ -> Harness.fail "not reported");
  Harness.test "a dependency named in a path is used" (fun () ->
      let packages, _ =
        list_codes_with_grants [ pays; ledger ]
          [
            ( { Path.owner = None; name = "store" },
              [ Grant.Full_path { module_names = [ "store"; "ledger" ]; name = "Ledger" } ] );
          ]
      in
      if list_problems packages <> [] then Harness.fail "reported");
  Harness.test "a dependency whose trait's method is called with a dot is used" (fun () ->
      let packages, actual =
        list_codes_with_grants
          [
            ("app.main", Fixtures.Capabilities.call_of_doubled);
            ("shapes.sizes", Fixtures.Capabilities.doubled_trait_for_int64);
          ]
          [ ({ Path.owner = None; name = "shapes" }, []) ]
      in
      expect_codes ~expected:[] (packages, actual);
      if list_problems packages <> [] then Harness.fail "reported");
  Harness.test "an unused dependency is reported for every kind of definition in the package"
    (fun () ->
      let packages, actual =
        list_codes_with_grants
          [ ("app.main", Fixtures.Capabilities.package_of_every_kind_of_definition); time ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      expect_codes ~expected:[] (packages, actual);
      match list_problems packages with
      | [ Unused_dependency { Path.owner = None; name = "clock_library" } ] -> ()
      | _ -> Harness.fail "not reported");
  Harness.test "an unused dependency is not reported for a package with an error" (fun () ->
      let packages, _ =
        list_codes_with_grants
          [ ("app.main", Fixtures.Capabilities.function_returning_true_as_int64); time ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      if list_problems packages <> [] then Harness.fail "reported");
  Harness.test "a dependency that only a test uses is left out of the code's packages" (fun () ->
      let shapes : Path.package = { owner = None; name = "shapes" }
      and limits : Path.package = { owner = None; name = "limits" } in
      let packages, actual =
        list_codes_with_grants
          [
            ("app.main", Fixtures.Capabilities.doubling_with_a_test_of_bounds);
            ("shapes.sizes", Fixtures.Capabilities.doubled_trait_for_int64);
            ("limits.bounds", Fixtures.Capabilities.bounds_most);
          ]
          [ (shapes, []); (limits, []) ]
      in
      expect_codes ~expected:[] (packages, actual);
      if list_problems packages <> [] then Harness.fail "a dependency is reported unused";
      match
        Database.find_code_packages (Support.make_database packages) { owner = None; name = "app" }
      with
      | Some code_packages when List.mem shapes code_packages && not (List.mem limits code_packages)
        ->
          ()
      | Some code_packages ->
          Harness.fail "found [%s]" (String.concat "; " (List.map Path.show_package code_packages))
      | None -> Harness.fail "the code's packages are not computed")

let ticks = Fixtures.Capabilities.ticks

let () =
  Harness.test "a function that uses a capability is not passed as one that uses none" (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.tick_passed_without_uses)
        "types.mismatch");
  Harness.test "a function that uses a capability is not bound as one that uses none" (fun () ->
      expect_one_diagnostic (ticks ^ Fixtures.Capabilities.tick_bound_without_uses) "types.mismatch");
  Harness.test "a function that uses a capability is not returned as one that uses none" (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.tick_returned_without_uses)
        "types.mismatch");
  Harness.test "a function that uses a capability is not stored as one that uses none" (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.tick_stored_without_uses)
        "types.mismatch");
  Harness.test "a function that uses a capability is not assigned as one that uses none" (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.tick_assigned_without_uses)
        "types.mismatch");
  Harness.test "function types inside a type must list the same capabilities" (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.list_of_actions_losing_uses)
        "types.mismatch");
  Harness.test "a function that uses nothing is passed as one that may use a capability" (fun () ->
      expect_fine (ticks ^ Fixtures.Capabilities.still_bound_using_clock));
  Harness.test "a branch's function meets the function type expected of the branches" (fun () ->
      expect_fine (ticks ^ Fixtures.Capabilities.branches_of_functions_using_clock));
  Harness.test "a branch's function that uses a capability is not bound as one that uses none"
    (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.branches_of_functions_bound_without_uses)
        "types.mismatch");
  Harness.test
    "a capability parameter is instantiated with the capabilities of the functions passed for it"
    (fun () -> expect_fine (ticks ^ Fixtures.Capabilities.each_time_of_tick_using_clock));
  Harness.test "the capabilities of a function passed for a capability parameter must be available"
    (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.each_time_of_tick_without_uses)
        "capabilities.not_available");
  Harness.test
    "a capability parameter is instantiated with the capabilities of a parenthesized lambda"
    (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.each_time_of_a_parenthesized_lambda)
        "capabilities.not_available");
  Harness.test
    "a capability parameter is instantiated with the capabilities of a function in a branch"
    (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.each_time_of_a_branch_of_functions)
        "capabilities.not_available");
  Harness.test
    "a capability parameter is instantiated with the capabilities of a lambda in a branch"
    (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.each_time_of_a_branch_with_a_lambda)
        "capabilities.not_available");
  Harness.test "a function passes its own capability parameter on" (fun () ->
      expect_fine (ticks ^ Fixtures.Capabilities.passes_on_its_own_capability));
  Harness.test "a function's own capability parameter is rigid in a lambda's type" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.own_capability_given_a_lambda_using_a_ticker
        "capabilities.lambda_uses");
  Harness.test "a function's own capability parameter is rigid in a binding's type" (fun () ->
      expect_one_diagnostic
        (ticks ^ Fixtures.Capabilities.own_capability_given_tick)
        "types.mismatch");
  Harness.test "a function calls itself with its own capability parameter" (fun () ->
      expect_fine Fixtures.Capabilities.repeat_passing_its_own_capability);
  Harness.test "a recursive call needs the capabilities that it passes for its capability parameter"
    (fun () ->
      let repeat uses =
        ticks
        ^ "fn repeat(action: (fn() -> Instant uses generic Mine), again: Bool) -> Instant\n  uses "
        ^ uses
        ^ "\n{\n  if again {\n    repeat(tick, again: false)\n  } else {\n    action()\n  }\n}\n"
      in
      expect_one_diagnostic (repeat "generic Mine") "capabilities.not_available";
      expect_fine (repeat "generic Mine, Clock"))

let later = ticks ^ Fixtures.Capabilities.later

let () =
  Harness.test "a call's result has the capabilities that were passed for the capability parameter"
    (fun () ->
      expect_one_diagnostic
        (later ^ Fixtures.Capabilities.later_of_tick_without_uses)
        "capabilities.not_available";
      expect_fine (later ^ Fixtures.Capabilities.later_of_tick_using_clock);
      expect_fine (later ^ Fixtures.Capabilities.later_of_still));
  Harness.test "a call's result must fit the function type that it is checked against" (fun () ->
      expect_one_diagnostic
        (later ^ Fixtures.Capabilities.later_of_tick_bound_without_uses)
        "types.mismatch";
      expect_fine (later ^ Fixtures.Capabilities.later_of_tick_bound_using_clock));
  Harness.test
    "a call needs no capability that it passes for a capability parameter its callee only returns"
    (fun () ->
      let chosen = Fixtures.Capabilities.chosen in
      expect_fine (chosen ^ Fixtures.Capabilities.chosen_kept_without_calling);
      expect_one_diagnostic
        (chosen ^ Fixtures.Capabilities.chosen_called_without_its_capability)
        "capabilities.not_available");
  Harness.test "a call's result may widen to more `uses` without requiring them at the call"
    (fun () -> expect_fine (ticks ^ Fixtures.Capabilities.checked_result_widened));
  Harness.test "a variable that is assigned a second function has the capabilities of both"
    (fun () ->
      expect_one_diagnostic
        (later ^ Fixtures.Capabilities.held_still_then_tick_without_uses)
        "capabilities.not_available";
      expect_fine (later ^ Fixtures.Capabilities.held_still_then_tick_using_clock));
  Harness.test "only a function, a method, or a theorem names a capability parameter" (fun () ->
      expect_one_diagnostic "type Holder(action: (fn() -> Instant uses generic Granted))\n"
        "resolve.unknown_name";
      expect_one_diagnostic "test \"t\" uses generic Granted {}\n" "resolve.unknown_name";
      expect_fine "type Holder(action: (fn() -> Instant uses Clock))\n")

let () =
  Harness.test "a function that may run forever is not bound as one that terminates" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.forever_bound_as_a_function_that_terminates
        "types.mismatch" ~says:"Expected `fn() -> Int64`, found `(fn() -> Int64 uses RunForever)`.");
  Harness.test "a function with a time clause is bound as a function type with the clause"
    (fun () -> expect_fine Fixtures.Capabilities.quick_bound_with_its_time_clause);
  Harness.test "function types inside a type must promise the same costs" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.list_of_actions_gaining_a_cost "types.mismatch"
        ~says:"Expected `List[(fn() -> Int64 cost time O(1))]`, found `List[fn() -> Int64]`.")

let readings = Fixtures.Capabilities.readings

let () =
  Harness.test "the next of a cursor needs the capabilities in its `Uses`" (fun () ->
      expect_one_diagnostic
        (readings ^ Fixtures.Capabilities.next_of_readings_without_uses)
        "capabilities.not_available");
  Harness.test "the next of a cursor is fine where its `Uses` are available" (fun () ->
      expect_fine (readings ^ Fixtures.Capabilities.next_of_readings_using_meter));
  Harness.test "a for loop over a cursor needs the capabilities in the cursor's `Uses`" (fun () ->
      expect_one_diagnostic
        (readings ^ Fixtures.Capabilities.for_loop_over_readings)
        "capabilities.not_available");
  Harness.test "a cursor whose `next` uses a capability meets a Cursor bound" (fun () ->
      expect_fine (readings ^ Fixtures.Capabilities.pull_from_readings_using_meter));
  Harness.test "a generic function that advances a cursor needs the cursor's capabilities"
    (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.pull_without_uses "capabilities.not_available");
  Harness.test "a call that passes a cursor needs the capabilities in the cursor's `Uses`"
    (fun () ->
      expect_one_diagnostic
        (readings ^ Fixtures.Capabilities.pull_from_readings)
        "capabilities.not_available");
  Harness.test "a method that Cursor provides needs the capabilities in the cursor's `Uses`"
    (fun () ->
      expect_one_diagnostic
        (readings ^ Fixtures.Capabilities.count_of_readings_without_uses)
        "capabilities.not_available");
  Harness.test "a method that Cursor provides runs where the cursor's `Uses` are available"
    (fun () -> expect_fine (readings ^ Fixtures.Capabilities.count_of_readings_using_meter));
  Harness.test "a cursor whose `next` uses no capability needs none" (fun () ->
      expect_fine Fixtures.Capabilities.counted_cursor);
  Harness.test "a cursor whose `next` uses a capability cannot be an any value" (fun () ->
      expect_one_diagnostic
        (readings ^ Fixtures.Capabilities.any_cursor_of_readings)
        "types.no_impl")

let feed = Fixtures.Capabilities.feed

let () =
  Harness.test "an impl that leaves out an associated capability set has the empty set" (fun () ->
      expect_fine (feed ^ Fixtures.Capabilities.pull_once_of_a_counter));
  Harness.test "a call needs the capabilities of the set that the impl defines" (fun () ->
      expect_one_diagnostic
        (feed ^ Fixtures.Capabilities.pull_once_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "a provided method needs the capabilities of the set that the impl defines"
    (fun () ->
      expect_one_diagnostic
        (feed ^ Fixtures.Capabilities.skip_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "a set defined from a parameter's set is the argument's set" (fun () ->
      expect_fine (feed ^ Fixtures.Capabilities.twice_of_a_gauge_using_meter);
      expect_one_diagnostic
        (feed ^ Fixtures.Capabilities.twice_of_twice_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "a method of an impl can use only the set that the impl defines" (fun () ->
      expect_one_diagnostic
        (feed ^ Fixtures.Capabilities.greedy_feed_pull_using_meter)
        "types.impl_uses");
  Harness.test "an impl defines only a set that its trait declares, and only once" (fun () ->
      expect_one_diagnostic
        (feed ^ Fixtures.Capabilities.impl_defining_an_undeclared_set)
        "types.extra_member";
      expect_one_diagnostic
        (feed ^ Fixtures.Capabilities.impl_defining_uses_twice)
        "types.extra_member");
  Harness.test "a set cannot be defined from itself" (fun () ->
      expect_one_diagnostic
        (feed ^ Fixtures.Capabilities.set_defined_as_itself)
        "types.unknown_associated_capability");
  Harness.test "an associated capability set is of a trait that declares it" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.trait_using_an_undeclared_set
        "types.unknown_associated_capability";
      expect_one_diagnostic Fixtures.Capabilities.unbounded_parameters_set
        "types.unknown_associated_capability";
      expect_one_diagnostic Fixtures.Capabilities.self_set_outside_a_trait
        "types.misplaced_self_type";
      expect_one_diagnostic Fixtures.Capabilities.set_of_an_unknown_name
        "resolve.not_a_generic_parameter";
      expect_one_diagnostic Fixtures.Capabilities.set_of_a_capability_parameter
        "resolve.not_a_generic_parameter");
  Harness.test "a trait's methods can use a set that a required trait declares" (fun () ->
      let rewind = Fixtures.Capabilities.rewind in
      expect_fine (feed ^ rewind ^ Fixtures.Capabilities.rewind_of_a_gauge_using_meter);
      expect_one_diagnostic
        (feed ^ rewind ^ Fixtures.Capabilities.back_twice_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "a function type can use an associated capability set" (fun () ->
      let apply = Fixtures.Capabilities.apply in
      expect_fine (feed ^ apply ^ Fixtures.Capabilities.apply_to_a_gauge);
      expect_one_diagnostic
        (feed ^ apply ^ Fixtures.Capabilities.apply_to_a_counter_using_meter)
        "capabilities.lambda_uses");
  Harness.test "a capability parameter adds to an associated capability set" (fun () ->
      let folded = Fixtures.Capabilities.folded in
      expect_fine (feed ^ folded ^ Fixtures.Capabilities.fold_of_a_counter_using_meter);
      expect_one_diagnostic
        (feed ^ folded ^ Fixtures.Capabilities.fold_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "an any value hides only a type whose associated capability sets are empty"
    (fun () ->
      expect_fine (feed ^ Fixtures.Capabilities.any_feed_of_a_counter);
      expect_one_diagnostic (feed ^ Fixtures.Capabilities.any_feed_of_a_gauge) "types.no_impl";
      expect_one_diagnostic
        (feed ^ Fixtures.Capabilities.any_feed_of_a_generic_source)
        "types.no_impl")

let () =
  Harness.test "an impl cannot take only the callbacks that terminate where its trait takes any"
    (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities.spin_passed_to_an_impl_whose_callback_drops_run_forever
        "types.signature_mismatch" ~at:("each", 2));
  Harness.test "a capability's implementation cannot take only the callbacks that terminate"
    (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities.spin_passed_to_a_capability_whose_impl_drops_run_forever
        "types.signature_mismatch" ~at:("run", 2));
  Harness.test "an impl cannot take only the callbacks that use no capability" (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities.note_passed_to_an_impl_whose_callback_drops_the_journal
        "types.signature_mismatch" ~at:("each", 2));
  Harness.test "an impl cannot swap the capability parameters of its trait's callbacks" (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities
        .note_passed_to_an_impl_that_swaps_the_capability_parameters_of_its_callbacks
        "types.signature_mismatch" ~at:("each", 2))

let () =
  let loop_needs_run_forever =
    "This loop has no measure, so it uses `RunForever`, which is not available here. Declare it \
     with `uses RunForever`, or give the loop a `decreases` clause"
  in
  Harness.test "a loop without a measure uses RunForever" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.while_loop_without_a_measure
        "capabilities.not_available" ~says:(loop_needs_run_forever ^ ".") ~at:("while", 1);
      expect_one_diagnostic Fixtures.Capabilities.cursor_loop_without_a_measure
        "capabilities.not_available"
        ~says:(loop_needs_run_forever ^ ", or implement `FiniteCursor` for `Countdown`.")
        ~at:("for value", 1));
  Harness.test "a function that uses RunForever holds a loop without a measure" (fun () ->
      expect_fine Fixtures.Capabilities.while_loop_without_a_measure_using_run_forever);
  Harness.test "a call of a function that uses RunForever uses it" (fun () ->
      expect_not_available Fixtures.Capabilities.call_of_a_function_that_runs_forever
        ~message:
          "This call uses `RunForever`, which is not available here. Declare it with `uses \
           RunForever`.");
  Harness.test "a parallel branch runs forever where its function does" (fun () ->
      expect_fine
        Fixtures.Capabilities.while_loop_without_a_measure_in_a_parallel_branch_using_run_forever;
      expect_one_diagnostic Fixtures.Capabilities.while_loop_without_a_measure_in_a_parallel_branch
        "capabilities.not_available" ~says:(loop_needs_run_forever ^ "."));
  Harness.test "a specification calls no function that uses RunForever" (fun () ->
      expect_not_available Fixtures.Capabilities.specification_calling_a_function_that_runs_forever
        ~message:"This call uses `RunForever`, but a specification must terminate.")

let () =
  Harness.test "a lambda that loops without a measure uses RunForever" (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities.lambda_looping_without_a_measure_bound_as_using_no_capability
        "capabilities.lambda_uses"
        ~says:
          "This lambda uses `RunForever`, which the function type it is passed as does not allow."
        ~notes:[ ("This loop has no measure, so it uses `RunForever`.", ("while", 1)) ];
      expect_one_diagnostic
        Fixtures.Capabilities.lambda_looping_without_a_measure_bound_as_using_a_capability_parameter
        "capabilities.lambda_uses"
        ~says:
          "This lambda uses `RunForever`, which the function type it is passed as does not allow.");
  Harness.test "a function type that names a capability parameter takes a lambda that terminates"
    (fun () ->
      expect_fine
        Fixtures.Capabilities
        .lambda_calling_the_enclosing_functions_callback_bound_as_using_a_capability_parameter;
      expect_fine Fixtures.Capabilities.lambda_calling_slow_bound_as_using_a_capability_parameter);
  Harness.test
    "a function type that names a capability parameter and RunForever takes a lambda that calls \
     the parameter's callback and loops" (fun () ->
      expect_fine
        Fixtures.Capabilities
        .lambda_calling_the_enclosing_functions_callback_then_looping_bound_as_using_run_forever);
  Harness.test
    "a function type that names a capability parameter takes no function that runs forever"
    (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.forever_bound_as_using_a_capability_parameter
        "types.mismatch"
        ~says:"Expected `(fn() uses generic Mine)`, found `(fn() uses RunForever)`."
        ~at:("forever", 2));
  Harness.test "a call passes RunForever on through a capability parameter" (fun () ->
      expect_not_available
        (ticks
       ^ Fixtures.Capabilities
         .each_time_of_a_lambda_calling_the_enclosing_functions_callback_then_looping)
        ~message:
          "This call uses `RunForever`, which is not available here. Declare it with `uses \
           RunForever`.";
      let text =
        ticks
        ^ Fixtures.Capabilities
          .each_time_of_a_lambda_calling_the_enclosing_functions_callback_then_looping_using_run_forever
      in
      expect_fine text;
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match (node.kind, node.type_) with
            | Lambda _, Function { uses; _ } -> Some (Types.list_capabilities uses)
            | _ -> None)
          (list_core_expressions text ~of_function:"run")
      with
      | [ [ Built_in Run_forever; Capability_parameter { name = "Mine"; _ } ] ] -> ()
      | _ -> Harness.fail "the lambda's type does not hold `RunForever` and `Mine` alone");
  Harness.test
    "a binding without a type holds a function that uses a capability parameter and RunForever"
    (fun () ->
      expect_fine
        (later
       ^ Fixtures.Capabilities
         .later_of_a_lambda_calling_the_enclosing_functions_callback_then_looping_bound_without_a_type
        ))

let () =
  Harness.test "an impl's method runs forever only where its trait's method allows it" (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities.impl_method_running_forever_where_its_trait_does_not "types.impl_uses"
        ~says:"`step` can use only the capabilities `Step` declares for it.");
  Harness.test "an associated capability set carries RunForever from an impl" (fun () ->
      expect_fine Fixtures.Capabilities.cursor_running_forever_through_its_capability_set);
  Harness.test "a function with a time clause can crash through Panic.crash and expect" (fun () ->
      expect_fine Fixtures.Capabilities.crash_and_expect_in_functions_with_a_time_clause);
  Harness.test "a function that uses RunForever has no time clause" (fun () ->
      List.iter
        (fun text ->
          expect_one_diagnostic text "types.unbounded_time"
            ~says:
              "A function that uses `RunForever` may run forever, so no `time` clause bounds it.")
        [
          Fixtures.Capabilities.time_clause_on_a_function_that_runs_forever;
          Fixtures.Capabilities.time_clause_on_a_function_type_that_runs_forever;
        ]);
  Harness.test "a function that uses RunForever unless C states its time clause when C" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.time_of_a_function_that_runs_forever_unless_finite
        "types.unbounded_time" ~says:"`when` a condition that implies `Source: FiniteCursor`"
        ~fixed:Fixtures.Capabilities.time_when_a_function_terminates;
      expect_fine Fixtures.Capabilities.time_when_a_function_terminates);
  Harness.test "a loop over a cursor that may not end uses RunForever unless it is finite"
    (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.loop_over_a_cursor_that_may_not_end
        "capabilities.not_available"
        ~says:
          "This loop's measure holds only when Source: FiniteCursor, so the loop uses `RunForever \
           unless Source: FiniteCursor`";
      expect_fine Fixtures.Capabilities.loop_over_a_cursor_unless_it_is_finite);
  Harness.test "collecting a FiniteCursor uses no RunForever" (fun () ->
      expect_fine Fixtures.Capabilities.collect_of_characters);
  Harness.test "collecting a generic cursor passes on the condition of RunForever" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.collect_through_a_cursor_that_may_not_end
        "capabilities.not_available"
        ~says:"Declare it with `uses RunForever unless Items: FiniteCursor`.";
      expect_fine Fixtures.Capabilities.collect_through_a_cursor_unless_it_is_finite);
  Harness.test "collecting a cursor that is not finite uses RunForever" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.collect_of_a_cursor_that_never_ends
        "capabilities.not_available" ~says:"This call uses `RunForever`, which");
  Harness.test "RunForever unless C does not cover a loop that runs forever under C" (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities.loop_that_runs_forever_under_a_condition_on_another_capability
        "capabilities.not_available" ~says:"This loop has no measure");
  Harness.test "a function value keeps the condition its type arguments decide" (fun () ->
      expect_fine Fixtures.Capabilities.function_value_of_a_function_with_a_condition;
      expect_one_diagnostic
        Fixtures.Capabilities.function_value_of_a_function_with_a_condition_that_may_run_forever
        "capabilities.not_available"
        ~says:"This call uses `RunForever unless Source: FiniteCursor`, which");
  Harness.test "an associated capability set takes a condition" (fun () ->
      expect_fine Fixtures.Capabilities.adapter_whose_capability_set_has_a_condition;
      expect_one_diagnostic Fixtures.Capabilities.adapter_called_where_its_source_may_not_end
        "capabilities.not_available"
        ~says:"This call uses `RunForever unless Source: FiniteCursor`, which";
      expect_one_diagnostic Fixtures.Capabilities.adapter_whose_capability_set_lacks_the_condition
        "capabilities.not_available"
        ~says:
          "Declare it with `RunForever unless Source: FiniteCursor` in the `impl`'s `capability \
           Uses`.");
  Harness.test "RunForever unless a subtrait covers RunForever unless its supertrait" (fun () ->
      expect_fine Fixtures.Capabilities.run_forever_unless_a_subtrait_covers_its_supertrait;
      expect_one_diagnostic
        Fixtures.Capabilities.run_forever_unless_a_supertrait_does_not_cover_its_subtrait
        "capabilities.not_available" ~says:"This call uses `RunForever unless Items: Short`");
  Harness.test "a time clause's condition implies RunForever's through a supertrait" (fun () ->
      expect_fine Fixtures.Capabilities.time_when_a_subtrait;
      expect_one_diagnostic Fixtures.Capabilities.time_when_an_unrelated_condition
        "types.unbounded_time" ~says:"`when` a condition that implies `Source: FiniteCursor`"
        ~fixed:Fixtures.Capabilities.time_when_an_unrelated_condition_fixed;
      expect_fine Fixtures.Capabilities.time_when_an_unrelated_condition_fixed);
  Harness.test "a call of a function that panics unless a condition on values needs no `Panic`"
    (fun () ->
      expect_fine Fixtures.Capabilities.call_of_a_function_that_panics_unless_a_condition_on_values);
  Harness.test "a function value of a function that panics unless a condition uses `Panic`"
    (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities.function_value_of_a_function_that_panics_unless_a_condition_on_values
        "capabilities.not_available" ~says:"This call uses `Panic`");
  Harness.test "a call through `any` of a method that panics unless a condition uses `Panic`"
    (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities.call_through_any_of_a_method_that_panics_unless_a_condition_on_values
        "capabilities.not_available" ~says:"This call uses `Panic`");
  Harness.test "a bound names the time of no callback that may run forever" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.time_of_a_callback_that_runs_forever
        "types.unbounded_time"
        ~says:
          "`work` may run forever, since its type uses `RunForever`, so `time(work)` has no value."
        ~at:("time(work)", 1))

let () =
  let spawning = Fixtures.Infer.tally ^ Fixtures.Capabilities.spawning_cursor in
  Harness.test
    "a monitor needs `Tasks` where its body uses `Tasks` through the `next` of a cursor, pulled by \
     a loop or called" (fun () ->
      expect_one_diagnostic
        (spawning
       ^ Fixtures.Capabilities.spawning_cursor_pulled_under_a_tally_provided_without_tasks)
        "capabilities.monitor_needs_tasks" ~at:("mut tally {", 1);
      expect_one_diagnostic
        (spawning
       ^ Fixtures.Capabilities.next_of_a_spawning_cursor_called_under_a_tally_provided_without_tasks
        )
        "capabilities.monitor_needs_tasks" ~at:("mut tally {", 1));
  Harness.test
    "a monitor that is provided with `Tasks` holds a cursor whose `next` uses `Tasks`, pulled by a \
     loop or called" (fun () ->
      expect_fine
        (spawning ^ Fixtures.Capabilities.spawning_cursor_under_a_tally_provided_with_tasks))

let () =
  let make_standard_packages files : Project.package list =
    [
      {
        name = Path.standard_package;
        dependencies = [];
        files = List.map (fun (name, text) -> (Support.parse_file name, text)) files;
      };
    ]
  in
  let check_in_standard packages =
    Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
      (Support.extend_standard_library packages)
  in
  let expect_one_in_standard =
    Support.expect_one_diagnostic ~setup:make_standard_packages ~file:"standard.probe"
      ~check:check_in_standard
  in
  let expect_fine_in_standard text =
    match
      check_in_standard
        (make_standard_packages [ ("standard.probe", text) ])
        (Support.parse_file "standard.probe")
    with
    | [] -> ()
    | reported -> Harness.fail "found [%s]" (String.concat "; " (Support.list_codes reported))
  in
  Harness.test "a call of an intrinsic needs the capabilities that the intrinsic uses" (fun () ->
      expect_one_in_standard Fixtures.Capabilities.shared_count_updated_without_tasks
        "capabilities.not_available"
        ~says:"This call uses `Tasks`, which is not available here. Declare it with `uses Tasks`"
        ~at:("intrinsic.shared_update", 1);
      expect_fine_in_standard Fixtures.Capabilities.shared_count_updated_using_tasks);
  Harness.test
    "a call of an intrinsic that reaches the operating system needs `System`, which nothing can \
     provide" (fun () ->
      expect_one_in_standard Fixtures.Capabilities.error_number_read_without_system
        "capabilities.not_available"
        ~says:"This call uses `System`, which is not available here. Declare it with `uses System`."
        ~at:("intrinsic.libc_errno", 1);
      expect_fine_in_standard Fixtures.Capabilities.error_number_read_using_system);
  Harness.test "the runtime does not grant `System` to a test" (fun () ->
      expect_one_in_standard Fixtures.Capabilities.test_using_system "types.no_real_implementation"
        ~says:
          "The runtime grants `System` only to the real implementations of the standard \
           capabilities, so it cannot provide it to a test.");
  Harness.test
    "a capability implemented by a monitor may take a callback that uses only `System`, since no \
     `provide` implements it" (fun () ->
      expect_fine_in_standard Fixtures.Capabilities.monitor_table_with_callbacks_that_use_system);
  Harness.test
    "an implementation of a capability that reaches the operating system declares `System`"
    (fun () ->
      expect_one_in_standard
        Fixtures.Capabilities.error_number_read_by_an_implementation_of_a_capability
        "capabilities.not_available" ~says:"This call uses `System`" ~at:("intrinsic.libc_errno", 1));
  Harness.test "nothing can implement `System`" (fun () ->
      expect_one_in_standard Fixtures.Capabilities.system_implemented
        "types.implements_built_in_capability" ~says:"Nothing can implement `System`");
  Harness.test
    "an implementation of a capability calls an intrinsic without the capabilities that the \
     intrinsic uses" (fun () ->
      expect_fine_in_standard
        Fixtures.Capabilities.shared_count_updated_by_an_implementation_of_a_capability);
  Harness.test
    "an intrinsic named as a value has a function type that uses the capabilities of the intrinsic"
    (fun () ->
      expect_one_in_standard
        Fixtures.Capabilities.shared_key_named_as_a_value_of_a_type_without_uses "types.mismatch"
        ~says:"found `(fn(Shared[Int64]) -> UInt64 uses Tasks)`" ~at:("intrinsic.shared_key", 1));
  Harness.test "a monitor needs `Tasks` where its body calls an intrinsic that uses `Tasks`"
    (fun () ->
      expect_one_in_standard
        ("use standard.intrinsic\n\n" ^ Fixtures.Infer.tally
       ^ Fixtures.Capabilities.shared_count_updated_under_a_tally_provided_without_tasks)
        "capabilities.monitor_needs_tasks" ~at:("mut tally {", 1))
