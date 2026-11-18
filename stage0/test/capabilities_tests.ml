let check packages =
  Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
    (Support.make_database packages)

let expect_one_diagnostic = Support.expect_one_diagnostic ~check
let expect_fine text = Support.expect_no_diagnostics ~check [ ("app::main", text) ]

let list_core_expressions text ~of_function =
  let module_ = Support.parse_module "app::main" in
  (Support.collect_core_nodes
     (Support.setup [ ("app::main", text) ])
     { module_; path = Top { module_; name = of_function }; ordinal = 0 })
    .expressions

let expect_not_available text ~message =
  match check (Support.setup [ ("app::main", text) ]) (Support.parse_file "app::main") with
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
      | [ [ [ { capability; impl = Impl _; arguments = { arguments = [ (_, Type tag) ]; _ } } ] ] ]
        when Path.equal capability (Support.make_top_path "standard::capabilities" "Clock")
             && Types.show tag = "Bool" ->
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
  Harness.test "a parallel branch has only Panic" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.clock_call_in_a_parallel_branch
        "capabilities.not_available");
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
  Harness.test "a test has Panic" (fun () -> expect_fine Fixtures.Capabilities.test_calling_panic);
  Harness.test "a place whose implementation mutates state is provided mut" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.counter_provided_as_tally
        "capabilities.provide_mode")

let () =
  Harness.test "a dependency can use only the capabilities that it is granted" (fun () ->
      let packages =
        Support.setup
          [
            ("app::main", Fixtures.Capabilities.call_of_a_dependencys_stamp);
            ("clock_library::time", Fixtures.Capabilities.time_stamp_using_clock);
          ]
      in
      let packages =
        Support.with_dependencies packages { owner = None; name = "app" }
          [ { package = { owner = None; name = "clock_library" }; capabilities = [] } ]
      in
      match Support.list_codes (check packages (Support.parse_file "app::main")) with
      | [ "capabilities.not_granted" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual))

let () =
  let with_grant files granted =
    let packages =
      Support.with_dependencies (Support.setup files) { owner = None; name = "app" }
        [ { package = { owner = None; name = "clock_library" }; capabilities = granted } ]
    in
    Support.list_codes (check packages (Support.parse_file "app::main"))
  in
  let library = ("clock_library::time", Fixtures.Capabilities.library_time) in
  Harness.test "a dependency's trait method can use only the granted capabilities" (fun () ->
      match with_grant [ ("app::main", Fixtures.Capabilities.wall_stamp_call); library ] [] with
      | "capabilities.not_granted" :: _ -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "a dependency's trait method can use a granted capability" (fun () ->
      match
        with_grant [ ("app::main", Fixtures.Capabilities.wall_stamp_call); library ] [ "Clock" ]
      with
      | [] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "providing a dependency's type checks the grants for the capabilities of its impls"
    (fun () ->
      match
        with_grant
          [ ("app::main", Fixtures.Capabilities.provide_of_a_dependencys_fixed_clock); library ]
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
  (packages, Support.list_codes (check packages (Support.parse_file "app::main")))

let expect_codes ~expected (_, actual) =
  if actual <> expected then
    Harness.fail "found [%s], expected [%s]" (String.concat "; " actual)
      (String.concat "; " expected)

let time = ("clock_library::time", Fixtures.Capabilities.time_stamp_using_clock)
let sources = ("framework::sources", Fixtures.Capabilities.sources_sources)
let timers = ("plugins::timers", Fixtures.Capabilities.timers_timers)

let () =
  let value = ("app::main", Fixtures.Capabilities.dependencys_function_as_a_value) in
  Harness.test "a function value of a dependency's function can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (list_codes_with_grants [ value; time ] [ ({ owner = None; name = "clock_library" }, []) ]));
  Harness.test "a function value of a dependency's function can use a granted capability" (fun () ->
      expect_codes ~expected:[]
        (list_codes_with_grants [ value; time ]
           [ ({ owner = None; name = "clock_library" }, [ "Clock" ]) ]));
  let bound = ("app::main", Fixtures.Capabilities.bound) in
  Harness.test
    "an impl of a dependency that satisfies a bound can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (list_codes_with_grants [ bound; sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ "Clock" ]);
             ({ owner = None; name = "plugins" }, []);
           ]));
  Harness.test "an impl of a dependency that satisfies a bound can use a granted capability"
    (fun () ->
      expect_codes ~expected:[]
        (list_codes_with_grants [ bound; sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ "Clock" ]);
             ({ owner = None; name = "plugins" }, [ "Clock" ]);
           ]));
  Harness.test "an impl of a dependency behind an `any` value can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (list_codes_with_grants
           [ ("app::main", Fixtures.Capabilities.any_timer_from_plugins); sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ "Clock" ]);
             ({ owner = None; name = "plugins" }, []);
           ]))

let ledger = ("store::ledger", Fixtures.Capabilities.ledger_ledger)
let pays = ("app::main", Fixtures.Capabilities.pays)

let list_problems packages =
  let app : Path.package = { owner = None; name = "app" } in
  let database = Support.make_database packages in
  Database.check database [ app ];
  Database.list_manifest_problems database app

let () =
  Harness.test "a grant names a capability outside the prelude by its full path" (fun () ->
      expect_codes ~expected:[]
        (list_codes_with_grants [ pays; ledger ]
           [ ({ owner = None; name = "store" }, [ "store::ledger::Ledger" ]) ]));
  Harness.test "a capability's name alone grants only one of the prelude" (fun () ->
      let packages, actual =
        list_codes_with_grants [ pays; ledger ] [ ({ owner = None; name = "store" }, [ "Ledger" ]) ]
      in
      expect_codes ~expected:[ "capabilities.not_granted" ] (packages, actual);
      match list_problems packages with
      | [ Not_a_capability { dependency = { Path.owner = None; name = "store" }; name = "Ledger" } ]
        ->
          ()
      | _ -> Harness.fail "the grant is not reported");
  Harness.test "a grant covers only the capabilities it names" (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (list_codes_with_grants [ pays; ledger ]
           [ ({ Path.owner = None; name = "store" }, [ "Clock" ]) ]))

let () =
  Harness.test "a dependency that nothing in the package names is reported" (fun () ->
      let packages, _ =
        list_codes_with_grants
          [ ("app::main", Fixtures.Capabilities.function_returning_one); time ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      match list_problems packages with
      | [ Unused_dependency { Path.owner = None; name = "clock_library" } ] -> ()
      | _ -> Harness.fail "not reported");
  Harness.test "a dependency named in a path is used" (fun () ->
      let packages, _ =
        list_codes_with_grants [ pays; ledger ]
          [ ({ Path.owner = None; name = "store" }, [ "store::ledger::Ledger" ]) ]
      in
      if list_problems packages <> [] then Harness.fail "reported");
  Harness.test "a dependency whose trait's method is called with a dot is used" (fun () ->
      let packages, actual =
        list_codes_with_grants
          [
            ("app::main", Fixtures.Capabilities.call_of_doubled);
            ("shapes::sizes", Fixtures.Capabilities.doubled_trait_for_int64);
          ]
          [ ({ Path.owner = None; name = "shapes" }, []) ]
      in
      expect_codes ~expected:[] (packages, actual);
      if list_problems packages <> [] then Harness.fail "reported");
  Harness.test "an unused dependency is reported for every kind of definition in the package"
    (fun () ->
      let packages, actual =
        list_codes_with_grants
          [ ("app::main", Fixtures.Capabilities.package_of_every_kind_of_definition); time ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      expect_codes ~expected:[] (packages, actual);
      match list_problems packages with
      | [ Unused_dependency { Path.owner = None; name = "clock_library" } ] -> ()
      | _ -> Harness.fail "not reported");
  Harness.test "an unused dependency is not reported for a package with an error" (fun () ->
      let packages, _ =
        list_codes_with_grants
          [ ("app::main", Fixtures.Capabilities.function_returning_true_as_int64); time ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      if list_problems packages <> [] then Harness.fail "reported");
  Harness.test "a dependency that only a test uses is left out of the code's packages" (fun () ->
      let shapes : Path.package = { owner = None; name = "shapes" }
      and limits : Path.package = { owner = None; name = "limits" } in
      let packages, actual =
        list_codes_with_grants
          [
            ("app::main", Fixtures.Capabilities.doubling_with_a_test_of_bounds);
            ("shapes::sizes", Fixtures.Capabilities.doubled_trait_for_int64);
            ("limits::bounds", Fixtures.Capabilities.bounds_most);
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
  Harness.test "a function that may not terminate is not bound as one that terminates" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.forever_bound_as_finite "types.mismatch");
  Harness.test "a function that promises to end can be bound as one that does" (fun () ->
      expect_fine Fixtures.Capabilities.quick_bound_as_finite);
  Harness.test "function types inside a type must promise the same costs" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.list_of_actions_gaining_a_cost "types.mismatch")

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
      expect_fine (feed ^ Fixtures.Capabilities.drain_of_a_counter));
  Harness.test "a call needs the capabilities of the set that the impl defines" (fun () ->
      expect_one_diagnostic
        (feed ^ Fixtures.Capabilities.drain_of_a_gauge_without_uses)
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
  let apply = Fixtures.Capabilities.apply_bounded_by_the_time_of_change in
  let both = Fixtures.Capabilities.both_bounded_by_the_times_of_first_and_second in
  Harness.test "a function with a time clause cannot call one without" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.function_with_time_calling_forever
        "capabilities.may_not_terminate");
  Harness.test "a call that passes a function without a time clause may not terminate" (fun () ->
      expect_one_diagnostic
        (apply ^ Fixtures.Capabilities.apply_of_slow_under_a_time_clause)
        "capabilities.may_not_terminate"
        ~says:
          "This call may not terminate, since `app::main::slow`, passed for `change`, has no \
           `time` clause, and this function has a `time` clause.");
  Harness.test "a lambda that calls a function without a time clause may not terminate" (fun () ->
      expect_one_diagnostic
        (apply ^ Fixtures.Capabilities.apply_of_a_lambda_calling_slow_under_a_time_clause)
        "capabilities.may_not_terminate"
        ~notes:
          [
            ( "This call may not terminate, since `app::main::slow` has no `time` clause.",
              ("slow(inner)", 1) );
          ]);
  Harness.test "a call that passes a lambda cites each lambda down to a cause that is not a lambda"
    (fun () ->
      expect_one_diagnostic
        (apply
       ^ Fixtures.Capabilities.apply_of_a_lambda_applying_a_lambda_calling_slow_under_a_time_clause
        )
        "capabilities.may_not_terminate"
        ~notes:
          [
            ( "This call may not terminate, since the lambda passed for `change` may not.",
              ("apply(outer", 1) );
            ( "This call may not terminate, since `app::main::slow` has no `time` clause.",
              ("slow(inner)", 1) );
          ]);
  Harness.test "a call that passes a lambda cites the first cause in the lambda" (fun () ->
      expect_one_diagnostic
        (apply
       ^ Fixtures.Capabilities.apply_of_a_lambda_looping_then_calling_slow_under_a_time_clause)
        "capabilities.may_not_terminate"
        ~notes:
          [
            ( "This loop may not terminate, since it has no measure. Give the loop a `decreases` \
               clause.",
              ("while", 1) );
          ]);
  Harness.test "a call that passes a lambda cites a cause in a `parallel` branch of the lambda"
    (fun () ->
      expect_one_diagnostic
        (apply
       ^ Fixtures.Capabilities.apply_of_a_lambda_looping_in_a_parallel_branch_under_a_time_clause)
        "capabilities.may_not_terminate"
        ~notes:
          [
            ( "This loop may not terminate, since it has no measure. Give the loop a `decreases` \
               clause.",
              ("while", 1) );
          ]);
  Harness.test
    "a call that passes a lambda cites no call of a callback that the enclosing function's time \
     clause follows" (fun () ->
      expect_one_diagnostic
        (apply
       ^ Fixtures.Capabilities.apply_of_a_lambda_calling_the_enclosing_functions_callback_then_slow
        )
        "capabilities.may_not_terminate"
        ~notes:
          [
            ( "This call may not terminate, since `app::main::slow` has no `time` clause.",
              ("slow(run", 1) );
          ]);
  Harness.test "a call names the lambda that may not terminate among the lambdas it passes"
    (fun () ->
      expect_one_diagnostic
        (apply ^ both
       ^ Fixtures.Capabilities.both_of_a_lambda_that_terminates_and_a_lambda_calling_slow)
        "capabilities.may_not_terminate" ~says:"since the lambda passed for `second` may not"
        ~notes:
          [
            ( "This call may not terminate, since `app::main::slow` has no `time` clause.",
              ("slow(inner)", 1) );
          ]);
  Harness.test "a call names no callback that the enclosing function's time clause follows"
    (fun () ->
      expect_one_diagnostic
        (apply ^ both ^ Fixtures.Capabilities.both_of_the_enclosing_functions_callback_and_slow)
        "capabilities.may_not_terminate"
        ~says:"since `app::main::slow`, passed for `second`, has no `time` clause");
  Harness.test "a `finite` function cannot call a callback whose type has no time clause" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.finite_function_calling_a_callback_without_time
        "capabilities.may_not_terminate");
  Harness.test "a function type with a time clause takes only functions that terminate" (fun () ->
      expect_one_diagnostic
        (apply ^ Fixtures.Capabilities.slow_passed_as_a_function_that_terminates)
        "types.mismatch");
  Harness.test "a trait method's callback with a time clause takes only functions that terminate"
    (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.spread_passed_to_flat_map "types.mismatch");
  Harness.test "a function of linear time is not passed as one of constant time" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.linear_spin_passed_as_constant_time
        "types.mismatch");
  Harness.test "a bound names the time of a callback only if the callback can terminate" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.time_of_a_callback_without_a_capability_parameter
        "types.unbounded_time");
  Harness.test "a specification calls only functions that terminate" (fun () ->
      expect_one_diagnostic
        (apply ^ Fixtures.Capabilities.ensures_calling_slow)
        "capabilities.may_not_terminate");
  Harness.test "a capability's implementation terminates when the capability's method does"
    (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.spinner_calling_a_function_without_time
        "capabilities.may_not_terminate");
  Harness.test "an impl of `From` makes no call that may not terminate" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.from_impl_calling_a_function_without_time
        "capabilities.may_not_terminate");
  Harness.test "an impl's time clause follows no callback that its trait's does not" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.visit_impl_naming_the_time_of_its_callback
        "types.impl_uses")

let () =
  let apply = Fixtures.Capabilities.apply_bounded_by_the_time_of_change in
  Harness.test "a function with a time clause holds no `while` loop without a measure" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.while_loop_without_a_measure_under_a_time_clause
        "capabilities.may_not_terminate"
        ~says:
          "This loop may not terminate, since it has no measure, and this function has a `time` \
           clause. Give the loop a `decreases` clause."
        ~at:("while", 1));
  Harness.test "a `while` condition that passes an argument mut gives its loop no measure"
    (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.while_loop_taking_a_count_under_a_time_clause
        "capabilities.may_not_terminate" ~says:"since it has no measure" ~at:("while", 1));
  Harness.test "a function with a time clause holds no loop over a cursor without a measure"
    (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.countdown_cursor_loop_under_a_time_clause
        "capabilities.may_not_terminate"
        ~says:
          "This loop may not terminate, since `Countdown` has no `remaining(self) -> UInt64` \
           method to give the loop a measure, and this function has a `time` clause. Give the loop \
           a `decreases` clause."
        ~at:("for value", 1));
  Harness.test "a function without a time clause holds loops without a measure" (fun () ->
      expect_fine Fixtures.Capabilities.loops_without_a_measure_and_without_a_time_clause);
  Harness.test "a parallel branch holds a loop without a measure where its function does" (fun () ->
      expect_fine Fixtures.Capabilities.while_loop_without_a_measure_in_a_parallel_branch;
      expect_one_diagnostic
        Fixtures.Capabilities.while_loop_without_a_measure_in_a_parallel_branch_under_a_time_clause
        "capabilities.may_not_terminate" ~at:("while", 1));
  Harness.test "a lambda that holds a loop without a measure may not terminate" (fun () ->
      let text = apply ^ Fixtures.Capabilities.apply_of_a_lambda_looping_without_a_measure in
      expect_fine text;
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match (node.kind, node.type_) with
            | Lambda _, Function { uses; _ } -> Some (Types.terminates uses)
            | Call { callee = Function { path; _ }; uses; _ }, _
              when Path.equal path (Support.make_top_path "app::main" "apply") ->
                Some (Types.terminates uses)
            | _ -> None)
          (list_core_expressions text ~of_function:"f")
      with
      | [ false; false ] -> ()
      | _ -> Harness.fail "the lambda or the call that passes it terminates");
  Harness.test
    "a call that passes a lambda with a loop without a measure may not terminate under a time \
     clause" (fun () ->
      expect_one_diagnostic
        (apply
       ^ Fixtures.Capabilities.apply_of_a_lambda_looping_without_a_measure_under_a_time_clause)
        "capabilities.may_not_terminate"
        ~says:
          "This call may not terminate, since the lambda passed for `change` may not, and this \
           function has a `time` clause."
        ~at:("apply(value,", 1)
        ~notes:
          [
            ( "This loop may not terminate, since it has no measure. Give the loop a `decreases` \
               clause.",
              ("while", 1) );
          ]);
  Harness.test "a lambda whose function type has a time clause holds no loop without a measure"
    (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.lambda_looping_without_a_measure_passed_as_finite
        "capabilities.may_not_terminate"
        ~says:
          "This loop may not terminate, since it has no measure, and the function type that this \
           lambda is passed as promises that the lambda terminates. Give the loop a `decreases` \
           clause."
        ~at:("while", 1))

let () =
  Harness.test
    "a function type that names a capability parameter takes no lambda that may not terminate by \
     itself" (fun () ->
      expect_one_diagnostic
        Fixtures.Capabilities.lambda_looping_without_a_measure_bound_as_using_a_capability_parameter
        "capabilities.may_not_terminate"
        ~says:
          "This loop may not terminate, since it has no measure, and the function type that this \
           lambda is passed as takes only a function that terminates if the functions passed for \
           `generic Mine` do. Give the loop a `decreases` clause."
        ~at:("while", 1);
      expect_one_diagnostic
        Fixtures.Capabilities.lambda_calling_slow_bound_as_using_a_capability_parameter
        "capabilities.may_not_terminate"
        ~says:
          "This call may not terminate, since `app::main::slow` has no `time` clause, and the \
           function type that this lambda is passed as takes only a function that terminates if \
           the functions passed for `generic Mine` do."
        ~at:("slow()", 2));
  Harness.test
    "a function type that names a capability parameter takes no named function that may not \
     terminate" (fun () ->
      expect_one_diagnostic Fixtures.Capabilities.forever_bound_as_using_a_capability_parameter
        "types.mismatch"
        ~says:"Expected `(fn() uses generic Mine)`, found `fn()`, which may not terminate."
        ~at:("forever", 2));
  Harness.test
    "a function type that names a capability parameter takes a lambda that calls a callback of \
     that parameter" (fun () ->
      expect_fine
        Fixtures.Capabilities
        .lambda_calling_the_enclosing_functions_callback_bound_as_using_a_capability_parameter);
  Harness.test
    "a call infers its callee's capability parameter from a lambda that uses the caller's \
     capability parameter and may not terminate" (fun () ->
      let text =
        ticks
        ^ Fixtures.Capabilities
          .each_time_of_a_lambda_calling_the_enclosing_functions_callback_then_looping
      in
      expect_fine text;
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match (node.kind, node.type_) with
            | Lambda _, Function { uses; _ } -> Some (uses :> Types.capability list)
            | _ -> None)
          (list_core_expressions text ~of_function:"run")
      with
      | [ [ Capability_parameter { name = "Mine"; _ }; Divergence Always ] ] -> ()
      | _ ->
          Harness.fail "the lambda's type does not hold `Mine` and unconditional divergence alone");
  Harness.test
    "a binding without a type holds a function that uses a capability parameter and may not \
     terminate" (fun () ->
      expect_fine
        (later
       ^ Fixtures.Capabilities
         .later_of_a_lambda_calling_the_enclosing_functions_callback_then_looping_bound_without_a_type
        ));
  Harness.test
    "a function type without `uses` and without a time clause takes a lambda that may not terminate"
    (fun () ->
      expect_fine
        Fixtures.Capabilities.lambda_looping_without_a_measure_bound_as_using_no_capability)
