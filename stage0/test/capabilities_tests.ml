(* The tests of capabilities: what code may call, lambdas' uses,
   capability parameters, provide, and dependency grants. *)

open Harness
open Support

let check database module_ =
  Resolve.diagnostics database module_
  @ Interface.diagnostics database module_
  @ Infer.diagnostics database module_

let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]

let () =
  test "a capability call needs its capability" (fun () ->
      one_diagnostic "fn f() -> Instant {\n  Clock.now()\n}\n" "capabilities.not_available");
  test "a function that declares a capability may call it" (fun () ->
      fine "fn f() -> Instant\n  uses Clock\n{\n  Clock.now()\n}\n");
  test "a call to a function with uses needs its capabilities" (fun () ->
      one_diagnostic
        "fn stamp() -> Instant\n\
        \  uses Clock\n\
         {\n\
        \  Clock.now()\n\
         }\n\n\
         fn f() -> Instant {\n\
        \  stamp()\n\
         }\n"
        "capabilities.not_available");
  test "provide makes a capability available in its block" (fun () ->
      fine
        "type FixedClock(time: Instant)\n\n\
         impl Clock for FixedClock {\n\
        \  fn now(self) -> Instant { self.time }\n\
        \  fn monotonic(self) -> Duration { todo }\n\
        \  fn sleep(self, duration: Duration) {}\n\
         }\n\n\
         fn stamp() -> Instant\n\
        \  uses Clock\n\
         {\n\
        \  Clock.now()\n\
         }\n\n\
         fn f() -> Instant {\n\
        \  provide FixedClock(time: Instant.epoch) {\n\
        \    stamp()\n\
        \  }\n\
         }\n");
  test "provide records each capability's impl with its generic arguments" (fun () ->
      let text =
        "type Fixed[Tag](time: Instant, tag: Tag)\n\n\
         impl Clock for Fixed[Tag] {\n\
        \  fn now(self) -> Instant { self.time }\n\
        \  fn monotonic(self) -> Duration { todo }\n\
        \  fn sleep(self, duration: Duration) {}\n\
         }\n\n\
         fn f() -> Instant {\n\
        \  provide Fixed(time: Instant.epoch, tag: true) {\n\
        \    Clock.now()\n\
        \  }\n\
         }\n"
      in
      let database = setup [ ("app::main", text) ] in
      let key : Resolve.Names.key =
        {
          module_ = module_of "app::main";
          path = Top { module_ = module_of "app::main"; name = "f" };
          ordinal = 0;
        }
      in
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
          (core_nodes database key).expressions
      with
      | [ [ [ { capability; impl = Impl _; arguments = [ (_, Type tag) ] } ] ] ]
        when Path.show capability = "standard::capabilities::Clock" && Types.show tag = "Bool" ->
          ()
      | _ -> fail "not recorded");
  test "a specification may not use Panic" (fun () ->
      one_diagnostic
        "fn checked() -> Bool\n\
        \  uses Panic\n\
        \  cost time finite\n\
         {\n\
        \  todo\n\
         }\n\n\
         fn f()\n\
        \  requires checked()\n\
         {\n\
         }\n"
        "capabilities.not_available");
  test "a specification cannot use the function's capabilities" (fun () ->
      one_diagnostic
        "fn stamp() -> Bool\n\
        \  uses Clock\n\
        \  cost time finite\n\
         {\n\
        \  todo\n\
         }\n\n\
         fn f()\n\
        \  uses Clock\n\
        \  requires stamp()\n\
         {\n\
         }\n"
        "capabilities.not_available");
  test "a loop invariant cannot use the function's capabilities" (fun () ->
      one_diagnostic
        "fn stamp() -> Bool\n\
        \  uses Clock\n\
        \  cost time finite\n\
         {\n\
        \  todo\n\
         }\n\n\
         fn f()\n\
        \  uses Clock\n\
         {\n\
        \  var count = 0\n\
        \  while count < 3\n\
        \    invariant stamp()\n\
        \  {\n\
        \    count += 1\n\
        \  }\n\
         }\n"
        "capabilities.not_available");
  test "a type's invariant may use no capability" (fun () ->
      one_diagnostic
        "fn stamp() -> Bool\n\
        \  uses Clock\n\
        \  cost time finite\n\
         {\n\
        \  todo\n\
         }\n\n\
         type Counted(count: Int64)\n\
        \  invariant stamp()\n"
        "capabilities.not_available");
  test "a law may use no capability" (fun () ->
      one_diagnostic
        "fn stamp() -> Bool\n\
        \  uses Clock\n\
        \  cost time finite\n\
         {\n\
        \  todo\n\
         }\n\n\
         trait Steady {\n\
        \  fn value(self) -> Int64\n\n\
        \  law timeless(first: Self) {\n\
        \    stamp()\n\
        \  }\n\
         }\n"
        "capabilities.not_available");
  test "a parallel branch has only Panic" (fun () ->
      one_diagnostic
        "fn f() -> Instant\n\
        \  uses Clock\n\
         {\n\
        \  parallel {\n\
        \    let now = Clock.now()\n\
        \  }\n\
        \  now\n\
         }\n"
        "capabilities.not_available");
  test "a lambda's uses must fit the function type it is passed as" (fun () ->
      one_diagnostic
        "fn apply(visit: fn(Int64) -> Int64) {}\n\n\
         fn f()\n\
        \  uses Clock\n\
         {\n\
        \  apply(fn(value) {\n\
        \    let _ = Clock.now()\n\
        \    value\n\
        \  })\n\
         }\n"
        "capabilities.lambda_uses");
  test "a loop over a value needs the capabilities that its `each` uses" (fun () ->
      one_diagnostic
        "type Ticker()\n\n\
         fn Ticker.each(self) yields Instant\n\
        \  uses Clock\n\
         {\n\
        \  yield Clock.now()\n\
         }\n\n\
         fn f(ticker: Ticker) {\n\
        \  for tick in ticker {\n\
        \    let _ = tick\n\
        \  }\n\
         }\n"
        "capabilities.not_available");
  test "a loop over a value can use the function's capabilities" (fun () ->
      fine
        "type Ticker()\n\n\
         fn Ticker.each(self) yields Instant\n\
        \  uses Clock\n\
         {\n\
        \  yield Clock.now()\n\
         }\n\n\
         fn f(ticker: Ticker)\n\
        \  uses Clock\n\
         {\n\
        \  for tick in ticker {\n\
        \    let _ = tick\n\
        \  }\n\
         }\n");
  test "a capability parameter is instantiated with the capabilities of the lambdas passed for it"
    (fun () ->
      fine
        "fn for_each[capability Granted](count: Int64, visit: (fn(Int64) uses Granted))\n\
        \  uses Granted\n\
         {\n\
        \  todo\n\
         }\n\n\
         fn f()\n\
        \  uses Clock\n\
         {\n\
        \  for_each(3, visit: fn(value) {\n\
        \    let _ = Clock.now()\n\
        \    let _ = value\n\
        \  })\n\
         }\n");
  test "a trait's method solves its capability parameter as a function does" (fun () ->
      let visitor =
        "trait Visitor {\n\
        \  fn visit_all[capability Granted](self, visit: (fn(Int64) uses Granted))\n\
        \    uses Granted\n\
         }\n\n\
         type Numbers(items: List[Int64])\n\n\
         impl Visitor for Numbers {\n\
        \  fn visit_all[capability Granted](self, visit: (fn(Int64) uses Granted))\n\
        \    uses Granted\n\
        \  {\n\
        \    todo\n\
        \  }\n\
         }\n\n"
      in
      let call =
        "{\n  numbers.visit_all(fn(value) {\n    let _ = Clock.now()\n    let _ = value\n  })\n}\n"
      in
      fine (visitor ^ "fn f(numbers: Numbers)\n  uses Clock\n" ^ call);
      one_diagnostic (visitor ^ "fn f(numbers: Numbers)\n" ^ call) "capabilities.not_available");
  test "a capability parameter's set must be available at the call" (fun () ->
      one_diagnostic
        "fn for_each[capability Granted](count: Int64, visit: (fn(Int64) uses Granted))\n\
        \  uses Granted\n\
         {\n\
        \  todo\n\
         }\n\n\
         fn f() {\n\
        \  for_each(3, visit: fn(value) {\n\
        \    let _ = Clock.now()\n\
        \    let _ = value\n\
        \  })\n\
         }\n"
        "capabilities.not_available");
  test "a test has Panic" (fun () ->
      fine "test \"crashes are allowed\" {\n  Panic.crash(\"no\")\n}\n");
  test "a place whose implementation changes state is provided mut" (fun () ->
      one_diagnostic
        "type Counter(count: Int64)\n\n\
         capability Tally {\n\
        \  fn add()\n\
         }\n\n\
         impl Tally for Counter {\n\
        \  fn add(mut self) { self.count += 1 }\n\
         }\n\n\
         fn f() {\n\
        \  var counter = Counter(count: 0)\n\
        \  provide counter {\n\
        \  }\n\
        \  let _ = counter\n\
         }\n"
        "capabilities.provide_mark")

let () =
  test "a dependency can use only the capabilities that it is granted" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "use clock_library::time\n\nfn f() -> Instant\n  uses Clock\n{\n  time::stamp()\n}\n"
            );
            ( "clock_library::time",
              "public fn stamp() -> Instant\n  uses Clock\n{\n  Clock.now()\n}\n" );
          ]
      in
      Database.Testing.set_manifest (Engine.of_context database) ~name:"app"
        ~dependencies:[ { package = "clock_library"; capabilities = [] } ];
      match codes (check database (module_of "app::main")) with
      | [ "capabilities.not_granted" ] -> ()
      | found -> fail "found [%s]" (String.concat "; " found))

let () =
  let with_grant files granted =
    let database = setup files in
    Database.Testing.set_manifest (Engine.of_context database) ~name:"app"
      ~dependencies:[ { package = "clock_library"; capabilities = granted } ];
    codes (check database (module_of "app::main"))
  in
  let library =
    ( "clock_library::time",
      "public trait Stamper {\n\
      \  fn stamp(self) -> Instant\n\
      \    uses Clock\n\
       }\n\n\
       public type Wall()\n\n\
       impl Stamper for Wall {\n\
      \  fn stamp(self) -> Instant\n\
      \    uses Clock\n\
      \  {\n\
      \    Clock.now()\n\
      \  }\n\
       }\n\n\
       public type Fixed()\n\n\
       impl Random for Fixed uses Clock {\n\
      \  fn next(self) -> UInt64 {\n\
      \    let _ = Clock.now()\n\
      \    4\n\
      \  }\n\
       }\n" )
  in
  test "a dependency's trait method can use only the granted capabilities" (fun () ->
      match
        with_grant
          [
            ( "app::main",
              "use clock_library::time\n\n\
               fn f(wall: time::Wall) -> Instant\n\
              \  uses Clock\n\
               {\n\
              \  wall.stamp()\n\
               }\n" );
            library;
          ]
          []
      with
      | "capabilities.not_granted" :: _ -> ()
      | found -> fail "found [%s]" (String.concat "; " found));
  test "a dependency's trait method can use a granted capability" (fun () ->
      match
        with_grant
          [
            ( "app::main",
              "use clock_library::time\n\n\
               fn f(wall: time::Wall) -> Instant\n\
              \  uses Clock\n\
               {\n\
              \  wall.stamp()\n\
               }\n" );
            library;
          ]
          [ "Clock" ]
      with
      | [] -> ()
      | found -> fail "found [%s]" (String.concat "; " found));
  test "providing a dependency's type checks the grants for the capabilities of its impls"
    (fun () ->
      match
        with_grant
          [
            ( "app::main",
              "use clock_library::time\n\n\
               fn f() -> UInt64\n\
              \  uses Clock\n\
               {\n\
              \  provide time::Fixed() {\n\
              \    Random.next()\n\
              \  }\n\
               }\n" );
            library;
          ]
          []
      with
      | [ "capabilities.not_granted" ] -> ()
      | found -> fail "found [%s]" (String.concat "; " found))

let () =
  test "an implementation of a capability may not call the capability directly" (fun () ->
      one_diagnostic
        "capability Notes {\n\
        \  fn note(text: StringSlice)\n\
         }\n\n\
         type Loud()\n\n\
         impl Notes for Loud {\n\
        \  fn note(self, text: StringSlice) {\n\
        \    Notes.note(text)\n\
        \  }\n\
         }\n"
        "capabilities.not_available");
  test "an implementation of a capability may hand the capability to a function value" (fun () ->
      fine
        "capability Notes {\n\
        \  fn note(text: StringSlice)\n\
        \  fn within(work: (fn() uses Notes))\n\
         }\n\n\
         type Quiet()\n\n\
         impl Notes for Quiet {\n\
        \  fn note(self, text: StringSlice) {}\n\
        \  fn within(self, work: (fn() uses Notes)) {\n\
        \    work()\n\
        \  }\n\
         }\n")

(* A grant wherever a dependency's code is named *)

(* The codes of [app::main], whose manifest lists the dependencies given,
   each with what it is granted. *)
let codes_with_grants files grants =
  let database = setup files in
  Database.Testing.set_manifest (Engine.of_context database) ~name:"app"
    ~dependencies:
      (List.map (fun (package, capabilities) -> { Workspace.package; capabilities }) grants);
  (database, codes (check database (module_of "app::main")))

let expect_codes ~expected (_, found) =
  if found <> expected then
    fail "found [%s], expected [%s]" (String.concat "; " found) (String.concat "; " expected)

let time =
  ("clock_library::time", "public fn stamp() -> Instant\n  uses Clock\n{\n  Clock.now()\n}\n")

let sources =
  ("framework::sources", "public trait Source {\n  fn read(self) -> Instant\n    uses Clock\n}\n")

let timers =
  ( "plugins::timers",
    "use framework::sources\n\n\
     public type Timer()\n\n\
     impl sources::Source for Timer {\n\
    \  fn read(self) -> Instant\n\
    \    uses Clock\n\
    \  {\n\
    \    Clock.now()\n\
    \  }\n\
     }\n" )

let () =
  let value =
    ( "app::main",
      "use clock_library::time\n\n\
       fn f() -> Instant\n\
      \  uses Clock\n\
       {\n\
      \  let stamp = time::stamp\n\
      \  stamp()\n\
       }\n" )
  in
  test "a function value of a dependency's function can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants [ value; time ] [ ("clock_library", []) ]));
  test "a function value of a dependency's function can use a granted capability" (fun () ->
      expect_codes ~expected:[]
        (codes_with_grants [ value; time ] [ ("clock_library", [ "Clock" ]) ]));
  let bound =
    ( "app::main",
      "use framework::sources\n\
       use plugins::timers\n\n\
       fn first[Reader: sources::Source](reader: Reader) -> Instant\n\
      \  uses Clock\n\
       {\n\
      \  reader.read()\n\
       }\n\n\
       fn f() -> Instant\n\
      \  uses Clock\n\
       {\n\
      \  first(timers::Timer())\n\
       }\n" )
  in
  test "an impl of a dependency that satisfies a bound can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants [ bound; sources; timers ]
           [ ("framework", [ "Clock" ]); ("plugins", []) ]));
  test "an impl of a dependency that satisfies a bound can use a granted capability" (fun () ->
      expect_codes ~expected:[]
        (codes_with_grants [ bound; sources; timers ]
           [ ("framework", [ "Clock" ]); ("plugins", [ "Clock" ]) ]));
  test "an impl of a dependency behind an `any` value can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants
           [
             ( "app::main",
               "use framework::sources\n\
                use plugins::timers\n\n\
                fn f() -> any sources::Source {\n\
               \  any timers::Timer()\n\
                }\n" );
             sources;
             timers;
           ]
           [ ("framework", [ "Clock" ]); ("plugins", []) ]))

(* What a grant names *)

let ledger =
  ( "store::ledger",
    "public capability Ledger {\n\
    \  fn record(amount: Int64)\n\
     }\n\n\
     public fn pay(amount: Int64)\n\
    \  uses Ledger\n\
     {\n\
    \  Ledger.record(amount)\n\
     }\n" )

let pays =
  ("app::main", "use store::ledger\n\nfn f()\n  uses ledger::Ledger\n{\n  ledger::pay(1)\n}\n")

let problems database = Query.demand database Package_checks.manifest_problems "app"

let () =
  test "a grant names a capability outside the prelude by its full path" (fun () ->
      expect_codes ~expected:[]
        (codes_with_grants [ pays; ledger ] [ ("store", [ "store::ledger::Ledger" ]) ]));
  test "a capability's name alone grants only one of the prelude" (fun () ->
      let database, found = codes_with_grants [ pays; ledger ] [ ("store", [ "Ledger" ]) ] in
      expect_codes ~expected:[ "capabilities.not_granted" ] (database, found);
      match problems database with
      | [ Not_a_capability { dependency = "store"; name = "Ledger" } ] -> ()
      | _ -> fail "the grant is not reported");
  test "a grant covers only the capabilities it names" (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants [ pays; ledger ] [ ("store", [ "Clock" ]) ]))

(* A dependency that nothing uses *)

let () =
  test "a dependency that nothing in the package names is reported" (fun () ->
      let database, _ =
        codes_with_grants
          [ ("app::main", "fn f() -> Int64 {\n  1\n}\n"); time ]
          [ ("clock_library", []) ]
      in
      match problems database with [ Unused "clock_library" ] -> () | _ -> fail "not reported");
  test "a dependency named in a path is used" (fun () ->
      let database, _ =
        codes_with_grants [ pays; ledger ] [ ("store", [ "store::ledger::Ledger" ]) ]
      in
      if problems database <> [] then fail "reported");
  test "a dependency whose trait's method is called with a dot is used" (fun () ->
      let database, found =
        codes_with_grants
          [
            ("app::main", "fn f(side: Int64) -> Int64 {\n  side.doubled()\n}\n");
            ( "shapes::sizes",
              "public trait Doubled {\n\
              \  fn doubled(self) -> Int64\n\
               }\n\n\
               impl Doubled for Int64 {\n\
              \  fn doubled(self) -> Int64 {\n\
              \    self\n\
              \  }\n\
               }\n" );
          ]
          [ ("shapes", []) ]
      in
      expect_codes ~expected:[] (database, found);
      if problems database <> [] then fail "reported");
  test "an unused dependency is reported for every kind of definition in the package" (fun () ->
      let database, found =
        codes_with_grants
          [
            ( "app::main",
              "public type Square(side: Int64)\n\
              \  derives Equal\n\n\
               public trait Sided {\n\
              \  fn sides(self) -> Int64\n\n\
              \  fn corners(self) -> Int64 {\n\
              \    self.sides()\n\
              \  }\n\
               }\n\n\
               impl Sided for Square {\n\
              \  fn sides(self) -> Int64 {\n\
              \    4\n\
              \  }\n\
               }\n\n\
               public capability Ledger {\n\
              \  fn record(amount: Int64)\n\
               }\n\n\
               public let limit: Int64 = 10\n\n\
               fn Square.width(self) -> Int64 {\n\
              \  self.side\n\
               }\n\n\
               test \"a square has four sides\" {\n\
              \  assert Square(1).sides() == 4\n\
               }\n" );
            time;
          ]
          [ ("clock_library", []) ]
      in
      expect_codes ~expected:[] (database, found);
      match problems database with [ Unused "clock_library" ] -> () | _ -> fail "not reported");
  test "an unused dependency is not reported for a package with an error" (fun () ->
      let database, _ =
        codes_with_grants
          [ ("app::main", "fn f() -> Int64 {\n  true\n}\n"); time ]
          [ ("clock_library", []) ]
      in
      if problems database <> [] then fail "reported")

(* Function values and the capabilities their types list *)

let ticks =
  "fn tick() -> Instant\n\
  \  uses Clock\n\
   {\n\
  \  Clock.now()\n\
   }\n\n\
   fn still() -> Instant {\n\
  \  todo\n\
   }\n\n\
   fn each_time[capability Granted](action: (fn() -> Instant uses Granted)) -> Instant\n\
  \  uses Granted\n\
   {\n\
  \  action()\n\
   }\n\n"

let () =
  test "a function that uses a capability is not passed as one that uses none" (fun () ->
      one_diagnostic
        (ticks
       ^ "fn apply(action: fn() -> Instant) -> Instant {\n\
         \  action()\n\
          }\n\n\
          fn f() -> Instant {\n\
         \  apply(tick)\n\
          }\n")
        "types.mismatch");
  test "a function that uses a capability is not bound as one that uses none" (fun () ->
      one_diagnostic
        (ticks ^ "fn f() -> Instant {\n  let action: fn() -> Instant = tick\n  action()\n}\n")
        "types.mismatch");
  test "a function that uses a capability is not returned as one that uses none" (fun () ->
      one_diagnostic (ticks ^ "fn f() -> fn() -> Instant {\n  tick\n}\n") "types.mismatch");
  test "a function that uses a capability is not stored as one that uses none" (fun () ->
      one_diagnostic
        (ticks ^ "type Job(action: fn() -> Instant)\n\nfn f() -> Job {\n  Job(tick)\n}\n")
        "types.mismatch");
  test "a function that uses a capability is not assigned as one that uses none" (fun () ->
      one_diagnostic
        (ticks
       ^ "fn f() -> Instant {\n\
         \  var action: fn() -> Instant = still\n\
         \  action = tick\n\
         \  action()\n\
          }\n")
        "types.mismatch");
  test "function types inside a type must list the same capabilities" (fun () ->
      one_diagnostic
        (ticks
       ^ "fn f() -> USize\n\
         \  uses Clock\n\
          {\n\
         \  let actions: List[(fn() -> Instant uses Clock)] = [tick]\n\
         \  let plain: List[fn() -> Instant] = actions\n\
         \  plain.length()\n\
          }\n")
        "types.mismatch");
  test "a function that uses nothing is passed as one that may use a capability" (fun () ->
      fine
        (ticks
       ^ "fn f() -> Instant\n\
         \  uses Clock\n\
          {\n\
         \  let action: (fn() -> Instant uses Clock) = still\n\
         \  action()\n\
          }\n"));
  test "a branch's function meets the function type expected of the branches" (fun () ->
      fine
        (ticks
       ^ "fn f(fast: Bool) -> Instant\n\
         \  uses Clock\n\
          {\n\
         \  let action: (fn() -> Instant uses Clock) = if fast { still } else { tick }\n\
         \  action()\n\
          }\n"));
  test "a branch's function that uses a capability is not bound as one that uses none" (fun () ->
      one_diagnostic
        (ticks
       ^ "fn f(fast: Bool) -> Instant {\n\
         \  let action: fn() -> Instant = if fast { still } else { tick }\n\
         \  action()\n\
          }\n")
        "types.mismatch");
  test "a capability parameter is instantiated with the capabilities of the functions passed for it"
    (fun () -> fine (ticks ^ "fn f() -> Instant\n  uses Clock\n{\n  each_time(tick)\n}\n"));
  test "the capabilities of a function passed for a capability parameter must be available"
    (fun () ->
      one_diagnostic
        (ticks ^ "fn f() -> Instant {\n  each_time(tick)\n}\n")
        "capabilities.not_available");
  test "a capability parameter is instantiated with the capabilities of a parenthesized lambda"
    (fun () ->
      one_diagnostic
        (ticks ^ "fn f() -> Instant {\n  each_time((fn() { Clock.now() }))\n}\n")
        "capabilities.not_available");
  test "a capability parameter is instantiated with the capabilities of a function in a branch"
    (fun () ->
      one_diagnostic
        (ticks ^ "fn f(fast: Bool) -> Instant {\n  each_time(if fast { still } else { tick })\n}\n")
        "capabilities.not_available");
  test "a capability parameter is instantiated with the capabilities of a lambda in a branch"
    (fun () ->
      one_diagnostic
        (ticks
       ^ "fn f(fast: Bool) -> Instant {\n\
         \  each_time(if fast { still } else { fn() { Clock.now() } })\n\
          }\n")
        "capabilities.not_available");
  test "a function passes its own capability parameter on" (fun () ->
      fine
        (ticks
       ^ "fn passes_on[capability Mine](action: (fn() -> Instant uses Mine)) -> Instant\n\
         \  uses Mine\n\
          {\n\
         \  each_time(action)\n\
          }\n"));
  test "a function's own capability parameter is rigid in a lambda's type" (fun () ->
      one_diagnostic
        "fn sneaky[capability Mine](action: (fn() -> Instant uses Mine)) -> Instant\n\
        \  uses Mine\n\
         {\n\
        \  let again: (fn() -> Instant uses Mine) = fn() { Clock.now() }\n\
        \  again()\n\
         }\n"
        "capabilities.lambda_uses");
  test "a function's own capability parameter is rigid in a binding's type" (fun () ->
      one_diagnostic
        (ticks
       ^ "fn sneaky[capability Mine](action: (fn() -> Instant uses Mine)) -> Instant\n\
         \  uses Mine\n\
          {\n\
         \  let again: (fn() -> Instant uses Mine) = tick\n\
         \  again()\n\
          }\n")
        "types.mismatch");
  test "a function calls itself with its own capability parameter" (fun () ->
      fine
        "fn repeat[capability Mine](action: (fn() -> Instant uses Mine), again: Bool) -> Instant\n\
        \  uses Mine\n\
         {\n\
        \  if again {\n\
        \    repeat(action, again: false)\n\
        \  } else {\n\
        \    action()\n\
        \  }\n\
         }\n");
  test "a recursive call needs the capabilities that it passes for its capability parameter"
    (fun () ->
      let repeat uses =
        ticks
        ^ "fn repeat[capability Mine](action: (fn() -> Instant uses Mine), again: Bool) -> Instant\n\
          \  uses " ^ uses
        ^ "\n{\n  if again {\n    repeat(tick, again: false)\n  } else {\n    action()\n  }\n}\n"
      in
      one_diagnostic (repeat "Mine") "capabilities.not_available";
      fine (repeat "Mine, Clock"))

(* A capability parameter in what a call gives, and in a type *)

let later =
  ticks
  ^ "fn later[capability Granted](action: (fn() -> Instant uses Granted)) -> (fn() -> Instant uses \
     Granted) {\n\
    \  action\n\
     }\n\n"

let () =
  test "a call's result has the capabilities that were passed for the capability parameter"
    (fun () ->
      one_diagnostic
        (later ^ "fn f() -> Instant {\n  let kept = later(tick)\n  kept()\n}\n")
        "capabilities.not_available";
      fine (later ^ "fn f() -> Instant\n  uses Clock\n{\n  let kept = later(tick)\n  kept()\n}\n");
      fine (later ^ "fn f() -> Instant {\n  let kept = later(still)\n  kept()\n}\n"));
  test "a call's result must fit the function type that it is checked against" (fun () ->
      one_diagnostic
        (later
       ^ "fn f()\n  uses Clock\n{\n  let kept: fn() -> Instant = later(tick)\n  let _ = kept\n}\n")
        "types.mismatch";
      fine
        (later
       ^ "fn f()\n\
         \  uses Clock\n\
          {\n\
         \  let kept: (fn() -> Instant uses Clock) = later(tick)\n\
         \  let _ = kept\n\
          }\n"));
  test "a variable that is assigned a second function has the capabilities of both" (fun () ->
      one_diagnostic
        (later ^ "fn f() -> Instant {\n  var kept = later(still)\n  kept = tick\n  kept()\n}\n")
        "capabilities.not_available";
      fine
        (later
       ^ "fn f() -> Instant\n\
         \  uses Clock\n\
          {\n\
         \  var kept = later(still)\n\
         \  kept = tick\n\
         \  kept()\n\
          }\n"));
  test
    "a type's capability parameter is instantiated with the capabilities of its fields' functions"
    (fun () ->
      let holder =
        ticks ^ "type Holder[capability Granted](action: (fn() -> Instant uses Granted))\n\n"
      in
      one_diagnostic
        (holder
       ^ "fn f() -> Instant {\n\
         \  let holder = Holder(action: tick)\n\
         \  let action = holder.action\n\
         \  action()\n\
          }\n")
        "capabilities.not_available";
      fine
        (holder
       ^ "fn f() -> Instant\n\
         \  uses Clock\n\
          {\n\
         \  let holder = Holder(action: tick)\n\
         \  let action = holder.action\n\
         \  action()\n\
          }\n"))

(* Function values and the costs their types promise *)

(* How many conversions of a function value to a function type with weaker
   costs the first definition of a text has. The prover must show that the
   given costs imply the expected ones at each. *)
let widenings text =
  List.length
    (List.filter
       (fun (node : Core.expression) ->
         match node.kind with Convert { conversion = Widen; _ } -> true | _ -> false)
       (first_core_nodes text).expressions)

let () =
  test "a function bound as a type that promises a cost leaves the cost to the prover" (fun () ->
      match
        widenings
          "fn f() -> Int64 {\n\
          \  let action: (fn() -> Int64 cost time finite) = forever\n\
          \  action()\n\
           }\n\n\
           fn forever() -> Int64 {\n\
          \  while true {}\n\
           }\n"
      with
      | 1 -> ()
      | found -> fail "%d conversions" found);
  test "a function that promises to end can be bound as one that does" (fun () ->
      fine
        "fn f() -> Int64 {\n\
        \  let action: (fn() -> Int64 cost time finite) = quick\n\
        \  action()\n\
         }\n\n\
         fn quick() -> Int64\n\
        \  cost time O(1)\n\
         {\n\
        \  1\n\
         }\n");
  test "function types inside a type must promise the same costs" (fun () ->
      one_diagnostic
        "fn f(actions: List[fn() -> Int64]) -> USize {\n\
        \  let bounded: List[(fn() -> Int64 cost time finite)] = actions\n\
        \  bounded.length()\n\
         }\n"
        "types.mismatch")

(* The cursor of a yielding method that uses a capability *)

let readings =
  "capability Meter {\n\
  \  fn read() -> Int64\n\
   }\n\n\
   type Fixed(value: Int64)\n\n\
   impl Meter for Fixed {\n\
  \  fn read(self) -> Int64 {\n\
  \    self.value\n\
  \  }\n\
   }\n\n\
   fn readings(count: Int64) yields Int64\n\
  \  uses Meter\n\
   {\n\
  \  var index = 0\n\
  \  while index < count {\n\
  \    yield Meter.read()\n\
  \    index += 1\n\
  \  }\n\
   }\n\n"

let () =
  test "the next of a cursor needs the capabilities of the cursor's method" (fun () ->
      one_diagnostic
        (readings
       ^ "fn first() -> Option[Int64] {\n\
         \  var cursor = provide Fixed(value: 7) {\n\
         \    readings(3)\n\
         \  }\n\
         \  mut cursor.next()\n\
          }\n")
        "capabilities.not_available");
  test "the next of a cursor is fine where the method's capabilities are available" (fun () ->
      fine
        (readings
       ^ "fn first() -> Option[Int64]\n\
         \  uses Meter\n\
          {\n\
         \  var cursor = readings(3)\n\
         \  mut cursor.next()\n\
          }\n"));
  test "a for loop over a cursor needs the capabilities of the cursor's method" (fun () ->
      one_diagnostic
        (readings
       ^ "fn total() -> Int64 {\n\
         \  var cursor = provide Fixed(value: 7) {\n\
         \    readings(3)\n\
         \  }\n\
         \  var sum = 0\n\
         \  for reading in mut cursor {\n\
         \    sum += reading\n\
         \  }\n\
         \  sum\n\
          }\n")
        "capabilities.not_available");
  test "a cursor whose method uses a capability does not meet a Cursor bound" (fun () ->
      one_diagnostic
        (readings
       ^ "fn pull[Source: Cursor](source: mut Source) -> Option[Source.Element] {\n\
         \  mut source.next()\n\
          }\n\n\
          fn first() -> Option[Int64]\n\
         \  uses Meter\n\
          {\n\
         \  var cursor = readings(3)\n\
         \  pull(mut cursor)\n\
          }\n")
        "types.unsatisfied_bound");
  test "a method that Cursor provides cannot run a cursor whose method uses a capability" (fun () ->
      one_diagnostic
        (readings
       ^ "fn length() -> USize\n\
         \  uses Meter\n\
          {\n\
         \  var cursor = readings(3)\n\
         \  own cursor.count()\n\
          }\n")
        "capabilities.not_available");
  test "a cursor whose method uses no capability meets a Cursor bound" (fun () ->
      fine
        "fn counted(count: Int64) yields Int64 {\n\
        \  var index = 0\n\
        \  while index < count {\n\
        \    yield index\n\
        \    index += 1\n\
        \  }\n\
         }\n\n\
         fn pull[Source: Cursor](source: mut Source) -> Option[Source.Element] {\n\
        \  mut source.next()\n\
         }\n\n\
         fn first() -> Option[Int64] {\n\
        \  var cursor = counted(3)\n\
        \  pull(mut cursor)\n\
         }\n")

let () = finish ()
