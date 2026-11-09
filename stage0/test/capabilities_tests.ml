(* The tests of capabilities: what code may call, lambdas' uses,
   capability parameters, provide, and dependency grants. See
   TYPECHECKER.md, "Capabilities". *)

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
      match Query.demand database Infer.checked key with
      | Some result -> (
          match List.filter_map Fun.id (Array.to_list result.checked.provides) with
          | [
           {
             implementations =
               [ (_, [ { capability; impl = Impl _; arguments = [ (_, Type tag) ] } ]) ];
           };
          ]
            when Path.show capability = "standard::capabilities::Clock" && Types.show tag = "Bool"
            ->
              ()
          | _ -> fail "not recorded")
      | None -> fail "not checked");
  test "a specification has only Panic" (fun () ->
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
  test "a capability parameter is what the lambdas passed for it use" (fun () ->
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
  test "a dependency may use only what it is granted" (fun () ->
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
      Query.set database Workspace.packages "app"
        {
          name = "app";
          dependencies = [ { package = "clock_library"; capabilities = [] } ];
          modules = [ module_of "app::main" ];
        };
      match codes (check database (module_of "app::main")) with
      | [ "capabilities.not_granted" ] -> ()
      | found -> fail "found [%s]" (String.concat "; " found))

let () =
  let with_grant files granted =
    let database = setup files in
    Query.set database Workspace.packages "app"
      {
        name = "app";
        dependencies = [ { package = "clock_library"; capabilities = granted } ];
        modules = [ module_of "app::main" ];
      };
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
  test "a dependency's trait method may use only what it is granted" (fun () ->
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
  test "a dependency's trait method may use what it is granted" (fun () ->
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
  test "providing a dependency's type checks what its impls use" (fun () ->
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
  test "an implementation of a capability may use the capability itself" (fun () ->
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

let () = finish ()
