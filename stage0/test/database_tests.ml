open Harness

let checked text =
  let pipeline = Support.pipeline (Support.setup [ ("app::main", text) ]) in
  (match Support.codes (Support.diagnostics pipeline (Support.file_of "app::main")) with
  | [] -> ()
  | codes -> fail "the program has diagnostics: %s" (String.concat ", " codes));
  pipeline

let expect_reads pipeline part ~includes ~excludes =
  let reads = Pipeline.For_testing.reads pipeline part in
  List.iter
    (fun read ->
      if not (List.mem read reads) then
        fail "%s does not read %s; it reads %s" part read (String.concat ", " reads))
    includes;
  List.iter (fun read -> if List.mem read reads then fail "%s reads %s" part read) excludes

let lowered name = "lowered app::main::" ^ name
let ground_types name = "ground types app::main::" ^ name
let test_key name = "test key app::main::" ^ name

let built ?(roots = []) files =
  let pipeline = Support.pipeline (Support.setup files) in
  List.iter
    (fun name ->
      Pipeline.For_testing.root pipeline
        (Code { path = Top { module_ = Support.module_of "app::main"; name }; type_arguments = [] }))
    roots;
  Pipeline.propagate pipeline;
  pipeline

let changes ~before ~after =
  List.filter_map
    (fun (name, text) ->
      match List.assoc_opt name before with
      | Some previous when previous = text -> None
      | Some _ | None -> Some (Support.file_of name, Some text))
    after
  @ List.filter_map
      (fun (name, _) ->
        if List.mem_assoc name after then None else Some (Support.file_of name, None))
      before

let propagate ?roots hot ~before ~after =
  let observed =
    Pipeline.For_testing.observe hot (fun () ->
        Pipeline.update hot (changes ~before ~after);
        Pipeline.propagate hot)
  in
  (match Pipeline.For_testing.differences hot (built ?roots after) with
  | [] -> ()
  | parts ->
      fail "the propagated database differs from a cold build in %s" (String.concat ", " parts));
  observed

let propagated ~before ~after = (propagate (built before) ~before ~after).recomputed

let laid_out ~roots ~before ~after =
  (propagate ~roots (built ~roots before) ~before ~after).recomputed

let expect_recomputed recomputed ~exactly =
  if recomputed <> exactly then
    fail "recomputed %s, not %s" (String.concat ", " recomputed) (String.concat ", " exactly)

let expect_untouched recomputed ~names =
  List.iter
    (fun part ->
      if List.exists (fun name -> Substring.contains part name) names then
        fail "recomputed %s; it recomputed %s" part (String.concat ", " recomputed))
    recomputed

let expect_included recomputed ~parts =
  List.iter
    (fun part ->
      if not (List.mem part recomputed) then
        fail "did not recompute %s; it recomputed %s" part (String.concat ", " recomputed))
    parts

let standard = lazy (Database.For_testing.standard_state ())

let settled loaded packages =
  let pipeline = Pipeline.create ~loaded:(Lazy.force standard :: loaded) packages in
  Pipeline.propagate pipeline;
  pipeline

let relaid ?(loaded = ([], [])) ~before ~after () =
  let hot = settled (fst loaded) before in
  let observed =
    Pipeline.For_testing.observe hot (fun () ->
        Pipeline.relayout hot ~loaded:(Lazy.force standard :: snd loaded) after;
        Pipeline.propagate hot)
  in
  (match Pipeline.For_testing.differences hot (settled (snd loaded) after) with
  | [] -> ()
  | parts -> fail "the relaid database differs from a cold build in %s" (String.concat ", " parts));
  observed.recomputed

let loaded_package files =
  let packages = Support.setup files in
  Pipeline.state (Pipeline.create ~loaded:[ Lazy.force standard ] packages) (List.hd packages).name

let saved pipeline =
  let entries = Pipeline.unsaved pipeline in
  Pipeline.mark_saved pipeline;
  entries

let committed log entries =
  List.fold_left (fun log (key, value) -> (key, value) :: List.remove_assoc key log) log entries

let live log =
  List.filter_map (fun (key, value) -> Option.map (fun value -> (key, value)) value) log

let reopened log files =
  let packages = Support.setup files in
  let texts (file : Path.file) =
    List.find_map (fun (package : Project.package) -> List.assoc_opt file package.files) packages
  in
  let pipeline = Pipeline.restore ~loaded:[ Lazy.force standard ] ~texts (live log) in
  Pipeline.relayout pipeline ~loaded:[ Lazy.force standard ] packages;
  pipeline

let expect_cold ?roots pipeline files =
  match Pipeline.For_testing.differences pipeline (built ?roots files) with
  | [] -> ()
  | parts -> fail "the reopened database differs from a cold build in %s" (String.concat ", " parts)

let reopened_recomputes ?roots log files =
  let pipeline = reopened log files in
  let observed = Pipeline.For_testing.observe pipeline (fun () -> Pipeline.propagate pipeline) in
  expect_cold ?roots pipeline files;
  observed

let tool_user =
  [
    ("app::main", "use lib::tools\nfn caller() -> Int64 { tools::helper() }\n");
    ("lib::tools", "public fn helper() -> Int64 { 1 }\n");
  ]

let mutual body =
  Printf.sprintf
    "fn f(n: Int64) -> Int64\n\
    \  cost time finite\n\
     { g(n) }\n\
     fn g(n: Int64) -> Int64\n\
    \  cost time finite\n\
     { %s }\n\
     fn h() -> Int64 { f(1) }\n"
    body

let acyclic = mutual "n"
let cyclic = mutual "f(n)"

let stepper =
  "trait Step {\n\
  \  fn step(own self) -> Int64\n\
  \    cost time finite\n\
   }\n\
   fn run(value: own any Step) -> Int64\n\
  \  cost time finite\n\
   {\n\
  \  own value.step()\n\
   }\n\
   type Foo()\n"

let stepper_that_runs =
  stepper
  ^ "impl Step for Foo {\n\
    \  fn step(own self) -> Int64\n\
    \    cost time finite\n\
    \  {\n\
    \    let value: any Step = any self\n\
    \    run(own value)\n\
    \  }\n\
     }\n"

let configured construction =
  Printf.sprintf
    "type Config(size: Int64 = start())\n\
     fn start() -> Int64\n\
    \  cost time finite\n\
     { make().size }\n\
     fn make() -> Config\n\
    \  cost time finite\n\
     { %s }\n"
    construction

let callee_and_caller =
  "fn callee(x: Int64) -> Int64 { x + 1 }\nfn caller() -> Int64 { callee(1) }\n"

let with_helper =
  [ ("app::main", callee_and_caller); ("app::extra", "fn helper() -> Int64 { 1 }\n") ]

let () =
  test "a client whose background process exits without serving gets an error at once" (fun () ->
      let started = Unix.gettimeofday () in
      (match
         (Database.call ~program:"/usr/bin/false" ~key:(scratch "unserved") ~progress:ignore 0
           : (int, string) result)
       with
      | Error _ -> ()
      | Ok _ -> fail "answered with no background process");
      let elapsed = Unix.gettimeofday () -. started in
      if elapsed > 2. then fail "the error took %.1f s" elapsed);
  test "the background process answers each request and sends its progress" (fun () ->
      let key = scratch "served" in
      let socket =
        match Database.For_testing.listen ~key with
        | Ok socket -> socket
        | Error message -> failwith message
      in
      match Unix.fork () with
      | 0 -> (
          Unix.dup2 socket Unix.stdin;
          match
            Database.serve ~key ~handle:(fun ~progress request ->
                progress "working";
                if request = "stop" then Database.stop ();
                String.length request)
          with
          | () -> Unix._exit 0
          | exception _ -> Unix._exit 1)
      | process ->
          Unix.close socket;
          Fun.protect
            ~finally:(fun () ->
              (try Unix.kill process Sys.sigkill with Unix.Unix_error _ -> ());
              ignore (Unix.waitpid [] process))
            (fun () ->
              let progressed = ref false in
              let served_length request =
                match
                  Database.call ~start_server:false ~key
                    ~progress:(fun text -> if text = "working" then progressed := true)
                    request
                with
                | Ok (length : int) -> length
                | Error message ->
                    fail "%s" message;
                    -1
              in
              let lengths = List.map served_length [ "one"; "three"; "stop" ] in
              if lengths <> [ 3; 5; 4 ] then
                fail "answered %s" (String.concat ", " (List.map string_of_int lengths));
              if not !progressed then fail "sent no progress"))

let () =
  test "a caller's checked body reads the callee's interface and not its body" (fun () ->
      expect_reads
        (checked "fn callee(x: Int64) -> Int64 { x + 1 }\nfn caller() -> Int64 { callee(1) }\n")
        "checked body app::main::caller" ~includes:[ "interface app::main::callee" ]
        ~excludes:
          [
            "checked body app::main::callee";
            "tree app::main::callee";
            "resolved body app::main::callee";
          ]);
  test "a contract reads no resolved names of its body" (fun () ->
      expect_reads
        (checked "fn f(x: Int64) -> Int64 requires x > 0 { x + 1 }\n")
        "contract app::main::f"
        ~includes:[ "resolved contract app::main::f" ]
        ~excludes:[ "resolved body app::main::f" ]);
  test "a checked body reads its callee's signature check" (fun () ->
      expect_reads
        (checked "fn callee(x: Int64) -> Int64 { x + 1 }\nfn caller() -> Int64 { callee(1) }\n")
        "checked body app::main::caller"
        ~includes:[ "signature check app::main::callee" ]
        ~excludes:[]);
  test "a type's facts read interfaces and type facts, and no signature check" (fun () ->
      expect_reads
        (checked "type Inner(value: Int64)\ntype Outer(inner: Inner)\n")
        "type facts app::main::Outer"
        ~includes:[ "interface app::main::Outer"; "type facts app::main::Inner" ]
        ~excludes:[ "signature check app::main::Outer"; "signature check app::main::Inner" ]);
  test "a caller's checked body and proof read no place or text of the callee" (fun () ->
      let pipeline = checked callee_and_caller in
      ignore (Pipeline.prove pipeline [ Support.file_of "app::main" ]);
      List.iter
        (fun part ->
          expect_reads pipeline part ~includes:[]
            ~excludes:[ "place app::main::callee"; "text app::main::callee" ])
        [ "checked body app::main::caller"; "proof app::main::caller" ]);
  test "a package check reads no place" (fun () ->
      expect_reads
        (checked "type Inner(value: Int64)\ntype Outer(inner: Inner)\n")
        "package check app type app::main::Outer" ~includes:[ "tree app::main::Outer" ]
        ~excludes:[ "place app::main::Outer"; "place app::main::Inner" ]);
  test "a reformat inside a definition recomputes only that definition's proof" (fun () ->
      expect_recomputed
        (propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 {\n  x + 1\n}\nfn caller() -> Int64 { callee(1) }\n"
               );
             ])
        ~exactly:
          [
            "entries app::main";
            "import check app/main/main.truss";
            "namespace app::main";
            "parsed app/main/main.truss";
            "proof app::main::callee";
          ]);
  test "moving a definition to another file of its module recomputes no definition's part"
    (fun () ->
      expect_recomputed
        (propagated
           ~before:[ ("app::main", callee_and_caller); ("app::main/other", "") ]
           ~after:
             [
               ("app::main", "fn caller() -> Int64 { callee(1) }\n");
               ("app::main/other", "fn callee(x: Int64) -> Int64 { x + 1 }\n");
             ])
        ~exactly:
          [
            "entries app::main";
            "import check app/main/main.truss";
            "import check app/main/other.truss";
            "namespace app::main";
            "parsed app/main/main.truss";
            "parsed app/main/other.truss";
          ]);
  test "an edit to a body recomputes no part of a caller" (fun () ->
      expect_untouched
        (propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 { x + 2 }\nfn caller() -> Int64 { callee(1) }\n" );
             ])
        ~names:[ "caller" ]);
  test "an edit to a signature recomputes the callers" (fun () ->
      let recomputed =
        propagated
          ~before:[ ("app::main", callee_and_caller) ]
          ~after:
            [
              ( "app::main",
                "fn callee(x: Int32) -> Int64 { 1 }\nfn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      if not (List.mem "checked body app::main::caller" recomputed) then
        fail "recomputed only %s" (String.concat ", " recomputed));
  test "an edit to an ensures recomputes the callers' proofs and not their checks" (fun () ->
      let recomputed =
        propagated
          ~before:[ ("app::main", callee_and_caller) ]
          ~after:
            [
              ( "app::main",
                "fn callee(x: Int64) -> Int64 ensures result == 1 { 1 }\n\
                 fn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      if not (List.mem "proof app::main::caller" recomputed) then
        fail "recomputed only %s" (String.concat ", " recomputed);
      expect_untouched recomputed ~names:[ "checked body app::main::caller" ]);
  test "adding the definition that a call names fixes the call" (fun () ->
      ignore
        (propagated
           ~before:[ ("app::main", "fn caller() -> Int64 { callee(1) }\n") ]
           ~after:[ ("app::main", callee_and_caller) ]));
  test "removing a definition deletes its parts and fails its callers" (fun () ->
      expect_untouched
        (propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:[ ("app::main", "fn caller() -> Int64 { callee(1) }\n") ])
        ~names:[ "app::main::callee" ]);
  test "a field that makes a type not plain recomputes the types that hold it" (fun () ->
      let recomputed =
        propagated
          ~before:[ ("app::main", "type Inner(value: Int64)\ntype Outer(inner: Inner)\n") ]
          ~after:[ ("app::main", "type Inner(value: String)\ntype Outer(inner: Inner)\n") ]
      in
      if not (List.mem "type facts app::main::Outer" recomputed) then
        fail "recomputed only %s" (String.concat ", " recomputed));
  test "a body that compares a type reads its impls and not the impl index" (fun () ->
      expect_reads
        (checked
           "type Box(value: Int64) derives Equal\n\
            fn same(left: Box, right: Box) -> Bool { left == right }\n")
        "checked body app::main::same"
        ~includes:[ "impls of type app app::main::Box" ]
        ~excludes:[ "impl index app"; "impl index standard" ]);
  test "a call that closes a cycle recomputes the proofs of the cycle's members and no other"
    (fun () ->
      let recomputed =
        propagated ~before:[ ("app::main", acyclic) ] ~after:[ ("app::main", cyclic) ]
      in
      expect_included recomputed
        ~parts:
          [
            "recursion group app::main::f";
            "recursion group app::main::g";
            "proof app::main::f";
            "proof app::main::g";
          ];
      expect_untouched recomputed ~names:[ "app::main::h"; "checked body app::main::f" ]);
  test "removing the call that closes a cycle splits its recursion group" (fun () ->
      let recomputed =
        propagated ~before:[ ("app::main", cyclic) ] ~after:[ ("app::main", acyclic) ]
      in
      expect_included recomputed ~parts:[ "proof app::main::f"; "proof app::main::g" ];
      expect_untouched recomputed ~names:[ "app::main::h"; "checked body app::main::f" ]);
  test "an impl that closes a cycle through a trait method recomputes the proofs on the cycle"
    (fun () ->
      expect_included
        (propagated ~before:[ ("app::main", stepper) ] ~after:[ ("app::main", stepper_that_runs) ])
        ~parts:[ "successors app app::main::Step.step(own self)"; "proof app::main::run" ]);
  test "a construction that runs a field default joins the recursion group of the default's callee"
    (fun () ->
      expect_included
        (propagated
           ~before:[ ("app::main", configured "Config(size: 1)") ]
           ~after:[ ("app::main", configured "Config()") ])
        ~parts:
          [
            "call edges app::main::make";
            "recursion group app::main::make";
            "recursion group app::main::start";
            "proof app::main::start";
          ]);
  test "adding a file and then removing it recomputes no part of the other file's definitions"
    (fun () ->
      let without_helper = [ ("app::main", callee_and_caller) ] in
      let hot = built without_helper in
      List.iter
        (fun (before, after) ->
          expect_untouched (propagate hot ~before ~after).recomputed ~names:[ "app::main::" ])
        [ (without_helper, with_helper); (with_helper, without_helper) ]);
  test "reformatting a callee recomputes no caller's proof" (fun () ->
      expect_recomputed
        (propagated
           ~before:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 requires x > 0 { x }\n\
                  fn caller() -> Int64 { callee(1) }\n" );
             ]
           ~after:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64\n\
                 \  requires x > 0\n\
                  {\n\
                 \  x\n\
                  }\n\
                  fn caller() -> Int64 { callee(1) }\n" );
             ])
        ~exactly:
          [
            "entries app::main";
            "import check app/main/main.truss";
            "namespace app::main";
            "parsed app/main/main.truss";
            "proof app::main::callee";
          ]);
  test "a field that changes a type's layout recomputes the layouts that hold it in place"
    (fun () ->
      let holders inner =
        [
          ( "app::main",
            "type Inner(" ^ inner
            ^ ")\n\
               type Outer(inner: Inner)\n\
               type Holder(items: List[Inner])\n\
               fn sizes(outer: Outer, holder: Holder) -> Int64 { 1 }\n" );
        ]
      in
      let recomputed =
        laid_out ~roots:[ "sizes" ] ~before:(holders "value: Int64")
          ~after:(holders "value: Int64, flag: Bool")
      in
      expect_included recomputed ~parts:[ "layout Inner"; "layout Outer" ];
      expect_untouched recomputed ~names:[ "layout Holder"; "layout List" ]);
  test "reordering a type's fields recomputes no layout of the types that hold it" (fun () ->
      let holders inner =
        [
          ( "app::main",
            "type Inner(" ^ inner
            ^ ")\ntype Outer(inner: Inner)\nfn size(outer: Outer) -> Int64 { 1 }\n" );
        ]
      in
      let recomputed =
        laid_out ~roots:[ "size" ]
          ~before:(holders "first: Int64, second: Bool")
          ~after:(holders "second: Bool, first: Int64")
      in
      expect_included recomputed ~parts:[ "layout Inner" ];
      expect_untouched recomputed ~names:[ "layout Outer" ]);
  test "an edit to a callee's body recomputes its lowered code and not its caller's" (fun () ->
      let recomputed =
        laid_out ~roots:[ "caller" ]
          ~before:[ ("app::main", callee_and_caller) ]
          ~after:
            [
              ( "app::main",
                "fn callee(x: Int64) -> Int64 { x + 2 }\nfn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      expect_included recomputed ~parts:[ lowered "callee"; test_key "callee"; test_key "caller" ];
      expect_untouched recomputed ~names:[ lowered "caller" ]);
  test "a call that is removed with its callee collects the callee's lowered code" (fun () ->
      expect_untouched
        (laid_out ~roots:[ "caller" ]
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:[ ("app::main", "fn caller() -> Int64 { 1 }\n") ])
        ~names:[ lowered "callee" ]);
  test "a removed reference collects exactly the instances that only it reached" (fun () ->
      let program test =
        [
          ( "app::main",
            "fn shared() -> Int64 { 1 }\n\
             fn only() -> Int64 { shared() + 1 }\n\
             fn kept() -> Int64 { shared() }\n\
             test \"sums\" {\n\
            \  assert " ^ test ^ "\n}\n" );
        ]
      in
      let before = program "kept() + only() == 3" in
      let after = program "kept() == 1" in
      let observed = propagate (built before) ~before ~after in
      let collected =
        List.filter (fun part -> not (String.starts_with ~prefix:"layout" part)) observed.collected
      in
      if collected <> [ ground_types "only"; lowered "only"; test_key "only" ] then
        fail "collected %s" (String.concat ", " collected);
      expect_untouched observed.recomputed ~names:[ lowered "shared"; lowered "kept" ]);
  test "removing a type collects the instances at that type without computing them" (fun () ->
      let program shape =
        [
          ( "app::main",
            shape
            ^ "test \"lists\" {\n\
              \  let shapes = [Shape(size: 1)]\n\
              \  assert shapes.length() == 1\n\
               }\n" );
        ]
      in
      expect_untouched
        (propagated ~before:(program "type Shape(size: Int64)\n") ~after:(program ""))
        ~names:[ "[Shape]" ]);
  test "a test that reaches a type defined as todo is blocked until the type is defined" (fun () ->
      let program definition =
        [
          ( "app::main",
            "type Session" ^ definition
            ^ "\n\
               fn none() -> Option[Session] { None }\n\
               test \"reaches\" {\n\
              \  assert none().is_none()\n\
               }\n" );
        ]
      in
      expect_included
        (propagated ~before:(program " = todo") ~after:(program "(id: Int64)"))
        ~parts:[ "layout Session"; lowered "none" ]);
  test "an edit to a constant recomputes the constants that fold it, in order" (fun () ->
      let constants first =
        [
          ( "app::main",
            "let first: Int64 = " ^ first
            ^ "\nlet second: Int64 = first + 1\nfn read() -> Int64 { second }\n" );
        ]
      in
      expect_included
        (laid_out ~roots:[ "read" ] ~before:(constants "1") ~after:(constants "2"))
        ~parts:[ lowered "first"; lowered "second" ]);
  test "adding a dependency to a manifest fixes the dependent's use of it" (fun () ->
      expect_included
        (relaid ~before:(Support.setup tool_user)
           ~after:(Support.setup ~dependencies:[ ("app", "lib") ] tool_user)
           ())
        ~parts:[ "namespace app::main"; "checked body app::main::caller" ]);
  test "adding a package and then removing it matches a cold build each time" (fun () ->
      let alone = Support.setup [ ("app::main", "fn caller() -> Int64 { 1 }\n") ] in
      let with_lib = Support.setup ~dependencies:[ ("app", "lib") ] tool_user in
      ignore (relaid ~before:alone ~after:with_lib ());
      expect_untouched
        (List.filter
           (fun part -> not (String.starts_with ~prefix:"successors app " part))
           (relaid ~before:with_lib ~after:alone ()))
        ~names:[ "lib::" ]);
  test "a new version of a loaded package recomputes only the readers of what changed" (fun () ->
      let version second =
        loaded_package
          [
            ( "lib::tools",
              "public fn first() -> Int64 { 1 }\npublic fn second() -> " ^ second ^ " { 2 }\n" );
          ]
      in
      let app =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [
            ( "app::main",
              "use lib::tools\n\
               fn uses_first() -> Int64 { tools::first() }\n\
               fn uses_second() -> Int64 { 1 }\n\
               fn calls_second() { tools::second() }\n" );
          ]
      in
      let recomputed =
        relaid ~loaded:([ version "Int64" ], [ version "Int32" ]) ~before:app ~after:app ()
      in
      expect_included recomputed ~parts:[ "checked body app::main::calls_second" ];
      expect_untouched recomputed ~names:[ "app::main::uses_first"; "app::main::uses_second" ]);
  test "reformatting an invariant recomputes the derived Deserialize and none of its readers"
    (fun () ->
      let signup invariant =
        [
          ( "app::main",
            "use standard::serialization\ntype Signup(age: UInt32)\n  invariant " ^ invariant
            ^ "\n  derives serialization::Deserialize\n" );
        ]
      in
      expect_recomputed
        (propagated ~before:(signup "age >= 13") ~after:(signup "age  >=\t13"))
        ~exactly:
          [
            "derived form derived standard::serialization::Deserialize for \
             app::main::Signup.deserialize";
            "entries app::main";
            "import check app/main/main.truss";
            "namespace app::main";
            "package check app type app::main::Signup";
            "parsed app/main/main.truss";
            "proof app::main::Signup";
          ])

let lowered_program test =
  [
    ( "app::main",
      "type Box(value: Int64) derives Equal\n\
       let base: Int64 = 2\n\
       fn shared() -> Int64 { base }\n\
       fn only() -> Int64 { shared() + 1 }\n\
       fn kept() -> Int64 { shared() }\n\
       fn same(left: Box, right: Box) -> Bool { left == right }\n\
       test \"sums\" {\n\
      \  assert " ^ test ^ "\n}\n" );
    ("app::main/cycle", cyclic);
  ]

let () =
  test "a database saved after a cold build and reopened recomputes nothing" (fun () ->
      let files = lowered_program "kept() + only() == 5" in
      let log = committed [] (saved (built ~roots:[ "same" ] files)) in
      expect_recomputed (reopened_recomputes ~roots:[ "same" ] log files).recomputed ~exactly:[]);
  test "a database reopened with a changed file recomputes what propagating the change does"
    (fun () ->
      let before = [ ("app::main", callee_and_caller) ] in
      let after =
        [
          ( "app::main",
            "fn callee(x: Int64) -> Int64 { x + 2 }\nfn caller() -> Int64 { callee(1) }\n" );
        ]
      in
      let log = committed [] (saved (built before)) in
      expect_recomputed (reopened_recomputes log after).recomputed
        ~exactly:(propagated ~before ~after));
  test "a database reopened without a file it saved removes the file's definitions" (fun () ->
      let log = committed [] (saved (built with_helper)) in
      ignore (reopened_recomputes log [ ("app::main", callee_and_caller) ]));
  test "a database saved after a change set reopens as the propagated database" (fun () ->
      let before = lowered_program "kept() + only() == 5" in
      let after = lowered_program "kept() == 2" in
      let hot = built before in
      let log = committed [] (saved hot) in
      ignore (propagate hot ~before ~after);
      let log = committed log (saved hot) in
      expect_recomputed (reopened_recomputes log after).recomputed ~exactly:[]);
  test "a database saved after a partial drain reopens with its stale parts" (fun () ->
      let before = lowered_program "kept() + only() == 5" in
      let after = lowered_program "kept() == 2" in
      let hot = built before in
      let log = committed [] (saved hot) in
      Pipeline.update hot (changes ~before ~after);
      Pipeline.check hot [ (Support.module_of "app::main").package ];
      let log = committed log (saved hot) in
      let propagated =
        (Pipeline.For_testing.observe hot (fun () -> Pipeline.propagate hot)).recomputed
      in
      expect_recomputed (reopened_recomputes log after).recomputed ~exactly:propagated);
  test "a database saved after a package is removed reopens without the package" (fun () ->
      let with_lib = Support.setup ~dependencies:[ ("app", "lib") ] tool_user in
      let alone = [ ("app::main", "fn caller() -> Int64 { 1 }\n") ] in
      let hot = settled [] with_lib in
      let log = committed [] (saved hot) in
      Pipeline.relayout hot ~loaded:[ Lazy.force standard ] (Support.setup alone);
      Pipeline.propagate hot;
      let log = committed log (saved hot) in
      expect_recomputed (reopened_recomputes log alone).recomputed ~exactly:[])

let project files =
  let root = Harness.scratch "project" in
  Harness.write_files root
    (("truss.toml", "[package]\nname = \"app\"\ntruss = \"0.1\"\n")
    :: List.map (fun (path, text) -> (path ^ ".truss", text)) files);
  root

let opened root =
  match Database.take_snapshot root with
  | Ok (snapshot, _) -> snapshot
  | Error message -> failwith message

let settled_on_disk root =
  let snapshot = opened root in
  let pipeline = Database.pipeline snapshot in
  let observed = Pipeline.For_testing.observe pipeline (fun () -> Pipeline.propagate pipeline) in
  let cold = Database.For_testing.cold_pipeline snapshot in
  Pipeline.propagate cold;
  (match Pipeline.For_testing.differences pipeline cold with
  | [] -> ()
  | parts ->
      fail "the database in .truss differs from a cold build in %s" (String.concat ", " parts));
  observed.recomputed

let edited_body = "fn callee(x: Int64) -> Int64 { x + 2 }\nfn caller() -> Int64 { callee(1) }\n"

let () =
  test "a database written to .truss and reopened recomputes nothing" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settled_on_disk root);
      Database.flush ();
      expect_recomputed (settled_on_disk root) ~exactly:[];
      Database.flush ());
  test "a copy of a project with a changed file recomputes what propagating the change does"
    (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settled_on_disk root);
      Database.flush ();
      let copy = Harness.scratch "copy" in
      if Sys.command (Filename.quote_command "cp" [ "-R"; root ^ "/."; copy ]) <> 0 then
        fail "cannot copy %s" root;
      Harness.write_files copy [ ("main/main.truss", edited_body) ];
      let copied = settled_on_disk copy in
      Database.flush ();
      ignore (opened root);
      Harness.write_files root [ ("main/main.truss", edited_body) ];
      let propagated = settled_on_disk root in
      Database.flush ();
      expect_recomputed copied ~exactly:propagated);
  test "an interrupted commit leaves the database as it was before the change set" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settled_on_disk root);
      Database.flush ();
      Harness.write_files root [ ("main/main.truss", edited_body) ];
      ignore (settled_on_disk root);
      Database.For_testing.interrupt_commit (Database.root (opened root));
      Harness.write_files root [ ("main/main.truss", callee_and_caller) ];
      expect_recomputed (settled_on_disk root) ~exactly:[];
      Database.flush ());
  test "a database written by another compiler is rebuilt" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settled_on_disk root);
      Database.flush ();
      let list = Filename.concat root ".truss/list" in
      File_system.write list
        (String.concat "\n"
           (List.map
              (fun line ->
                if String.starts_with ~prefix:"header compiler " line then "header compiler other"
                else line)
              (String.split_on_char '\n' (File_system.read list))));
      expect_included (settled_on_disk root)
        ~parts:[ "namespace app::main"; "checked body app::main::caller" ];
      Database.flush ())

let expect_cold pipeline snapshot =
  let cold = Database.For_testing.cold_pipeline snapshot in
  Pipeline.propagate cold;
  match Pipeline.For_testing.differences pipeline cold with
  | [] -> ()
  | parts -> fail "the database differs from a cold build in %s" (String.concat ", " parts)

let () =
  test "a trial is a copy of the database, propagated with the files that differ" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      let snapshot = opened root in
      let worktree = Database.pipeline snapshot in
      Pipeline.propagate worktree;
      let trial = Database.trial snapshot [ ("main/main.truss", Some edited_body) ] in
      let pipeline = Database.pipeline trial in
      let recomputed =
        (Pipeline.For_testing.observe pipeline (fun () -> Pipeline.propagate pipeline)).recomputed
      in
      expect_included recomputed ~parts:[ "checked body app::main::callee" ];
      expect_untouched recomputed ~names:[ "app::main::caller" ];
      expect_cold pipeline trial;
      expect_cold worktree snapshot;
      Database.flush ());
  test "a trial that renames the package leaves the worktree's database as it was" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      let snapshot = opened root in
      let worktree = Database.pipeline snapshot in
      Pipeline.propagate worktree;
      let trial =
        Database.trial snapshot
          [ ("truss.toml", Some "[package]\nname = \"tool\"\ntruss = \"0.1\"\n") ]
      in
      let pipeline = Database.pipeline trial in
      Pipeline.propagate pipeline;
      expect_cold pipeline trial;
      expect_cold worktree snapshot;
      Database.flush ())
