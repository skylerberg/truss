let named_program ~entry_name ~helper_name returned =
  let helper =
    Codegen_support.instance helper_name
      (Codegen_support.function_
         ~result:(Codegen_support.value Codegen_support.int32)
         []
         [ Codegen_support.block [] (Return (Some (Codegen_support.constant_int32 returned))) ])
  in
  let main =
    Codegen_support.instance entry_name
      (Codegen_support.function_
         ~result:(Codegen_support.value Codegen_support.int32)
         [ Codegen_support.local (Lowered.Value Codegen_support.int32) ]
         [
           Codegen_support.block
             [ Codegen_support.call helper_name [] (Some (Codegen_support.at 0)) ]
             (Return (Some (Codegen_support.copy 0)));
         ])
  in
  [ main; helper ]

let lookup instances key =
  let env = Codegen_support.shape_env () in
  Emit_c.fragment env
    (Code
       (List.find
          (fun instance -> Instance.equal (Emit_c.Builder.instance_key instance) key)
          (List.map (fun instance -> instance env) instances)))

let references program key = Emit_c.references (lookup program key)

module Instance_key = Structural_key.Make (struct
  type t = Instance.key
end)

module Instance_table = Hashtbl.Make (Instance_key)

let find_components program root =
  Strongly_connected.find_components (module Instance_key) ~successors:(references program) [ root ]

let reach_key program root =
  let link key = (Reachable.own_hash (lookup program key), references program key) in
  let known = Instance_table.create 16 in
  List.iter
    (fun members ->
      List.iter
        (fun (key, reach_key) -> Instance_table.replace known key reach_key)
        (Reachable.component_keys ~link ~deep:(Instance_table.find known) members))
    (find_components program root);
  Instance_table.find known root

let show_components program root =
  List.map
    (fun members -> String.concat " " (List.map Instance.to_string members))
    (find_components program (Codegen_support.key root))

let ping_pong ?(ping = "ping") ?(pong = "pong") returned =
  let calls name callees =
    Codegen_support.instance name
      (Codegen_support.function_
         ~result:(Codegen_support.value Codegen_support.int32)
         [ Codegen_support.local (Lowered.Value Codegen_support.int32) ]
         [
           Codegen_support.block
             (List.map
                (fun callee -> Codegen_support.call callee [] (Some (Codegen_support.at 0)))
                callees)
             (Return (Some (Codegen_support.copy 0)));
         ])
  in
  let helper =
    Codegen_support.instance "helper"
      (Codegen_support.function_
         ~result:(Codegen_support.value Codegen_support.int32)
         []
         [ Codegen_support.block [] (Return (Some (Codegen_support.constant_int32 returned))) ])
  in
  [ calls "start" [ ping ]; calls ping [ pong ]; calls pong [ ping; "helper" ]; helper ]

let () =
  Codegen_support.test "a build reaches each called instance once, in order" (fun () ->
      let program = named_program ~entry_name:"start" ~helper_name:"helper" 1 in
      let reached = Reachable.reachable ~lookup:(lookup program) [ Codegen_support.key "start" ] in
      Codegen_support.expect_string ~expected:"test::start test::helper"
        (String.concat " "
           (List.map (fun fragment -> Instance.to_string (Emit_c.key fragment)) reached)));
  Codegen_support.test "a drop reaches the type's drop function" (fun () ->
      let dropping_instance =
        Codegen_support.instance "f"
          (Codegen_support.function_ ~parameters:[ 0 ]
             [ Codegen_support.local (Codegen_support.value Codegen_support.text) ]
             [ Codegen_support.block [ Drop (Codegen_support.at 0) ] (Return None) ])
      in
      let references =
        Emit_c.references
          (let env = Codegen_support.shape_env ~extra:Codegen_support.drop_shapes () in
           Emit_c.fragment env (Code (dropping_instance env)))
      in
      Codegen_support.expect_string ~expected:"drop Text"
        (String.concat " " (List.map Instance.to_string references)));
  let test_key ~entry_name ~helper_name returned =
    reach_key (named_program ~entry_name ~helper_name returned) (Codegen_support.key entry_name)
  in
  Codegen_support.test "renaming the definitions a test reaches keeps its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        <> test_key ~entry_name:"begin" ~helper_name:"assist" 1
      then Codegen_support.fail "the keys differ");
  Codegen_support.test "changing the code a test reaches changes its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        = test_key ~entry_name:"start" ~helper_name:"helper" 2
      then Codegen_support.fail "the keys are equal");
  Codegen_support.test "changing a helper changes its own hash and not its caller's" (fun () ->
      let own returned name =
        let program = named_program ~entry_name:"start" ~helper_name:"helper" returned in
        Reachable.own_hash (lookup program (Codegen_support.key name))
      in
      if own 1 "helper" = own 2 "helper" then Codegen_support.fail "the helper's hash is the same";
      if own 1 "start" <> own 2 "start" then Codegen_support.fail "the caller's hash changed");
  Codegen_support.test "instances that call each other are one component, after the ones they reach"
    (fun () ->
      Harness.expect_strings
        ~expected:[ "test::helper"; "test::ping test::pong"; "test::start" ]
        (show_components (ping_pong 1) "start"));
  Codegen_support.test "an instance that calls only itself is a component of its own" (fun () ->
      let again =
        Codegen_support.instance "again"
          (Codegen_support.function_
             ~result:(Codegen_support.value Codegen_support.int32)
             [ Codegen_support.local (Lowered.Value Codegen_support.int32) ]
             [
               Codegen_support.block
                 [ Codegen_support.call "again" [] (Some (Codegen_support.at 0)) ]
                 (Return (Some (Codegen_support.copy 0)));
             ])
      in
      Harness.expect_strings ~expected:[ "test::again" ] (show_components [ again ] "again"));
  Codegen_support.test "a test that reaches instances that call each other has a key" (fun () ->
      if
        reach_key (ping_pong 1) (Codegen_support.key "start")
        = reach_key (ping_pong 2) (Codegen_support.key "start")
      then Codegen_support.fail "a change inside the group left the key the same");
  Codegen_support.test "a group's key does not depend on its instances' names" (fun () ->
      let renamed = ping_pong ~ping:"alpha" ~pong:"omega" 1 in
      if
        reach_key (ping_pong 1) (Codegen_support.key "start")
        <> reach_key renamed (Codegen_support.key "start")
      then Codegen_support.fail "the keys differ")

let () =
  Codegen_support.test
    "the test runner reports each test's outcome, message, and echo output, a leak, and a worker \
     that ends without a word" (fun () ->
      let _, compile =
        Codegen_support.load
          ~roots:[ Code { path = Well_known.path Run_tests; type_arguments = [] } ]
          "fn suite() {\n}\n"
      in
      let site : Lowered.site =
        { definition = Top { module_ = Codegen_support.example; name = "suite" }; offset = 3 }
      in
      let text value = Lowered.Constant (Bytes value) in
      let length value = Lowered.Constant (Integer (UInt64, Z.of_int (String.length value))) in
      let ending failure message =
        Lowered.Fail
          { failure; message = text message; length = length message; site; reported = None }
      in
      let suite name blocks = Codegen_support.instance name (Codegen_support.function_ [] blocks) in
      let tests =
        [
          suite "passes" [ Codegen_support.block [] (Return None) ];
          suite "fails" [ Codegen_support.block [] (ending Assertion "values differ") ];
          suite "panics" [ Codegen_support.block [] (ending Panic "boom") ];
          suite "echoes"
            [
              Codegen_support.block
                [ Echo { text = text "42"; length = length "42"; site } ]
                (Return None);
            ];
          suite "never_ends" [ Codegen_support.block [] (Goto 0) ];
          suite "unfinished" [ Codegen_support.block [] (ending Todo "hole of type Int64") ];
          suite "leaks"
            [
              Codegen_support.block
                [
                  Call
                    {
                      target = Intrinsic Allocate;
                      arguments =
                        [
                          Constant (Integer (UInt64, Z.of_int 8));
                          Constant (Integer (UInt64, Z.one));
                        ];
                      result = Discarded;
                    };
                ]
                (Return None);
            ];
          suite "quits"
            [
              Codegen_support.block
                [
                  Call
                    {
                      target = Foreign (Libc.declaration Codegen_support.host Exit);
                      arguments = [ Codegen_support.constant_int32 3 ];
                      result = Discarded;
                    };
                ]
                Unreachable;
            ];
        ]
      in
      incr Codegen_support.counter;
      let output =
        Filename.concat
          (Lazy.force Codegen_support.scratch)
          (Printf.sprintf "tests%d" !Codegen_support.counter)
      in
      match Compile.For_testing.build_supplied_tests compile ~time_limit_ms:300 tests ~output with
      | Error message -> Codegen_support.fail "%s" message
      | Ok () ->
          let status, out, _ = Process.run output [] in
          Codegen_support.expect_int ~expected:1 status;
          Codegen_support.expect_string
            ~expected:
              (String.concat ""
                 [
                   "test 0 passed\n";
                   "test 1 failed\nmessage 41\nvalues differ\n  at example/main.truss:1:4\n";
                   "test 2 panicked\nmessage 32\nboom\n  at example/main.truss:1:4\n";
                   "test 3 passed\necho 27\nexample/main.truss:1:4: 42\n\n";
                   "test 4 timed_out\nmessage 23\nran past the time limit\n";
                   "test 5 incomplete\n\
                    message 46\n\
                    hole of type Int64\n\
                   \  at example/main.truss:1:4\n";
                   "test 6 panicked\nmessage 45\ncompiler bug: the test left 1 block allocated\n";
                   "test 7 crashed\nmessage 19\nended with status 3\n";
                 ])
            (match Compile.For_testing.parse_report out with
            | Ok records -> Codegen_support.render_records records
            | Error message -> message))

let () =
  Codegen_support.test "an object that a build finds again is as new as that build" (fun () ->
      let directory = Filename.concat (Lazy.force Codegen_support.scratch) "aged-objects" in
      let cache = Build.cache directory in
      let objects () =
        match
          Build.For_testing.objects
            (Lazy.force Codegen_support.compiler)
            cache
            (Lazy.force Codegen_support.settings)
            [ ("one", "int one(void) { return 1; }\n") ]
        with
        | Ok [ path ] -> path
        | Ok _ -> failwith "one source made several objects"
        | Error message -> failwith message
      in
      let path = objects () in
      let long_ago = Unix.time () -. (30. *. 86400.) in
      Unix.utimes path long_ago long_ago;
      let actual = objects () in
      Codegen_support.expect_string ~expected:path actual;
      if (Unix.stat actual).st_mtime < Unix.time () -. 3600. then
        Codegen_support.fail "an object that was found kept the time it was compiled at")
