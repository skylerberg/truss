let make_named_program ~entry_name ~helper_name returned =
  let helper =
    Codegen_support.define_function helper_name
      (Codegen_support.function_
         ~result:(Codegen_support.value Codegen_support.int32)
         []
         [ Codegen_support.block [] (Return (Some (Codegen_support.constant_int32 returned))) ])
  in
  let main =
    Codegen_support.define_function entry_name
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

let lookup program wanted =
  let env = Codegen_support.make_shape_env () in
  List.find
    (fun fragment -> Lowered.Item.equal (Emit_c.item fragment) wanted)
    (List.map (fun program_fragment -> program_fragment env) program)

let list_references program item = Emit_c.references (lookup program item)

module Item_table = Hashtbl.Make (Lowered.Item)

let list_components program root =
  Strongly_connected.list_components
    (module Lowered.Item)
    ~list_successors:(list_references program) [ root ]

let derive_component_keys program ~read_known_key component =
  match
    Lowering.derive_test_keys
      ~read_lowered:(fun item -> Ok (Lowering.Compiled (lookup program item)))
      ~read_known_key:(fun item -> Ok (read_known_key item))
      component
  with
  | Ok keys -> keys
  | Error _ -> Codegen_support.fail "a program of supplied fragments cannot be built"

let derive_test_key program root =
  let known = Item_table.create 16 in
  List.iter
    (fun component ->
      List.iter
        (fun (key, test_key) -> Item_table.replace known key test_key)
        (derive_component_keys program ~read_known_key:(Item_table.find known) component))
    (list_components program root);
  Item_table.find known root

let show_components program root =
  List.map
    (fun members -> String.concat " " (List.map Lowered.Item.to_string members))
    (list_components program (Codegen_support.code_item root))

let make_ping_pong returned =
  let make_caller name callees =
    Codegen_support.define_function name
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
    Codegen_support.define_function "helper"
      (Codegen_support.function_
         ~result:(Codegen_support.value Codegen_support.int32)
         []
         [ Codegen_support.block [] (Return (Some (Codegen_support.constant_int32 returned))) ])
  in
  [
    make_caller "start" [ "ping" ];
    make_caller "ping" [ "pong" ];
    make_caller "pong" [ "ping"; "helper" ];
    helper;
  ]

let () =
  Codegen_support.test "a drop reaches the type's drop function" (fun () ->
      let dropping_function =
        Codegen_support.define_function "f"
          (Codegen_support.function_ ~parameters:[ 0 ]
             [ Codegen_support.local (Codegen_support.value Codegen_support.text) ]
             [ Codegen_support.block [ Drop (Codegen_support.at 0) ] (Return None) ])
      in
      let references =
        Emit_c.references
          (let env = Codegen_support.make_shape_env ~extra:Codegen_support.drop_shapes () in
           dropping_function env)
      in
      Codegen_support.expect_string ~expected:"drop Text"
        (String.concat " " (List.map Lowered.Item.to_string references)));
  let test_key ~entry_name ~helper_name returned =
    derive_test_key
      (make_named_program ~entry_name ~helper_name returned)
      (Codegen_support.code_item entry_name)
  in
  Codegen_support.test "renaming a definition that a test reaches changes its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        = test_key ~entry_name:"start" ~helper_name:"assist" 1
      then Codegen_support.fail "the keys are equal");
  Codegen_support.test "changing the code a test reaches changes its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        = test_key ~entry_name:"start" ~helper_name:"helper" 2
      then Codegen_support.fail "the keys are equal");
  Codegen_support.test "a caller's key reads its callee's code only through the callee's key"
    (fun () ->
      let start = Codegen_support.code_item "start" in
      let derive_start_key returned =
        List.assoc start
          (derive_component_keys
             (make_named_program ~entry_name:"start" ~helper_name:"helper" returned)
             ~read_known_key:(fun _ -> "the callee's key")
             [ start ])
      in
      if derive_start_key 1 <> derive_start_key 2 then
        Codegen_support.fail "the caller's key changed");
  Codegen_support.test "items that call each other are one component, after the ones they reach"
    (fun () ->
      Harness.expect_strings
        ~expected:[ "test.helper"; "test.ping test.pong"; "test.start" ]
        (show_components (make_ping_pong 1) "start"));
  Codegen_support.test "an item that calls only itself is a component of its own" (fun () ->
      let again =
        Codegen_support.define_function "again"
          (Codegen_support.function_
             ~result:(Codegen_support.value Codegen_support.int32)
             [ Codegen_support.local (Lowered.Value Codegen_support.int32) ]
             [
               Codegen_support.block
                 [ Codegen_support.call "again" [] (Some (Codegen_support.at 0)) ]
                 (Return (Some (Codegen_support.copy 0)));
             ])
      in
      Harness.expect_strings ~expected:[ "test.again" ] (show_components [ again ] "again"));
  Codegen_support.test "a test that reaches items that call each other has a key" (fun () ->
      if
        derive_test_key (make_ping_pong 1) (Codegen_support.code_item "start")
        = derive_test_key (make_ping_pong 2) (Codegen_support.code_item "start")
      then Codegen_support.fail "a change inside the group left the key the same");
  Codegen_support.test "the items of a group have keys of their own" (fun () ->
      let program = make_ping_pong 1 in
      if
        derive_test_key program (Codegen_support.code_item "ping")
        = derive_test_key program (Codegen_support.code_item "pong")
      then Codegen_support.fail "the keys are equal")

let () =
  Codegen_support.test
    "the test runner reports each test's outcome, message, and echo output, a leak, and a worker \
     that ends without a word" (fun () ->
      let database, backend =
        Codegen_support.load
          ~roots:
            [
              Code
                {
                  path = Well_known.make_path Run_tests;
                  instantiation = Ground.no_instantiation;
                  assumes_condition = false;
                };
            ]
          "fn suite() {\n}\n"
      in
      let site : Lowered.site =
        { definition = Top { module_ = Codegen_support.example; name = "suite" }; offset = 3 }
      in
      let make_text value = Lowered.Constant (Bytes value) in
      let make_length value = Lowered.Constant (Integer (UInt64, Z.of_int (String.length value))) in
      let make_ending failure message =
        Lowered.Fail
          {
            failure;
            message = make_text message;
            length = make_length message;
            site;
            reported = None;
            trace = None;
          }
      in
      let make_suite name blocks =
        Codegen_support.define_function name (Codegen_support.function_ [] blocks)
      in
      let tests =
        [
          make_suite "passes" [ Codegen_support.block [] (Return None) ];
          make_suite "fails" [ Codegen_support.block [] (make_ending Assertion "values differ") ];
          make_suite "panics" [ Codegen_support.block [] (make_ending Panic "boom") ];
          make_suite "echoes"
            [
              Codegen_support.block
                [ Echo { text = make_text "42"; length = make_length "42"; site } ]
                (Return None);
            ];
          make_suite "never_ends" [ Codegen_support.block [] (Goto 0) ];
          make_suite "unfinished"
            [ Codegen_support.block [] (make_ending Todo "hole of type Int64") ];
          make_suite "leaks"
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
          make_suite "quits"
            [
              Codegen_support.block
                [
                  Call
                    {
                      target = Foreign (Libc.make_declaration Codegen_support.host Exit);
                      arguments = [ Codegen_support.constant_int32 3 ];
                      result = Discarded;
                    };
                ]
                Unreachable;
            ];
        ]
      in
      let env = Lowering.make_env Codegen_support.host (Database.make_interface_lookups database) in
      let roots =
        List.map
          (fun make_fragment ->
            let fragment = make_fragment env in
            Database.For_testing.supply_lowered database (Emit_c.item fragment) (Compiled fragment);
            Emit_c.item fragment)
          tests
      in
      Database.For_testing.lower_roots database;
      let output = Codegen_support.make_scratch_path "tests" in
      match Backend.For_testing.build_test_program backend ~time_limit_ms:300 roots ~output with
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
            (match Backend.Test_report.For_testing.parse ~tests:8 out with
            | Ok records -> Codegen_support.render_records records
            | Error message -> message))

let () =
  List.iter
    (fun (name, profile) ->
      Codegen_support.test
        (Printf.sprintf "a %s build of a program that was built before renders no unit" name)
        (fun () ->
          let _, backend =
            Codegen_support.load ~profile
              "fn double(value: Int64) -> Int64\n\
              \  requires value >= 0 && value <= 100\n\
               {\n\
              \  value * 2\n\
               }\n\
               fn main(arguments: Slice[String]) -> ExitCode {\n\
              \  if double(21) == 42 { ExitCode.success } else { ExitCode.failure }\n\
               }\n"
          in
          let build () =
            match Codegen_support.build_program backend ~main:Codegen_support.example_main with
            | Ok _ -> ()
            | Error message -> Codegen_support.fail "%s" message
          in
          build ();
          let rendered = Backend.For_testing.count_rendered_units () in
          build ();
          Codegen_support.expect_int ~expected:rendered
            (Backend.For_testing.count_rendered_units ())))
    [ ("development", Backend.Development); ("release", Release) ]

let () =
  Codegen_support.test "an object that a build finds again is as new as that build" (fun () ->
      let directory = Filename.concat (Lazy.force Codegen_support.scratch) "aged-objects" in
      let c_compiler =
        match C_compiler.find ~objects:directory () with
        | Ok c_compiler -> c_compiler
        | Error message -> failwith message
      in
      let compile_objects () =
        match
          C_compiler.For_testing.compile_objects c_compiler Development
            [ C_compiler.make_source ~name:"one" "int one(void) { return 1; }\n" ]
        with
        | Ok [ path ] -> path
        | Ok _ -> failwith "one source made several objects"
        | Error message -> failwith message
      in
      let path = compile_objects () in
      let long_ago = Unix.time () -. (30. *. 86400.) in
      Unix.utimes path long_ago long_ago;
      let actual = compile_objects () in
      Codegen_support.expect_string ~expected:path actual;
      if (Unix.stat actual).st_mtime < Unix.time () -. 3600. then
        Codegen_support.fail "an object that was found kept the time it was compiled at")

let () =
  Codegen_support.test "a release object names its Truss file and no directory it was built in"
    (fun () ->
      let directory = Filename.concat (Lazy.force Codegen_support.scratch) "release-objects" in
      let c_compiler =
        match C_compiler.find ~objects:directory () with
        | Ok c_compiler -> c_compiler
        | Error message -> failwith message
      in
      match
        C_compiler.For_testing.compile_objects c_compiler Release
          [
            C_compiler.make_source ~name:"one"
              "#line 3 \"example/main.truss\"\nint one(void) { return 1; }\n";
          ]
      with
      | Ok [ path ] ->
          let object_bytes = In_channel.with_open_bin path In_channel.input_all in
          if not (String.includes ~affix:"example/main.truss" object_bytes) then
            Codegen_support.fail "the object does not name example/main.truss";
          List.iter
            (fun named ->
              if String.includes ~affix:named object_bytes then
                Codegen_support.fail "the object names %s" named)
            [ Sys.getcwd (); directory ]
      | Ok _ -> failwith "one source made several objects"
      | Error message -> failwith message)

let () =
  Codegen_support.test
    "a release object names a file of a project's package by its path in the project" (fun () ->
      let directory = Filename.concat (Lazy.force Codegen_support.scratch) "placed-objects" in
      let c_compiler =
        match
          C_compiler.find
            ~debug_prefix_maps:[ ("example/", "packages/example/") ]
            ~objects:directory ()
        with
        | Ok c_compiler -> c_compiler
        | Error message -> failwith message
      in
      match
        C_compiler.For_testing.compile_objects c_compiler Release
          [
            C_compiler.make_source ~name:"one"
              "#line 3 \"example/main.truss\"\nint one(void) { return 1; }\n";
          ]
      with
      | Ok [ path ] ->
          let object_bytes = In_channel.with_open_bin path In_channel.input_all in
          if not (String.includes ~affix:"packages/example" object_bytes) then
            Codegen_support.fail "the object does not name packages/example"
      | Ok _ -> failwith "one source made several objects"
      | Error message -> failwith message)

let () =
  Codegen_support.test "a release object of the program's start attributes its code to <runtime>"
    (fun () ->
      let directory = Filename.concat (Lazy.force Codegen_support.scratch) "startup-objects" in
      let c_compiler =
        match C_compiler.find ~objects:directory () with
        | Ok c_compiler -> c_compiler
        | Error message -> failwith message
      in
      match
        C_compiler.For_testing.compile_objects c_compiler Release
          [ C_compiler.make_source ~name:"startup" (Startup.render_program_start "truss_entry") ]
      with
      | Ok [ path ] ->
          let object_bytes = In_channel.with_open_bin path In_channel.input_all in
          if not (String.includes ~affix:"<runtime>" object_bytes) then
            Codegen_support.fail "the object does not name <runtime>";
          if String.includes ~affix:"<stdin>" object_bytes then
            Codegen_support.fail "the object names <stdin>"
      | Ok _ -> failwith "one source made several objects"
      | Error message -> failwith message)
