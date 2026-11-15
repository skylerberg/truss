(* The instances a build reaches, test keys, and the test runner. *)

open Memory_layout
open Codegen_support

(* Reachable instances, and test keys *)

(* A program whose [entry] calls [helper], under the given names, and whose
   [helper] returns [value]. *)
let named_program ~entry_name ~helper_name returned =
  let helper =
    instance helper_name
      (function_ ~result:(value int32) [] [ block [] (Return (Some (constant_int32 returned))) ])
  in
  let main =
    instance entry_name
      (function_ ~result:(value int32)
         [ local (Lowered.Value int32) ]
         [ block [ call helper_name [] (Some (at 0)) ] (Return (Some (copy 0))) ])
  in
  [ main; helper ]

(* An instance of a small program, as C. *)
let lookup instances key =
  let env = shape_env () in
  Emit_c.fragment env
    (Code
       (List.find
          (fun instance -> Instance.equal (Emit_c.Builder.instance_key instance) key)
          (List.map (fun instance -> instance env) instances)))

(* Each instance's references in a small program. *)
let references program key = Emit_c.references (lookup program key)

(* The key of everything an instance can reach, composed as the queries of
   [Compile] compose it. *)
let reach_key program root =
  let own key = Reachable.own_hash (lookup program key) in
  let groups = Reachable.groups ~edges:(references program) [ root ] in
  let rec reach key =
    match Reachable.Keys.find_opt key groups with
    | None -> Reachable.unit_key ~own:(own key) (List.map reach (references program key))
    | Some members ->
        Reachable.group_key
          ~link:(fun member -> (own member, references program member))
          ~deep:reach ~members key
  in
  reach root

(* A program whose [start] calls [ping], which calls [pong], which calls
   [ping] and a helper that returns [returned]. *)
let ping_pong ?(ping = "ping") ?(pong = "pong") returned =
  let calls name callees =
    instance name
      (function_ ~result:(value int32)
         [ local (Lowered.Value int32) ]
         [
           block
             (List.map (fun callee -> call callee [] (Some (at 0))) callees)
             (Return (Some (copy 0)));
         ])
  in
  let helper =
    instance "helper"
      (function_ ~result:(value int32) [] [ block [] (Return (Some (constant_int32 returned))) ])
  in
  [ calls "start" [ ping ]; calls ping [ pong ]; calls pong [ ping; "helper" ]; helper ]

let () =
  test "a build reaches each called instance once, in order" (fun () ->
      let program = named_program ~entry_name:"start" ~helper_name:"helper" 1 in
      let reached = Reachable.reachable ~lookup:(lookup program) [ key "start" ] in
      expect_string ~expected:"test::start test::helper"
        (String.concat " "
           (List.map (fun fragment -> Instance.to_string (Emit_c.key fragment)) reached)));
  test "a drop reaches the type's drop function" (fun () ->
      let dropping_instance =
        instance "f"
          (function_ ~parameters:[ 0 ]
             [ local (value text) ]
             [ block [ Drop (at 0) ] (Return None) ])
      in
      let references =
        Emit_c.references
          (let env = shape_env ~extra:drop_shapes () in
           Emit_c.fragment env (Code (dropping_instance env)))
      in
      expect_string ~expected:"drop Text"
        (String.concat " " (List.map Instance.to_string references)));
  let test_key ~entry_name ~helper_name returned =
    reach_key (named_program ~entry_name ~helper_name returned) (key entry_name)
  in
  test "renaming the definitions a test reaches keeps its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        <> test_key ~entry_name:"begin" ~helper_name:"assist" 1
      then fail "the keys differ");
  test "changing the code a test reaches changes its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        = test_key ~entry_name:"start" ~helper_name:"helper" 2
      then fail "the keys are equal");
  test "changing a helper changes its own hash and not its caller's" (fun () ->
      let own returned name =
        let program = named_program ~entry_name:"start" ~helper_name:"helper" returned in
        Reachable.own_hash (lookup program (key name))
      in
      if own 1 "helper" = own 2 "helper" then fail "the helper's hash is the same";
      if own 1 "start" <> own 2 "start" then fail "the caller's hash changed");
  test "instances that call each other are one group" (fun () ->
      let actual = Reachable.groups ~edges:(references (ping_pong 1)) [ key "start" ] in
      let names key = List.map Instance.to_string (Reachable.Keys.find key actual) in
      expect_string ~expected:"test::ping test::pong" (String.concat " " (names (key "ping")));
      if Reachable.Keys.mem (key "start") actual then fail "the caller is in a group");
  test "an instance that calls only itself is in no group" (fun () ->
      let again =
        instance "again"
          (function_ ~result:(value int32)
             [ local (Lowered.Value int32) ]
             [ block [ call "again" [] (Some (at 0)) ] (Return (Some (copy 0))) ])
      in
      let actual = Reachable.groups ~edges:(references [ again ]) [ key "again" ] in
      if not (Reachable.Keys.is_empty actual) then fail "found a group");
  test "a test that reaches instances that call each other has a key" (fun () ->
      if reach_key (ping_pong 1) (key "start") = reach_key (ping_pong 2) (key "start") then
        fail "a change inside the group left the key the same");
  test "a group's key does not depend on its instances' names" (fun () ->
      let renamed = ping_pong ~ping:"alpha" ~pong:"omega" 1 in
      if reach_key (ping_pong 1) (key "start") <> reach_key renamed (key "start") then
        fail "the keys differ")

(* The test runner *)

let () =
  test
    "the test runner reports each test's outcome, message, and echo output, a leak, and a worker \
     that ends without a word" (fun () ->
      (* The tests are made by hand, so that one can leave a block
         allocated, which no source compiles to. They report positions in a
         definition of a module that is loaded. *)
      let _, compile = load "fn suite() {\n}\n" in
      let site : Lowered.site =
        { definition = Top { module_ = example; name = "suite" }; line = 2; column = 3 }
      in
      let text value = Lowered.Constant (Bytes value) in
      let length value = Lowered.Constant (Integer (USize, Z.of_int (String.length value))) in
      let ending failure message =
        Lowered.Fail
          { failure; message = text message; length = length message; site; reported = None }
      in
      let suite name blocks = instance name (function_ [] blocks) in
      let tests =
        [
          suite "passes" [ block [] (Return None) ];
          suite "fails" [ block [] (ending Assertion "values differ") ];
          suite "panics" [ block [] (ending Panic "boom") ];
          suite "echoes"
            [ block [ Echo { text = text "42"; length = length "42"; site } ] (Return None) ];
          suite "never_ends" [ block [] (Goto 0) ];
          suite "unfinished" [ block [] (ending Todo "hole of type Int64") ];
          suite "leaks"
            [
              block
                [
                  Call
                    {
                      target = Intrinsic Allocate;
                      arguments =
                        [
                          Constant (Integer (USize, Z.of_int 8)); Constant (Integer (USize, Z.one));
                        ];
                      result = Discarded;
                    };
                ]
                (Return None);
            ];
          suite "quits"
            [
              block
                [
                  Call
                    {
                      target = Foreign (Libc.declaration host Exit);
                      arguments = [ constant_int32 3 ];
                      result = Discarded;
                    };
                ]
                Unreachable;
            ];
        ]
      in
      incr counter;
      let output = Filename.concat (Lazy.force scratch) (Printf.sprintf "tests%d" !counter) in
      match Compile.For_testing.build_supplied_tests compile ~time_limit:300 tests ~output with
      | Error message -> fail "%s" message
      | Ok () ->
          let status, out, _ = Process.run output [] in
          expect_int ~expected:1 status;
          expect_string
            ~expected:
              (String.concat ""
                 [
                   "test 0 passed\n";
                   "test 1 failed\nmessage 41\nvalues differ\n  at example/main.truss:3:3\n";
                   "test 2 panicked\nmessage 32\nboom\n  at example/main.truss:3:3\n";
                   "test 3 passed\necho 27\nexample/main.truss:3:3: 42\n\n";
                   "test 4 timed_out\nmessage 23\nran past the time limit\n";
                   "test 5 incomplete\n\
                    message 46\n\
                    hole of type Int64\n\
                   \  at example/main.truss:3:3\n";
                   "test 6 panicked\nmessage 45\ncompiler bug: the test left 1 block allocated\n";
                   "test 7 crashed\nmessage 19\nended with status 3\n";
                 ])
            (match Compile.For_testing.parse_report out with
            | Ok records -> render_records records
            | Error message -> message))

let () =
  test "an object that a build finds again is as new as that build" (fun () ->
      let directory = Filename.concat (Lazy.force scratch) "aged-objects" in
      let cache = Build.cache directory in
      let objects () =
        match
          Build.For_testing.objects (Lazy.force compiler) cache (Lazy.force settings)
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
      expect_string ~expected:path actual;
      if (Unix.stat actual).st_mtime < Unix.time () -. 3600. then
        fail "an object that was found kept the time it was compiled at")

let () =
  test "a program still running at its time limit is stopped" (fun () ->
      let started = Unix.gettimeofday () in
      let status, _, _ = Process.run ~time_limit:100 "/bin/sleep" [ "5" ] in
      if status <> 137 then fail "status %d" status;
      if Unix.gettimeofday () -. started > 2. then fail "it was not stopped")
