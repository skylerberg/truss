(* What a build reaches, test keys, and the test runner. *)

open Memory_layout
open Codegen_support

(* What a build reaches, and test keys *)

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
         [ local (Lir.Value int32) ]
         [ block [ call helper_name [] (Some (at 0)) ] (Return (Some (copy 0))) ])
  in
  [ main; helper ]

let lookup instances key = List.find (fun (i : Lir.t) -> Instance.equal i.key key) instances

let () =
  test "a build reaches each called instance once, in order" (fun () ->
      let program = named_program ~entry_name:"start" ~helper_name:"helper" 1 in
      let reached =
        Reachable.reachable (shape_env ())
          ~lookup:(fun k -> Lir.Code (lookup program k))
          [ key "start" ]
      in
      expect_string ~expected:"test::start test::helper"
        (String.concat " "
           (List.map
              (function
                | Lir.Code i -> Instance.to_string i.key
                | Data d -> Instance.to_string d.data_key
                | Table t -> Instance.to_string t.table_key
                | Evidence e -> Instance.to_string e.evidence_key)
              reached)));
  test "a drop reaches the type's drop function" (fun () ->
      let f =
        instance "f"
          (function_ ~parameters:[ 0 ]
             [ local (value text) ]
             [ block [ Drop (at 0) ] (Return None) ])
      in
      let references = Reachable.references (shape_env ~extra:drop_shapes ()) f in
      expect_string ~expected:"drop Text"
        (String.concat " " (List.map Instance.to_string references)));
  let test_key ~entry_name ~helper_name returned =
    let program = named_program ~entry_name ~helper_name returned in
    Reachable.test_key (shape_env ())
      ~lookup:(fun k -> Lir.Code (lookup program k))
      (key entry_name)
  in
  test "renaming the definitions a test reaches keeps its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        <> test_key ~entry_name:"begin" ~helper_name:"assist" 1
      then fail "the keys differ");
  test "changing what a test reaches changes its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        = test_key ~entry_name:"start" ~helper_name:"helper" 2
      then fail "the keys are equal")

(* The test runner *)

let () =
  test "the test runner reports each test's outcome, message, and echo output in order, and a leak"
    (fun () ->
      let site : Lir.site = { definition = definition "suite"; line = 2; column = 3 } in
      let text value = Lir.Constant (Bytes value) in
      let length value = Lir.Constant (Integer (USize, Z.of_int (String.length value))) in
      let ending failure message =
        Lir.Fail { failure; message = text message; length = length message; site }
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
        ]
      in
      incr counter;
      let output = Filename.concat (Lazy.force scratch) (Printf.sprintf "tests%d" !counter) in
      let symbols = List.map (fun (t : Lir.t) -> Instance.symbol t.key) tests in
      let sources =
        [
          ("tests", Startup.tests_calling ~time_limit:300 symbols);
          ( "anchors",
            Positions.anchors_file target_64
              [ { definition = definition "suite"; path = "suite.truss"; first_line = 10 } ] );
        ]
      in
      match
        Build.program (Lazy.force compiler) (Lazy.force cache) (shape_env ()) settings
          ~files:[ List.map (fun t -> Lir.Code t) tests ]
          ~sources ~output
      with
      | Error message -> fail "%s" message
      | Ok () ->
          let status, out, _ = Toolchain.run output [] in
          expect_int ~expected:1 status;
          expect_string
            ~expected:
              (String.concat ""
                 [
                   "test 0 passed\n";
                   "test 1 failed\nmessage 35\nvalues differ\n  at suite.truss:12:3\n";
                   "test 2 panicked\nmessage 26\nboom\n  at suite.truss:12:3\n";
                   "test 3 passed\necho 21\nsuite.truss:12:3: 42\n\n";
                   "test 4 timed_out\nmessage 23\nran past the time limit\n";
                   "test 5 incomplete\nmessage 40\nhole of type Int64\n  at suite.truss:12:3\n";
                   "test 6 panicked\nmessage 45\ncompiler bug: the test left 1 block allocated\n";
                 ])
            out)

let () = Harness.finish ()
