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

(* What each instance of a small program refers to. *)
let references program key =
  Reachable.compiled_references (shape_env ()) (Lir.Code (lookup program key))

(* The key of everything an instance can reach, composed as the queries of
   [Compile] compose it. *)
let reach_key program root =
  let own key =
    Reachable.own_hash ~references:(references program key) (Lir.Code (lookup program key))
  in
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
         [ local (Lir.Value int32) ]
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
                | Table t -> Instance.to_string t.table_key)
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
    reach_key (named_program ~entry_name ~helper_name returned) (key entry_name)
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
      then fail "the keys are equal");
  test "changing a helper changes its own hash and not its caller's" (fun () ->
      let own returned name =
        let program = named_program ~entry_name:"start" ~helper_name:"helper" returned in
        let compiled = Lir.Code (lookup program (key name)) in
        Reachable.own_hash
          ~references:(Reachable.compiled_references (shape_env ()) compiled)
          compiled
      in
      if own 1 "helper" = own 2 "helper" then fail "the helper's hash is the same";
      if own 1 "start" <> own 2 "start" then fail "the caller's hash changed");
  test "instances that call each other are one group" (fun () ->
      let found = Reachable.groups ~edges:(references (ping_pong 1)) [ key "start" ] in
      let names key = List.map Instance.to_string (Reachable.Keys.find key found) in
      expect_string ~expected:"test::ping test::pong" (String.concat " " (names (key "ping")));
      if Reachable.Keys.mem (key "start") found then fail "the caller is in a group");
  test "an instance that calls only itself is in no group" (fun () ->
      let again =
        instance "again"
          (function_ ~result:(value int32)
             [ local (Lir.Value int32) ]
             [ block [ call "again" [] (Some (at 0)) ] (Return (Some (copy 0))) ])
      in
      let found = Reachable.groups ~edges:(references [ again ]) [ key "again" ] in
      if not (Reachable.Keys.is_empty found) then fail "found a group");
  test "a test that reaches instances that call each other has a key" (fun () ->
      if reach_key (ping_pong 1) (key "start") = reach_key (ping_pong 2) (key "start") then
        fail "a change inside the group left the key the same");
  test "a group's key does not depend on its instances' names" (fun () ->
      let renamed = List.map (fun (i : Lir.t) -> i) (ping_pong ~ping:"alpha" ~pong:"omega" 1) in
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
      let site : Lir.site =
        { definition = Top { module_ = example; name = "suite" }; line = 2; column = 3 }
      in
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
      match Compile.build_made_tests compile ~time_limit:300 tests ~output with
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
            (match Compile.parse_report out with
            | Ok records -> render_records records
            | Error message -> message))

let () =
  test "an object that a build finds again is as new as that build" (fun () ->
      let directory = Filename.concat (Lazy.force scratch) "aged-objects" in
      let cache = Build.cache directory in
      let objects () =
        match
          Build.objects (Lazy.force compiler) cache settings
            [ ("one", "int one(void) { return 1; }\n") ]
        with
        | Ok [ path ] -> path
        | Ok _ -> failwith "one source made several objects"
        | Error message -> failwith message
      in
      let path = objects () in
      let long_ago = Unix.time () -. (30. *. 86400.) in
      Unix.utimes path long_ago long_ago;
      let found = objects () in
      expect_string ~expected:path found;
      if (Unix.stat found).st_mtime < Unix.time () -. 3600. then
        fail "an object that was found kept the time it was compiled at")

let () =
  test "a program still running at its time limit is stopped" (fun () ->
      let started = Unix.gettimeofday () in
      let status, _, _ = Process.run ~time_limit:100 "/bin/sleep" [ "5" ] in
      if status <> 137 then fail "status %d" status;
      if Unix.gettimeofday () -. started > 2. then fail "it was not stopped")

(* The compiler's libraries *)

type form = Word of string | Forms of form list

(* The forms of a dune file. A comment runs from a semicolon to the end of
   its line, and a string in quotes is one word. *)
let forms text =
  let length = String.length text in
  let rec skip_line i = if i < length && text.[i] <> '\n' then skip_line (i + 1) else i in
  let rec quoted i =
    if text.[i] = '\\' then quoted (i + 2) else if text.[i] = '"' then i + 1 else quoted (i + 1)
  in
  let rec word i =
    if i < length && not (List.mem text.[i] [ ' '; '\n'; '\t'; '('; ')'; ';' ]) then word (i + 1)
    else i
  in
  (* The forms from [i] to the closing parenthesis, and where it is. *)
  let rec several i found =
    if i >= length then (List.rev found, i)
    else
      match text.[i] with
      | ' ' | '\n' | '\t' -> several (i + 1) found
      | ';' -> several (skip_line i) found
      | ')' -> (List.rev found, i + 1)
      | '(' ->
          let inner, next = several (i + 1) [] in
          several next (Forms inner :: found)
      | '"' ->
          let next = quoted (i + 1) in
          several next (Word (String.sub text i (next - i)) :: found)
      | _ ->
          let next = word i in
          several next (Word (String.sub text i (next - i)) :: found)
  in
  fst (several 0 [])

let rec dune_files directory =
  Array.to_list (Sys.readdir directory)
  |> List.concat_map (fun entry ->
      let path = Filename.concat directory entry in
      if Sys.is_directory path then dune_files path else if entry = "dune" then [ path ] else [])

(* Each library under [root]: its name, its directory, and the libraries
   that it lists. *)
let libraries root =
  List.concat_map
    (fun path ->
      List.filter_map
        (function
          | Forms (Word "library" :: fields) ->
              let field name =
                List.find_map
                  (function
                    | Forms (Word found :: values) when found = name ->
                        Some
                          (List.filter_map
                             (function Word word -> Some word | Forms _ -> None)
                             values)
                    | _ -> None)
                  fields
              in
              Option.map
                (fun name ->
                  (name, (Filename.dirname path, Option.value (field "libraries") ~default:[])))
                (Option.bind (field "name") (fun names -> List.nth_opt names 0))
          | _ -> None)
        (forms (In_channel.with_open_bin path In_channel.input_all)))
    (dune_files root)

let () =
  (* The prover and the code database do not depend on code generation,
     and code generation does not depend on the prover. Only a driver sees
     both: the command line, the library that runs compiled code for the
     prover, a test, or a tool. *)
  test "only a driver depends on code generation, which does not depend on the prover" (fun () ->
      let root = "../../../stage0" in
      let libraries = libraries root in
      let directory name = Option.map fst (List.assoc_opt name libraries) in
      let rec reached found name =
        List.fold_left
          (fun found listed ->
            if List.mem listed found || directory listed = None then found
            else reached (listed :: found) listed)
          found
          (match List.assoc_opt name libraries with Some (_, listed) -> listed | None -> [])
      in
      let within part name =
        match directory name with
        | Some directory ->
            let prefix = Filename.concat root part in
            directory = prefix || String.starts_with ~prefix:(prefix ^ "/") directory
        | None -> false
      in
      let drives name =
        List.exists (fun part -> within part name) [ "cli"; "running"; "test"; "tools" ]
      in
      List.iter
        (fun (name, _) ->
          List.iter
            (fun other ->
              if within "codegen" name then
                begin if within "prover" other || drives other then
                  fail "%s is code generation's, and depends on %s" name other
                end
              else if (not (drives name)) && within "codegen" other then
                fail "%s depends on %s, which is code generation's" name other)
            (reached [] name))
        libraries;
      List.iter
        (fun name -> if directory name = None then fail "found no library %s" name)
        [ "compile"; "prover"; "solver"; "database"; "running" ])

let () = Harness.finish ()
