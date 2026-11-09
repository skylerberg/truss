(* The tests of the query engine: which queries run again after a change.
   See TYPECHECKER.md, "One definition at a time, through queries". *)

open Harness

let expect_log database expected =
  let actual = Query.executed database in
  if actual <> expected then
    fail "expected [%s], ran [%s]" (String.concat "; " expected) (String.concat "; " actual);
  Query.clear_log database

(* A small build: two "files" as inputs, a length per file, and a total that
   reads the lengths. *)
let setup () =
  let database = Query.create () in
  let files = Query.input ~name:"file" ~show:Fun.id () in
  let length =
    Query.query ~name:"length" ~show:Fun.id (fun database file ->
        String.length (Query.get database files file))
  in
  let parity =
    Query.query ~name:"parity" ~show:Fun.id (fun database file ->
        Query.demand database length file mod 2)
  in
  let total =
    Query.query ~name:"total"
      ~show:(fun () -> "")
      (fun database () ->
        let first = Query.demand database parity "a" in
        first + Query.demand database parity "b")
  in
  Query.set database files "a" "one";
  Query.set database files "b" "three";
  (database, files, total)

let () =
  test "a first demand runs every query it reaches" (fun () ->
      let database, _, total = setup () in
      let value = Query.demand database total () in
      if value <> 2 then fail "total %d" value;
      expect_log database [ "total()"; "parity(a)"; "length(a)"; "parity(b)"; "length(b)" ]);
  test "a second demand with no change runs nothing" (fun () ->
      let database, _, total = setup () in
      ignore (Query.demand database total ());
      Query.clear_log database;
      ignore (Query.demand database total ());
      expect_log database []);
  test "a change runs only what read it" (fun () ->
      let database, files, total = setup () in
      ignore (Query.demand database total ());
      Query.clear_log database;
      Query.set database files "b" "four";
      let value = Query.demand database total () in
      if value <> 1 then fail "total %d" value;
      expect_log database [ "length(b)"; "parity(b)"; "total()" ]);
  test "a result that comes out the same stops the work above it" (fun () ->
      let database, files, total = setup () in
      ignore (Query.demand database total ());
      Query.clear_log database;
      Query.set database files "b" "seven";
      ignore (Query.demand database total ());
      expect_log database [ "length(b)" ]);
  test "setting an input to the value it has changes nothing" (fun () ->
      let database, files, total = setup () in
      ignore (Query.demand database total ());
      Query.clear_log database;
      Query.set database files "a" "one";
      ignore (Query.demand database total ());
      expect_log database []);
  test "reading an input that is not set records it" (fun () ->
      let database = Query.create () in
      let files = Query.input ~name:"file" ~show:Fun.id () in
      let present =
        Query.query ~name:"present" ~show:Fun.id (fun database file ->
            Option.is_some (Query.find database files file))
      in
      if Query.demand database present "a" then fail "present before it was set";
      Query.set database files "a" "";
      if not (Query.demand database present "a") then fail "absent after it was set";
      Query.remove database files "a";
      if Query.demand database present "a" then fail "present after it was removed");
  test "a query that asks for itself is a cycle naming each query on it" (fun () ->
      let database = Query.create () in
      let rec first =
        lazy
          (Query.query ~name:"first" ~show:Fun.id (fun database key ->
               Query.demand database (Lazy.force second) key))
      and second =
        lazy
          (Query.query ~name:"second" ~show:Fun.id (fun database key ->
               Query.demand database (Lazy.force first) key + 1))
      in
      match Query.demand database (Lazy.force first) "k" with
      | _ -> fail "no cycle"
      | exception Query.Cycle labels ->
          if labels <> [ "first(k)"; "second(k)" ] then
            fail "cycle [%s]" (String.concat "; " labels));
  test "a query that catches a cycle runs again at the next revision" (fun () ->
      let database = Query.create () in
      let toggle = Query.input ~name:"toggle" ~show:(fun () -> "") () in
      let rec looped =
        lazy
          (Query.query ~name:"looped"
             ~show:(fun () -> "")
             (fun database () ->
               if Query.get database toggle () then Query.demand database (Lazy.force looped) ()
               else 0))
      in
      let guarded =
        Query.query ~name:"guarded"
          ~show:(fun () -> "")
          (fun database () ->
            try Query.demand database (Lazy.force looped) () with Query.Cycle _ -> -1)
      in
      Query.set database toggle () true;
      if Query.demand database guarded () <> -1 then fail "no cycle while toggled";
      Query.set database toggle () false;
      if Query.demand database guarded () <> 0 then fail "cycle kept after it was removed")

let () = finish ()
