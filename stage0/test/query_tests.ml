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
  let database = Query.create ~log:true () in
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
      let database = Query.create ~log:true () in
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
      let database = Query.create ~log:true () in
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
      let database = Query.create ~log:true () in
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

let unit_query name compute = Query.query ~name ~show:(fun () -> "") compute

let () =
  test "a query that raises keeps its trace, so a caller that caught it runs again" (fun () ->
      let database = Query.create ~log:true () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let inner = unit_query "inner" (fun database () -> Query.get database value ()) in
      let outer =
        unit_query "outer" (fun database () ->
            try Query.demand database inner () with Not_found -> 0)
      in
      if Query.demand database outer () <> 0 then fail "unset input read as a value";
      Query.set database value () 5;
      let result = Query.demand database outer () in
      if result <> 5 then fail "stale result %d after the input was set" result);
  test "a query that raised is not run again in the same revision" (fun () ->
      let database = Query.create ~log:true () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let inner = unit_query "inner" (fun database () -> Query.get database value ()) in
      let attempt () = try Query.demand database inner () with Not_found -> 0 in
      ignore (attempt ());
      ignore (attempt ());
      expect_log database [ "inner()" ]);
  test "an exception while a trace is checked reaches the query that handles it" (fun () ->
      let database = Query.create ~log:true () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let inner = unit_query "inner" (fun database () -> Query.get database value ()) in
      let outer =
        unit_query "outer" (fun database () ->
            try Query.demand database inner () with Not_found -> 0)
      in
      Query.set database value () 5;
      ignore (Query.demand database outer ());
      Query.remove database value ();
      let result = Query.demand database outer () in
      if result <> 0 then fail "result %d after the input was removed" result);
  test "a cycle that appears at a later revision reaches the query that catches it" (fun () ->
      let database = Query.create ~log:true () in
      let toggle = Query.input ~name:"toggle" ~show:(fun () -> "") () in
      let rec d =
        lazy
          (unit_query "d" (fun database () ->
               if Query.get database toggle () then Query.demand database (Lazy.force e) () else 1))
      and e = lazy (unit_query "e" (fun database () -> Query.demand database (Lazy.force d) ())) in
      let c =
        unit_query "c" (fun database () ->
            try Query.demand database (Lazy.force d) () with Query.Cycle _ -> -1)
      in
      Query.set database toggle () false;
      if Query.demand database c () <> 1 then fail "no value before the cycle";
      Query.set database toggle () true;
      let result = Query.demand database c () in
      if result <> -1 then fail "result %d once the cycle appeared" result);
  test "a cycle is named the same whether it is found by running or by checking a trace" (fun () ->
      let database = Query.create ~log:true () in
      let tick = Query.input ~name:"tick" ~show:(fun () -> "") () in
      let rec a = lazy (unit_query "a" (fun database () -> Query.demand database (Lazy.force b) ()))
      and b =
        lazy
          (unit_query "b" (fun database () ->
               ignore (Query.get database tick ());
               try Query.demand database (Lazy.force a) ()
               with Query.Cycle labels -> List.length labels))
      in
      Query.set database tick () 0;
      let first = Query.demand database (Lazy.force a) () in
      Query.set database tick () 1;
      let second = Query.demand database (Lazy.force a) () in
      if first <> 2 || second <> 2 then fail "cycle lengths %d and %d" first second);
  test "checking a trace stops at its first change" (fun () ->
      let database = Query.create ~log:true () in
      let switch = Query.input ~name:"switch" ~show:(fun () -> "") () in
      let expensive = unit_query "expensive" (fun _ () -> 7) in
      let reader =
        unit_query "reader" (fun database () ->
            if Query.get database switch () then Query.demand database expensive () else 0)
      in
      Query.set database switch () true;
      ignore (Query.demand database reader ());
      Query.set database switch () false;
      Query.clear_log database;
      ignore (Query.demand database reader ());
      expect_log database [ "reader()" ]);
  test "databases do not share results" (fun () ->
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let read = unit_query "read" (fun database () -> Query.get database value ()) in
      let first = Query.create () and second = Query.create () in
      Query.set first value () 1;
      Query.set second value () 2;
      let one = Query.demand first read () in
      let two = Query.demand second read () in
      if one <> 1 || two <> 2 then fail "read %d and %d" one two);
  test "an input cannot change while a query runs" (fun () ->
      let database = Query.create () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let writer = unit_query "writer" (fun database () -> Query.set database value () 1) in
      match Query.demand database writer () with
      | () -> fail "the input changed"
      | exception Invalid_argument _ -> ())

let () = finish ()
