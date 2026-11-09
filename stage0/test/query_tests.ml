(* The tests of the engine: which queries are computed again after a change,
   and what a change reaches. See DATABASE.md, "Pushing changes". *)

open Harness

let expect_log engine expected =
  let actual = Engine.executed engine in
  if actual <> expected then
    fail "expected [%s], ran [%s]" (String.concat "; " expected) (String.concat "; " actual);
  Engine.clear_log engine

let unit_query name compute = Query.query ~name ~show:(fun () -> "") compute

(* A small build: two "files" as inputs, a length per file, and a total that
   reads the lengths. *)
let setup () =
  let engine = Engine.create ~log:true () in
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
    unit_query "total" (fun database () ->
        let first = Query.demand database parity "a" in
        first + Query.demand database parity "b")
  in
  Engine.set engine files "a" "one";
  Engine.set engine files "b" "three";
  (engine, files, total)

let labels nodes = List.map Engine.label nodes

let () =
  test "a first demand runs every query it reaches" (fun () ->
      let engine, _, total = setup () in
      let value = Engine.get engine total () in
      if value <> 2 then fail "total %d" value;
      expect_log engine [ "total()"; "parity(a)"; "length(a)"; "parity(b)"; "length(b)" ]);
  test "a second demand with no change runs nothing" (fun () ->
      let engine, _, total = setup () in
      ignore (Engine.get engine total ());
      Engine.clear_log engine;
      ignore (Engine.get engine total ());
      expect_log engine []);
  test "a change runs only what read it" (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      Engine.clear_log engine;
      Engine.set engine files "b" "four";
      let value = Engine.get engine total () in
      if value <> 1 then fail "total %d" value;
      expect_log engine [ "length(b)"; "parity(b)"; "total()" ]);
  test "a result that comes out the same stops the work above it" (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      Engine.clear_log engine;
      Engine.set engine files "b" "seven";
      ignore (Engine.get engine total ());
      expect_log engine [ "length(b)" ]);
  test "setting an input to the value it has changes nothing" (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      Engine.clear_log engine;
      Engine.set engine files "a" "one";
      ignore (Engine.get engine total ());
      expect_log engine []);
  test "reading an input that is not set records it" (fun () ->
      let engine = Engine.create ~log:true () in
      let files = Query.input ~name:"file" ~show:Fun.id () in
      let present =
        Query.query ~name:"present" ~show:Fun.id (fun database file ->
            Option.is_some (Query.find database files file))
      in
      if Engine.get engine present "a" then fail "present before it was set";
      Engine.set engine files "a" "";
      if not (Engine.get engine present "a") then fail "absent after it was set";
      Engine.remove engine files "a";
      if Engine.get engine present "a" then fail "present after it was removed")

(* Pushing *)

let () =
  test "stabilizing brings kept results up to date" (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      ignore (Engine.stabilize engine);
      Engine.set engine files "b" "four";
      let change = Engine.stabilize engine in
      if labels change.computed <> [ "length(b)"; "parity(b)"; "total()" ] then
        fail "computed [%s]" (String.concat "; " (labels change.computed));
      if labels change.changed <> [ "length(b)"; "parity(b)"; "total()" ] then
        fail "changed [%s]" (String.concat "; " (labels change.changed));
      Engine.clear_log engine;
      if Engine.get engine total () <> 1 then fail "stale total";
      expect_log engine []);
  test "a change computes nothing that cannot read it" (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      ignore (Engine.stabilize engine);
      Engine.set engine files "a" "two";
      let change = Engine.stabilize engine in
      if List.mem "length(b)" (labels change.computed) then fail "computed length(b)";
      if labels change.changed <> [] then
        fail "changed [%s]" (String.concat "; " (labels change.changed)));
  test "a query that stops reading an input is not computed when it changes" (fun () ->
      let engine = Engine.create ~log:true () in
      let switch = Query.input ~name:"switch" ~show:(fun () -> "") () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let reader =
        unit_query "reader" (fun database () ->
            if Query.get database switch () then Query.get database value () else 0)
      in
      Engine.set engine switch () true;
      Engine.set engine value () 1;
      ignore (Engine.get engine reader ());
      Engine.set engine switch () false;
      ignore (Engine.get engine reader ());
      Engine.clear_log engine;
      Engine.set engine value () 2;
      ignore (Engine.stabilize engine);
      expect_log engine []);
  test "a result nothing reads any more is dropped" (fun () ->
      let engine, _, total = setup () in
      ignore (Engine.get engine total ());
      Engine.release engine total ();
      let left = labels (List.filter (fun node -> Engine.reads node <> []) (Engine.nodes engine)) in
      if left <> [] then fail "kept [%s]" (String.concat "; " left));
  test "readers and reads are the edges in both directions" (fun () ->
      let engine, _, total = setup () in
      ignore (Engine.get engine total ());
      let node label = List.find (fun n -> Engine.label n = label) (Engine.nodes engine) in
      if labels (Engine.reads (node "total()")) <> [ "parity(a)"; "parity(b)" ] then fail "reads";
      if labels (Engine.readers (node "length(a)")) <> [ "parity(a)" ] then fail "readers")

(* Cycles and exceptions *)

let () =
  test "a query that asks for itself is a cycle naming each query on it" (fun () ->
      let engine = Engine.create ~log:true () in
      let rec first =
        lazy
          (Query.query ~name:"first" ~show:Fun.id (fun database key ->
               Query.demand database (Lazy.force second) key))
      and second =
        lazy
          (Query.query ~name:"second" ~show:Fun.id (fun database key ->
               Query.demand database (Lazy.force first) key + 1))
      in
      match Engine.get engine (Lazy.force first) "k" with
      | _ -> fail "no cycle"
      | exception Query.Cycle labels ->
          if labels <> [ "first(k)"; "second(k)" ] then
            fail "cycle [%s]" (String.concat "; " labels));
  test "a query that catches a cycle still has the cycle as its result" (fun () ->
      let engine = Engine.create () in
      let rec looped =
        lazy
          (unit_query "looped" (fun database () -> Query.demand database (Lazy.force guarded) ()))
      and guarded =
        lazy
          (unit_query "guarded" (fun database () ->
               try Query.demand database (Lazy.force looped) () with Query.Cycle _ -> -1))
      in
      match Engine.get engine (Lazy.force guarded) () with
      | _ -> fail "the cycle was caught"
      | exception Query.Cycle _ -> ());
  test "a cycle that is removed leaves results that are current" (fun () ->
      let engine = Engine.create () in
      let toggle = Query.input ~name:"toggle" ~show:(fun () -> "") () in
      let rec first =
        lazy
          (unit_query "first" (fun database () ->
               if Query.get database toggle () then Query.demand database (Lazy.force second) () + 1
               else 5))
      and second =
        lazy
          (unit_query "second" (fun database () -> Query.demand database (Lazy.force first) () + 1))
      in
      Engine.set engine toggle () true;
      (match Engine.get engine (Lazy.force second) () with
      | _ -> fail "no cycle"
      | exception Query.Cycle _ -> ());
      Engine.set engine toggle () false;
      let value = Engine.get engine (Lazy.force second) () in
      if value <> 6 then fail "second is %d" value);
  test "a cycle that appears later reaches every query on it" (fun () ->
      let engine = Engine.create () in
      let toggle = Query.input ~name:"toggle" ~show:(fun () -> "") () in
      let rec d =
        lazy
          (unit_query "d" (fun database () ->
               if Query.get database toggle () then Query.demand database (Lazy.force e) () else 1))
      and e = lazy (unit_query "e" (fun database () -> Query.demand database (Lazy.force d) ())) in
      Engine.set engine toggle () false;
      if Engine.get engine (Lazy.force e) () <> 1 then fail "no value before the cycle";
      Engine.set engine toggle () true;
      match Engine.get engine (Lazy.force e) () with
      | _ -> fail "no cycle once it appeared"
      | exception Query.Cycle _ -> ());
  test "a query that raises is computed again when what it read changes" (fun () ->
      let engine = Engine.create ~log:true () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let inner = unit_query "inner" (fun database () -> Query.get database value ()) in
      let outer =
        unit_query "outer" (fun database () ->
            try Query.demand database inner () with Not_found -> 0)
      in
      if Engine.get engine outer () <> 0 then fail "unset input read as a value";
      Engine.set engine value () 5;
      let result = Engine.get engine outer () in
      if result <> 5 then fail "stale result %d after the input was set" result);
  test "a query that raised is not computed again with no change" (fun () ->
      let engine = Engine.create ~log:true () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let inner = unit_query "inner" (fun database () -> Query.get database value ()) in
      let attempt () = try Engine.get engine inner () with Not_found -> 0 in
      ignore (attempt ());
      ignore (attempt ());
      expect_log engine [ "inner()" ]);
  test "checking what a result read stops at its first change" (fun () ->
      let engine = Engine.create ~log:true () in
      let switch = Query.input ~name:"switch" ~show:(fun () -> "") () in
      let expensive = unit_query "expensive" (fun _ () -> 7) in
      let reader =
        unit_query "reader" (fun database () ->
            if Query.get database switch () then Query.demand database expensive () else 0)
      in
      Engine.set engine switch () true;
      ignore (Engine.get engine reader ());
      Engine.set engine switch () false;
      Engine.clear_log engine;
      ignore (Engine.get engine reader ());
      expect_log engine [ "reader()" ]);
  test "engines do not share results" (fun () ->
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let read = unit_query "read" (fun database () -> Query.get database value ()) in
      let first = Engine.create () and second = Engine.create () in
      Engine.set first value () 1;
      Engine.set second value () 2;
      let one = Engine.get first read () in
      let two = Engine.get second read () in
      if one <> 1 || two <> 2 then fail "read %d and %d" one two);
  test "an input cannot change while a query runs" (fun () ->
      let engine = Engine.create () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let writer = unit_query "writer" (fun _ () -> Engine.set engine value () 1) in
      match Engine.get engine writer () with
      | () -> fail "the input changed"
      | exception Invalid_argument _ -> ())

(* Frozen layers *)

let () =
  test "a result computed from a frozen layer alone is found done by another engine" (fun () ->
      let layer = Engine.frozen_layer () in
      let value = Query.input ~name:"layer_value" ~show:(fun () -> "") () in
      Engine.set layer value () 3;
      let double = unit_query "double" (fun database () -> 2 * Query.get database value ()) in
      let first = Engine.create ~log:true ~shared:layer () in
      let second = Engine.create ~log:true ~shared:layer () in
      if Engine.get first double () <> 6 then fail "first";
      if Engine.get second double () <> 6 then fail "second";
      expect_log first [ "double()" ];
      expect_log second []);
  test "a result that reads an engine's own input stays in that engine" (fun () ->
      let layer = Engine.frozen_layer () in
      let shared_value = Query.input ~name:"shared_value" ~show:(fun () -> "") () in
      let own_value = Query.input ~name:"own_value" ~show:(fun () -> "") () in
      Engine.set layer shared_value () 3;
      let sum =
        unit_query "sum" (fun database () ->
            Query.get database shared_value () + Query.get database own_value ())
      in
      let first = Engine.create ~shared:layer () and second = Engine.create ~shared:layer () in
      Engine.set first own_value () 1;
      Engine.set second own_value () 2;
      if Engine.get first sum () <> 4 || Engine.get second sum () <> 5 then fail "shared a result");
  test "a frozen layer's input cannot change once read" (fun () ->
      let layer = Engine.frozen_layer () in
      let value = Query.input ~name:"frozen_value" ~show:(fun () -> "") () in
      Engine.set layer value () 3;
      let engine = Engine.create ~shared:layer () in
      let read = unit_query "frozen_read" (fun database () -> Query.get database value ()) in
      ignore (Engine.get engine read ());
      match Engine.set layer value () 4 with
      | () -> fail "the input changed"
      | exception Invalid_argument _ -> ())

(* Forking *)

let () =
  test "a fork diverges from the engine it was made from" (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      let fork = Engine.fork engine in
      Engine.set fork files "b" "four";
      if Engine.get fork total () <> 1 then fail "the fork's total is stale";
      if Engine.get engine total () <> 2 then fail "the original changed");
  test "a fork of a saved engine diverges too" (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      ignore (Engine.stabilize engine);
      let fork = Engine.fork engine in
      ignore (Engine.stabilize fork);
      Engine.set fork files "a" "four";
      ignore (Engine.stabilize fork);
      if Engine.get fork total () <> 1 then fail "the fork's total is stale")

let () = finish ()
