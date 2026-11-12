(* The tests of the engine: which queries are computed again after a change,
   what a change reaches, phase by phase, and what an engine over a base
   holds. *)

open Harness

let expect_log engine expected =
  let actual = Engine.executed engine in
  if actual <> expected then
    fail "expected [%s], ran [%s]" (String.concat "; " expected) (String.concat "; " actual);
  Engine.clear_log engine

let unit_query ?(phase = Phases.syntax) name compute =
  Query.query ~name ~phase ~show:(fun () -> "") compute

type build = { files : (string, string) Query.input; total : (unit, int) Query.query }

(* A small build: two "files" as inputs, a length per file, and a total that
   reads the lengths' parities. The lengths are of an earlier phase than
   what reads them. *)
let build () =
  let files = Query.input ~name:"file" ~show:Fun.id () in
  let length =
    Query.query ~name:"length" ~phase:Phases.syntax ~show:Fun.id (fun database file ->
        String.length (Query.get database files file))
  in
  let parity =
    Query.query ~name:"parity" ~phase:Phases.bodies ~show:Fun.id (fun database file ->
        Query.demand database length file mod 2)
  in
  let total =
    unit_query ~phase:Phases.bodies "total" (fun database () ->
        let first = Query.demand database parity "a" in
        first + Query.demand database parity "b")
  in
  { files; total }

let fill engine build =
  Engine.set engine build.files "a" "one";
  Engine.set engine build.files "b" "three"

let setup () =
  let engine = Engine.create ~log:true () in
  let build = build () in
  fill engine build;
  (engine, build.files, build.total)

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
        Query.query ~name:"present" ~phase:Phases.syntax ~show:Fun.id (fun database file ->
            Option.is_some (Query.find database files file))
      in
      if Engine.get engine present "a" then fail "present before it was set";
      Engine.set engine files "a" "";
      if not (Engine.get engine present "a") then fail "absent after it was set";
      Engine.remove engine files "a";
      if Engine.get engine present "a" then fail "present after it was removed")

(* Pushing *)

let () =
  test "stabilizing brings every root up to date" (fun () ->
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
  test "a result that is no longer a root, and that nothing reads, is collected" (fun () ->
      let engine, _, total = setup () in
      ignore (Engine.get engine total ());
      Engine.unroot engine total ();
      let left =
        labels (List.filter (fun node -> Engine.reads engine node <> []) (Engine.nodes engine))
      in
      if left <> [] then fail "not collected: [%s]" (String.concat "; " left));
  test "readers and reads are the edges in both directions" (fun () ->
      let engine, _, total = setup () in
      ignore (Engine.get engine total ());
      let node label = List.find (fun node -> Engine.label node = label) (Engine.nodes engine) in
      if labels (Engine.reads engine (node "total()")) <> [ "parity(a)"; "parity(b)" ] then
        fail "reads";
      if labels (Engine.readers engine (node "length(a)")) <> [ "parity(a)" ] then fail "readers")

(* Phases *)

(* [count] results of a later phase that all read one result of an earlier
   phase, which comes out the same whatever the input is. *)
let fan count =
  let engine = Engine.create () in
  let source = Query.input ~name:"source" ~show:(fun () -> "") () in
  let hub =
    unit_query ~phase:Phases.syntax "hub" (fun database () -> Query.get database source () / 1000)
  in
  let reader =
    Query.query ~name:"reader" ~phase:Phases.bodies ~show:string_of_int (fun database index ->
        Query.demand database hub () + index)
  in
  Engine.set engine source () 1;
  for index = 1 to count do
    ignore (Engine.get engine reader index)
  done;
  (engine, source)

(* The work one change of the input costs. *)
let work (engine, source) =
  let before = Engine.counters engine in
  Engine.set engine source () 2;
  ignore (Engine.stabilize engine);
  let after = Engine.counters engine in
  ( after.marked - before.marked,
    after.confirmed - before.confirmed,
    after.computed - before.computed )

let () =
  test "a result that comes out the same marks nothing in a later phase" (fun () ->
      let marked, confirmed, computed = work (fan 10) in
      if (marked, confirmed, computed) <> (1, 0, 1) then
        fail "marked %d, confirmed %d, computed %d" marked confirmed computed);
  test "a change that changes nothing costs the same with ten readers and with a thousand"
    (fun () ->
      let few = work (fan 10) and many = work (fan 1000) in
      if few <> many then fail "the work grew with the readers");
  test "a result that changes marks what reads it in a later phase" (fun () ->
      let engine, source = fan 10 in
      let before = Engine.counters engine in
      Engine.set engine source () 5000;
      ignore (Engine.stabilize engine);
      let after = Engine.counters engine in
      if after.computed - before.computed <> 11 then
        fail "computed %d" (after.computed - before.computed));
  test "a query cannot read one of a later phase" (fun () ->
      let engine = Engine.create () in
      let late = unit_query ~phase:Phases.bodies "late" (fun _ () -> 1) in
      let early =
        unit_query ~phase:Phases.syntax "early" (fun database () -> Query.demand database late ())
      in
      match Engine.get engine early () with
      | _ -> fail "read a later phase"
      | exception Invalid_argument _ -> ());
  test "a marked result whose reads did not change is confirmed without being computed" (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      let before = Engine.counters engine in
      (* The length is the same, so its parity is marked and then confirmed. *)
      Engine.set engine files "b" "seven";
      ignore (Engine.stabilize engine);
      let after = Engine.counters engine in
      if after.computed - before.computed <> 1 then
        fail "computed %d" (after.computed - before.computed);
      if after.marked - before.marked <> 1 then fail "marked %d" (after.marked - before.marked))

(* Dropping *)

let () =
  test "a result a running query has read is not collected before the query ends" (fun () ->
      (* [n] reads [x] and then [y]. [y] used to read [x] and no longer
         does, and nothing else reads [x], so while [n] is computed again
         [x] loses its last reader before [n] counts as one. *)
      let engine = Engine.create () in
      let flag = Query.input ~name:"flag" ~show:(fun () -> "") () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let x_query = unit_query "x" (fun database () -> Query.get database value ()) in
      let y_query =
        unit_query "y" (fun database () ->
            if Query.get database flag () then Query.demand database x_query () else 0)
      in
      let node =
        unit_query "n" (fun database () ->
            if Query.get database flag () then Query.demand database y_query ()
            else
              let direct = Query.demand database x_query () in
              direct + Query.demand database y_query ())
      in
      Engine.set engine flag () true;
      Engine.set engine value () 1;
      ignore (Engine.get engine node ());
      Engine.set engine flag () false;
      ignore (Engine.stabilize engine);
      Engine.set engine value () 99;
      let result = Engine.get engine node () in
      if result <> 99 then fail "n is %d" result);
  test "a result is collected once the query that stopped reading it has ended" (fun () ->
      let engine = Engine.create () in
      let flag = Query.input ~name:"flag" ~show:(fun () -> "") () in
      let helper = unit_query "helper" (fun _ () -> 1) in
      let reader =
        unit_query "reader" (fun database () ->
            if Query.get database flag () then Query.demand database helper () else 0)
      in
      Engine.set engine flag () true;
      ignore (Engine.get engine reader ());
      Engine.set engine flag () false;
      ignore (Engine.get engine reader ());
      if List.mem "helper()" (labels (Engine.nodes engine)) then fail "the helper was not collected");
  test "an input that is set is not collected when nothing reads it" (fun () ->
      let engine = Engine.create () in
      let switch = Query.input ~name:"switch" ~show:(fun () -> "") () in
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let reader =
        unit_query "reader" (fun database () ->
            if Query.get database switch () then Query.get database value () else 0)
      in
      Engine.set engine switch () true;
      Engine.set engine value () 7;
      ignore (Engine.get engine reader ());
      Engine.set engine switch () false;
      ignore (Engine.get engine reader ());
      Engine.set engine switch () true;
      if Engine.get engine reader () <> 7 then fail "the input lost its value")

let created = ref None

let[@inline never] make_and_forget () =
  let engine, _, total = setup () in
  ignore (Engine.get engine total ());
  let weak = Weak.create 1 in
  Weak.set weak 0 (Some engine);
  created := Some weak

let () =
  test "an engine nothing refers to is freed with everything it held" (fun () ->
      make_and_forget ();
      Gc.full_major ();
      match !created with
      | Some weak -> if Weak.check weak 0 then fail "the engine is still held"
      | None -> fail "no engine was made")

(* Cycles and exceptions *)

let () =
  test "a query that asks for itself is a cycle naming each query on it" (fun () ->
      let engine = Engine.create ~log:true () in
      let rec first =
        lazy
          (Query.query ~name:"first" ~phase:Phases.syntax ~show:Fun.id (fun database key ->
               Query.demand database (Lazy.force second) key))
      and second =
        lazy
          (Query.query ~name:"second" ~phase:Phases.syntax ~show:Fun.id (fun database key ->
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
      let rec d_query =
        lazy
          (unit_query "d" (fun database () ->
               if Query.get database toggle () then Query.demand database (Lazy.force e_query) ()
               else 1))
      and e_query =
        lazy (unit_query "e" (fun database () -> Query.demand database (Lazy.force d_query) ()))
      in
      Engine.set engine toggle () false;
      if Engine.get engine (Lazy.force e_query) () <> 1 then fail "no value before the cycle";
      Engine.set engine toggle () true;
      match Engine.get engine (Lazy.force e_query) () with
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
      (* The query changes an engine, so it is no function of what it reads. *)
      Engine.skip_audit engine;
      let value = Query.input ~name:"value" ~show:(fun () -> "") () in
      let writer = unit_query "writer" (fun _ () -> Engine.set engine value () 1) in
      match Engine.get engine writer () with
      | () -> fail "the input changed"
      | exception Invalid_argument _ -> ())

(* Bases *)

(* A base holding the small build with its total computed, and an engine
   over it. *)
let over_base () =
  let build = build () in
  let base = Engine.create () in
  fill base build;
  ignore (Engine.get base build.total ());
  Engine.freeze base;
  (base, Engine.create ~log:true ~bases:[ base ] (), build)

let () =
  test "an engine reads its base's results without computing them" (fun () ->
      let _, engine, build = over_base () in
      if Engine.get engine build.total () <> 2 then fail "another total";
      expect_log engine [];
      if Engine.count engine <> 0 then fail "holds %d nodes of its own" (Engine.count engine));
  test "a change over a base computes only what read it, and leaves the base as it was" (fun () ->
      let base, engine, build = over_base () in
      Engine.set engine build.files "b" "four";
      if Engine.get engine build.total () <> 1 then fail "a stale total";
      expect_log engine [ "length(b)"; "parity(b)"; "total()" ];
      if Engine.get base build.total () <> 2 then fail "the base changed");
  test "an engine over a base holds only what its change reached" (fun () ->
      let _, engine, build = over_base () in
      Engine.set engine build.files "b" "four";
      ignore (Engine.get engine build.total ());
      let held = List.sort compare (labels (Engine.differing engine)) in
      if held <> [ "file(b)"; "length(b)"; "parity(b)"; "total()" ] then
        fail "holds [%s]" (String.concat "; " held));
  test "a result over a base that comes out the same is the last one copied" (fun () ->
      let _, engine, build = over_base () in
      (* The same length, so nothing of the later phase is reached. *)
      Engine.set engine build.files "b" "seven";
      if Engine.get engine build.total () <> 2 then fail "another total";
      let held = List.sort compare (labels (Engine.differing engine)) in
      if held <> [ "file(b)"; "length(b)" ] then fail "holds [%s]" (String.concat "; " held));
  test "two engines over one base each see only their own changes" (fun () ->
      let build = build () in
      let base = Engine.create () in
      fill base build;
      ignore (Engine.get base build.total ());
      Engine.freeze base;
      let first = Engine.create ~bases:[ base ] () and second = Engine.create ~bases:[ base ] () in
      Engine.set first build.files "a" "four";
      Engine.set second build.files "b" "four";
      let one = Engine.get first build.total () and two = Engine.get second build.total () in
      if (one, two) <> (1, 1) then fail "totals %d and %d" one two;
      Engine.set first build.files "b" "four";
      if Engine.get first build.total () <> 0 then fail "the first missed its second change";
      if Engine.get second build.total () <> 1 then fail "the second saw the first's change");
  test "a change after a result over a base was read still reaches it" (fun () ->
      let _, engine, build = over_base () in
      if Engine.get engine build.total () <> 2 then fail "another total";
      Engine.set engine build.files "a" "four";
      if Engine.get engine build.total () <> 1 then fail "a stale total");
  test "a new result over a base is told when what it read of the base changes" (fun () ->
      let _, engine, build = over_base () in
      let doubled =
        unit_query ~phase:Phases.bodies "doubled" (fun database () ->
            2 * Query.demand database build.total ())
      in
      if Engine.get engine doubled () <> 4 then fail "another result";
      Engine.set engine build.files "a" "four";
      if Engine.get engine doubled () <> 2 then fail "a stale result");
  test "an input removed over a base is seen as not set" (fun () ->
      let files = Query.input ~name:"file" ~show:Fun.id () in
      let present =
        Query.query ~name:"present" ~phase:Phases.syntax ~show:Fun.id (fun database file ->
            Option.is_some (Query.find database files file))
      in
      let base = Engine.create () in
      Engine.set base files "a" "";
      if not (Engine.get base present "a") then fail "absent in the base";
      Engine.freeze base;
      let engine = Engine.create ~bases:[ base ] () in
      Engine.remove engine files "a";
      if Engine.get engine present "a" then fail "still present";
      if not (Engine.get base present "a") then fail "the base changed");
  test "a frozen engine cannot change" (fun () ->
      let base, _, build = over_base () in
      match Engine.set base build.files "a" "four" with
      | () -> fail "the base changed"
      | exception Invalid_argument _ -> ());
  test "an engine over a base cannot be made before the base is frozen" (fun () ->
      let base = Engine.create () in
      match Engine.create ~bases:[ base ] () with
      | _ -> fail "made over an engine that can still change"
      | exception Invalid_argument _ -> ())

(* Checking the engine *)

let () =
  test "an audit finds nothing in an engine whose queries are pure functions of their reads"
    (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      Engine.set engine files "b" "four";
      match Engine.audit engine with
      | [] -> ()
      | problems -> fail "found [%s]" (String.concat "; " problems));
  test "an audit finds a result that depends on something the query did not read" (fun () ->
      let engine = Engine.create () in
      let hidden = ref 1 in
      let impure = unit_query "impure" (fun _ () -> !hidden) in
      ignore (Engine.get engine impure ());
      hidden := 2;
      (match Engine.audit engine with
      | [ _ ] -> ()
      | problems -> fail "found [%s]" (String.concat "; " problems));
      hidden := 1);
  test "an audit over a base compares with an engine that has no base" (fun () ->
      let _, engine, build = over_base () in
      Engine.set engine build.files "b" "four";
      ignore (Engine.get engine build.total ());
      match Engine.audit ~include_bases:true engine with
      | [] -> ()
      | problems -> fail "found [%s]" (String.concat "; " problems))

(* A source, a result of an early phase that reads it, and a result of a
   later phase that reads that. *)
let two_phases ?(fail_when = fun () -> false) () =
  let source = Query.input ~name:"known_source" ~show:Fun.id () in
  let early =
    Query.query ~name:"known_early" ~phase:Phases.proofs ~show:Fun.id (fun database key ->
        String.length (Query.get database source key))
  in
  let late =
    Query.query ~name:"known_late" ~phase:Phases.verdicts ~show:Fun.id (fun database key ->
        if fail_when () then raise Stack_overflow;
        Query.demand database early key * 2)
  in
  (source, early, late)

let () =
  test "a read outside a query brings the state up to date only through its phase" (fun () ->
      let engine = Engine.create ~log:true () in
      let source, early, late = two_phases () in
      Engine.set engine source "a" "one";
      ignore (Engine.get engine late "a");
      Engine.clear_log engine;
      Engine.set engine source "a" "three";
      ignore (Engine.get engine early "a");
      expect_log engine [ "known_early(a)" ];
      ignore (Engine.stabilize engine);
      expect_log engine [ "known_late(a)" ]);
  test "a known result is given until a change could have reached it, and nothing is computed"
    (fun () ->
      let engine = Engine.create ~log:true () in
      let source, _, late = two_phases () in
      let database = Engine.context engine in
      Engine.set engine source "a" "one";
      Engine.set engine source "b" "two";
      if Query.known database late "a" <> None then fail "a result that was never computed";
      ignore (Engine.get engine late "a");
      ignore (Engine.get engine late "b");
      Engine.clear_log engine;
      Engine.set engine source "a" "three";
      if Query.known database late "a" <> None then fail "a result whose read changed";
      if Query.known database late "b" <> Some 6 then fail "a result no change reached";
      expect_log engine [ "known_early(a)" ];
      if Engine.get engine late "a" <> 10 then fail "the result after the change";
      if Query.known database late "a" <> Some 10 then fail "the result once computed");
  test "a known result cannot be asked for inside a query" (fun () ->
      let engine = Engine.create () in
      let _, early, _ = two_phases () in
      let asks =
        Query.query ~name:"known_asks" ~phase:Phases.verdicts ~show:Fun.id (fun database key ->
            Query.known database early key)
      in
      match Engine.get engine asks "a" with
      | _ -> fail "it answered"
      | exception Invalid_argument _ -> ());
  test "a result whose query raised a fatal exception is computed again, not taken for current"
    (fun () ->
      let failing = ref false in
      let engine = Engine.create () in
      Engine.skip_audit engine;
      let source, _, late = two_phases ~fail_when:(fun () -> !failing) () in
      Engine.set engine source "a" "one";
      ignore (Engine.get engine late "a");
      Engine.set engine source "a" "three";
      failing := true;
      (match Engine.stabilize engine with
      | _ -> fail "the fatal exception was lost"
      | exception Stack_overflow -> ());
      failing := false;
      ignore (Engine.stabilize engine);
      if Query.known (Engine.context engine) late "a" <> Some 10 then
        fail "the result is not the one for the new input")

let () =
  test "a phase reads the phases it was declared after, and those they read" (fun () ->
      let first = Query.phase ~name:"test_first" ~after:[] in
      let second = Query.phase ~name:"test_second" ~after:[ first ] in
      let third = Query.phase ~name:"test_third" ~after:[ second ] in
      let early = Query.query ~name:"phase_early" ~phase:first ~show:Fun.id (fun _ key -> key) in
      let late =
        Query.query ~name:"phase_late" ~phase:third ~show:Fun.id (fun database key ->
            Query.demand database early key)
      in
      let backwards =
        Query.query ~name:"phase_backwards" ~phase:second ~show:Fun.id (fun database key ->
            Query.demand database late key)
      in
      let engine = Engine.create () in
      if Engine.get engine late "a" <> "a" then fail "the later phase did not read the earlier";
      match Engine.get engine backwards "a" with
      | _ -> fail "a phase read one declared after it"
      | exception Invalid_argument _ -> ());
  test "two phases cannot have one name" (fun () ->
      ignore (Query.phase ~name:"test_twice" ~after:[]);
      match Query.phase ~name:"test_twice" ~after:[] with
      | _ -> fail "the second was declared"
      | exception Invalid_argument _ -> ())

let () =
  test "an observed result is computed and collected, and makes no root" (fun () ->
      let engine, _, total = setup () in
      let value = Query.demand (Engine.observer engine) total () in
      if value <> 2 then fail "total %d" value;
      if List.exists (fun node -> not (Engine.is_input node)) (Engine.nodes engine) then
        fail "the engine holds [%s]" (String.concat "; " (labels (Engine.nodes engine))));
  test "observing a root leaves it a root" (fun () ->
      let engine, files, total = setup () in
      ignore (Engine.get engine total ());
      ignore (Query.demand (Engine.observer engine) total ());
      Engine.clear_log engine;
      Engine.set engine files "a" "four";
      ignore (Engine.stabilize engine);
      if not (List.mem () (Engine.computed engine total)) then
        fail "the root was not brought up to date");
  test "comparing with another engine makes no root in it" (fun () ->
      let build = build () in
      let mine = Engine.create () and theirs = Engine.create () in
      fill mine build;
      fill theirs build;
      ignore (Engine.get mine build.total ());
      List.iter
        (fun node -> ignore (Engine.current_in node theirs))
        (List.filter (fun node -> not (Engine.is_input node)) (Engine.nodes mine));
      if List.exists (fun node -> not (Engine.is_input node)) (Engine.nodes theirs) then
        fail "the other engine holds [%s]" (String.concat "; " (labels (Engine.nodes theirs))))

let () =
  test "an audit before a phase leaves the later phases' results alone" (fun () ->
      let engine = Engine.create ~log:true () in
      Engine.skip_audit engine;
      let hidden = ref 1 in
      let source = Query.input ~name:"audit_source" ~show:Fun.id () in
      let early =
        Query.query ~name:"audit_early" ~phase:Phases.syntax ~show:Fun.id (fun database key ->
            String.length (Query.get database source key))
      in
      let late =
        Query.query ~name:"audit_late" ~phase:Phases.proofs ~show:Fun.id (fun database key ->
            Query.demand database early key + !hidden)
      in
      Engine.set engine source "a" "one";
      ignore (Engine.get engine late "a");
      (* The later result now differs from what a new engine computes. *)
      hidden := 2;
      if Engine.audit ~before:Phases.proofs engine <> [] then
        fail "the audit computed a result of a later phase";
      if Engine.audit engine = [] then fail "the whole audit found nothing")
