(* The tests of the store, and of the states and facts the engine keeps in
   it. *)

open Harness

let counter = ref 0

let fresh_directory () =
  incr counter;
  let directory =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "truss-store-test-%d-%d" (Unix.getpid ()) !counter)
  in
  if Sys.file_exists directory then ignore (Sys.command ("rm -rf " ^ Filename.quote directory));
  directory

let segment_files directory =
  let segments = Filename.concat directory "segments" in
  Array.to_list (Sys.readdir segments)
  |> List.filter (fun f -> Filename.check_suffix f ".segment")
  |> List.map (Filename.concat segments)

let () =
  test "a value put in the store is got back by its name" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let name = Store.put store "hello" in
      if Store.get store name <> Some "hello" then fail "got something else");
  test "a value is named by its BLAKE3 hash" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      if Store.put store "hello" <> Blake3.hash "hello" then fail "another name");
  test "putting a value twice adds it once" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      ignore (Store.put store "hello");
      let size = Store.size store in
      ignore (Store.put store "hello");
      if Store.size store <> size then fail "grew from %d to %d" size (Store.size store));
  test "a name the store does not have gets nothing" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      if Store.get store (Blake3.hash "missing") <> None then fail "got a value");
  test "a sealed segment is found again through its index" (fun () ->
      let directory = fresh_directory () in
      let store = Store.open_ directory in
      let name = Store.put store "kept" in
      Store.close store;
      let indexes =
        Array.to_list (Sys.readdir (Filename.concat directory "segments"))
        |> List.filter (fun f -> Filename.check_suffix f ".index")
      in
      if List.length indexes <> 1 then fail "%d indexes" (List.length indexes);
      let again = Store.open_ directory in
      if Store.get again name <> Some "kept" then fail "lost after sealing");
  test "a second store on one directory sees what the first adds" (fun () ->
      let directory = fresh_directory () in
      let first = Store.open_ directory in
      let second = Store.open_ directory in
      let name = Store.put first "shared" in
      Store.flush first;
      Store.refresh second;
      if Store.get second name <> Some "shared" then fail "not seen");
  test "a damaged record is missing" (fun () ->
      let directory = fresh_directory () in
      let store = Store.open_ directory in
      let name = Store.put store "fragile" in
      Store.close store;
      List.iter
        (fun path ->
          let contents = Bytes.of_string (In_channel.with_open_bin path In_channel.input_all) in
          let last = Bytes.length contents - 10 in
          Bytes.set contents last (Char.chr ((Char.code (Bytes.get contents last) + 1) land 255));
          Out_channel.with_open_bin path (fun out -> Out_channel.output_bytes out contents))
        (segment_files directory);
      let again = Store.open_ directory in
      if Store.get again name <> None then fail "a damaged value was got");
  test "a result is found by its kind and key" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      Store.add_result store ~kind:"tests" ~key:"k" "passed";
      if Store.find_result store ~kind:"tests" ~key:"k" <> Some "passed" then fail "not found";
      if Store.find_result store ~kind:"proofs" ~key:"k" <> None then fail "found as another kind")

let () =
  test "a pointer gives back what it was last pointed at" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let pointer = Store.pointer store "session" in
      Store.point pointer "first";
      Store.point pointer "second";
      if Store.read pointer <> Some "second" then fail "another value");
  test "a pointer never pointed holds nothing" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      if Store.read (Store.pointer store "session") <> None then fail "holds a value");
  test "a pointer cut short holds nothing" (fun () ->
      let directory = fresh_directory () in
      let store = Store.open_ directory in
      let pointer = Store.pointer store "session" in
      Store.point pointer "whole";
      let path = Filename.concat (Filename.concat directory "pointers") "session.pointer" in
      let contents = In_channel.with_open_bin path In_channel.input_all in
      Out_channel.with_open_bin path (fun out ->
          Out_channel.output_string out (String.sub contents 0 (String.length contents - 2)));
      if Store.read pointer <> None then fail "read a damaged pointer");
  test "a pointer another process holds cannot be taken" (fun () ->
      let directory = fresh_directory () in
      let store = Store.open_ directory in
      let pointer = Store.pointer store "session" in
      if not (Store.lock pointer) then fail "could not take it";
      match Unix.fork () with
      | 0 ->
          let other = Store.pointer (Store.open_ directory) "session" in
          Unix._exit (if Store.lock other then 1 else 0)
      | child -> (
          match Unix.waitpid [] child with
          | _, Unix.WEXITED 0 -> ()
          | _ -> fail "another process took it"))

let () =
  test "collecting keeps live values and removes the rest" (fun () ->
      let directory = fresh_directory () in
      let writer = Store.open_ directory in
      let live = Store.put writer "live" in
      let dead = Store.put writer "dead" in
      Store.close writer;
      let store = Store.open_ directory in
      Store.collect store ~budget:0 ~live:(fun name -> name = live);
      Store.close store;
      let again = Store.open_ directory in
      if Store.get again live <> Some "live" then fail "lost a live value";
      if Store.get again dead <> None then fail "kept a dead value");
  test "collecting within the budget removes nothing" (fun () ->
      let directory = fresh_directory () in
      let writer = Store.open_ directory in
      let dead = Store.put writer "dead" in
      Store.close writer;
      let store = Store.open_ directory in
      Store.collect store ~budget:max_int ~live:(fun _ -> false);
      if Store.get store dead <> Some "dead" then fail "removed a value")

(* States and facts *)

let version = "test"
let value_input = Query.input ~name:"saved_value" ~show:(fun () -> "") ()

let unit_query name ?saved ?portable ?(phase = Query.Syntax) compute =
  Query.query ~name ~phase ?saved ?portable ~show:(fun () -> "") compute

let doubled =
  unit_query "saved_doubled" ~saved:true ~portable:true (fun database () ->
      2 * Query.get database value_input ())

let through_unsaved =
  unit_query "unsaved_middle" (fun database () -> Query.get database value_input () + 1)

let reads_through =
  unit_query "saved_reads_through" ~saved:true ~portable:true ~phase:Bodies (fun database () ->
      Query.demand database through_unsaved () * 10)

let other_input = Query.input ~name:"saved_other" ~show:(fun () -> "") ()

let tripled =
  unit_query "saved_tripled" ~saved:true (fun database () -> 3 * Query.get database other_input ())

let attached store =
  let engine = Engine.create ~log:true () in
  Engine.attach engine store ~version;
  engine

(* A store holding one state: two inputs, two saved results of the first,
   and one of the second. *)
let written () =
  let store = Store.open_ (fresh_directory ()) in
  let engine = attached store in
  Engine.set engine value_input () 4;
  Engine.set engine other_input () 1;
  ignore (Engine.get engine doubled ());
  ignore (Engine.get engine reads_through ());
  ignore (Engine.get engine tripled ());
  (store, Engine.write engine)

let opened ?(bases = []) store artifact =
  match Engine.open_ ~log:true store ~version ~bases artifact with
  | Some engine -> engine
  | None -> failwith "the store has no such state"

let () =
  test "a saved result is found done in a state opened from the store" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      if Engine.get engine doubled () <> 8 then fail "another result";
      if Engine.executed engine <> [] then
        fail "computed [%s]" (String.concat "; " (Engine.executed engine)));
  test "a change in an opened state computes what read it" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      Engine.set engine value_input () 5;
      if Engine.get engine doubled () <> 10 then fail "stale result");
  test "a saved result that read through an unsaved one sees changes in an opened state" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      if Engine.get engine reads_through () <> 50 then fail "stale before the change";
      Engine.set engine value_input () 6;
      let value = Engine.get engine reads_through () in
      if value <> 70 then fail "result %d after the change" value);
  test "an opened state holds nothing of its own until something changes" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      ignore (Engine.get engine doubled ());
      if Engine.count engine <> 0 then fail "holds %d nodes" (Engine.count engine));
  test "two states opened from one artifact each see only their own changes" (fun () ->
      let store, artifact = written () in
      let first = opened store artifact and second = opened store artifact in
      Engine.set first value_input () 5;
      if Engine.get first doubled () <> 10 then fail "the first is stale";
      if Engine.get second doubled () <> 8 then fail "the second saw the first's change");
  test "writing again writes a difference holding only what changed" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      Engine.set engine value_input () 7;
      ignore (Engine.get engine doubled ());
      let changed = Engine.write engine in
      let debt = Engine.debt engine in
      if debt.depth <> 1 then fail "%d differences" debt.depth;
      (* The input and the three results that read it, of the six nodes. *)
      if debt.whole <> 6 then fail "the whole state holds %d nodes" debt.whole;
      if debt.differences <> 4 then fail "the difference holds %d nodes" debt.differences;
      if Engine.get (opened store changed) doubled () <> 14 then fail "the change was not written";
      if Engine.get (opened store artifact) doubled () <> 8 then fail "the earlier state changed");
  test "the whole state is written again when asked" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      Engine.set engine value_input () 7;
      ignore (Engine.get engine doubled ());
      let whole = Engine.write ~full:true engine in
      if (Engine.debt engine).depth <> 0 then fail "still a difference";
      let again = opened store whole in
      if Engine.get again doubled () <> 14 then fail "another result";
      if Engine.get again reads_through () <> 80 then fail "lost a result");
  test "a result that is unchanged is not written, and nothing is written twice" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      if Engine.unwritten engine then fail "something to write after opening";
      Engine.set engine value_input () 7;
      ignore (Engine.get engine doubled ());
      if not (Engine.unwritten engine) then fail "nothing to write after a change";
      ignore (Engine.write engine);
      if Engine.unwritten engine then fail "something to write after writing");
  test "a result whose value is gone from the store is computed again" (fun () ->
      let store, artifact = written () in
      (* Another store holding the artifact, and none of the values. *)
      let empty = Store.open_ (fresh_directory ()) in
      let copied = Store.put empty (Option.get (Store.get store artifact)) in
      let engine = opened empty copied in
      Engine.set engine value_input () 4;
      if Engine.get engine doubled () <> 8 then fail "another result";
      if not (List.mem "saved_doubled()" (Engine.executed engine)) then fail "not computed")

let () =
  test "a result computed in one state is found by another that reads the same" (fun () ->
      let store, _ = written () in
      let engine = attached store in
      Engine.set engine value_input () 4;
      if Engine.get engine doubled () <> 8 then fail "another result";
      if Engine.executed engine <> [] then
        fail "computed [%s]" (String.concat "; " (Engine.executed engine));
      if (Engine.counters engine).adopted <> 1 then fail "not found as a fact");
  test "a result is computed when what it reads has another value" (fun () ->
      let store, _ = written () in
      let engine = attached store in
      Engine.set engine value_input () 5;
      if Engine.get engine doubled () <> 10 then fail "another result";
      if Engine.executed engine <> [ "saved_doubled()" ] then fail "not computed");
  test "going back to an earlier input finds the earlier result" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      Engine.set engine value_input () 5;
      ignore (Engine.get engine doubled ());
      Engine.record engine;
      Engine.clear_log engine;
      Engine.set engine value_input () 4;
      if Engine.get engine doubled () <> 8 then fail "another result";
      if Engine.get engine reads_through () <> 50 then fail "another result read through";
      (* The results that are not saved are computed, being cheap; the saved
         ones are found. *)
      if
        List.exists
          (fun label -> label = "saved_doubled()" || label = "saved_reads_through()")
          (Engine.executed engine)
      then fail "computed [%s]" (String.concat "; " (Engine.executed engine)));
  test "a result found as a fact reads what the computed one read" (fun () ->
      let store, _ = written () in
      let engine = attached store in
      Engine.set engine value_input () 4;
      ignore (Engine.get engine reads_through ());
      Engine.set engine value_input () 9;
      let value = Engine.get engine reads_through () in
      if value <> 100 then fail "result %d after the change" value)

(* Fingerprints follow from what a value is, not from how it lies in memory *)

let pair_input = Query.input ~name:"saved_pair" ~show:(fun () -> "") ()

let pair_length =
  unit_query "saved_pair_length" ~saved:true ~portable:true (fun database () ->
      let left, right = Query.get database pair_input () in
      String.length left + String.length right)

let left_text =
  unit_query "saved_left_text" ~saved:true (fun database () ->
      fst (Query.get database pair_input ()))

let right_text =
  unit_query "saved_right_text" ~saved:true (fun database () ->
      snd (Query.get database pair_input ()))

let both_texts =
  unit_query "unsaved_both_texts" ~phase:Declarations (fun database () ->
      (Query.demand database left_text (), Query.demand database right_text ()))

let reads_both =
  unit_query "saved_reads_both" ~saved:true ~phase:Bodies (fun database () ->
      let left, right = Query.demand database both_texts () in
      String.length left + String.length right)

let () =
  test "a fact is found by an equal value whose parts are not the same blocks" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let first = attached store in
      let shared = String.make 3 'a' in
      Engine.set first pair_input () (shared, shared);
      ignore (Engine.get first pair_length ());
      Engine.record first;
      let second = attached store in
      Engine.set second pair_input () (String.make 3 'a', String.make 3 'a');
      ignore (Engine.get second pair_length ());
      if (Engine.counters second).adopted <> 1 then fail "not found as a fact");
  test "a result that is not kept comes out the same when an opened state computes it again"
    (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let engine = attached store in
      (* Both halves are one block here, and two when each is read back. *)
      let shared = String.make 3 'a' in
      Engine.set engine pair_input () (shared, shared);
      ignore (Engine.get engine reads_both ());
      let again = opened store (Engine.write engine) in
      ignore (Engine.get again both_texts ());
      let counters = Engine.counters again in
      if counters.computed <> 1 then fail "computed %d results" counters.computed;
      if counters.changed <> 0 then fail "%d results changed" counters.changed;
      if counters.marked <> 0 then fail "marked %d results" counters.marked)

(* What fuzzing the engine found *)

let switch_input = Query.input ~name:"saved_switch" ~show:(fun () -> "") ()

let leaf =
  unit_query "saved_leaf" ~saved:true (fun database () -> Query.get database value_input ())

let top =
  unit_query "saved_top" ~saved:true ~phase:Bodies (fun database () ->
      if Query.get database switch_input () then Query.demand database leaf () else 0)

let maybe_input = Query.input ~name:"saved_maybe" ~show:(fun () -> "") ()

let defaulted =
  unit_query "saved_defaulted" ~saved:true (fun database () ->
      Option.value (Query.find database maybe_input ()) ~default:7)

let () =
  test "a result dropped since the whole state was written is not read from it" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let engine = attached store in
      Engine.set engine switch_input () true;
      Engine.set engine value_input () 1;
      if Engine.get engine top () <> 1 then fail "another result";
      ignore (Engine.write engine);
      (* The leaf is dropped, and the input it read changes after. *)
      Engine.set engine switch_input () false;
      if Engine.get engine top () <> 0 then fail "another result without the leaf";
      Engine.set engine value_input () 5;
      let again = opened store (Engine.write engine) in
      Engine.set again switch_input () true;
      let value = Engine.get again top () in
      if value <> 5 then fail "read the leaf of the earlier state: %d" value);
  test "an input that was read and is not set is part of a written difference" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      if Engine.get engine defaulted () <> 7 then fail "another result";
      let again = opened store (Engine.write engine) in
      if Engine.get again defaulted () <> 7 then fail "another result when opened";
      if Engine.executed again <> [] then
        fail "computed [%s]" (String.concat "; " (Engine.executed again));
      Engine.set again maybe_input () 3;
      if Engine.get again defaulted () <> 3 then fail "setting the input did not reach it");
  test "a node the chain does not hold is written with the first node that reads it" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let engine = attached store in
      Engine.set engine value_input () 4;
      ignore (Engine.get engine doubled ());
      (* An input that is set and removed is held, and not written, since
         nothing reads it yet. *)
      Engine.set engine maybe_input () 1;
      Engine.remove engine maybe_input ();
      ignore (Engine.write engine);
      if Engine.get engine defaulted () <> 7 then fail "another result";
      let again = opened store (Engine.write engine) in
      if Engine.get again defaulted () <> 7 then fail "another result when opened";
      if Engine.executed again <> [] then
        fail "computed [%s]" (String.concat "; " (Engine.executed again)));
  test "a result that returns to the whole state's takes the place of a difference's" (fun () ->
      let store, artifact = written () in
      let engine = opened store artifact in
      Engine.set engine value_input () 5;
      if Engine.get engine doubled () <> 10 then fail "another result";
      ignore (Engine.write engine);
      Engine.set engine value_input () 4;
      if Engine.get engine doubled () <> 8 then fail "another result after going back";
      let again = opened store (Engine.write engine) in
      let value = Engine.get again doubled () in
      if value <> 8 then fail "read the earlier difference's result: %d" value);
  test "a result a request kept after it was written is current in a state opened later" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let engine = attached store in
      Engine.set engine switch_input () false;
      Engine.set engine value_input () 1;
      ignore (Engine.get engine top ());
      ignore (Engine.write engine);
      (* The leaf is new in a difference, and only [top] reads it. *)
      Engine.set engine switch_input () true;
      ignore (Engine.get engine top ());
      ignore (Engine.write engine);
      (* A request keeps it, and then nothing reads it. *)
      ignore (Engine.get engine leaf ());
      Engine.set engine switch_input () false;
      ignore (Engine.get engine top ());
      let again = opened store (Engine.write engine) in
      Engine.set again value_input () 5;
      let last = opened store (Engine.write again) in
      let value = Engine.get last leaf () in
      if value <> 5 then fail "the leaf of an earlier state: %d" value)

let layer_value = Query.input ~name:"layer_input" ~show:(fun () -> "") ()
let own_value = Query.input ~name:"own_input" ~show:(fun () -> "") ()

let layer_unsaved =
  unit_query "layer_unsaved" (fun database () -> Query.get database layer_value () + 1)

let reads_layer =
  unit_query "reads_layer" ~saved:true ~phase:Bodies (fun database () ->
      Query.demand database layer_unsaved () + Query.get database own_value ())

let reads_reader =
  unit_query "reads_reader" ~saved:true ~phase:Bodies (fun database () ->
      10 * Query.demand database reads_layer ())

let () =
  test "a saved result that read an unsaved result of a fixed base sees changes when opened"
    (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let base = Engine.create () in
      Engine.set base layer_value () 1;
      Engine.freeze ~fixed:true base;
      let engine = Engine.create ~bases:[ base ] () in
      Engine.attach engine store ~version;
      Engine.set engine own_value () 5;
      ignore (Engine.get engine reads_reader ());
      let artifact = Engine.write engine in
      let again = opened ~bases:[ base ] store artifact in
      if Engine.get again reads_reader () <> 70 then fail "another result";
      Engine.set again own_value () 6;
      let value = Engine.get again reads_reader () in
      if value <> 80 then fail "result %d after the change" value)

let () =
  test "an input whose value the store lost is an error, and never reads as not set" (fun () ->
      let store, artifact = written () in
      let directory = Store.directory store in
      Store.close store;
      let store = Store.open_ directory in
      let lost = Blake3.hash (Marshal.to_string 4 [ Marshal.No_sharing ]) in
      Store.collect store ~budget:0 ~live:(fun name -> name <> lost);
      match Engine.open_ store ~version ~bases:[] artifact with
      | None -> fail "the state did not open"
      | Some engine -> (
          Engine.skip_audit engine;
          if Engine.inputs_stored engine then fail "every input is said to be stored";
          match Query.find (Engine.context engine) value_input () with
          | _ -> fail "the input was read"
          | exception Engine.Lost _ -> ()))

let () = finish ()
