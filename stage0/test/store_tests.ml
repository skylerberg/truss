(* The tests of the store, and of saving and loading the engine's graph
   through it. See DATABASE.md, "Content hashes and the store". *)

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
  test "a journal gives back its records in order" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let journal = Store.journal store "session" in
      Store.append journal "first";
      Store.append journal "second";
      if Store.records journal <> [ "first"; "second" ] then fail "other records");
  test "a journal cut short gives its whole records" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let journal = Store.journal store "session" in
      Store.append journal "first";
      Store.append journal "second";
      let path = Store.journal_name journal in
      let contents = In_channel.with_open_bin path In_channel.input_all in
      Out_channel.with_open_bin path (fun out ->
          Out_channel.output_string out (String.sub contents 0 (String.length contents - 3)));
      if Store.records journal <> [ "first" ] then fail "other records");
  test "compacting a journal leaves one record" (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let journal = Store.journal store "session" in
      Store.append journal "first";
      Store.compact journal "base";
      if Store.records journal <> [ "base" ] then fail "other records");
  test "a journal another process holds cannot be taken" (fun () ->
      let directory = fresh_directory () in
      let store = Store.open_ directory in
      let journal = Store.journal store "session" in
      if not (Store.lock journal) then fail "could not take it";
      match Unix.fork () with
      | 0 ->
          let other = Store.journal (Store.open_ directory) "session" in
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

(* Saving and loading *)

let unit_query name ?saved compute = Query.query ~name ?saved ~show:(fun () -> "") compute
let value_input = Query.input ~name:"saved_value" ~show:(fun () -> "") ()

let doubled =
  unit_query "saved_doubled" ~saved:true (fun database () -> 2 * Query.get database value_input ())

let through_unsaved =
  unit_query "unsaved_middle" (fun database () -> Query.get database value_input () + 1)

let reads_through =
  unit_query "saved_reads_through" ~saved:true (fun database () ->
      Query.demand database through_unsaved () * 10)

let saved_session () =
  let store = Store.open_ (fresh_directory ()) in
  let journal = Store.journal store "session" in
  let engine = Engine.create () in
  Engine.attach engine store;
  Engine.set engine value_input () 4;
  ignore (Engine.get engine doubled ());
  ignore (Engine.get engine reads_through ());
  Engine.save engine journal;
  (store, journal)

let () =
  test "a saved result is found done after loading" (fun () ->
      let store, journal = saved_session () in
      match Engine.load ~log:true store journal with
      | None -> fail "nothing loaded"
      | Some engine ->
          if Engine.get engine doubled () <> 8 then fail "another result";
          if Engine.executed engine <> [] then
            fail "computed [%s]" (String.concat "; " (Engine.executed engine)));
  test "a change after loading computes what read it" (fun () ->
      let store, journal = saved_session () in
      match Engine.load ~log:true store journal with
      | None -> fail "nothing loaded"
      | Some engine ->
          Engine.set engine value_input () 5;
          if Engine.get engine doubled () <> 10 then fail "stale result");
  test "a saved result that read through an unsaved one sees changes after loading" (fun () ->
      let store, journal = saved_session () in
      match Engine.load store journal with
      | None -> fail "nothing loaded"
      | Some engine ->
          if Engine.get engine reads_through () <> 50 then fail "stale before the change";
          Engine.set engine value_input () 6;
          let value = Engine.get engine reads_through () in
          if value <> 70 then fail "result %d after the change" value);
  test "saving again appends only what changed" (fun () ->
      let store, journal = saved_session () in
      match Engine.load store journal with
      | None -> fail "nothing loaded"
      | Some engine -> (
          let before = List.length (Store.records journal) in
          Engine.set engine value_input () 7;
          ignore (Engine.get engine doubled ());
          Engine.save engine journal;
          let after = List.length (Store.records journal) in
          if after <> before + 1 then fail "%d records, then %d" before after;
          match Engine.load store journal with
          | Some reloaded ->
              if Engine.get reloaded doubled () <> 14 then fail "the change was not saved"
          | None -> fail "nothing loaded again"));
  test "a result whose value is gone from the store is computed again" (fun () ->
      let store, journal = saved_session () in
      let empty = Store.open_ (fresh_directory ()) in
      ignore store;
      match Engine.load ~log:true empty journal with
      | None -> fail "nothing loaded"
      | Some engine ->
          Engine.set engine value_input () 4;
          if Engine.get engine doubled () <> 8 then fail "another result";
          if not (List.mem "saved_doubled()" (Engine.executed engine)) then fail "not computed")

let layer_value = Query.input ~name:"layer_input" ~show:(fun () -> "") ()
let own_value = Query.input ~name:"own_input" ~show:(fun () -> "") ()

let layer_unsaved =
  unit_query "layer_unsaved" (fun database () -> Query.get database layer_value () + 1)

let reads_layer =
  unit_query "reads_layer" ~saved:true (fun database () ->
      Query.demand database layer_unsaved () + Query.get database own_value ())

let reads_reader =
  unit_query "reads_reader" ~saved:true (fun database () ->
      10 * Query.demand database reads_layer ())

let () =
  test "a saved result that read an unsaved frozen result still sees changes after loading"
    (fun () ->
      let store = Store.open_ (fresh_directory ()) in
      let journal = Store.journal store "session" in
      let layer = Engine.frozen_layer () in
      Engine.set layer layer_value () 1;
      let engine = Engine.create ~shared:layer () in
      Engine.attach engine store;
      Engine.set engine own_value () 5;
      ignore (Engine.get engine reads_reader ());
      Engine.save engine journal;
      match Engine.load ~shared:layer store journal with
      | None -> fail "nothing loaded"
      | Some loaded ->
          Engine.set loaded own_value () 6;
          let value = Engine.get loaded reads_reader () in
          if value <> 80 then fail "result %d after the change" value)

let () = finish ()
