open Harness

let fresh_directory () = scratch "cache"

let write_file path text =
  Out_channel.with_open_bin path (fun channel -> output_string channel text)

let segment_files directory =
  let segments = Filename.concat directory "segments" in
  Array.to_list (try Sys.readdir segments with Sys_error _ -> [||])
  |> List.filter (fun file -> Filename.check_suffix file ".segment")
  |> List.map (Filename.concat segments)
  |> List.sort compare

let file_size path = (Unix.stat path).st_size
let segments_size directory = List.fold_left ( + ) 0 (List.map file_size (segment_files directory))
let found cache key = Cache.find_result cache ~kind:Test_result ~key

let written directory key value =
  let cache = Cache.open_ directory in
  Cache.add_result cache ~kind:Test_result ~key value;
  Cache.close cache

let age path ~days =
  let time = Unix.time () -. (days *. 24. *. 3600.) in
  Unix.utimes path time time

let () =
  test "a result is found by its kind and key" (fun () ->
      let cache = Cache.open_ (fresh_directory ()) in
      Cache.add_result cache ~kind:Test_result ~key:"k" "passed";
      if found cache "k" <> Some "passed" then fail "not found";
      if Cache.find_result cache ~kind:Solver_answer ~key:"k" <> None then
        fail "found as another kind");
  test "a key the cache does not have finds nothing" (fun () ->
      let cache = Cache.open_ (fresh_directory ()) in
      if found cache "missing" <> None then fail "found a result");
  test "adding a result twice writes it once" (fun () ->
      let directory = fresh_directory () in
      let cache = Cache.open_ directory in
      Cache.add_result cache ~kind:Test_result ~key:"k" "passed";
      Cache.flush cache;
      let size = segments_size directory in
      Cache.add_result cache ~kind:Test_result ~key:"k" "passed";
      Cache.flush cache;
      if segments_size directory <> size then
        fail "grew from %d to %d" size (segments_size directory));
  test "a sealed segment is found again through its index" (fun () ->
      let directory = fresh_directory () in
      written directory "k" "kept";
      let indexes =
        Array.to_list (Sys.readdir (Filename.concat directory "segments"))
        |> List.filter (fun file -> Filename.check_suffix file ".index")
      in
      if List.length indexes <> 1 then fail "%d indexes" (List.length indexes);
      if found (Cache.open_ directory) "k" <> Some "kept" then fail "lost after sealing");
  test "a cache finds what another cache on its directory flushed" (fun () ->
      let directory = fresh_directory () in
      let first = Cache.open_ directory in
      Cache.add_result first ~kind:Test_result ~key:"k" "shared";
      Cache.flush first;
      if found (Cache.open_ directory) "k" <> Some "shared" then fail "not seen");
  test "a damaged record is missing" (fun () ->
      let directory = fresh_directory () in
      written directory "k" "fragile";
      List.iter
        (fun path ->
          let contents = Bytes.of_string (In_channel.with_open_bin path In_channel.input_all) in
          let last = Bytes.length contents - 10 in
          Bytes.set contents last (Char.chr ((Char.code (Bytes.get contents last) + 1) land 255));
          Out_channel.with_open_bin path (fun out -> Out_channel.output_bytes out contents))
        (segment_files directory);
      if found (Cache.open_ directory) "k" <> None then fail "a damaged result was found")

let () =
  test "collecting past the budget removes the least recently written results first" (fun () ->
      let directory = fresh_directory () in
      let segment_of key days =
        let before = segment_files directory in
        written directory key "result";
        let segment =
          List.find (fun path -> not (List.mem path before)) (segment_files directory)
        in
        age segment ~days;
        segment
      in
      let oldest = segment_of "oldest" 3. in
      ignore (segment_of "middle" 2.);
      ignore (segment_of "newest" 1.);
      let cache = Cache.open_ directory in
      Cache.collect cache ~budget:(segments_size directory - file_size oldest);
      Cache.close cache;
      let again = Cache.open_ directory in
      if found again "oldest" <> None then fail "kept the oldest result";
      if found again "middle" = None || found again "newest" = None then
        fail "removed a newer result");
  test "collecting keeps what the collecting process used" (fun () ->
      let directory = fresh_directory () in
      written directory "used" "result";
      written directory "unused" "result";
      let cache = Cache.open_ directory in
      if found cache "used" = None then fail "not found before collecting";
      Cache.collect cache ~budget:0;
      Cache.close cache;
      let again = Cache.open_ directory in
      if found again "used" = None then fail "removed a result the process used";
      if found again "unused" <> None then fail "kept a result no process used");
  test "collecting within the budget removes nothing" (fun () ->
      let directory = fresh_directory () in
      written directory "k" "result";
      let cache = Cache.open_ directory in
      Cache.collect cache ~budget:max_int;
      if found cache "k" = None then fail "removed a result");
  test "collecting past the budget removes the cache file used least recently" (fun () ->
      let cache = Cache.open_ (fresh_directory ()) in
      let objects = Cache.cache_files cache "objects" in
      let file name =
        let path = Filename.concat objects name in
        write_file path "object";
        path
      in
      let unused = file "unused.o" and recent = file "recent.o" in
      age unused ~days:8.;
      Cache.collect cache ~budget:(String.length "object");
      if Sys.file_exists unused then fail "kept the file used least recently";
      if not (Sys.file_exists recent) then fail "removed the recent file");
  test "collecting within the budget keeps an unused cache file" (fun () ->
      let cache = Cache.open_ (fresh_directory ()) in
      let path = Filename.concat (Cache.cache_files cache "objects") "unused.o" in
      write_file path "object";
      Unix.utimes path 1. 1.;
      Cache.collect cache ~budget:max_int;
      if not (Sys.file_exists path) then fail "removed a file")

let () =
  test "many small segments are gathered into one, and every record is kept" (fun () ->
      let directory = fresh_directory () in
      for index = 0 to 39 do
        written directory (string_of_int index) (Printf.sprintf "result %d" index)
      done;
      let cache = Cache.open_ directory in
      Cache.compact cache;
      Cache.close cache;
      let segments = List.length (segment_files directory) in
      if segments > 2 then fail "%d segments are left" segments;
      let again = Cache.open_ directory in
      for index = 0 to 39 do
        if found again (string_of_int index) <> Some (Printf.sprintf "result %d" index) then
          fail "result %d is gone" index
      done);
  test "a few small segments are left as they are" (fun () ->
      let directory = fresh_directory () in
      for index = 1 to 5 do
        written directory (string_of_int index) "result"
      done;
      let cache = Cache.open_ directory in
      Cache.compact cache;
      if List.length (segment_files directory) <> 5 then fail "the segments were rewritten")
