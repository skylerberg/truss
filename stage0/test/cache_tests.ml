let fresh_directory () = Harness.scratch "cache"

let open_cache directory =
  match Cache.open_ directory with Ok cache -> cache | Error message -> failwith message

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
  let cache = open_cache directory in
  Cache.add_result cache ~kind:Test_result ~key value;
  Cache.close cache

let age path ~days =
  let time = Unix.time () -. (days *. 24. *. 3600.) in
  Unix.utimes path time time

let () =
  Harness.test "a result is found by its kind and key" (fun () ->
      let cache = open_cache (fresh_directory ()) in
      Cache.add_result cache ~kind:Test_result ~key:"k" "passed";
      if found cache "k" <> Some "passed" then Harness.fail "not found";
      if Cache.find_result cache ~kind:Solver_answer ~key:"k" <> None then
        Harness.fail "found as another kind");
  Harness.test "a key the cache does not have finds nothing" (fun () ->
      let cache = open_cache (fresh_directory ()) in
      if found cache "missing" <> None then Harness.fail "found a result");
  Harness.test "adding a result twice writes it once" (fun () ->
      let directory = fresh_directory () in
      let cache = open_cache directory in
      Cache.add_result cache ~kind:Test_result ~key:"k" "passed";
      Cache.flush cache;
      let size = segments_size directory in
      Cache.add_result cache ~kind:Test_result ~key:"k" "passed";
      Cache.flush cache;
      if segments_size directory <> size then
        Harness.fail "grew from %d to %d" size (segments_size directory));
  Harness.test "a sealed segment is found again through its index" (fun () ->
      let directory = fresh_directory () in
      written directory "k" "kept";
      let indexes =
        Array.to_list (Sys.readdir (Filename.concat directory "segments"))
        |> List.filter (fun file -> Filename.check_suffix file ".index")
      in
      if List.length indexes <> 1 then Harness.fail "%d indexes" (List.length indexes);
      if found (open_cache directory) "k" <> Some "kept" then Harness.fail "lost after sealing");
  Harness.test "a cache finds what another cache on its directory flushed" (fun () ->
      let directory = fresh_directory () in
      let first = open_cache directory in
      Cache.add_result first ~kind:Test_result ~key:"k" "shared";
      Cache.flush first;
      if found (open_cache directory) "k" <> Some "shared" then Harness.fail "not seen");
  Harness.test "a damaged record is missing" (fun () ->
      let directory = fresh_directory () in
      written directory "k" "fragile";
      List.iter
        (fun path ->
          let contents = Bytes.of_string (In_channel.with_open_bin path In_channel.input_all) in
          let last = Bytes.length contents - 10 in
          Bytes.set contents last (Char.chr ((Char.code (Bytes.get contents last) + 1) land 255));
          Out_channel.with_open_bin path (fun out -> Out_channel.output_bytes out contents))
        (segment_files directory);
      if found (open_cache directory) "k" <> None then Harness.fail "a damaged result was found")

let () =
  Harness.test "collecting past the budget removes the least recently written results first"
    (fun () ->
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
      let cache = open_cache directory in
      Cache.collect cache ~budget:(segments_size directory - file_size oldest);
      Cache.close cache;
      let again = open_cache directory in
      if found again "oldest" <> None then Harness.fail "kept the oldest result";
      if found again "middle" = None || found again "newest" = None then
        Harness.fail "removed a newer result");
  Harness.test "collecting keeps what the collecting process used" (fun () ->
      let directory = fresh_directory () in
      written directory "used" "result";
      written directory "unused" "result";
      let cache = open_cache directory in
      if found cache "used" = None then Harness.fail "not found before collecting";
      Cache.collect cache ~budget:0;
      Cache.close cache;
      let again = open_cache directory in
      if found again "used" = None then Harness.fail "removed a result the process used";
      if found again "unused" <> None then Harness.fail "kept a result no process used");
  Harness.test "collecting within the budget removes nothing" (fun () ->
      let directory = fresh_directory () in
      written directory "k" "result";
      let cache = open_cache directory in
      Cache.collect cache ~budget:max_int;
      if found cache "k" = None then Harness.fail "removed a result");
  Harness.test "collecting past the budget removes the cache file used least recently" (fun () ->
      let cache = open_cache (fresh_directory ()) in
      let objects = Cache.make_objects_directory cache in
      let file name =
        let path = Filename.concat objects name in
        write_file path "object";
        path
      in
      let unused = file "unused.o" and recent = file "recent.o" in
      age unused ~days:8.;
      Cache.collect cache ~budget:(String.length "object");
      if Sys.file_exists unused then Harness.fail "kept the file used least recently";
      if not (Sys.file_exists recent) then Harness.fail "removed the recent file");
  Harness.test "collecting within the budget keeps an unused cache file" (fun () ->
      let cache = open_cache (fresh_directory ()) in
      let path = Filename.concat (Cache.make_objects_directory cache) "unused.o" in
      write_file path "object";
      Unix.utimes path 1. 1.;
      Cache.collect cache ~budget:max_int;
      if not (Sys.file_exists path) then Harness.fail "removed a file")

let () =
  Harness.test "many small segments are gathered into one, and every record is kept" (fun () ->
      let directory = fresh_directory () in
      for index = 0 to 39 do
        written directory (string_of_int index) (Printf.sprintf "result %d" index)
      done;
      let cache = open_cache directory in
      Cache.compact cache;
      Cache.close cache;
      let segments = List.length (segment_files directory) in
      if segments > 2 then Harness.fail "%d segments are left" segments;
      let again = open_cache directory in
      for index = 0 to 39 do
        if found again (string_of_int index) <> Some (Printf.sprintf "result %d" index) then
          Harness.fail "result %d is gone" index
      done);
  Harness.test "a few small segments are left as they are" (fun () ->
      let directory = fresh_directory () in
      for index = 1 to 5 do
        written directory (string_of_int index) "result"
      done;
      let cache = open_cache directory in
      Cache.compact cache;
      if List.length (segment_files directory) <> 5 then Harness.fail "the segments were rewritten")

let () =
  Harness.test "a new cache's directory can be read and written by its user alone" (fun () ->
      let directory = Filename.concat (fresh_directory ()) "new" in
      ignore (open_cache directory);
      let permissions = (Unix.stat directory).st_perm in
      if permissions land 0o077 <> 0 then Harness.fail "made with mode %o" permissions);
  Harness.test
    "a cache is refused in a directory that its group or other users can write, where they could \
     plant results" (fun () ->
      List.iter
        (fun permissions ->
          let directory = fresh_directory () in
          Unix.chmod directory permissions;
          match Cache.open_ directory with
          | Ok _ -> Harness.fail "opened a cache in a directory of mode %o" permissions
          | Error message ->
              if
                not
                  (String.starts_with
                     ~prefix:("Users other than its owner can write the cache " ^ directory)
                     message)
              then Harness.fail "refused with: %s" message)
        [ 0o775; 0o757 ]);
  Harness.test "a cache is refused at a path that is not a directory" (fun () ->
      let path = Filename.concat (fresh_directory ()) "file" in
      write_file path "";
      match Cache.open_ path with
      | Ok _ -> Harness.fail "opened a cache in a file"
      | Error message ->
          Harness.expect_string ~expected:("The cache " ^ path ^ " is not a directory.") message);
  Harness.test
    "with HOME unset, the default cache is in the home directory of the user's account, not in the \
     shared temporary directory" (fun () ->
      Harness.with_environment
        [ ("TRUSS_CACHE", ""); ("XDG_CACHE_HOME", ""); ("HOME", "") ]
        (fun () ->
          match Cache.default_directory () with
          | Ok directory ->
              Harness.expect_string
                ~expected:
                  (Filename.concat
                     (Filename.concat (Unix.getpwuid (Unix.getuid ())).pw_dir ".cache")
                     "truss")
                directory
          | Error message -> Harness.fail "%s" message))
