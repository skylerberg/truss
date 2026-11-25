let make_fresh_directory () = Harness.make_scratch_directory "cache"

let open_cache directory =
  match Cache.open_ directory with Ok cache -> cache | Error message -> failwith message

let write_file path text =
  Out_channel.with_open_bin path (fun channel -> output_string channel text)

let age path ~days =
  let time = Unix.time () -. (days *. 24. *. 3600.) in
  Unix.utimes path time time

let () =
  Harness.test "collecting past the budget removes the cache file used least recently" (fun () ->
      let cache = open_cache (make_fresh_directory ()) in
      let objects = Cache.make_objects_directory cache in
      let make_file_path name =
        let path = Filename.concat objects name in
        write_file path "object";
        path
      in
      let unused = make_file_path "unused.o" and recent = make_file_path "recent.o" in
      age unused ~days:8.;
      Cache.collect cache ~budget:(String.length "object");
      if Sys.file_exists unused then Harness.fail "kept the file used least recently";
      if not (Sys.file_exists recent) then Harness.fail "removed the recent file");
  Harness.test "collecting within the budget keeps an unused cache file" (fun () ->
      let cache = open_cache (make_fresh_directory ()) in
      let path = Filename.concat (Cache.make_objects_directory cache) "unused.o" in
      write_file path "object";
      Unix.utimes path 1. 1.;
      Cache.collect cache ~budget:max_int;
      if not (Sys.file_exists path) then Harness.fail "removed a file")

let () =
  Harness.test "a new cache's directory can be read and written by its user alone" (fun () ->
      let directory = Filename.concat (make_fresh_directory ()) "new" in
      ignore (open_cache directory);
      let permissions = (Unix.stat directory).st_perm in
      if permissions land 0o077 <> 0 then Harness.fail "made with mode %o" permissions);
  Harness.test
    "a cache is refused in a directory that its group or other users can write, where they could \
     plant compiled objects" (fun () ->
      List.iter
        (fun permissions ->
          let directory = make_fresh_directory () in
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
      let path = Filename.concat (make_fresh_directory ()) "file" in
      write_file path "";
      match Cache.open_ path with
      | Ok _ -> Harness.fail "opened a cache in a file"
      | Error message ->
          Harness.expect_string ~expected:("The cache " ^ path ^ " is not a directory.") message);
  Harness.test
    "with HOME unset, the default cache is in the home directory of the user's account, not in the \
     shared temporary directory" (fun () ->
      List.iter Unix.unsetenv [ "TRUSS_CACHE"; "XDG_CACHE_HOME"; "HOME" ];
      match Cache.locate_default_directory () with
      | Ok directory ->
          Harness.expect_string
            ~expected:
              (Filename.concat
                 (Filename.concat (Unix.getpwuid (Unix.getuid ())).pw_dir ".cache")
                 "truss")
            directory
      | Error message -> Harness.fail "%s" message)
