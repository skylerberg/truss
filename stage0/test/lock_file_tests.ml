let make_lock_path name = Filename.concat (Harness.make_scratch_directory "lock-file") name

let is_true_in_child work =
  match Unix.fork () with
  | 0 -> Unix._exit (match work () with true -> 0 | false -> 1 | exception _ -> 2)
  | child -> (
      match Unix.waitpid [] child with
      | _, WEXITED 0 -> true
      | _, WEXITED 1 -> false
      | _ -> failwith "the child failed")

let is_free_in_child path =
  is_true_in_child (fun () ->
      match Lock_file.acquire_if_free path with
      | Some lock ->
          Lock_file.release lock;
          true
      | None -> false)

let () =
  Harness.test "a lock file exists while it is held, and its release removes it" (fun () ->
      let path = make_lock_path "held.lock" in
      let lock = Lock_file.acquire path in
      if not (Sys.file_exists path) then Harness.fail "acquiring made no file";
      Lock_file.release lock;
      if Sys.file_exists path then Harness.fail "releasing left the file");
  Harness.test "another process cannot take a held lock until its holder releases it" (fun () ->
      let path = make_lock_path "contended.lock" in
      let lock = Lock_file.acquire path in
      if is_free_in_child path then Harness.fail "another process took the held lock";
      Lock_file.release lock;
      if not (is_free_in_child path) then Harness.fail "another process could not take it after");
  Harness.test "a lock this process holds reads as held, and checking does not release it"
    (fun () ->
      let path = make_lock_path "own.lock" in
      let lock = Lock_file.acquire path in
      if not (Lock_file.is_held path) then Harness.fail "its own lock did not read as held";
      if is_free_in_child path then Harness.fail "checking released the lock";
      Lock_file.release lock);
  Harness.test "another process's lock reads as held" (fun () ->
      let path = make_lock_path "theirs.lock" in
      let lock = Lock_file.acquire path in
      if not (is_true_in_child (fun () -> Lock_file.is_held path)) then
        Harness.fail "another process's lock did not read as held";
      Lock_file.release lock;
      if Lock_file.is_held path then Harness.fail "a released lock read as held");
  Harness.test "taking a lock this process already holds is a compiler bug" (fun () ->
      let path = make_lock_path "twice.lock" in
      let lock = Lock_file.acquire path in
      (match Lock_file.acquire_if_free path with
      | exception Compiler_bug.Bug _ -> ()
      | Some _ | None -> Harness.fail "took a lock it already held");
      if is_free_in_child path then Harness.fail "the refused attempt released the lock";
      Lock_file.release lock);
  Harness.test "a process waiting for a lock takes the file that replaces the released one"
    (fun () ->
      let path = make_lock_path "replaced.lock" in
      let lock = Lock_file.acquire path in
      let ready, signal = Unix.pipe ~cloexec:true () in
      match Unix.fork () with
      | 0 ->
          ignore (Lock_file.acquire path);
          ignore (Unix.write_substring signal "x" 0 1);
          Unix.sleep 60;
          Unix._exit 0
      | waiter ->
          Fun.protect
            ~finally:(fun () ->
              Unix.kill waiter Sys.sigkill;
              ignore (Unix.waitpid [] waiter))
            (fun () ->
              Unix.sleepf 0.2;
              Lock_file.release lock;
              let byte = Bytes.create 1 in
              ignore (Unix.read ready byte 0 1);
              if not (Sys.file_exists path && Lock_file.is_held path) then
                Harness.fail "the waiter holds no file at the lock's path"))
