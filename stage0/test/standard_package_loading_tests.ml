let () =
  Harness.test
    "a standard library database that cannot be loaded is loaded by the next caller, not refused \
     for the rest of the process" (fun () ->
      let default_cache = Sys.getenv_opt "TRUSS_CACHE" in
      let writable_cache = Harness.scratch "writable-cache" in
      Unix.chmod writable_cache 0o777;
      Unix.putenv "TRUSS_CACHE" writable_cache;
      (match Workspace.For_testing.load_standard_package_database () with
      | _ -> Harness.fail "loaded the standard library through a cache that other users can write"
      | exception Workspace.Unusable_cache _ -> ());
      (match default_cache with
      | Some cache -> Unix.putenv "TRUSS_CACHE" cache
      | None -> Unix.unsetenv "TRUSS_CACHE");
      ignore (Workspace.For_testing.load_standard_package_database ()))
