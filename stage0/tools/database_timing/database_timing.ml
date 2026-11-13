(* Timing the code database on a generated package: the cost of a first
   check, of starting again, and of an edit. This is a tool,
   not a test.

     dune exec stage0/tools/database_timing/database_timing.exe -- [MODULES]

   The package has a module [core] with one function, [leaf], and MODULES
   modules, forty unless given, of twenty-five functions each, every one of
   which calls [leaf] and the function before it. It is made in a temporary
   directory with a store of its own, and both are deleted at the end. *)

let functions = 25

let module_text ?(first = "core::leaf(value)") ?(more = "") index =
  let buffer = Buffer.create 2048 in
  Buffer.add_string buffer "use demo::core\n\n";
  for place = 0 to functions - 1 do
    let body =
      if place = 0 then first
      else Printf.sprintf "core::leaf(value) + f%d_%d(value)" index (place - 1)
    in
    Printf.bprintf buffer "internal fn f%d_%d(value: Int64) -> Int64 {\n  %s\n}\n\n" index place
      body
  done;
  Buffer.add_string buffer more;
  Buffer.contents buffer

let core_text body = Printf.sprintf "internal fn leaf(value: Int64) -> Int64 {\n  %s\n}\n" body

let timed run =
  let start = Unix.gettimeofday () in
  let result = run () in
  (result, (Unix.gettimeofday () -. start) *. 1000.)

let () =
  let modules = match Sys.argv with [| _; count |] -> int_of_string count | _ -> 40 in
  let root = Filename.temp_dir "truss-timing" "" in
  at_exit (fun () -> File_system.remove root);
  Unix.putenv "TRUSS_CACHE" (Filename.concat root "store");
  let directory = Filename.concat root "demo" in
  Unix.mkdir directory 0o755;
  let file name = Filename.concat directory name in
  File_system.write (file "truss.toml") "[package]\nname = \"demo\"\ntruss = \"0.1\"\n";
  File_system.write (file "core.truss") (core_text "value");
  for index = 0 to modules - 1 do
    File_system.write (file (Printf.sprintf "m%d.truss" index)) (module_text index)
  done;
  Printf.printf "%d modules, %d functions\n" (modules + 1) ((modules * functions) + 1);
  let opened label =
    let session, milliseconds =
      timed (fun () ->
          match Database.open_session directory with
          | Ok (session, _) -> session
          | Error message -> failwith message)
    in
    Printf.printf "%-58s %8.1f ms\n%!" label milliseconds;
    session
  in
  let check session =
    List.iter
      (fun (_, package) ->
        List.iter
          (fun module_ -> ignore (Database.diagnostics session module_))
          (Database.package_modules session package))
      (Database.packages session)
  in
  let step session label run =
    let counters () = Engine.counters (Database.For_testing.engine session) in
    let before = counters () in
    let (), milliseconds = timed run in
    let after = counters () in
    Printf.printf "%-58s %8.1f ms   computed %d, found %d\n%!" label milliseconds
      (after.computed - before.computed)
      (after.adopted - before.adopted)
  in
  let edit session label name text =
    File_system.write (file name) text;
    step session label (fun () ->
        Database.refresh session;
        check session;
        Database.save_session session)
  in
  let session = opened "open, with an empty store" in
  step session "check every module" (fun () -> check session);
  step session "save" (fun () -> Database.save_session session);
  Database.reset ();
  let session = opened "open again, as a new process does" in
  step session "check every module" (fun () -> check session);
  edit session "check and save after editing one body" "m0.truss"
    (module_text ~first:"core::leaf(value) + 0" 0);
  edit session "check and save after editing the body all call" "core.truss" (core_text "value + 0");
  edit session "check and save after adding a function" "m0.truss"
    (module_text ~more:"internal fn added() -> Int64 {\n  1\n}\n" 0);
  Database.reset ()
