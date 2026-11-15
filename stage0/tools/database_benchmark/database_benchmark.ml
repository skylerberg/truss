module Names = Resolve.Names

let functions = 25
let last = functions - 1
let default_sizes = [ 50; 200; 800 ]
let module_name index = Printf.sprintf "m%d" index
let function_name index place = Printf.sprintf "f%d_%d" index place
let parent index = (index - 1) / 2
let module_path index = Printf.sprintf "%s/%s.truss" (module_name index) (module_name index)
let core_path = "core/core.truss"

let core_text =
  {|public type Point(x: Int64, y: Int64)

public trait Measured {
  fn measure(self) -> Int64
}

impl Measured for Point {
  fn measure(self) -> Int64 {
    self.x + self.y
  }
}

internal fn origin() -> Point {
  Point(x: 1, y: 2)
}

internal fn leaf(value: Int64) -> Int64 {
  value
}
|}

let callee index place =
  if place > 0 then function_name index (place - 1)
  else if index = 0 then "core::leaf"
  else module_name (parent index) ^ "::" ^ function_name (parent index) last

let body index place = Printf.sprintf "core::leaf(value) + %s(value)" (callee index place)

let module_text index =
  let buffer = Buffer.create 2048 in
  Buffer.add_string buffer "use demo::core\n";
  if index > 0 then Printf.bprintf buffer "use demo::%s\n" (module_name (parent index));
  for place = 0 to last do
    Printf.bprintf buffer "\ninternal fn %s(value: Int64) -> Int64 {\n  %s\n}\n"
      (function_name index place) (body index place)
  done;
  Printf.bprintf buffer
    "\ninternal fn measured_%d(point: core::Point) -> Int64 {\n  point.measure() + point.x\n}\n"
    index;
  Printf.bprintf buffer "\ntest \"%s\" {\n  assert %s(1) + measured_%d(core::origin()) > 0\n}\n"
    (module_name index) (function_name index last) index;
  Buffer.contents buffer

let replace_all ~old ~by text =
  let length = String.length old in
  let buffer = Buffer.create (String.length text) in
  let rec copy start position replaced =
    if position + length > String.length text then begin
      Buffer.add_substring buffer text start (String.length text - start);
      replaced
    end
    else if String.sub text position length = old then begin
      Buffer.add_substring buffer text start (position - start);
      Buffer.add_string buffer by;
      copy (position + length) (position + length) (replaced + 1)
    end
    else copy start (position + 1) replaced
  in
  if copy 0 0 0 = 0 then failwith (Printf.sprintf "no %S to replace" old);
  Buffer.contents buffer

type project = { root : string; modules : int; texts : (string, string) Hashtbl.t }

let writes = ref 0

let write project path text =
  let file = Filename.concat project.root path in
  File_system.make_directory (Filename.dirname file);
  File_system.write file text;
  incr writes;
  let modified = Unix.gettimeofday () +. float_of_int !writes in
  Unix.utimes file modified modified;
  Hashtbl.replace project.texts path text

let rewrite project path ~old ~by =
  write project path (replace_all ~old ~by (Hashtbl.find project.texts path))

let remove project path =
  File_system.remove (Filename.concat project.root (Filename.dirname path));
  Hashtbl.remove project.texts path

let create root modules =
  let project = { root; modules; texts = Hashtbl.create (modules + 2) } in
  File_system.make_directory root;
  write project "truss.toml" "[package]\nname = \"demo\"\ntruss = \"0.1\"\n";
  write project core_path core_text;
  for index = 0 to modules - 1 do
    write project (module_path index) (module_text index)
  done;
  project

type step = { name : string; change : unit -> unit; has_errors : bool }

let step ?(has_errors = false) name change = { name; change; has_errors }

let edits project =
  let leaf = project.modules - 1 and middle = project.modules / 2 in
  let edit_body ?(by = " + 0") index place =
    rewrite project (module_path index) ~old:(body index place) ~by:(body index place ^ by)
  in
  let before = Hashtbl.create 2 in
  let remember path = Hashtbl.replace before path (Hashtbl.find project.texts path) in
  let restore path = write project path (Hashtbl.find before path) in
  [
    step "Edit one function's body" (fun () ->
        remember (module_path leaf);
        edit_body leaf (last / 2));
    step "Undo that edit" (fun () -> restore (module_path leaf));
    step "Edit the body of the function every function calls" (fun () ->
        rewrite project core_path ~old:"-> Int64 {\n  value\n}" ~by:"-> Int64 {\n  value + 0\n}");
    step "Edit the body of a function every test reaches" (fun () -> edit_body 0 last);
    step "Change the signature of the function every function calls" (fun () ->
        rewrite project core_path ~old:"fn leaf(value: Int64) -> Int64 {\n  value + 0\n}"
          ~by:"fn leaf(value: Int64, extra: Int64 = 0) -> Int64 {\n  value + extra\n}");
    step "Add a field to the type every module reads" (fun () ->
        rewrite project core_path ~old:"Point(x: Int64, y: Int64)"
          ~by:"Point(x: Int64, y: Int64, z: Int64)";
        rewrite project core_path ~old:"Point(x: 1, y: 2)" ~by:"Point(x: 1, y: 2, z: 3)");
    step "Add a function to one module" (fun () ->
        let path = module_path middle in
        write project path
          (Hashtbl.find project.texts path ^ "\ninternal fn added() -> Int64 {\n  1\n}\n"));
    step "Rename a function and its callers" (fun () ->
        List.iter
          (fun index ->
            rewrite project (module_path index) ~old:(function_name 0 last) ~by:"renamed")
          [ 0; 1; 2 ]);
    step ~has_errors:true "Introduce a type error" (fun () ->
        remember (module_path middle);
        edit_body ~by:" + true" middle (last / 2));
    step "Fix the type error" (fun () -> restore (module_path middle));
    step "Remove a module" (fun () -> remove project (module_path leaf));
    step "Add the module back" (fun () -> write project (module_path leaf) (module_text leaf));
    step "Edit a tenth of the modules at once, as switching branches does" (fun () ->
        for index = 0 to project.modules - 1 do
          if index mod 10 = 0 then edit_body index 5
        done);
  ]

type work = {
  update_ms : float;
  check_ms : float;
  lower_ms : float;
  save_ms : float;
  marked : int;
  confirmed : int;
  computed : int;
  adopted : int;
  written_bytes : int;
}

let timed run =
  let start = Unix.gettimeofday () in
  let result = run () in
  (result, 1000. *. (Unix.gettimeofday () -. start))

let rec bytes_under path =
  match Unix.lstat path with
  | { st_kind = S_DIR; _ } ->
      Array.fold_left
        (fun total entry -> total + bytes_under (Filename.concat path entry))
        0 (Sys.readdir path)
  | { st_kind = S_REG; st_size; _ } -> st_size
  | _ -> 0
  | exception Unix.Unix_error _ -> 0

let counters session = Engine.counters (Database.For_testing.engine session)

let no_work : Engine.counters =
  { marked = 0; confirmed = 0; computed = 0; changed = 0; adopted = 0; copied = 0; collected = 0 }

let diagnostics session =
  List.concat_map
    (fun (_, package) ->
      List.concat_map (Database.diagnostics session) (Database.package_files session package))
    (Database.packages session)

let tests session =
  List.concat_map
    (fun (_, package) ->
      List.filter_map
        (fun (declaration : Names.declaration) ->
          match declaration.path with
          | Test _ when declaration.ordinal = 0 -> Some declaration.path
          | _ -> None)
        (Query.demand (Database.context session) Names.package_declarations package))
    (Database.packages session)

let lower ~has_errors session =
  let tests = tests session in
  let keys =
    Compile.test_keys (Cli.Compiler.lowering_only session (Database.context session)) tests
  in
  if List.length keys <> List.length tests && not has_errors then
    failwith (Printf.sprintf "%d of %d tests have a key" (List.length keys) (List.length tests))

let measure ~name ~has_errors update =
  let store_bytes = bytes_under (Database.store_directory ()) in
  let (session, (before : Engine.counters)), update_ms = timed update in
  let reported, check_ms = timed (fun () -> diagnostics session) in
  if reported <> [] <> has_errors then
    failwith
      (Printf.sprintf "%s: %d diagnostics: %s" name (List.length reported)
         (String.concat "; "
            (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) reported)));
  let (), lower_ms = timed (fun () -> lower ~has_errors session) in
  let after = counters session in
  let (), save_ms =
    timed (fun () ->
        Database.save_session session;
        Database.flush_store ())
  in
  ( session,
    {
      update_ms;
      check_ms;
      lower_ms;
      save_ms;
      marked = after.marked - before.marked;
      confirmed = after.confirmed - before.confirmed;
      computed = after.computed - before.computed;
      adopted = after.adopted - before.adopted;
      written_bytes = bytes_under (Database.store_directory ()) - store_bytes;
    } )

let open_project directory =
  match Database.open_session directory with
  | Ok (session, _) -> (session, no_work)
  | Error message -> failwith message

let copy source destination =
  File_system.make_directory destination;
  match Process.run "cp" [ "-R"; source ^ "/."; destination ] with
  | 0, _, _ -> ()
  | _, _, errors -> failwith ("cp: " ^ errors)

type outcome = { steps : (string * work) list; result_count : int; heap_bytes : int }

let run_once ~scratch ~standard ~modules =
  let directory name = Filename.concat scratch name in
  Database.reset ();
  List.iter (fun name -> File_system.remove (directory name)) [ "store"; "demo"; "worktree" ];
  copy standard (directory "store");
  Unix.putenv "TRUSS_CACHE" (directory "store");
  let project = create (directory "demo") modules in
  let session, first_build =
    measure ~name:"First build" ~has_errors:false (fun () -> open_project project.root)
  in
  Gc.full_major ();
  let heap_bytes = (Gc.stat ()).live_words * (Sys.word_size / 8) in
  let result_count = List.length (Engine.nodes (Database.For_testing.engine session)) in
  let edited =
    List.rev
      (List.fold_left
         (fun measured { name; change; has_errors } ->
           change ();
           let _, work =
             measure ~name ~has_errors (fun () ->
                 let before = counters session in
                 Database.refresh session;
                 (session, before))
           in
           (name, work) :: measured)
         [] (edits project))
  in
  Database.reset ();
  let reopened = "Open the project again in a new process" in
  let _, opened_again =
    measure ~name:reopened ~has_errors:false (fun () -> open_project project.root)
  in
  copy project.root (directory "worktree");
  let worktree = "Open a copy of the project, as a new worktree does" in
  let _, opened_copy =
    measure ~name:worktree ~has_errors:false (fun () -> open_project (directory "worktree"))
  in
  Database.reset ();
  {
    steps =
      (("First build", first_build) :: edited)
      @ [ (reopened, opened_again); (worktree, opened_copy) ];
    result_count;
    heap_bytes;
  }

let median values =
  let sorted = List.sort Float.compare values in
  List.nth sorted (List.length sorted / 2)

let counts work = (work.marked, work.confirmed, work.computed, work.adopted)

let summarize ~modules outcomes =
  let first_run = List.hd outcomes in
  List.iteri
    (fun run outcome ->
      List.iter2
        (fun (name, work) (_, first_work) ->
          let show work =
            Printf.sprintf "marked %d, confirmed %d, computed %d, adopted %d" work.marked
              work.confirmed work.computed work.adopted
          in
          if counts work <> counts first_work then
            failwith
              (Printf.sprintf "%d modules, %s: run 1 counted %s, and run %d %s" modules name
                 (show first_work) (run + 1) (show work)))
        outcome.steps first_run.steps)
    outcomes;
  let median_of field index =
    median (List.map (fun outcome -> field (snd (List.nth outcome.steps index))) outcomes)
  in
  Printf.printf "\n### %d modules, %d functions\n\n" modules ((modules * (functions + 1)) + 3);
  Printf.printf "The first build leaves %d results and %.0f MB of live heap.\n\n"
    first_run.result_count
    (float_of_int first_run.heap_bytes /. 1e6);
  print_string
    "| Step | Update ms | Check ms | Lower ms | Save ms | Marked | Confirmed | Computed | Adopted \
     | Written KB |\n\
     |---|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n";
  List.iteri
    (fun index (name, work) ->
      Printf.printf "| %s | %.1f | %.1f | %.1f | %.1f | %d | %d | %d | %d | %d |\n" name
        (median_of (fun work -> work.update_ms) index)
        (median_of (fun work -> work.check_ms) index)
        (median_of (fun work -> work.lower_ms) index)
        (median_of (fun work -> work.save_ms) index)
        work.marked work.confirmed work.computed work.adopted
        ((int_of_float (median_of (fun work -> float_of_int work.written_bytes) index) + 512) / 1024))
    first_run.steps

let command program arguments =
  match Process.run program arguments with
  | 0, output, _ -> Some (String.trim output)
  | _ | (exception _) -> None

let processor () =
  match command "sysctl" [ "-n"; "machdep.cpu.brand_string" ] with
  | Some name -> name
  | None -> (
      match
        List.find_map
          (fun line ->
            match String.index_opt line ':' with
            | Some colon when String.starts_with ~prefix:"model name" line ->
                Some (String.trim (String.sub line (colon + 1) (String.length line - colon - 1)))
            | _ -> None)
          (In_channel.with_open_text "/proc/cpuinfo" In_channel.input_lines)
      with
      | Some name -> name
      | None | (exception Sys_error _) -> "an unknown processor")

let busy_seconds () =
  match In_channel.with_open_text "/proc/stat" In_channel.input_line with
  | Some line -> (
      match List.filter (( <> ) "") (String.split_on_char ' ' line) with
      | "cpu" :: user :: nice :: system :: _idle :: _iowait :: irq :: softirq :: steal :: _ ->
          Some
            (float_of_int
               (List.fold_left
                  (fun total field -> total + int_of_string field)
                  0
                  [ user; nice; system; irq; softirq; steal ])
            /. 100.)
      | _ -> None)
  | None | (exception Sys_error _) -> None

let own_seconds () =
  let times = Unix.times () in
  times.tms_utime +. times.tms_stime +. times.tms_cutime +. times.tms_cstime

let run_in_new_process ~scratch ~standard ~modules =
  match Process.run Sys.executable_name [ "--run"; string_of_int modules; standard; scratch ] with
  | 0, output, _ -> (Marshal.from_string output 0 : outcome)
  | status, _, errors ->
      failwith (Printf.sprintf "a run of %d modules exited with %d: %s" modules status errors)

let benchmark arguments =
  let rec parse runs sizes = function
    | "--runs" :: count :: rest -> parse (int_of_string count) sizes rest
    | size :: rest -> parse runs (int_of_string size :: sizes) rest
    | [] -> (runs, match List.rev sizes with [] -> default_sizes | sizes -> sizes)
  in
  let runs, sizes = parse 3 [] arguments in
  if runs < 1 || List.exists (fun modules -> modules < 10) sizes then begin
    prerr_endline
      "usage: database_benchmark [--runs N] [MODULES ...], with N >= 1 and MODULES >= 10";
    exit 2
  end;
  let scratch = Filename.temp_dir "truss-benchmark" "" in
  at_exit (fun () -> File_system.remove scratch);
  let started = Unix.gettimeofday () and busy_before = busy_seconds () in
  let own_before = own_seconds () in
  let standard = Filename.concat scratch "standard" in
  Unix.putenv "TRUSS_CACHE" standard;
  let (), standard_time =
    timed (fun () ->
        Database.For_testing.prepare_store ();
        Database.flush_store ())
  in
  Database.reset ();
  let runs_directory = Filename.concat scratch "run" in
  let summaries =
    List.map
      (fun modules ->
        ( modules,
          List.init runs (fun _ -> run_in_new_process ~scratch:runs_directory ~standard ~modules) ))
      sizes
  in
  let elapsed = Unix.gettimeofday () -. started in
  let interference =
    match (busy_before, busy_seconds ()) with
    | Some before, Some after ->
        Printf.sprintf "Other processes used %.1f CPU-seconds during the run's %.0f seconds."
          (Float.max 0. (after -. before -. (own_seconds () -. own_before)))
          elapsed
    | _ ->
        Printf.sprintf
          "The run took %.0f seconds, and this system does not report other processes' CPU time."
          elapsed
  in
  let date =
    let time = Unix.localtime (Unix.time ()) in
    Printf.sprintf "%d-%02d-%02d" (time.tm_year + 1900) (time.tm_mon + 1) time.tm_mday
  in
  Printf.printf
    "Run on %s, on %s (%s, %d logical cores). %s Each run is a process of its own, and each time \
     is the median of %d runs.\n\n\
     Checking the standard library into an empty store took %.0f ms.\n"
    date
    (Option.value (command "uname" [ "-sm" ]) ~default:"an unknown system")
    (processor ())
    (Domain.recommended_domain_count ())
    interference runs standard_time;
  List.iter (fun (modules, outcomes) -> summarize ~modules outcomes) summaries

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "--run"; modules; standard; scratch ] ->
      File_system.make_directory scratch;
      let outcome = run_once ~scratch ~standard ~modules:(int_of_string modules) in
      print_string (Marshal.to_string (outcome : outcome) [])
  | arguments -> benchmark arguments
