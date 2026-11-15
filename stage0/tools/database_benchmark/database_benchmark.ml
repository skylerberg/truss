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

let write project path text =
  let file = Filename.concat project.root path in
  File_system.make_directory (Filename.dirname file);
  File_system.write file text;
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
  lower_ms : float option;
  save_ms : float;
  computed : int;
  collected : int;
  written_bytes : int;
}

let timed run =
  let start = Unix.gettimeofday () in
  let result = run () in
  (result, 1000. *. (Unix.gettimeofday () -. start))

let rec add_file_sizes sizes path =
  match Unix.lstat path with
  | { st_kind = S_DIR; _ } ->
      Array.iter (fun entry -> add_file_sizes sizes (Filename.concat path entry)) (Sys.readdir path)
  | { st_kind = S_REG; st_size; _ } -> Hashtbl.replace sizes path st_size
  | _ -> ()
  | exception Unix.Unix_error _ -> ()

let file_sizes root =
  let sizes = Hashtbl.create 64 in
  List.iter (add_file_sizes sizes) [ Database.store_directory (); Filename.concat root ".truss" ];
  sizes

let written_bytes ~before ~after =
  Hashtbl.fold
    (fun path size total ->
      total + max 0 (size - Option.value (Hashtbl.find_opt before path) ~default:0))
    after 0

let observing pipeline run =
  let result = ref None in
  let observed = Pipeline.For_testing.observe pipeline (fun () -> result := Some (run ())) in
  (Option.get !result, observed)

let snapshot_of root =
  match Database.take_snapshot root with
  | Ok (snapshot, _) -> snapshot
  | Error message -> failwith message

let own_packages snapshot = List.map snd (Database.packages snapshot)

let diagnostics snapshot pipeline =
  List.concat_map
    (fun package ->
      List.concat_map (Pipeline.file_diagnostics pipeline) (Database.package_files snapshot package))
    (own_packages snapshot)

let tests snapshot pipeline =
  let packages = own_packages snapshot in
  let names = Pipeline.names pipeline packages in
  List.concat_map
    (fun package ->
      List.filter_map
        (fun (declaration : Names.declaration) ->
          match declaration.path with
          | Test _ when declaration.ordinal = 0 -> Some declaration.path
          | _ -> None)
        (names.package_declarations package))
    packages

let lower snapshot pipeline =
  let tests = tests snapshot pipeline in
  let compiler = Cli.Compiler.lowering_only pipeline (own_packages snapshot) in
  let keys = List.filter_map (Compile.result_key compiler) tests in
  if List.length keys <> List.length tests then
    failwith (Printf.sprintf "%d of %d tests have a key" (List.length keys) (List.length tests))

let measure ~name ~has_errors ~root update =
  let before = file_sizes root in
  let (snapshot, pipeline, update_observed), update_ms = timed update in
  let (reported, check_observed), check_ms =
    timed (fun () -> observing pipeline (fun () -> diagnostics snapshot pipeline))
  in
  if reported <> [] <> has_errors then
    failwith
      (Printf.sprintf "%s: %d diagnostics: %s" name (List.length reported)
         (String.concat "; "
            (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) reported)));
  let lowering =
    if has_errors then None
    else Some (timed (fun () -> snd (observing pipeline (fun () -> lower snapshot pipeline))))
  in
  let (), save_ms = timed Database.For_testing.save in
  let observations =
    update_observed :: check_observed :: Option.to_list (Option.map fst lowering)
  in
  let count parts = List.length (List.sort_uniq compare (List.concat_map parts observations)) in
  ( pipeline,
    {
      update_ms;
      check_ms;
      lower_ms = Option.map snd lowering;
      save_ms;
      computed = count (fun (observed : Pipeline.For_testing.observed) -> observed.recomputed);
      collected = count (fun (observed : Pipeline.For_testing.observed) -> observed.collected);
      written_bytes = written_bytes ~before ~after:(file_sizes root);
    } )

let open_project root () =
  let snapshot = snapshot_of root in
  let pipeline = Database.pipeline snapshot in
  let (), propagated = observing pipeline (fun () -> Pipeline.propagate pipeline) in
  (snapshot, pipeline, propagated)

let refresh_project root pipeline () =
  let snapshot, propagated =
    observing pipeline (fun () ->
        let snapshot = snapshot_of root in
        if Database.pipeline snapshot != pipeline then
          failwith "refreshing the project gave a different pipeline";
        Pipeline.propagate pipeline;
        snapshot)
  in
  (snapshot, pipeline, propagated)

let copy source destination =
  File_system.make_directory destination;
  match Process.run "cp" [ "-R"; source ^ "/."; destination ] with
  | 0, _, _ -> ()
  | _, _, errors -> failwith ("cp: " ^ errors)

type outcome = { steps : (string * work) list; heap_bytes : int }

let build_and_edit ~scratch ~standard ~modules =
  let directory name = Filename.concat scratch name in
  List.iter (fun name -> File_system.remove (directory name)) [ "store"; "demo"; "worktree" ];
  copy standard (directory "store");
  Unix.putenv "TRUSS_CACHE" (directory "store");
  let project = create (directory "demo") modules in
  let pipeline, first_build =
    measure ~name:"First build" ~has_errors:false ~root:project.root (open_project project.root)
  in
  Gc.full_major ();
  let heap_bytes = (Gc.stat ()).live_words * (Sys.word_size / 8) in
  let edit_steps =
    List.map
      (fun { name; change; has_errors } ->
        change ();
        ( name,
          snd (measure ~name ~has_errors ~root:project.root (refresh_project project.root pipeline))
        ))
      (edits project)
  in
  Database.flush ();
  { steps = ("First build", first_build) :: edit_steps; heap_bytes }

let open_again ~scratch =
  let directory name = Filename.concat scratch name in
  Unix.putenv "TRUSS_CACHE" (directory "store");
  let reopen_step name root =
    (name, snd (measure ~name ~has_errors:false ~root (open_project root)))
  in
  let project = directory "demo" and worktree = directory "worktree" in
  let reopened = reopen_step "Open the project again in a new process" project in
  copy project worktree;
  let copied = reopen_step "Open a copy of the project, as a new worktree does" worktree in
  Database.flush ();
  [ reopened; copied ]

let in_new_process arguments =
  match Process.run Sys.executable_name arguments with
  | 0, output, _ -> Marshal.from_string output 0
  | status, _, errors ->
      failwith (Printf.sprintf "%s exited with %d: %s" (String.concat " " arguments) status errors)

let run ~scratch ~standard ~modules =
  let edited : outcome = in_new_process [ "--edit"; string_of_int modules; standard; scratch ] in
  let reopen_steps : (string * work) list = in_new_process [ "--reopen"; scratch ] in
  { edited with steps = edited.steps @ reopen_steps }

let median values =
  let sorted = List.sort Float.compare values in
  List.nth sorted (List.length sorted / 2)

let counts work = (work.computed, work.collected)

let summarize ~modules outcomes =
  let first_run = List.hd outcomes in
  List.iteri
    (fun run outcome ->
      List.iter2
        (fun (name, work) (_, first_work) ->
          let show work = Printf.sprintf "computed %d, collected %d" work.computed work.collected in
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
  Printf.printf "The first build computes %d parts and leaves %.0f MB of live heap.\n\n"
    (snd (List.hd first_run.steps)).computed
    (float_of_int first_run.heap_bytes /. 1e6);
  print_string
    "| Step | Update ms | Check ms | Lower ms | Save ms | Computed | Collected | Written KB |\n\
     |---|---:|---:|---:|---:|---:|---:|---:|\n";
  List.iteri
    (fun index (name, work) ->
      Printf.printf "| %s | %.1f | %.1f | %s | %.1f | %d | %d | %d |\n" name
        (median_of (fun work -> work.update_ms) index)
        (median_of (fun work -> work.check_ms) index)
        (match work.lower_ms with
        | Some _ ->
            Printf.sprintf "%.1f"
              (median_of (fun work -> Option.value work.lower_ms ~default:0.) index)
        | None -> "–")
        (median_of (fun work -> work.save_ms) index)
        work.computed work.collected
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
        ignore (Database.For_testing.standard_state ());
        Database.flush ())
  in
  let runs_directory = Filename.concat scratch "run" in
  let summaries =
    List.map
      (fun modules ->
        (modules, List.init runs (fun _ -> run ~scratch:runs_directory ~standard ~modules)))
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
    "Run on %s, on %s (%s, %d logical cores). %s Each run is two processes of its own, and each \
     time is the median of %d runs.\n\n\
     Checking the standard library into an empty store took %.0f ms.\n"
    date
    (Option.value (command "uname" [ "-sm" ]) ~default:"an unknown system")
    (processor ())
    (Domain.recommended_domain_count ())
    interference runs standard_time;
  List.iter (fun (modules, outcomes) -> summarize ~modules outcomes) summaries

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "--edit"; modules; standard; scratch ] ->
      File_system.make_directory scratch;
      let edited = build_and_edit ~scratch ~standard ~modules:(int_of_string modules) in
      print_string (Marshal.to_string (edited : outcome) [])
  | [ "--reopen"; scratch ] ->
      print_string (Marshal.to_string (open_again ~scratch : (string * work) list) [])
  | arguments -> benchmark arguments
