let functions = 25
let last = functions - 1
let default_sizes = [ 50; 200; 800 ]
let make_module_name index = Printf.sprintf "m%d" index
let make_function_name index place = Printf.sprintf "f%d_%d" index place
let compute_parent index = (index - 1) / 2

let make_module_path index =
  Printf.sprintf "%s/%s.truss" (make_module_name index) (make_module_name index)

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

let make_callee index place =
  if place > 0 then make_function_name index (place - 1)
  else if index = 0 then "core.leaf"
  else
    make_module_name (compute_parent index) ^ "." ^ make_function_name (compute_parent index) last

let make_body index place = Printf.sprintf "core.leaf(value) + %s(value)" (make_callee index place)

let make_module_text index =
  let buffer = Buffer.create 2048 in
  Buffer.add_string buffer "use demo.core\n";
  if index > 0 then Printf.bprintf buffer "use demo.%s\n" (make_module_name (compute_parent index));
  for place = 0 to last do
    Printf.bprintf buffer "\ninternal fn %s(value: Int64) -> Int64 {\n  %s\n}\n"
      (make_function_name index place) (make_body index place)
  done;
  Printf.bprintf buffer
    "\ninternal fn measured_%d(point: core.Point) -> Int64 {\n  point.measure() + point.x\n}\n"
    index;
  Printf.bprintf buffer "\ntest \"%s\" {\n  assert %s(1) + measured_%d(core.origin()) > 0\n}\n"
    (make_module_name index) (make_function_name index last) index;
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

let create_project root modules =
  let project = { root; modules; texts = Hashtbl.create (modules + 2) } in
  File_system.make_directory root;
  write project "truss.toml" "[package]\nname = \"demo\"\ntruss = \"0.1\"\n";
  write project core_path core_text;
  for index = 0 to modules - 1 do
    write project (make_module_path index) (make_module_text index)
  done;
  project

type step = { name : string; change : unit -> unit; has_errors : bool }

let make_step ?(has_errors = false) name change = { name; change; has_errors }

let list_edits project =
  let leaf = project.modules - 1 and middle = project.modules / 2 in
  let edit_body ?(by = " + 0") index place =
    rewrite project (make_module_path index) ~old:(make_body index place)
      ~by:(make_body index place ^ by)
  in
  let before = Hashtbl.create 2 in
  let remember path = Hashtbl.replace before path (Hashtbl.find project.texts path) in
  let restore path = write project path (Hashtbl.find before path) in
  [
    make_step "Edit one function's body" (fun () ->
        remember (make_module_path leaf);
        edit_body leaf (last / 2));
    make_step "Undo that edit" (fun () -> restore (make_module_path leaf));
    make_step "Edit the body of the function every function calls" (fun () ->
        rewrite project core_path ~old:"-> Int64 {\n  value\n}" ~by:"-> Int64 {\n  value + 0\n}");
    make_step "Edit the body of a function every test reaches" (fun () -> edit_body 0 last);
    make_step "Change the signature of the function every function calls" (fun () ->
        rewrite project core_path ~old:"fn leaf(value: Int64) -> Int64 {\n  value + 0\n}"
          ~by:"fn leaf(value: Int64, extra: Int64 = 0) -> Int64 {\n  value + extra\n}");
    make_step "Add a field to the type every module reads" (fun () ->
        rewrite project core_path ~old:"Point(x: Int64, y: Int64)"
          ~by:"Point(x: Int64, y: Int64, z: Int64)";
        rewrite project core_path ~old:"Point(x: 1, y: 2)" ~by:"Point(x: 1, y: 2, z: 3)");
    make_step "Add a function to one module" (fun () ->
        let path = make_module_path middle in
        write project path
          (Hashtbl.find project.texts path ^ "\npublic fn added() -> Int64 {\n  1\n}\n"));
    make_step "Rename a function and its callers" (fun () ->
        List.iter
          (fun index ->
            rewrite project (make_module_path index) ~old:(make_function_name 0 last) ~by:"renamed")
          [ 0; 1; 2 ]);
    make_step ~has_errors:true "Introduce a type error" (fun () ->
        remember (make_module_path middle);
        edit_body ~by:" + true" middle (last / 2));
    make_step "Fix the type error" (fun () -> restore (make_module_path middle));
    make_step "Remove a module" (fun () -> remove project (make_module_path leaf));
    make_step "Add the module back" (fun () ->
        write project (make_module_path leaf) (make_module_text leaf));
    make_step "Edit a tenth of the modules at once, as switching branches does" (fun () ->
        for index = 0 to project.modules - 1 do
          if index mod 10 = 0 then edit_body index 5
        done);
  ]

type work = {
  update_ms : float;
  check_ms : float;
  key_ms : float option;
  save_ms : float;
  computed : int;
  collected : int;
  written_bytes : int;
}

let measure_time run =
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

let read_file_sizes root =
  let sizes = Hashtbl.create 64 in
  List.iter (add_file_sizes sizes)
    [ Cache.directory (Workspace.open_cache ()); Filename.concat root ".truss" ];
  sizes

let count_written_bytes ~before ~after =
  Hashtbl.fold
    (fun path size total ->
      total + max 0 (size - Option.value (Hashtbl.find_opt before path) ~default:0))
    after 0

let read_snapshot root =
  match Workspace.take_snapshot root with
  | Ok (snapshot, _) -> snapshot
  | Error message -> failwith message

let list_own_packages snapshot = List.map snd (Workspace.list_packages snapshot)

let list_errors snapshot database =
  List.filter Diagnostic.is_error
    (List.concat_map
       (fun package ->
         List.concat_map
           (Database.list_file_diagnostics database)
           (Workspace.list_package_files snapshot package))
       (list_own_packages snapshot))

let list_tests snapshot database =
  let names = Database.make_name_lookups database in
  List.concat_map
    (fun package ->
      List.filter_map
        (fun (declaration : Resolve.Names.declaration) ->
          match declaration.key.path with
          | Test _ when declaration.key.ordinal = 0 -> Some declaration.key.path
          | _ -> None)
        (names.list_package_declarations package))
    (list_own_packages snapshot)

let compute_test_keys snapshot database =
  let tests = list_tests snapshot database in
  match Database.find_lowered_lookups database (list_own_packages snapshot) with
  | Error message -> failwith message
  | Ok lookups ->
      List.iter
        (fun test ->
          match lookups.read_test_key (Lowering.make_root test) with
          | Ok _ -> ()
          | Error (Unsupported unsupported) ->
              failwith
                (Printf.sprintf "%s has no key: %s" (Path.show test)
                   (Catalog.Codegen_description.describe_failure ~show_file:Path.show_file
                      (Unsupported { construct = unsupported.construct; location = None })))
          | Error (Todo_types _) ->
              failwith
                (Printf.sprintf "%s has no key: it reaches a type defined as todo" (Path.show test)))
        tests

let measure ~name ~has_errors ~root update =
  let before = read_file_sizes root in
  let ((snapshot, database), update_observed), update_ms =
    measure_time (fun () -> Database.For_testing.observe update)
  in
  let (errors, check_observed), check_ms =
    measure_time (fun () -> Database.For_testing.observe (fun () -> list_errors snapshot database))
  in
  if errors <> [] <> has_errors then
    failwith
      (Printf.sprintf "%s: %d errors: %s" name (List.length errors)
         (String.concat "; "
            (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) errors)));
  let keying =
    if has_errors then None
    else
      Some
        (measure_time (fun () ->
             snd (Database.For_testing.observe (fun () -> compute_test_keys snapshot database))))
  in
  let (), save_ms = measure_time Workspace.For_testing.save in
  let observations = update_observed :: check_observed :: Option.to_list (Option.map fst keying) in
  let count list_parts =
    List.length (List.sort_uniq compare (List.concat_map list_parts observations))
  in
  {
    update_ms;
    check_ms;
    key_ms = Option.map snd keying;
    save_ms;
    computed = count (fun (observed : Database.For_testing.observed) -> observed.recomputed);
    collected = count (fun (observed : Database.For_testing.observed) -> observed.collected);
    written_bytes = count_written_bytes ~before ~after:(read_file_sizes root);
  }

let open_project root () =
  let snapshot = read_snapshot root in
  (snapshot, Workspace.open_database snapshot)

let copy_directory source destination =
  File_system.make_directory destination;
  match Process.run "cp" [ "-R"; source ^ "/."; destination ] with
  | 0, _, _ -> ()
  | _, _, errors -> failwith ("cp: " ^ errors)

type outcome = { steps : (string * work) list; heap_bytes : int }

let build_and_edit ~scratch ~standard ~modules =
  let make_directory name = Filename.concat scratch name in
  List.iter (fun name -> File_system.remove (make_directory name)) [ "cache"; "demo"; "worktree" ];
  copy_directory standard (make_directory "cache");
  Unix.putenv "TRUSS_CACHE" (make_directory "cache");
  let project = create_project (make_directory "demo") modules in
  let first_build =
    measure ~name:"First build" ~has_errors:false ~root:project.root (open_project project.root)
  in
  Gc.full_major ();
  let heap_bytes = (Gc.stat ()).live_words * (Sys.word_size / 8) in
  let edit_steps =
    List.map
      (fun { name; change; has_errors } ->
        change ();
        (name, measure ~name ~has_errors ~root:project.root (open_project project.root)))
      (list_edits project)
  in
  Workspace.flush ();
  { steps = ("First build", first_build) :: edit_steps; heap_bytes }

let open_again ~scratch =
  let make_directory name = Filename.concat scratch name in
  Unix.putenv "TRUSS_CACHE" (make_directory "cache");
  let measure_reopen name root =
    (name, measure ~name ~has_errors:false ~root (open_project root))
  in
  let project = make_directory "demo" and worktree = make_directory "worktree" in
  let reopened = measure_reopen "Open the project again in a new process" project in
  copy_directory project worktree;
  let copied = measure_reopen "Open a copy of the project, as a new worktree does" worktree in
  Workspace.flush ();
  [ reopened; copied ]

let run_in_new_process arguments =
  match Process.run Sys.executable_name arguments with
  | 0, output, _ -> Marshal.from_string output 0
  | status, _, errors ->
      failwith (Printf.sprintf "%s exited with %d: %s" (String.concat " " arguments) status errors)

let run ~scratch ~standard ~modules =
  let edited : outcome =
    run_in_new_process [ "--edit"; string_of_int modules; standard; scratch ]
  in
  let reopen_steps : (string * work) list = run_in_new_process [ "--reopen"; scratch ] in
  { edited with steps = edited.steps @ reopen_steps }

let compute_median values =
  let sorted = List.sort Float.compare values in
  List.nth sorted (List.length sorted / 2)

let list_counts work = (work.computed, work.collected)

let summarize ~modules outcomes =
  let first_run = List.hd outcomes in
  List.iteri
    (fun run outcome ->
      List.iter2
        (fun (name, work) (_, first_work) ->
          let show work = Printf.sprintf "computed %d, collected %d" work.computed work.collected in
          if list_counts work <> list_counts first_work then
            failwith
              (Printf.sprintf "%d modules, %s: run 1 counted %s, and run %d %s" modules name
                 (show first_work) (run + 1) (show work)))
        outcome.steps first_run.steps)
    outcomes;
  let compute_step_median field index =
    compute_median (List.map (fun outcome -> field (snd (List.nth outcome.steps index))) outcomes)
  in
  Printf.printf "\n### %d modules, %d functions\n\n" modules ((modules * (functions + 1)) + 3);
  Printf.printf "The first build computes %d parts and leaves %.0f MB of live heap.\n\n"
    (snd (List.hd first_run.steps)).computed
    (float_of_int first_run.heap_bytes /. 1e6);
  print_string
    "| Step | Update ms | Check ms | Key ms | Save ms | Computed | Collected | Written KB |\n\
     |---|---:|---:|---:|---:|---:|---:|---:|\n";
  List.iteri
    (fun index (name, work) ->
      Printf.printf "| %s | %.1f | %.1f | %s | %.1f | %d | %d | %d |\n" name
        (compute_step_median (fun work -> work.update_ms) index)
        (compute_step_median (fun work -> work.check_ms) index)
        (match work.key_ms with
        | Some _ ->
            Printf.sprintf "%.1f"
              (compute_step_median (fun work -> Option.value work.key_ms ~default:0.) index)
        | None -> "–")
        (compute_step_median (fun work -> work.save_ms) index)
        work.computed work.collected
        ((int_of_float (compute_step_median (fun work -> float_of_int work.written_bytes) index)
         + 512)
        / 1024))
    first_run.steps

let find_command_output program arguments =
  match Process.run program arguments with
  | 0, output, _ -> Some (String.trim output)
  | _ | (exception _) -> None

let read_processor_name () =
  match find_command_output "sysctl" [ "-n"; "machdep.cpu.brand_string" ] with
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

let find_busy_seconds () =
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

let read_own_seconds () =
  let times = Unix.times () in
  times.tms_utime +. times.tms_stime +. times.tms_cutime +. times.tms_cstime

let run_benchmark arguments =
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
  let started = Unix.gettimeofday () and busy_before = find_busy_seconds () in
  let own_before = read_own_seconds () in
  let standard = Filename.concat scratch "standard" in
  File_system.make_directory standard;
  Unix.putenv "TRUSS_CACHE" (Filename.concat scratch "standard-build");
  let (), standard_ms =
    measure_time (fun () -> Workspace.For_testing.copy_standard_package_database ~into:standard)
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
    match (busy_before, find_busy_seconds ()) with
    | Some before, Some after ->
        Printf.sprintf "Other processes used %.1f CPU-seconds during the run's %.0f seconds."
          (Float.max 0. (after -. before -. (read_own_seconds () -. own_before)))
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
     Checking the standard library into an empty cache took %.0f ms.\n"
    date
    (Option.value (find_command_output "uname" [ "-sm" ]) ~default:"an unknown system")
    (read_processor_name ())
    (Domain.recommended_domain_count ())
    interference runs standard_ms;
  List.iter (fun (modules, outcomes) -> summarize ~modules outcomes) summaries

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "--edit"; modules; standard; scratch ] ->
      File_system.make_directory scratch;
      let edited = build_and_edit ~scratch ~standard ~modules:(int_of_string modules) in
      print_string (Marshal.to_string (edited : outcome) [])
  | [ "--reopen"; scratch ] ->
      print_string (Marshal.to_string (open_again ~scratch : (string * work) list) [])
  | arguments -> run_benchmark arguments
