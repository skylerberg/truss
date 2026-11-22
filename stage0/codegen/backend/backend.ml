type profile = Profile.t = Development | Release

let raise_bug format = Compiler_bug.raise_bug ~stage:"Backend" format

module Item_table = Hashtbl.Make (Lowered.Item)

type 'value ran = 'value Lowering.ran = Ran of 'value | Unfinished of string | Stopped of string
type results = { find : string -> string option; add : string -> string -> unit }

type t = {
  lookups : Lowering.lowered_lookups;
  positions : Lowering.Positions.t;
  c_compiler : C_compiler.t;
  profile : profile;
  show_file : Path.file -> string;
  results : results option;
  evaluation_cpu_time_limit_ms : int;
  programs : string;
  lowered : Lowering.lowered Item_table.t;
  attempted : unit Item_table.t;
}

let make_positions (lookups : Lowering.lowered_lookups) =
  Lowering.Positions.create lookups.interface.names ~read_source:lookups.read_source

let make_env backend = Lowering.make_env backend.lookups.system backend.lookups.interface

exception Cannot_build of string

let describe_stopped_evaluation evaluated report =
  Printf.sprintf "Evaluating %s stopped: %s" (Lowered.Item.to_string evaluated) report

let raise_cannot_build format = Printf.ksprintf (fun message -> raise (Cannot_build message)) format

type location = Lowering.Positions.location = { file : Path.file; line : int; column : int }

let locate_todo_type (lookups : Lowering.lowered_lookups) positions (path : Path.t) =
  let names = lookups.interface.names in
  match
    Option.map (fun key -> (names.read_definition key, names.read_spans key)) (names.find_key path)
  with
  | Some ({ kind = Type_definition { name; _ }; _ }, spans) ->
      Lowering.Positions.locate positions path spans.(name.id).start
  | Some _ | None ->
      raise_bug "%s is reached as a type defined as todo, and has no definition" (Path.show path)

let resolve_position backend site : Emit_c.position =
  let { file; line; column } = Lowering.Positions.locate_site backend.positions site in
  { file = backend.show_file file; line; column }

let show_location backend ({ file; line; column } : location) =
  Printf.sprintf "%s:%d:%d" (backend.show_file file) line column

let raise_unsupported backend (unsupported : Lowering.unsupported) =
  let where =
    match unsupported.at with
    | None -> ""
    | Some at -> show_location backend (Lowering.Positions.locate_site backend.positions at) ^ ": "
  in
  raise_cannot_build "%sStage0 cannot build this yet: %s." where unsupported.construct

let describe_todo_types backend todo_types =
  String.concat "\n"
    (List.map
       (fun path ->
         Printf.sprintf "the type %s is defined as todo\n  at %s" (Path.show path)
           (show_location backend (locate_todo_type backend.lookups backend.positions path)))
       todo_types)

let raise_unbuildable backend : Lowering.unbuildable -> 'never = function
  | Unsupported unsupported -> raise_unsupported backend unsupported
  | Todo_types todo_types -> raise_cannot_build "%s" (describe_todo_types backend todo_types)

let list_todo_types (lookups : Lowering.lowered_lookups) root =
  match lookups.read_test_key root with
  | Error (Todo_types todo_types) -> todo_types
  | Ok _ | Error (Unsupported _) -> []

let read_lowered backend item =
  match Item_table.find_opt backend.lowered item with
  | Some lowered -> lowered
  | None -> (
      match backend.lookups.find_lowered item with
      | Some (Ok lowered) ->
          Item_table.replace backend.lowered item lowered;
          lowered
      | Some (Error unbuildable) -> raise_unbuildable backend unbuildable
      | None -> raise_bug "%s is requested from code with errors" (Lowered.Item.to_string item))

let read_test_key backend root =
  match backend.lookups.read_test_key root with
  | Ok test_key -> test_key
  | Error unbuildable -> raise_unbuildable backend unbuildable

let programs_built = Atomic.make 0

let make_program_path backend =
  Filename.concat backend.programs
    (Printf.sprintf "program-%d-%d" (Unix.getpid ()) (Atomic.fetch_and_add programs_built 1))

let wall_clock_factor = 30
let show_profile = function Development -> "development" | Release -> "release"
let derive_result_key = Blake3.derive_key ~context:"truss 2026-11-18 result key"

let make_result_key backend root =
  derive_result_key
    (Cbor.encode
       (Cbor.Array
          [
            Cbor.int Emit_c.version;
            Cbor.Text (Libc.show_system backend.lookups.system);
            Cbor.Text (show_profile backend.profile);
            Bytes (C_compiler.make_fingerprint backend.c_compiler backend.profile);
            Bytes (read_test_key backend root);
          ]))

let list_needed_evaluators backend roots =
  List.filter_map
    (function
      | Lowering.Evaluated { evaluator; _ } -> Some evaluator
      | Unit _ -> None
      | Unbuildable unbuildable -> raise_unbuildable backend unbuildable)
    (backend.lookups.list_linked backend.profile roots)

let read_evaluated : Lowered.Item.t -> Lowered.Item.t = function
  | Evaluator evaluated -> evaluated
  | item -> raise_bug "%s is no evaluator" (Lowered.Item.to_string item)

let find_run backend evaluator =
  let evaluated = read_evaluated evaluator in
  match backend.lookups.find_evaluation evaluated with
  | Some (Ran _) as run -> run
  | Some (Unfinished _ | Stopped _) as run when Item_table.mem backend.attempted evaluated -> run
  | Some (Unfinished _ | Stopped _) | None -> None

let record_run backend evaluator run =
  let evaluated = read_evaluated evaluator in
  Item_table.replace backend.attempted evaluated ();
  backend.lookups.record_evaluation evaluated run

let compile_fragment backend item =
  let compiled =
    match read_lowered backend item with
    | Compiled fragment | Folded (_, fragment) -> fragment
    | Evaluate (evaluator, ty) -> (
        match find_run backend evaluator with
        | Some (Ran encoded) -> Lowering.make_data (make_env backend) item ty encoded
        | Some (Unfinished report | Stopped report) ->
            raise_cannot_build "%s" (describe_stopped_evaluation item report)
        | None -> raise_bug "%s is compiled before it is evaluated" (Lowered.Item.to_string item))
  in
  if not (Lowered.Item.equal (Emit_c.item compiled) item) then
    raise_bug "%s compiled to %s" (Lowered.Item.to_string item)
      (Lowered.Item.to_string (Emit_c.item compiled));
  compiled

module Test_report = Test_report

let run_test_program ?on_start program ~count on_record =
  let is_reported = Array.make count false in
  let reader =
    Test_report.make_reader ~tests:count ?on_start (fun number record ->
        is_reported.(number) <- true;
        on_record number record)
  in
  let status, _, errors =
    Fun.protect
      ~finally:(fun () -> try Sys.remove program with Sys_error _ -> ())
      (fun () -> Process.run ~input:"" ~on_output:(Test_report.feed reader) program [])
  in
  if Array.mem false is_reported then
    raise_cannot_build "The test program ended with status %d before reporting every test:\n%s"
      status errors

let make_run (record : Test_report.record) =
  let message = Option.value record.message ~default:"" in
  match record.outcome with
  | Passed -> Ran (Option.value record.output ~default:"")
  | Incomplete -> Unfinished message
  | Panicked -> Stopped ("panic: " ^ message)
  | Failed -> Stopped ("assertion failed: " ^ message)
  | Timed_out | Crashed -> Stopped message

let units_rendered = Atomic.make 0

let make_stored_source backend item ~text_hash : C_compiler.source =
  {
    name = Lowered.Item.to_string item;
    text_hash;
    render =
      (fun () ->
        Atomic.incr units_rendered;
        backend.lookups.render_unit backend.profile item);
  }

let rec build ?report_progress ?(tests = false) ?dsym_bundle backend ~roots ~startup ~output =
  let linked = list_linked backend roots in
  let sources =
    C_compiler.make_source ~name:"the runtime" (Startup.render_runtime ~tests)
    :: List.map fst linked
    @ [
        C_compiler.make_source ~name:"startup" startup;
        C_compiler.make_source ~name:"sites"
          (Emit_c.render_sites_file ~resolve_position:(resolve_position backend)
             (List.concat_map snd linked));
      ]
  in
  match
    C_compiler.build_executable ?report_progress ?dsym_bundle backend.c_compiler backend.profile
      ~sources ~output
  with
  | Ok () -> ()
  | Error message -> raise (Cannot_build message)

and list_linked backend roots =
  let linked = backend.lookups.list_linked backend.profile roots in
  match
    List.filter_map
      (function
        | Lowering.Evaluated { evaluator; _ } when Option.is_none (find_run backend evaluator) ->
            Some evaluator
        | Evaluated _ | Unit _ | Unbuildable _ -> None)
      linked
  with
  | _ :: _ as evaluators ->
      run_evaluators backend evaluators;
      list_linked backend roots
  | [] ->
      List.map
        (function
          | Lowering.Unit { item; text_hash; sites } ->
              (make_stored_source backend item ~text_hash, sites)
          | Evaluated { item; evaluator } -> (
              match find_run backend evaluator with
              | Some (Unfinished report | Stopped report) ->
                  raise_cannot_build "%s" (describe_stopped_evaluation item report)
              | Some (Ran _) | None ->
                  raise_bug "%s is evaluated, and has no unit" (Lowered.Item.to_string item))
          | Unbuildable unbuildable -> raise_unbuildable backend unbuildable)
        linked

and build_test_program ?report_progress ?(cpu_time_limit_ms = 0) backend ~time_limit_ms ~roots
    ~output =
  build ?report_progress backend ~tests:true ~roots:(Lowering.test_runner :: roots)
    ~startup:
      (Startup.render_tests_start ~time_limit_ms ~cpu_time_limit_ms
         ~runner:(Emit_c.make_symbol Lowering.test_runner)
         (List.map Emit_c.make_symbol roots))
    ~output

and run_evaluators backend evaluators =
  let backend = { backend with profile = Development } in
  let has_run evaluator = Option.is_some (find_run backend evaluator) in
  let dependencies = Item_table.create 16 in
  let find_stored_run evaluator =
    Option.map
      (fun output -> Ran output)
      (Option.bind backend.results (fun results -> results.find (make_result_key backend evaluator)))
  in
  let rec note_dependencies dependents evaluator =
    if List.exists (Lowered.Item.equal evaluator) dependents then
      match evaluator with
      | Evaluator (Constant path) ->
          record_run backend evaluator
            (Unfinished (Printf.sprintf "the value of %s depends on itself" (Path.show path)))
      | _ ->
          raise_bug "%s is evaluated by code that reads its result"
            (Lowered.Item.to_string evaluator)
    else if not (has_run evaluator || Item_table.mem dependencies evaluator) then
      match find_stored_run evaluator with
      | Some run -> record_run backend evaluator run
      | None -> (
          match list_needed_evaluators backend [ evaluator; Lowering.test_runner ] with
          | needed ->
              Item_table.replace dependencies evaluator needed;
              List.iter (note_dependencies (evaluator :: dependents)) needed
          | exception Cannot_build message -> record_run backend evaluator (Stopped message))
  in
  List.iter (note_dependencies []) evaluators;
  let find_run_without_a_program evaluator =
    List.find_map
      (fun needed ->
        match find_run backend needed with
        | Some (Ran _) -> None
        | Some (Unfinished report) -> Some (Unfinished report)
        | Some (Stopped report) ->
            Some (Stopped (describe_stopped_evaluation (read_evaluated needed) report))
        | None -> raise_bug "%s is needed before it is evaluated" (Lowered.Item.to_string needed))
      (Item_table.find dependencies evaluator)
  in
  let run_in_one_program ready =
    let runnable =
      Array.of_list
        (List.filter
           (fun evaluator ->
             match find_run_without_a_program evaluator with
             | Some run ->
                 record_run backend evaluator run;
                 false
             | None -> true)
           ready)
    in
    if Array.length runnable > 0 then begin
      let cpu_time_limit_ms = max 1 backend.evaluation_cpu_time_limit_ms in
      let program = make_program_path backend in
      build_test_program backend ~cpu_time_limit_ms
        ~time_limit_ms:(wall_clock_factor * cpu_time_limit_ms)
        ~roots:(Array.to_list runnable) ~output:program;
      run_test_program program ~count:(Array.length runnable) (fun number record ->
          let evaluator = runnable.(number) and run = make_run record in
          (match (run, backend.results) with
          | Ran output, Some results -> results.add (make_result_key backend evaluator) output
          | _ -> ());
          record_run backend evaluator run)
    end
  in
  let rec run_ready () =
    let pending =
      Item_table.fold
        (fun evaluator needed pending ->
          if has_run evaluator then pending else (evaluator, needed) :: pending)
        dependencies []
    in
    match
      List.filter_map
        (fun (evaluator, needed) -> if List.for_all has_run needed then Some evaluator else None)
        pending
    with
    | [] -> if pending <> [] then raise_bug "evaluations wait for each other's results"
    | ready ->
        run_in_one_program (List.sort Lowered.Item.compare ready);
        run_ready ()
  in
  run_ready ()

let capture_failure work =
  match work () with
  | result -> Ok result
  | exception Cannot_build message -> Error message
  | exception Test_report.Malformed message -> Error message

let is_cacheable (record : Test_report.record) =
  record.outcome = Passed && record.message = None && record.echo = None && record.output = None

let find_stored results key =
  Option.map
    (fun microseconds ->
      {
        Test_report.outcome = Passed;
        message = None;
        echo = None;
        output = None;
        microseconds;
        cached = true;
      })
    (Option.bind (Option.bind (results.find key) Cbor.decode) Cbor.find_int)

let store results key (record : Test_report.record) =
  results.add key (Cbor.encode (Cbor.int record.microseconds))

type progress =
  | Lowering
  | Compiling of { compiled : int; total : int }
  | Running of { tests : int }
  | Started of { test : int }
  | Ended of { test : int; record : Test_report.record }

let make_incomplete_record message =
  {
    Test_report.outcome = Incomplete;
    message = Some message;
    echo = None;
    output = None;
    microseconds = 0;
    cached = false;
  }

let rec read_executed_fragment (lookups : Lowering.lowered_lookups) item =
  match lookups.find_lowered item with
  | Some (Ok (Compiled fragment | Folded (_, fragment))) -> Some fragment
  | Some (Ok (Evaluate (evaluator, _))) -> read_executed_fragment lookups evaluator
  | Some (Error _) | None -> None

let trace_item lookups item =
  Emit_c.trace_reachable ~lookup:(read_executed_fragment lookups) [ item ]

let find_unfinished backend evaluators =
  List.find_map
    (fun evaluator ->
      match find_run backend evaluator with
      | Some (Unfinished report) -> Some (read_evaluated evaluator, report)
      | Some (Ran _ | Stopped _) | None -> None)
    evaluators

let run_tests ?(rerun = false) ?(report_progress = ignore) backend ~time_limit_ms tests =
  capture_failure @@ fun () ->
  let results = backend.results in
  let roots = List.map Lowering.make_root tests in
  report_progress Lowering;
  let is_keyed test =
    results <> None && not (Interface.Definition.is_external_test backend.lookups.interface test)
  in
  let known =
    List.mapi
      (fun index (test, root) ->
        match list_todo_types backend.lookups root with
        | _ :: _ as todo_types ->
            ( index,
              root,
              None,
              Some (make_incomplete_record (describe_todo_types backend todo_types)) )
        | [] ->
            let key = if is_keyed test then Some (make_result_key backend root) else None in
            let known_record =
              match (results, key) with
              | Some results, Some key when not rerun -> find_stored results key
              | _ -> None
            in
            (index, root, key, known_record))
      (List.combine tests roots)
  in
  List.iter
    (fun (index, _, _, known_record) ->
      Option.iter (fun record -> report_progress (Ended { test = index; record })) known_record)
    known;
  let fresh = Hashtbl.create 16 in
  let end_test index record =
    Hashtbl.replace fresh index record;
    report_progress (Ended { test = index; record })
  in
  let missing = List.filter (fun (_, _, _, known_record) -> known_record = None) known in
  let needed = list_needed_evaluators backend (List.map (fun (_, root, _, _) -> root) missing) in
  run_evaluators backend needed;
  let runnable =
    Array.of_list
      (if Option.is_some (find_unfinished backend needed) then
         List.filter
           (fun (index, root, _, _) ->
             match find_unfinished backend (list_needed_evaluators backend [ root ]) with
             | Some (evaluated, report) ->
                 end_test index
                   (make_incomplete_record
                      (Printf.sprintf "the constant %s is not computed: %s"
                         (Lowered.Item.to_string evaluated)
                         report));
                 false
             | None -> true)
           missing
       else missing)
  in
  if Array.length runnable > 0 then begin
    let program = make_program_path backend in
    build_test_program backend ~time_limit_ms
      ~roots:(Array.to_list (Array.map (fun (_, root, _, _) -> root) runnable))
      ~output:program
      ~report_progress:(fun compiled total -> report_progress (Compiling { compiled; total }));
    report_progress (Running { tests = Array.length runnable });
    let read_test_index number =
      let index, _, _, _ = runnable.(number) in
      index
    in
    run_test_program program ~count:(Array.length runnable)
      ~on_start:(fun number -> report_progress (Started { test = read_test_index number }))
      (fun number record ->
        let _, _, key, _ = runnable.(number) in
        (match (results, key) with
        | Some results, Some key when is_cacheable record -> store results key record
        | _ -> ());
        end_test (read_test_index number) record)
  end;
  List.map
    (fun (index, _, _, known_record) ->
      match known_record with
      | Some record -> record
      | None -> (
          match Hashtbl.find_opt fresh index with
          | Some record -> record
          | None -> raise_bug "the test %d has no result" index))
    known

type unshippable = { failure : [ `Todo | `Echo ]; location : location; way : Path.t list }

let trace_root lookups root = trace_item lookups (Lowering.make_root root)

let list_reached_definitions lookups root =
  List.sort_uniq Path.compare
    (List.filter_map
       (fun (_, way) ->
         match List.rev way with
         | ( Lowered.Item.Code { path; _ }
           | Constant path
           | Generated (Program_main path | Test_main path) )
           :: _ ->
             Some path
         | _ -> None)
       (trace_root lookups root))

let list_unshippable (lookups : Lowering.lowered_lookups) ~main =
  let reached = trace_root lookups main in
  let positions = make_positions lookups in
  begin
    let list_definitions keys =
      List.fold_left
        (fun acc (item : Lowered.Item.t) ->
          match item with
          | Code { path; _ } | Constant path -> (
              match acc with last :: _ when Path.equal last path -> acc | _ -> path :: acc)
          | _ -> acc)
        [ main ] keys
      |> List.rev
    in
    let reports =
      List.map
        (fun path ->
          {
            failure = `Todo;
            location = locate_todo_type lookups positions path;
            way = [ main; path ];
          })
        (list_todo_types lookups (Lowering.make_root main))
      @ List.concat_map
          (fun (compiled, keys) ->
            List.map
              (fun (failure, site) ->
                {
                  failure = (match failure with Emit_c.Echo -> `Echo | Todo -> `Todo);
                  location = Lowering.Positions.locate_site positions site;
                  way = list_definitions keys;
                })
              (Emit_c.failures compiled))
          reached
    in
    List.sort_uniq
      (fun left right -> compare (left.location, left.failure) (right.location, right.failure))
      reports
    |> List.fold_left
         (fun acc report ->
           match acc with
           | last :: _ when last.location = report.location -> acc
           | _ -> report :: acc)
         []
    |> List.rev
  end

let make_program_root backend ~main =
  let root = Lowering.make_root main in
  match list_todo_types backend.lookups root with
  | [] -> root
  | todo_types ->
      raise_cannot_build "%s"
        (String.concat "\n"
           (List.map
              (fun path ->
                Printf.sprintf
                  "%s: the type %s is defined as todo, and `main` can reach it, so the program \
                   cannot be built."
                  (show_location backend (locate_todo_type backend.lookups backend.positions path))
                  (Path.show path))
              todo_types))

let build_program backend ~main ~output ~is_kept =
  capture_failure @@ fun () ->
  let root = make_program_root backend ~main in
  let dsym_bundle =
    match (backend.profile, backend.lookups.system.os) with
    | Release, Macos when is_kept -> Some (output ^ ".dSYM")
    | _ -> None
  in
  build ?dsym_bundle backend ~roots:[ root ]
    ~startup:(Startup.render_program_start (Emit_c.make_symbol root))
    ~output

let list_reached_todo_types lookups root = list_todo_types lookups (Lowering.make_root root)

let evaluate backend evaluated =
  let lowered =
    List.map (fun item -> capture_failure (fun () -> read_lowered backend item)) evaluated
  in
  let ran =
    capture_failure (fun () ->
        run_evaluators backend
          (List.filter_map
             (function Ok (Lowering.Evaluate (evaluator, _)) -> Some evaluator | _ -> None)
             lowered))
  in
  let stop item message =
    backend.lookups.record_evaluation item (Stopped message);
    Stopped message
  in
  List.map2
    (fun item (lowered : (Lowering.lowered, string) result) ->
      match (lowered, ran) with
      | Error message, _ | Ok (Evaluate _), Error message -> stop item message
      | Ok (Folded (data, _)), _ -> Ran data.value
      | Ok (Evaluate (evaluator, ty)), Ok () -> (
          match find_run backend evaluator with
          | Some (Ran encoded) -> Ran (Lowering.Encoding.decode (make_env backend) ty encoded)
          | Some (Unfinished report) -> Unfinished report
          | Some (Stopped report) -> Stopped report
          | None -> raise_bug "%s is not evaluated" (Lowered.Item.to_string item))
      | Ok (Compiled _), _ -> raise_bug "%s is lowered to code" (Lowered.Item.to_string item))
    evaluated lowered

let create ?(show_file = Path.show_file) ?results ?(evaluation_cpu_time_limit_ms = 10_000)
    ?(programs = Filename.get_temp_dir_name ()) lookups c_compiler profile =
  {
    lookups;
    positions = make_positions lookups;
    c_compiler;
    profile;
    show_file;
    results;
    evaluation_cpu_time_limit_ms;
    programs;
    lowered = Item_table.create 64;
    attempted = Item_table.create 8;
  }

module For_testing = struct
  let is_folded backend path =
    match read_lowered backend (Lowered.Item.Constant path) with
    | Folded _ -> true
    | Evaluate _ -> false
    | Compiled _ -> raise_bug "%s is not a constant" (Path.show path)

  let build_test_program backend ~time_limit_ms roots ~output =
    capture_failure (fun () -> build_test_program backend ~time_limit_ms ~roots ~output)

  let compile_fragment backend item =
    run_evaluators backend (list_needed_evaluators backend [ item ]);
    compile_fragment backend item

  let render_unit backend item =
    Emit_c.render_file (make_env backend) backend.profile
      ~resolve_position:(resolve_position backend)
      [ (compile_fragment backend item, External) ]

  let count_built_programs () = Atomic.get programs_built
  let count_rendered_units () = Atomic.get units_rendered
end
