type profile = Profile.t = Development | Release

let raise_bug format = Compiler_bug.raise_bug ~stage:"Backend" format

module Item_table = Hashtbl.Make (Lowered.Item)

type 'a ran = Ran of 'a | Reached_todo of string | Stopped of string
type results = { find : string -> string option; add : string -> string -> unit }

type t = {
  lookups : Lowering.lowered_lookups;
  monomorphic : Monomorphic.context;
  c_compiler : C_compiler.t;
  profile : profile;
  show_file : Path.file -> string;
  is_worked_on : Path.package -> bool;
  results : results option;
  evaluation_cpu_time_limit_ms : int;
  programs : string;
  runs : (string, string ran) Hashtbl.t;
  evaluating : Lowered.Item.t list ref;
}

let make_env backend =
  Memory_layout.create backend.lookups.system
    ~compute_shape:(Monomorphic.compute_shape backend.monomorphic)

exception Cannot_build of string
exception Constant_reaches_todo of { constant : Path.t; report : string }

let describe_stopped_evaluation constant report =
  Printf.sprintf "Evaluating %s stopped: %s" (Path.show constant) report

let raise_cannot_build format = Printf.ksprintf (fun message -> raise (Cannot_build message)) format

type location = { file : Path.file; line : int; column : int }

let locate_offset (lookups : Lowering.lowered_lookups) (definition : Path.t) offset =
  let names = lookups.interface.names in
  match Option.map names.read_place (names.find_key definition) with
  | Some { file; base } ->
      let line, column = Source.compute_position (lookups.read_source file) (base + offset) in
      { file; line; column }
  | None -> raise_bug "%s has no place in a file" (Path.show definition)

let locate_site lookups (site : Lowered.site) = locate_offset lookups site.definition site.offset

let locate_todo_type (lookups : Lowering.lowered_lookups) (path : Path.t) =
  let names = lookups.interface.names in
  match
    Option.map (fun key -> (names.read_definition key, names.read_spans key)) (names.find_key path)
  with
  | Some ({ kind = Type_definition { name; _ }; _ }, spans) ->
      locate_offset lookups path spans.(name.id).start
  | Some _ | None ->
      raise_bug "%s is reached as a type defined as todo, and has no definition" (Path.show path)

let make_position backend ({ file; line; column } : location) : Emit_c.position =
  { file = backend.show_file file; line; column }

let resolve_position backend site = make_position backend (locate_site backend.lookups site)

let render_code_unit backend env fragment ~copies =
  Emit_c.render_file env backend.profile ~resolve_position:(resolve_position backend)
    ((fragment, Emit_c.External) :: List.map (fun copy -> (copy, Emit_c.Internal)) copies)

let show_location backend ({ file; line; column } : location) =
  Printf.sprintf "%s:%d:%d" (backend.show_file file) line column

let raise_unsupported backend (unsupported : Lowering.unsupported) =
  let where =
    match unsupported.at with
    | None -> ""
    | Some at -> show_location backend (locate_site backend.lookups at) ^ ": "
  in
  raise_cannot_build "%sStage0 cannot build this yet: %s." where unsupported.construct

let read_lowered backend item =
  match backend.lookups.find_lowered item with
  | Some (Ok lowered) -> lowered
  | Some (Error unsupported) -> raise_unsupported backend unsupported
  | None -> raise_bug "%s is requested from code with errors" (Lowered.Item.to_string item)

let read_test_key backend root =
  match backend.lookups.read_test_key root with
  | Ok test_key -> test_key
  | Error unsupported -> raise_unsupported backend unsupported

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

let list_small_callees ~find ~is_worked_on fragment =
  match Emit_c.item fragment with
  | Code _ as caller ->
      List.filter_map
        (fun (item : Lowered.Item.t) ->
          match (item, find item) with
          | Code { path = callee; _ }, Some copy
            when (not (Lowered.Item.equal item caller))
                 && (not (is_worked_on (Path.locate_package callee)))
                 && Emit_c.is_small copy ->
              Some copy
          | _ -> None)
        (List.sort_uniq Lowered.Item.compare (Emit_c.called fragment))
  | _ -> []

let rec build ?report_progress ?(tests = false) ?(supplied = []) ?dsym_bundle backend ~roots
    ~startup ~output =
  let lookup item =
    match
      List.find_opt (fun fragment -> Lowered.Item.equal (Emit_c.item fragment) item) supplied
    with
    | Some fragment -> fragment
    | None -> compile_fragment backend item
  in
  let linked = Emit_c.list_linked ~lookup roots in
  let linked_by_item =
    Item_table.of_seq
      (List.to_seq (List.map (fun fragment -> (Emit_c.item fragment, fragment)) linked))
  in
  let list_copied =
    match backend.profile with
    | Development ->
        list_small_callees
          ~find:(Item_table.find_opt linked_by_item)
          ~is_worked_on:backend.is_worked_on
    | Release -> fun _ -> []
  in
  let env = make_env backend in
  let render_unit index fragment =
    ( Printf.sprintf "file %d" index,
      render_code_unit backend env fragment ~copies:(list_copied fragment) )
  in
  let units =
    (("the runtime", Startup.render_runtime ~tests) :: List.mapi render_unit linked)
    @ [
        ("startup", startup);
        ("sites", Emit_c.render_sites_file ~resolve_position:(resolve_position backend) linked);
        ("capabilities", Emit_c.render_capabilities_file linked);
      ]
  in
  match
    C_compiler.build_executable ?report_progress ?dsym_bundle backend.c_compiler backend.profile
      ~units ~output
  with
  | Ok () -> ()
  | Error message -> raise (Cannot_build message)

and build_test_program ?report_progress ?supplied backend ~time_limit_ms ~roots ~output =
  build ?report_progress ?supplied backend ~tests:true ~roots:(Lowering.test_runner :: roots)
    ~startup:
      (Startup.render_tests_start ~time_limit_ms
         ~runner:(Emit_c.make_symbol Lowering.test_runner)
         (List.map Emit_c.make_symbol roots))
    ~output

and build_and_run :
    'result. t -> roots:Lowered.Item.t list -> startup:string -> (string -> 'result) -> 'result =
 fun backend ~roots ~startup run ->
  let program = make_program_path backend in
  build backend ~roots ~startup ~output:program;
  let result = run program in
  (try Sys.remove program with Sys_error _ -> ());
  result

and run_while_compiling : 'value. t -> Lowered.Item.t -> read:(string -> 'value) -> 'value ran =
 fun backend root ~read ->
  let backend = { backend with profile = Development } in
  let key = make_result_key backend root in
  let ran =
    match Hashtbl.find_opt backend.runs key with
    | Some ran -> ran
    | None ->
        (if List.exists (Lowered.Item.equal root) !(backend.evaluating) then
           match root with
           | Evaluator path ->
               raise_cannot_build "the value of %s depends on itself" (Path.show path)
           | _ ->
               raise_bug "%s is evaluated by code that reads its result"
                 (Lowered.Item.to_string root));
        backend.evaluating := root :: !(backend.evaluating);
        Fun.protect ~finally:(fun () -> backend.evaluating := List.tl !(backend.evaluating))
        @@ fun () ->
        let ran =
          match Option.bind backend.results (fun results -> results.find key) with
          | Some output -> Ran output
          | None -> (
              let cpu_time_limit_ms = backend.evaluation_cpu_time_limit_ms in
              let time_limit_ms = wall_clock_factor * max 1 cpu_time_limit_ms in
              match
                build_and_run backend ~roots:[ root ]
                  ~startup:
                    (Startup.render_evaluator_start ~cpu_time_limit_ms (Emit_c.make_symbol root))
                  (fun program -> Process.run_with_time_limit ~time_limit_ms program [])
              with
              | exception Constant_reaches_todo { report; _ } -> Reached_todo report
              | None ->
                  Stopped
                    (Printf.sprintf
                       "it was still running after %d ms, and had used less than %d ms of CPU time"
                       time_limit_ms cpu_time_limit_ms)
              | Some (0, output, _) ->
                  Option.iter (fun results -> results.add key output) backend.results;
                  Ran output
              | Some (status, _, _) when status = Process.status_of_signal Sys.sigprof ->
                  Stopped (Printf.sprintf "it used more than %d ms of CPU time" cpu_time_limit_ms)
              | Some (status, _, errors) when status = Startup.todo_status ->
                  Reached_todo (String.trim errors)
              | Some (status, _, errors) -> (
                  match String.trim errors with
                  | "" -> Stopped (Printf.sprintf "it ended with status %d" status)
                  | report -> Stopped report))
        in
        Hashtbl.replace backend.runs key ran;
        ran
  in
  match ran with
  | Ran output -> Ran (read output)
  | Reached_todo report -> Reached_todo report
  | Stopped report -> Stopped report

and run_evaluator backend path ty =
  run_while_compiling backend (Lowered.Item.Evaluator path) ~read:(fun encoded ->
      Lowering.Encoding.decode (make_env backend) ty encoded)

and compile_fragment backend item =
  let compiled =
    match read_lowered backend item with
    | Compiled fragment | Folded (_, fragment) -> fragment
    | Evaluate (path, ty) -> (
        match run_evaluator backend path ty with
        | Ran value ->
            Emit_c.make_data_fragment (make_env backend) { data_item = Constant path; ty; value }
        | Reached_todo report -> raise (Constant_reaches_todo { constant = path; report })
        | Stopped report -> raise_cannot_build "%s" (describe_stopped_evaluation path report))
  in
  if not (Lowered.Item.equal (Emit_c.item compiled) item) then
    raise_bug "%s compiled to %s" (Lowered.Item.to_string item)
      (Lowered.Item.to_string (Emit_c.item compiled));
  compiled

let capture_failure work =
  match work () with
  | result -> Ok result
  | exception Cannot_build message -> Error message
  | exception Constant_reaches_todo { constant; report } ->
      Error (describe_stopped_evaluation constant report)
  | exception Test_report.Malformed message -> Error message

module Test_report = Test_report

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

let describe_todo_types backend todo_types =
  String.concat "\n"
    (List.map
       (fun path ->
         Printf.sprintf "the type %s is defined as todo\n  at %s" (Path.show path)
           (show_location backend (locate_todo_type backend.lookups path)))
       todo_types)

let rec read_executed_fragment (lookups : Lowering.lowered_lookups) item =
  match lookups.find_lowered item with
  | Some (Ok (Compiled fragment | Folded (_, fragment))) -> Some fragment
  | Some (Ok (Evaluate (path, _))) -> read_executed_fragment lookups (Lowered.Item.Evaluator path)
  | Some (Error _) | None -> None

let trace_item lookups item =
  Emit_c.trace_reachable ~lookup:(read_executed_fragment lookups) [ item ]

let reaches_evaluator backend root constant =
  List.exists
    (fun (fragment, _) -> Lowered.Item.equal (Emit_c.item fragment) (Evaluator constant))
    (trace_item backend.lookups root)

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
        match backend.lookups.list_reached_todo_types root with
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
  let output = make_program_path backend in
  let rec build_runnable = function
    | [] -> [||]
    | missing -> (
        match
          build_test_program backend ~time_limit_ms
            ~roots:(List.map (fun (_, root, _, _) -> root) missing)
            ~output
            ~report_progress:(fun compiled total -> report_progress (Compiling { compiled; total }))
        with
        | () -> Array.of_list missing
        | exception Constant_reaches_todo { constant; report } ->
            let unfinished, runnable =
              List.partition
                (fun (_, root, _, _) -> reaches_evaluator backend root constant)
                missing
            in
            if unfinished = [] then
              raise_cannot_build "%s" (describe_stopped_evaluation constant report);
            List.iter
              (fun (index, _, _, _) ->
                end_test index
                  (make_incomplete_record
                     (Printf.sprintf "the constant %s is not computed: %s" (Path.show constant)
                        report)))
              unfinished;
            build_runnable runnable)
  in
  let missing =
    build_runnable (List.filter (fun (_, _, _, known_record) -> known_record = None) known)
  in
  if Array.length missing > 0 then begin
    report_progress (Running { tests = Array.length missing });
    let read_test_index number =
      let index, _, _, _ = missing.(number) in
      index
    in
    let reader =
      Test_report.make_reader ~tests:(Array.length missing)
        ~on_start:(fun number -> report_progress (Started { test = read_test_index number }))
        (fun number record ->
          let _, _, key, _ = missing.(number) in
          (match (results, key) with
          | Some results, Some key when is_cacheable record -> store results key record
          | _ -> ());
          end_test (read_test_index number) record)
    in
    let status, _, errors =
      Fun.protect
        ~finally:(fun () -> try Sys.remove output with Sys_error _ -> ())
        (fun () -> Process.run ~input:"" ~on_output:(Test_report.feed reader) output [])
    in
    if Array.exists (fun (index, _, _, _) -> not (Hashtbl.mem fresh index)) missing then
      raise_cannot_build "The test program ended with status %d before reporting every test:\n%s"
        status errors
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

let build_supplied_tests backend ~time_limit_ms supplied ~output =
  capture_failure @@ fun () ->
  let supplied_env = make_env backend in
  let fragments = List.map (fun build -> build supplied_env) supplied in
  build_test_program backend ~supplied:fragments ~time_limit_ms
    ~roots:(List.map Emit_c.item fragments) ~output

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
          { failure = `Todo; location = locate_todo_type lookups path; way = [ main; path ] })
        (lookups.list_reached_todo_types (Lowering.make_root main))
      @ List.concat_map
          (fun (compiled, keys) ->
            List.map
              (fun (failure, site) ->
                {
                  failure = (match failure with Emit_c.Echo -> `Echo | Todo -> `Todo);
                  location = locate_site lookups site;
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
  match backend.lookups.list_reached_todo_types root with
  | [] -> root
  | todo_types ->
      raise_cannot_build "%s"
        (String.concat "\n"
           (List.map
              (fun path ->
                Printf.sprintf
                  "%s: the type %s is defined as todo, and `main` can reach it, so the program \
                   cannot be built."
                  (show_location backend (locate_todo_type backend.lookups path))
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

let list_reached_todo_types (lookups : Lowering.lowered_lookups) root =
  lookups.list_reached_todo_types (Lowering.make_root root)

let evaluate_call backend ~function_ ~arguments =
  capture_failure @@ fun () ->
  match Interface.Impls.read_signature backend.lookups.interface function_ with
  | Some { output = Returns result; _ } ->
      let ty = Monomorphic.ground backend.monomorphic Types.no_substitution result in
      let item = Lowered.Item.Call_evaluation { function_; arguments } in
      run_while_compiling backend item ~read:(fun encoded ->
          Lowering.Encoding.decode (make_env backend) ty encoded)
  | _ -> raise_bug "%s has no result to evaluate" (Path.show function_)

let evaluate_predicate backend ~function_ ~arguments =
  Result.map
    (function
      | Ran (Lowered.Static_scalar (Bool holds)) -> Ok holds
      | Ran _ -> raise_bug "%s returned a value that is not a Bool" (Path.show function_)
      | Reached_todo report | Stopped report -> Error report)
    (evaluate_call backend ~function_ ~arguments)

let evaluate_constant backend path =
  capture_failure @@ fun () ->
  match read_lowered backend (Constant path) with
  | Folded (data, _) -> Ran data.value
  | Evaluate (path, ty) -> run_evaluator backend path ty
  | Compiled _ -> raise_bug "the constant %s is lowered to code" (Path.show path)

let evaluate_assertion backend ~definition ~condition =
  capture_failure @@ fun () ->
  let item = Lowered.Item.Assertion { definition; condition } in
  match read_lowered backend item with
  | Folded (data, _) -> Ran data.value
  | Compiled _ ->
      run_while_compiling backend item ~read:(fun encoded ->
          Lowering.Encoding.decode (make_env backend)
            (Monomorphic.ground backend.monomorphic Types.no_substitution Types.bool)
            encoded)
  | Evaluate _ -> raise_bug "%s is lowered to a constant" (Lowered.Item.to_string item)

let create ?(show_file = Path.show_file) ?results ?(evaluation_cpu_time_limit_ms = 10_000)
    ?(programs = Filename.get_temp_dir_name ())
    ?(is_worked_on = fun package -> package <> Path.standard_package) lookups c_compiler profile =
  {
    lookups;
    monomorphic = Lowering.make_monomorphic_context lookups.interface;
    c_compiler;
    profile;
    show_file;
    is_worked_on;
    results;
    evaluation_cpu_time_limit_ms;
    programs;
    runs = Hashtbl.create 8;
    evaluating = ref [];
  }

module For_testing = struct
  let is_folded backend path =
    match read_lowered backend (Lowered.Item.Constant path) with
    | Folded _ -> true
    | Evaluate _ -> false
    | Compiled _ -> raise_bug "%s is not a constant" (Path.show path)

  let build_supplied_tests = build_supplied_tests
  let compile_fragment = compile_fragment

  let render_unit backend item =
    render_code_unit backend (make_env backend) (compile_fragment backend item) ~copies:[]

  let evaluate_call = evaluate_call
end
