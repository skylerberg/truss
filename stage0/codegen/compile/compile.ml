module Lookups = Lookups

type unsupported = Lower.unsupported = { construct : string; at : Lowered.site option }

type lowered =
  | Compiled of Emit_c.fragment
  | Folded of Lowered.data * Emit_c.fragment
  | Evaluate of Path.t * Ground.ty

type requests = {
  settings : Lookups.settings;
  source : Path.file -> Source.t;
  interface : Interface.Lookups.t;
  mir : Mir.lookups;
  lowered : Instance.key -> (lowered, unsupported) result;
  test_key : Instance.key -> (string, unsupported) result;
  reached_todo_types : Instance.key -> Path.t list;
}

exception Todo_type = Monomorphic.Todo_type
exception Infinite_size = Memory_layout.Infinite_size

let bug format = Compiler_bug.bug ~stage:"Compile" format

let make (context : Lower.context) (key : Instance.key) : lowered =
  let env = Lower.env context in
  let emitted compiled = Compiled (Emit_c.fragment env compiled) in
  let drop_and_copy = Lower.drop_and_copy context in
  let code instance = emitted (Code instance) in
  match key with
  | Code { path; type_arguments } -> code (Lower.lower_source_code context ~path ~type_arguments)
  | Generated generated -> code (Lower.lower_generated context generated)
  | Table table -> emitted (Table (Lower.lower_table context table))
  | Constant path -> (
      match Lower.lower_constant context path with
      | Folded data -> Folded (data, Emit_c.fragment env (Data data))
      | Run ty -> Evaluate (path, ty))
  | Drop ty -> code (Drop_and_copy.drop drop_and_copy ty)
  | Copy ty -> code (Drop_and_copy.copy drop_and_copy ty)
  | Any_drop ty -> code (Drop_and_copy.any_drop drop_and_copy ty)
  | Any_copy ty -> code (Drop_and_copy.any_copy drop_and_copy ty)
  | Debug ty -> code (Debug_output.debug env ty)
  | Encode ty -> code (Encoding.encode env ty)
  | Evaluator path -> code (Lower.lower_evaluator context path)
  | Template_check { from_template; literals; clauses } ->
      code (Lower.lower_template_check context ~from_template ~literals ~clauses)
  | Call_evaluation { function_; arguments } ->
      code (Lower.lower_call_evaluation context ~function_ ~arguments)

let lower (settings : Lookups.settings) (lookups : Lookups.t) key =
  let env =
    Memory_layout.create settings.system
      ~shape_of:(Monomorphic.shape (Lower.monomorphic lookups.interface))
  in
  match
    Compiler_bug.while_doing ~stage:"Compile"
      ("lowering " ^ Instance.to_string key)
      (fun () -> make (Lower.context settings ~env lookups) key)
  with
  | lowered -> Ok lowered
  | exception Lower.Unsupported unsupported -> Error unsupported

let evaluated_own_hash =
  Blake3.derive_key ~context:"truss 2026-11-12 evaluated constant own hash" ""

let references = function
  | Compiled fragment | Folded (_, fragment) -> Emit_c.references fragment
  | Evaluate (path, _) -> [ Instance.Evaluator path ]

let own_hash = function
  | Compiled fragment | Folded (_, fragment) -> Reachable.own_hash fragment
  | Evaluate _ -> evaluated_own_hash

let call_node (interface : Interface.Lookups.t) (path : Path.t) =
  match path with
  | Method { owner; name; receiver }
    when not (List.exists (Path.equal path) (Mir.Call_edges.written_methods interface.names owner))
    -> (
      match Interface.Impls.impl_interface interface owner with
      | Some impl -> Path.Method { owner = impl.implements.trait; name; receiver }
      | None -> path)
  | _ -> path

let is_runtime_call (path : Path.t) =
  Well_known.is Write_fully path
  ||
  match path with
  | Method { owner = Top { module_; _ }; name = "new"; receiver = Static } ->
      Well_known.is_system_module module_
  | _ -> false

let bound_methods (interface : Interface.Lookups.t) path type_arguments =
  match Interface.Impls.signature interface path with
  | Some (signature : Types.signature) ->
      let rec pairs (generics : Types.generic list) (arguments : Ground.argument list) =
        match (generics, arguments) with
        | ( { kind = Type_generic bounds; _ } :: generics,
            Type (Named { path = head; _ }) :: arguments ) ->
            (bounds, head) :: pairs generics arguments
        | _ :: generics, _ :: arguments -> pairs generics arguments
        | _ -> []
      in
      List.concat_map
        (fun ((bounds : Types.trait_reference list), head) ->
          let traits =
            List.concat_map
              (fun (bound : Types.trait_reference) ->
                Mir.Call_edges.traits_with_required interface bound.trait)
              bounds
          in
          List.concat_map
            (fun package ->
              List.concat_map
                (Mir.Call_edges.impl_methods interface)
                (Mir.Call_edges.impls_for interface package traits
                   (Named { path = head; arguments = [] })))
            (List.sort_uniq Path.compare_package
               (Path.package head :: List.map Path.package traits)))
        (pairs signature.generics type_arguments)
  | None -> []

let check_calls (interface : Interface.Lookups.t) ~list_call_edges (key : Instance.key) lowered =
  match (key, lowered) with
  | Code { path = caller; type_arguments }, Compiled fragment -> (
      match caller with
      | Method { owner = Derived _; _ } -> ()
      | _ -> (
          match list_call_edges (call_node interface caller) with
          | None -> ()
          | Some call_edges ->
              let allowed =
                call_edges
                @ List.concat_map
                    (fun callee -> Option.value (list_call_edges callee) ~default:[])
                    call_edges
                @ bound_methods interface caller type_arguments
              in
              List.iter
                (fun (called : Instance.key) ->
                  match called with
                  | Code { path = callee; _ }
                    when not
                           (is_runtime_call callee
                           || List.exists (Path.equal callee) allowed
                           || List.exists (Path.equal (call_node interface callee)) allowed) ->
                      bug "%s calls %s, which is not among its call edges" (Instance.to_string key)
                        (Instance.to_string called)
                  | _ -> ())
                (Emit_c.called fragment)))
  | _ -> ()

let test_keys ~lowered ~known members =
  Reachable.component_keys
    ~link:(fun key ->
      let code = lowered key in
      (own_hash code, references code))
    ~deep:known members

type 'a ran = Ran of 'a | Ran_too_long | Stopped of string
type results = { find : string -> string option; add : string -> string -> unit }

type t = {
  requests : requests;
  monomorphic : Monomorphic.context;
  toolchain : Toolchain.t;
  cache : Build.cache;
  settings : Build.settings;
  file_name : Path.file -> string;
  worked_on : Path.package -> bool;
  results : results option;
  evaluation_time_limit_ms : int;
  programs : string;
  runs : (string, string ran) Hashtbl.t;
}

let env compiler =
  Memory_layout.create compiler.requests.settings.system
    ~shape_of:(Monomorphic.shape compiler.monomorphic)

let lowered compiler key =
  match compiler.requests.lowered key with
  | Ok lowered -> lowered
  | Error unsupported -> raise (Lower.Unsupported unsupported)

let reach compiler root =
  match compiler.requests.test_key root with
  | Ok reach_key -> reach_key
  | Error unsupported -> raise (Lower.Unsupported unsupported)

let programs_built = Atomic.make 0

let fresh_program compiler =
  Filename.concat compiler.programs
    (Printf.sprintf "program-%d-%d" (Unix.getpid ()) (Atomic.fetch_and_add programs_built 1))

exception Cannot_build of string

let cannot_build format = Printf.ksprintf (fun message -> raise (Cannot_build message)) format
let derive_result_key = Blake3.derive_key ~context:"truss 2026-11-13 result key"

let result_key compiler root =
  derive_result_key
    (Cbor.encode
       (Cbor.Array
          [
            Cbor.int Emit_c.version;
            Cbor.Text (Libc.system_name compiler.requests.settings.system);
            Bytes (reach compiler root);
            Cbor.Array (List.map (fun flag -> Cbor.Text flag) compiler.settings.extra);
          ]))

let test_key compiler test = result_key compiler (Lower.test_key test)

let position compiler (definition : Path.t) offset : Emit_c.position =
  let names = compiler.requests.interface.names in
  match Option.map names.place (names.key definition) with
  | Some { file; base } ->
      let line, column = Source.position (compiler.requests.source file) (base + offset) in
      { file = compiler.file_name file; line; column }
  | None -> bug "%s has no place in a file" (Path.show definition)

let site_position compiler (site : Lowered.site) = position compiler site.definition site.offset

let show_position (position : Emit_c.position) =
  Printf.sprintf "%s:%d:%d" position.file position.line position.column

let todo_type_position compiler (path : Path.t) =
  let names = compiler.requests.interface.names in
  match Option.map (fun key -> (names.definition key, names.spans key)) (names.key path) with
  | Some ({ kind = Type_definition { name; _ }; _ }, spans) ->
      position compiler path spans.(name.id).start
  | Some _ | None ->
      bug "%s is reached as a type defined as todo, and has no definition" (Path.show path)

let small_callees ~find ~worked_on fragment =
  match Emit_c.key fragment with
  | Code _ ->
      List.filter_map
        (fun (key : Instance.key) ->
          match (key, find key) with
          | Code { path = callee; _ }, Some copy
            when (not (worked_on (Path.package callee))) && Emit_c.is_small copy ->
              Some copy
          | _ -> None)
        (Emit_c.called fragment)
  | _ -> []

let test_runner : Instance.key = Code { path = Well_known.path Run_tests; type_arguments = [] }

let roots ~tests ~mains =
  (if tests = [] then [] else test_runner :: List.map Lower.test_key tests)
  @ List.map (fun main -> Instance.Generated (Program_main main)) mains

let rec build ?progress ?tests ?(supplied = []) compiler ~roots ~startup ~output =
  let lookup key =
    match List.find_opt (fun fragment -> Instance.equal (Emit_c.key fragment) key) supplied with
    | Some fragment -> fragment
    | None -> compiled compiler key
  in
  let units = Reachable.reachable ~lookup roots in
  let units_by_key =
    List.fold_left
      (fun units_by_key unit -> Reachable.Keys.add (Emit_c.key unit) unit units_by_key)
      Reachable.Keys.empty units
  in
  let sources =
    [ ("startup", startup); ("sites", Emit_c.sites_file ~position:(site_position compiler) units) ]
  in
  let find key = Reachable.Keys.find_opt key units_by_key in
  let copied =
    match compiler.settings.build with
    | Development -> small_callees ~find ~worked_on:compiler.worked_on
    | Release -> fun _ -> []
  in
  match
    Build.program ?progress ?tests ~copied compiler.toolchain compiler.cache (env compiler)
      compiler.settings
      ~files:(List.map (fun unit -> [ unit ]) units)
      ~sources ~output
  with
  | Ok () -> ()
  | Error message -> raise (Cannot_build message)

and build_test_program ?progress ?supplied compiler ~time_limit_ms ~roots ~output =
  build ?progress ?supplied compiler ~tests:true ~roots:(test_runner :: roots)
    ~startup:
      (Startup.tests_calling ~time_limit_ms ~runner:(Instance.symbol test_runner)
         (List.map Instance.symbol roots))
    ~output

and build_and_run :
    'result. t -> roots:Instance.key list -> startup:string -> (string -> 'result) -> 'result =
 fun compiler ~roots ~startup run ->
  let program = fresh_program compiler in
  build compiler ~roots ~startup ~output:program;
  let result = run program in
  (try Sys.remove program with Sys_error _ -> ());
  result

and run_while_compiling : 'value. t -> Instance.key -> read:(string -> 'value) -> 'value ran =
 fun compiler root ~read ->
  let key = result_key compiler root in
  let ran =
    match Hashtbl.find_opt compiler.runs key with
    | Some ran -> ran
    | None ->
        let ran =
          match Option.bind compiler.results (fun results -> results.find key) with
          | Some output -> Ran output
          | None -> (
              match
                build_and_run compiler ~roots:[ root ]
                  ~startup:(Startup.evaluator_calling (Instance.symbol root))
                  (fun program ->
                    Process.run_with_time_limit ~time_limit_ms:compiler.evaluation_time_limit_ms
                      program [])
              with
              | None -> Ran_too_long
              | Some (0, output, _) ->
                  Option.iter (fun results -> results.add key output) compiler.results;
                  Ran output
              | Some (status, _, errors) -> (
                  match String.trim errors with
                  | "" -> Stopped (Printf.sprintf "it ended with status %d" status)
                  | report -> Stopped report))
        in
        Hashtbl.replace compiler.runs key ran;
        ran
  in
  match ran with
  | Ran output -> Ran (read output)
  | Ran_too_long -> Ran_too_long
  | Stopped report -> Stopped report

and compiled compiler key =
  let data (data : Lowered.data) = Emit_c.fragment (env compiler) (Data data) in
  let compiled =
    match lowered compiler key with
    | Compiled fragment | Folded (_, fragment) -> fragment
    | Evaluate (path, ty) -> (
        match
          run_while_compiling compiler (Instance.Evaluator path) ~read:(fun encoded ->
              Encoding.decode (env compiler) ty encoded)
        with
        | Ran value -> data { data_key = Constant path; ty; value }
        | Ran_too_long ->
            cannot_build "Evaluating %s ran past the time limit of %d ms." (Path.show path)
              compiler.evaluation_time_limit_ms
        | Stopped report -> cannot_build "Evaluating %s stopped: %s" (Path.show path) report)
  in
  if not (Instance.equal (Emit_c.key compiled) key) then
    bug "%s compiled to %s" (Instance.to_string key) (Instance.to_string (Emit_c.key compiled));
  compiled

let unsupported_message compiler (unsupported : Lower.unsupported) =
  let where =
    match unsupported.at with
    | None -> ""
    | Some at -> show_position (site_position compiler at) ^ ": "
  in
  where ^ "Stage0 cannot build this yet: " ^ unsupported.construct ^ "."

let reporting compiler work =
  match work () with
  | result -> Ok result
  | exception Cannot_build message -> Error message
  | exception Lower.Unsupported unsupported -> Error (unsupported_message compiler unsupported)

type outcome = Passed | Failed | Panicked | Incomplete | Timed_out | Crashed

let outcomes =
  [
    ("passed", Passed);
    ("failed", Failed);
    ("panicked", Panicked);
    ("incomplete", Incomplete);
    ("timed_out", Timed_out);
    ("crashed", Crashed);
  ]

let show_outcome outcome = fst (List.find (fun (_, shown) -> shown = outcome) outcomes)

type record = {
  outcome : outcome;
  message : string option;
  echo : string option;
  microseconds : int;
  cached : bool;
}

type reader = {
  pending : Buffer.t;
  mutable message : string option;
  mutable echo : string option;
  on_start : int -> unit;
  on_record : int -> record -> unit;
}

let reader ?(on_start = ignore) on_record =
  { pending = Buffer.create 1024; message = None; echo = None; on_start; on_record }

let malformed text = cannot_build "A test report cannot be read: %s" text

let rec drain reader =
  let text = Buffer.contents reader.pending in
  match String.index_opt text '\n' with
  | None -> ()
  | Some stop -> (
      let line = String.sub text 0 stop in
      let consume count =
        Buffer.clear reader.pending;
        Buffer.add_string reader.pending (String.sub text count (String.length text - count))
      in
      match String.split_on_char ' ' line with
      | [ (("message" | "echo") as label); count ] ->
          let count =
            match int_of_string_opt count with
            | Some parsed_count -> parsed_count
            | None -> malformed line
          in
          if String.length text >= stop + 1 + count + 1 then begin
            let content = String.sub text (stop + 1) count in
            if label = "message" then reader.message <- Some content
            else reader.echo <- Some content;
            consume (stop + 1 + count + 1);
            drain reader
          end
      | [ "start"; number ] -> (
          match int_of_string_opt number with
          | Some number ->
              consume (stop + 1);
              reader.on_start number;
              drain reader
          | None -> malformed line)
      | [ "test"; number; outcome; microseconds ] -> (
          match
            ( int_of_string_opt number,
              List.assoc_opt outcome outcomes,
              int_of_string_opt microseconds )
          with
          | Some number, Some outcome, Some microseconds ->
              let record =
                {
                  outcome;
                  message = reader.message;
                  echo = reader.echo;
                  microseconds;
                  cached = false;
                }
              in
              reader.message <- None;
              reader.echo <- None;
              consume (stop + 1);
              reader.on_record number record;
              drain reader
          | _ -> malformed line)
      | _ -> malformed line)

let feed reader text =
  Buffer.add_string reader.pending text;
  drain reader

let parse_report text =
  let records = ref [] in
  let reader = reader (fun number record -> records := (number, record) :: !records) in
  match
    feed reader text;
    if Buffer.length reader.pending > 0 || reader.message <> None || reader.echo <> None then
      malformed "it ends partway through a record"
  with
  | () -> Ok (List.map snd (List.sort (fun (left, _) (right, _) -> compare left right) !records))
  | exception Cannot_build message -> Error message

let is_cacheable record = record.outcome = Passed && record.message = None && record.echo = None

let stored results key =
  Option.map
    (fun microseconds ->
      { outcome = Passed; message = None; echo = None; microseconds; cached = true })
    (Option.bind (results.find key) int_of_string_opt)

let store results key record = results.add key (string_of_int record.microseconds)

type progress =
  | Lowering
  | Compiling of { compiled : int; total : int }
  | Running of { tests : int }
  | Started of { test : int }
  | Ended of { test : int; record : record }

let external_test compiler test =
  match Interface.Definition.test_uses compiler.requests.interface test with
  | Some uses -> uses <> Types.no_capabilities
  | None -> false

let incomplete_record compiler todo_types =
  {
    outcome = Incomplete;
    message =
      Some
        (String.concat "\n"
           (List.map
              (fun path ->
                Printf.sprintf "the type %s is defined as todo\n  at %s" (Path.show path)
                  (show_position (todo_type_position compiler path)))
              todo_types));
    echo = None;
    microseconds = 0;
    cached = false;
  }

let run_tests ?(rerun = false) ?(progress = ignore) compiler ~time_limit_ms tests =
  reporting compiler @@ fun () ->
  let results = compiler.results in
  let roots = List.map Lower.test_key tests in
  progress Lowering;
  let keyed test = results <> None && not (external_test compiler test) in
  let known =
    List.mapi
      (fun index (test, root) ->
        match compiler.requests.reached_todo_types root with
        | _ :: _ as todo_types -> (index, root, None, Some (incomplete_record compiler todo_types))
        | [] ->
            let key = if keyed test then Some (test_key compiler test) else None in
            let known_record =
              match (results, key) with
              | Some results, Some key when not rerun -> stored results key
              | _ -> None
            in
            (index, root, key, known_record))
      (List.combine tests roots)
  in
  List.iter
    (fun (index, _, _, known_record) ->
      Option.iter (fun record -> progress (Ended { test = index; record })) known_record)
    known;
  let missing =
    Array.of_list (List.filter (fun (_, _, _, known_record) -> known_record = None) known)
  in
  let fresh = Array.make (Array.length missing) None in
  if Array.length missing > 0 then begin
    let roots = Array.to_list (Array.map (fun (_, root, _, _) -> root) missing) in
    let output = fresh_program compiler in
    build_test_program compiler ~time_limit_ms ~roots ~output ~progress:(fun compiled total ->
        progress (Compiling { compiled; total }));
    progress (Running { tests = Array.length missing });
    let index_of number =
      if number < 0 || number >= Array.length missing then
        malformed (Printf.sprintf "a test numbered %d" number);
      let index, _, _, _ = missing.(number) in
      index
    in
    let reader =
      reader
        ~on_start:(fun number -> progress (Started { test = index_of number }))
        (fun number record ->
          let index = index_of number in
          let _, _, key, _ = missing.(number) in
          fresh.(number) <- Some record;
          (match (results, key) with
          | Some results, Some key when is_cacheable record -> store results key record
          | _ -> ());
          progress (Ended { test = index; record }))
    in
    let _, report, errors =
      Fun.protect
        ~finally:(fun () -> try Sys.remove output with Sys_error _ -> ())
        (fun () -> Process.run ~on_output:(feed reader) output [])
    in
    if Array.exists Option.is_none fresh then
      cannot_build "The test program ended before reporting every test:\n%s%s" report errors
  end;
  let fresh = ref (List.filter_map Fun.id (Array.to_list fresh)) in
  List.map
    (fun (_, _, _, known_record) ->
      match known_record with
      | Some record -> record
      | None -> (
          match !fresh with
          | record :: rest ->
              fresh := rest;
              record
          | [] -> bug "fewer results than tests"))
    known

let build_supplied_tests compiler ~time_limit_ms supplied ~output =
  reporting compiler @@ fun () ->
  let supplied_env = env compiler in
  let supplied = List.map (fun instance -> instance supplied_env) supplied in
  build_test_program compiler
    ~supplied:(List.map (fun instance -> Emit_c.fragment supplied_env (Code instance)) supplied)
    ~time_limit_ms
    ~roots:(List.map Emit_c.Builder.instance_key supplied)
    ~output

type unshippable = {
  failure : [ `Todo | `Echo ];
  file : string;
  line : int;
  column : int;
  way : Path.t list;
}

let reached compiler ~main =
  match compiler.requests.reached_todo_types (Generated (Program_main main)) with
  | [] -> Reachable.running ~lookup:(compiled compiler) [ Instance.Generated (Program_main main) ]
  | _ :: _ -> []

let reached_definitions compiler ~main =
  reporting compiler @@ fun () ->
  List.sort_uniq Path.compare
    (List.filter_map
       (fun (_, way) ->
         match List.rev way with
         | (Instance.Code { path; _ } | Constant path | Generated (Program_main path)) :: _ ->
             Some path
         | _ -> None)
       (reached compiler ~main))

let unshippable compiler ~main =
  reporting compiler @@ fun () ->
  let reached = reached compiler ~main in
  begin
    let definitions keys =
      List.fold_left
        (fun acc (key : Instance.key) ->
          match key with
          | Code { path; _ } -> (
              match acc with last :: _ when Path.equal last path -> acc | _ -> path :: acc)
          | _ -> acc)
        [ main ] keys
      |> List.rev
    in
    let reports =
      List.map
        (fun path ->
          let ({ file; line; column } : Emit_c.position) = todo_type_position compiler path in
          { failure = `Todo; file; line; column; way = [ main; path ] })
        (compiler.requests.reached_todo_types (Generated (Program_main main)))
      @ List.concat_map
          (fun (compiled, keys) ->
            List.map
              (fun (failure, site) ->
                let ({ file; line; column } : Emit_c.position) = site_position compiler site in
                {
                  failure = (match failure with Emit_c.Echo -> `Echo | Todo -> `Todo);
                  file;
                  line;
                  column;
                  way = definitions keys;
                })
              (Emit_c.failures compiled))
          reached
    in
    List.sort_uniq
      (fun left right ->
        compare
          (left.file, left.line, left.column, left.failure)
          (right.file, right.line, right.column, right.failure))
      reports
    |> List.fold_left
         (fun acc report ->
           match acc with
           | last :: _
             when (last.file, last.line, last.column) = (report.file, report.line, report.column) ->
               acc
           | _ -> report :: acc)
         []
    |> List.rev
  end

let program_root compiler ~main =
  let root = Instance.Generated (Program_main main) in
  match compiler.requests.reached_todo_types root with
  | [] -> root
  | todo_types ->
      cannot_build "%s"
        (String.concat "\n"
           (List.map
              (fun path ->
                Printf.sprintf
                  "%s: the type %s is defined as todo, and `main` can reach it, so the program \
                   cannot be built."
                  (show_position (todo_type_position compiler path))
                  (Path.show path))
              todo_types))

let run_program ?input compiler ~main ~arguments =
  reporting compiler @@ fun () ->
  let root = program_root compiler ~main in
  build_and_run compiler ~roots:[ root ]
    ~startup:(Startup.program_calling (Instance.symbol root))
    (fun program -> Process.run ?input program arguments)

let build_program compiler ~main ~output =
  reporting compiler @@ fun () ->
  let root = program_root compiler ~main in
  build compiler ~roots:[ root ] ~startup:(Startup.program_calling (Instance.symbol root)) ~output

let reached_todo_types compiler (root : Path.t) =
  compiler.requests.reached_todo_types
    (match root with Test _ -> Lower.test_key root | _ -> Generated (Program_main root))

let run_template_check compiler ~from_template ~literals ~clauses =
  let ran =
    reporting compiler @@ fun () ->
    run_while_compiling compiler
      (Instance.Template_check { from_template; literals; clauses })
      ~read:(fun output ->
        let holds = Encoding.decode_booleans output in
        if List.length holds <> List.length clauses then
          bug "checking a template of %s wrote %d results for %d clauses" (Path.show from_template)
            (List.length holds) (List.length clauses);
        holds)
  in
  match ran with
  | Ok (Ran holds) -> Ok holds
  | Ok Ran_too_long ->
      Error (Printf.sprintf "it ran past the time limit of %d ms" compiler.evaluation_time_limit_ms)
  | Ok (Stopped report) | Error report -> Error report

let evaluate_call compiler ~function_ ~arguments =
  reporting compiler @@ fun () ->
  match Interface.Impls.signature compiler.requests.interface function_ with
  | Some { output = Returns result; _ } ->
      let ty = Monomorphic.ground compiler.monomorphic [] result in
      let key = Instance.Call_evaluation { function_; arguments } in
      run_while_compiling compiler key ~read:(fun encoded ->
          Encoding.decode (env compiler) ty encoded)
  | _ -> bug "%s has no result to evaluate" (Path.show function_)

let create ?(file_name = Path.show_file) ?results ?(evaluation_time_limit_ms = 10_000)
    ?(programs = Filename.get_temp_dir_name ())
    ?(worked_on = fun package -> package <> Path.standard_package) requests toolchain cache settings
    =
  {
    requests;
    monomorphic = Lower.monomorphic requests.interface;
    toolchain;
    cache;
    settings;
    file_name;
    worked_on;
    results;
    evaluation_time_limit_ms;
    programs;
    runs = Hashtbl.create 8;
  }

module For_testing = struct
  let is_folded compiler path =
    match lowered compiler (Instance.Constant path) with
    | Folded _ -> true
    | Evaluate _ -> false
    | Compiled _ -> bug "%s is not a constant" (Path.show path)

  module Intrinsics = Intrinsics

  let parse_report = parse_report
  let build_supplied_tests = build_supplied_tests
  let compiled = compiled
  let run_program = run_program
  let evaluate_call = evaluate_call
  let drop_and_copy = Drop_and_copy.create
  let is_trivial = Drop_and_copy.is_trivial
  let drop = Drop_and_copy.drop
  let copy = Drop_and_copy.copy
  let copy_signature = Drop_and_copy.For_testing.copy_signature
end
