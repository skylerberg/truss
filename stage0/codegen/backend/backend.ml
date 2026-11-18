module Lookups = Lookups

type unsupported = Lower.unsupported = { construct : string; at : Lowered.site option }

type lowered =
  | Compiled of Emit_c.fragment
  | Folded of Lowered.data * Emit_c.fragment
  | Evaluate of Path.t * Ground.ty

type requests = {
  settings : Lookups.settings;
  read_source : Path.file -> Source.t;
  interface : Interface.Lookups.t;
  mir : Mir.lookups;
  find_lowered : Instance.key -> (lowered, unsupported) result option;
  read_test_key : Instance.key -> (string, unsupported) result;
  list_reached_todo_types : Instance.key -> Path.t list;
}

type profile = Emit_c.profile = Development | Release

exception Todo_type = Monomorphic.Todo_type
exception Infinite_size = Memory_layout.Infinite_size

let raise_bug format = Compiler_bug.raise_bug ~stage:"Backend" format

let make (context : Lower.context) (key : Instance.key) : lowered =
  let env = Lower.env context in
  let emit compiled = Compiled (Emit_c.make_fragment env compiled) in
  let drop_and_copy = Lower.drop_and_copy context in
  let emit_code instance = emit (Code instance) in
  match key with
  | Code { path; instantiation } -> emit_code (Lower.lower_source_code context ~path ~instantiation)
  | Generated generated -> emit_code (Lower.lower_generated context generated)
  | Table table -> emit (Table (Lower.lower_table context table))
  | Constant path -> (
      match Lower.lower_constant context path with
      | Folded data -> Folded (data, Emit_c.make_fragment env (Data data))
      | Run ty -> Evaluate (path, ty))
  | Drop ty -> emit_code (Drop_and_copy.drop drop_and_copy ty)
  | Copy ty -> emit_code (Drop_and_copy.copy drop_and_copy ty)
  | Any_drop ty -> emit_code (Drop_and_copy.build_any_drop drop_and_copy ty)
  | Any_copy ty -> emit_code (Drop_and_copy.build_any_copy drop_and_copy ty)
  | Debug ty -> emit_code (Debug_output.build_debug env ty)
  | Encode ty -> emit_code (Encoding.encode env ty)
  | Evaluator path -> emit_code (Lower.lower_evaluator context path)
  | Template_check { from_template; literals; clauses } ->
      emit_code (Lower.lower_template_check context ~from_template ~literals ~clauses)
  | Call_evaluation { function_; arguments } ->
      emit_code (Lower.lower_call_evaluation context ~function_ ~arguments)

let lower (settings : Lookups.settings) (lookups : Lookups.t) key =
  let env =
    Memory_layout.create settings.system
      ~compute_shape:(Monomorphic.compute_shape (Lower.make_monomorphic_context lookups.interface))
  in
  match
    Compiler_bug.run_while_doing ~stage:"Backend"
      ("lowering " ^ Instance.to_string key)
      (fun () -> make (Lower.make_context settings ~env lookups) key)
  with
  | lowered -> Ok lowered
  | exception Lower.Unsupported unsupported -> Error unsupported

let list_references = function
  | Compiled fragment | Folded (_, fragment) -> Emit_c.references fragment
  | Evaluate (path, _) -> [ Instance.Evaluator path ]

let resolve_call_node (interface : Interface.Lookups.t) (path : Path.t) =
  match path with
  | Method { owner; name; receiver } when not (Mir.Call_edges.defines interface.names owner path)
    -> (
      match Interface.Definition.find_impl_interface interface owner with
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

let list_bound_methods (interface : Interface.Lookups.t) path type_arguments =
  match Interface.Impls.read_signature interface path with
  | Some (signature : Types.signature) ->
      let rec pair_generics (generics : Types.generic list) (arguments : Ground.argument list) =
        match (generics, arguments) with
        | ( { kind = Type_generic bounds; _ } :: generics,
            Type (Named { path = head; _ }) :: arguments ) ->
            (bounds, head) :: pair_generics generics arguments
        | _ :: generics, _ :: arguments -> pair_generics generics arguments
        | _ -> []
      in
      List.concat_map
        (fun ((bounds : Types.trait_reference list), head) ->
          let traits =
            List.concat_map
              (fun (bound : Types.trait_reference) ->
                Mir.Call_edges.list_traits_with_required interface bound.trait)
              bounds
          in
          List.concat_map
            (fun package ->
              List.concat_map
                (Mir.Call_edges.list_impl_methods interface)
                (Mir.Call_edges.list_impls_for interface package traits
                   (Named { path = head; arguments = [] })))
            (List.sort_uniq Path.compare_package
               (Path.locate_package head :: List.map Path.locate_package traits)))
        (pair_generics signature.generics type_arguments)
  | None -> []

let check_calls (interface : Interface.Lookups.t) ~find_call_edges (key : Instance.key) lowered =
  match (key, lowered) with
  | Code { path = caller; instantiation }, Compiled fragment -> (
      match find_call_edges (resolve_call_node interface caller) with
      | None -> ()
      | Some call_edges ->
          let allowed =
            call_edges
            @ List.concat_map
                (fun callee -> Option.value (find_call_edges callee) ~default:[])
                call_edges
            @ list_bound_methods interface caller instantiation.type_arguments
          in
          List.iter
            (fun (called : Instance.key) ->
              match called with
              | Code { path = callee; _ }
                when not
                       (is_runtime_call callee
                       || List.exists (Path.equal callee) allowed
                       || List.exists (Path.equal (resolve_call_node interface callee)) allowed) ->
                  raise_bug "%s calls %s, which is not among its call edges"
                    (Instance.to_string key) (Instance.to_string called)
              | _ -> ())
            (Emit_c.called fragment))
  | _ -> ()

module Instance_table = Hashtbl.Make (Instance)

let derive_fragment_hash = Blake3.derive_key ~context:"truss 2026-11-16 instance fragment hash"

let evaluated_fragment_hash =
  Blake3.derive_key ~context:"truss 2026-11-16 evaluated constant fragment hash" ""

let hash_fragment = function
  | Compiled fragment | Folded (_, fragment) ->
      derive_fragment_hash (Emit_c.render_fragment fragment)
  | Evaluate _ -> evaluated_fragment_hash

let derive_test_key = Blake3.derive_key ~context:"truss 2026-11-12 reach key"
let encode_test_key fields = derive_test_key (Cbor.encode (Cbor.Array fields))

let derive_cycle_member_key ~read_known_key members start =
  let visit_order = Instance_table.create 8 in
  let rec visit visited = function
    | [] -> List.rev visited
    | key :: queue ->
        if Instance_table.mem visit_order key then visit visited queue
        else begin
          Instance_table.replace visit_order key (Instance_table.length visit_order);
          let fragment_hash, references = Instance_table.find members key in
          visit
            ((fragment_hash, references) :: visited)
            (queue @ List.filter (Instance_table.mem members) references)
        end
  in
  encode_test_key
    [
      Text "group";
      Cbor.Array
        (List.map
           (fun (fragment_hash, references) ->
             Cbor.Array
               [
                 Bytes fragment_hash;
                 Cbor.Array
                   (List.map
                      (fun reference ->
                        if Instance_table.mem members reference then
                          Cbor.Array
                            [ Text "in"; Cbor.int (Instance_table.find visit_order reference) ]
                        else Cbor.Array [ Text "out"; Bytes (read_known_key reference) ])
                      references);
               ])
           (visit [] [ start ]));
    ]

let derive_test_keys ~read_lowered ~read_known_key component =
  match component with
  | [ key ] ->
      let code = read_lowered key in
      [
        ( key,
          encode_test_key
            [
              Text "unit";
              Bytes (hash_fragment code);
              Cbor.Array
                (List.map
                   (fun reference -> Cbor.Bytes (read_known_key reference))
                   (list_references code));
            ] );
      ]
  | component ->
      let members = Instance_table.create 8 in
      List.iter
        (fun member ->
          let code = read_lowered member in
          Instance_table.replace members member (hash_fragment code, list_references code))
        component;
      List.map
        (fun member -> (member, derive_cycle_member_key ~read_known_key members member))
        component

type 'a ran = Ran of 'a | Ran_too_long | Stopped of string
type results = { find : string -> string option; add : string -> string -> unit }

type t = {
  requests : requests;
  monomorphic : Monomorphic.context;
  c_compiler : C_compiler.t;
  profile : profile;
  show_file : Path.file -> string;
  is_worked_on : Path.package -> bool;
  results : results option;
  evaluation_time_limit_ms : int;
  programs : string;
  runs : (string, string ran) Hashtbl.t;
}

let make_env backend =
  Memory_layout.create backend.requests.settings.system
    ~compute_shape:(Monomorphic.compute_shape backend.monomorphic)

let read_lowered backend key =
  match backend.requests.find_lowered key with
  | Some (Ok lowered) -> lowered
  | Some (Error unsupported) -> raise (Lower.Unsupported unsupported)
  | None -> raise_bug "%s is requested from code with errors" (Instance.to_string key)

let read_test_key backend root =
  match backend.requests.read_test_key root with
  | Ok test_key -> test_key
  | Error unsupported -> raise (Lower.Unsupported unsupported)

let programs_built = Atomic.make 0

let make_program_path backend =
  Filename.concat backend.programs
    (Printf.sprintf "program-%d-%d" (Unix.getpid ()) (Atomic.fetch_and_add programs_built 1))

exception Cannot_build of string

let raise_cannot_build format = Printf.ksprintf (fun message -> raise (Cannot_build message)) format

let select_optimization : profile -> C_compiler.optimization = function
  | Development -> O1
  | Release -> O2_lto

let show_profile = function Development -> "development" | Release -> "release"
let derive_result_key = Blake3.derive_key ~context:"truss 2026-11-17 result key"

let make_result_key backend root =
  derive_result_key
    (Cbor.encode
       (Cbor.Array
          [
            Cbor.int Emit_c.version;
            Cbor.Text (Libc.show_system backend.requests.settings.system);
            Cbor.Text (show_profile backend.profile);
            Bytes
              (C_compiler.make_fingerprint backend.c_compiler (select_optimization backend.profile));
            Bytes (read_test_key backend root);
          ]))

type location = { file : Path.file; line : int; column : int }

let locate_offset (requests : requests) (definition : Path.t) offset =
  let names = requests.interface.names in
  match Option.map names.read_place (names.find_key definition) with
  | Some { file; base } ->
      let line, column = Source.compute_position (requests.read_source file) (base + offset) in
      { file; line; column }
  | None -> raise_bug "%s has no place in a file" (Path.show definition)

let locate_site requests (site : Lowered.site) = locate_offset requests site.definition site.offset

let locate_todo_type (requests : requests) (path : Path.t) =
  let names = requests.interface.names in
  match
    Option.map (fun key -> (names.read_definition key, names.read_spans key)) (names.find_key path)
  with
  | Some ({ kind = Type_definition { name; _ }; _ }, spans) ->
      locate_offset requests path spans.(name.id).start
  | Some _ | None ->
      raise_bug "%s is reached as a type defined as todo, and has no definition" (Path.show path)

let make_position backend ({ file; line; column } : location) : Emit_c.position =
  { file = backend.show_file file; line; column }

let show_location backend ({ file; line; column } : location) =
  Printf.sprintf "%s:%d:%d" (backend.show_file file) line column

let list_small_callees ~find ~is_worked_on fragment =
  match Emit_c.key fragment with
  | Code _ as caller ->
      List.filter_map
        (fun (key : Instance.key) ->
          match (key, find key) with
          | Code { path = callee; _ }, Some copy
            when (not (Instance.equal key caller))
                 && (not (is_worked_on (Path.locate_package callee)))
                 && Emit_c.is_small copy ->
              Some copy
          | _ -> None)
        (List.sort_uniq Instance.compare (Emit_c.called fragment))
  | _ -> []

let test_runner : Instance.key =
  Code { path = Well_known.make_path Run_tests; instantiation = Ground.no_instantiation }

let make_test_root path = Instance.Code { path; instantiation = Ground.no_instantiation }

let list_roots ~tests ~mains =
  (if tests = [] then [] else test_runner :: List.map make_test_root tests)
  @ List.map (fun main -> Instance.Generated (Program_main main)) mains

let rec build ?report_progress ?(tests = false) ?(supplied = []) backend ~roots ~startup ~output =
  let lookup key =
    match List.find_opt (fun fragment -> Instance.equal (Emit_c.key fragment) key) supplied with
    | Some fragment -> fragment
    | None -> compile_fragment backend key
  in
  let linked = Emit_c.list_linked ~lookup roots in
  let linked_by_key =
    Instance_table.of_seq (List.to_seq (List.map (fun unit -> (Emit_c.key unit, unit)) linked))
  in
  let list_copied =
    match backend.profile with
    | Development ->
        list_small_callees
          ~find:(Instance_table.find_opt linked_by_key)
          ~is_worked_on:backend.is_worked_on
    | Release -> fun _ -> []
  in
  let env = make_env backend in
  let render_unit index fragment =
    ( Printf.sprintf "file %d" index,
      Emit_c.render_file env backend.profile
        ((fragment, Emit_c.External)
        :: List.map (fun copy -> (copy, Emit_c.Internal)) (list_copied fragment)) )
  in
  let units =
    (("the runtime", Startup.render_runtime ~tests) :: List.mapi render_unit linked)
    @ [
        ("startup", startup);
        ( "sites",
          Emit_c.render_sites_file
            ~resolve_position:(fun site ->
              make_position backend (locate_site backend.requests site))
            linked );
      ]
  in
  match
    C_compiler.build_executable ?report_progress backend.c_compiler
      (select_optimization backend.profile)
      ~units ~output
  with
  | Ok () -> ()
  | Error message -> raise (Cannot_build message)

and build_test_program ?report_progress ?supplied backend ~time_limit_ms ~roots ~output =
  build ?report_progress ?supplied backend ~tests:true ~roots:(test_runner :: roots)
    ~startup:
      (Startup.render_tests_start ~time_limit_ms
         ~runner:(Instance.make_symbol test_runner)
         (List.map Instance.make_symbol roots))
    ~output

and build_and_run :
    'result. t -> roots:Instance.key list -> startup:string -> (string -> 'result) -> 'result =
 fun backend ~roots ~startup run ->
  let program = make_program_path backend in
  build backend ~roots ~startup ~output:program;
  let result = run program in
  (try Sys.remove program with Sys_error _ -> ());
  result

and run_while_compiling : 'value. t -> Instance.key -> read:(string -> 'value) -> 'value ran =
 fun backend root ~read ->
  let key = make_result_key backend root in
  let ran =
    match Hashtbl.find_opt backend.runs key with
    | Some ran -> ran
    | None ->
        let ran =
          match Option.bind backend.results (fun results -> results.find key) with
          | Some output -> Ran output
          | None -> (
              match
                build_and_run backend ~roots:[ root ]
                  ~startup:(Startup.render_evaluator_start (Instance.make_symbol root))
                  (fun program ->
                    Process.run_with_time_limit ~time_limit_ms:backend.evaluation_time_limit_ms
                      program [])
              with
              | None -> Ran_too_long
              | Some (0, output, _) ->
                  Option.iter (fun results -> results.add key output) backend.results;
                  Ran output
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
  | Ran_too_long -> Ran_too_long
  | Stopped report -> Stopped report

and compile_fragment backend key =
  let emit_data (data : Lowered.data) = Emit_c.make_fragment (make_env backend) (Data data) in
  let compiled =
    match read_lowered backend key with
    | Compiled fragment | Folded (_, fragment) -> fragment
    | Evaluate (path, ty) -> (
        match
          run_while_compiling backend (Instance.Evaluator path) ~read:(fun encoded ->
              Encoding.decode (make_env backend) ty encoded)
        with
        | Ran value -> emit_data { data_key = Constant path; ty; value }
        | Ran_too_long ->
            raise_cannot_build "Evaluating %s ran past the time limit of %d ms." (Path.show path)
              backend.evaluation_time_limit_ms
        | Stopped report -> raise_cannot_build "Evaluating %s stopped: %s" (Path.show path) report)
  in
  if not (Instance.equal (Emit_c.key compiled) key) then
    raise_bug "%s compiled to %s" (Instance.to_string key)
      (Instance.to_string (Emit_c.key compiled));
  compiled

let show_unsupported backend (unsupported : Lower.unsupported) =
  let where =
    match unsupported.at with
    | None -> ""
    | Some at -> show_location backend (locate_site backend.requests at) ^ ": "
  in
  where ^ "Stage0 cannot build this yet: " ^ unsupported.construct ^ "."

let capture_failure backend work =
  match work () with
  | result -> Ok result
  | exception Cannot_build message -> Error message
  | exception Lower.Unsupported unsupported -> Error (show_unsupported backend unsupported)

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
  output : string option;
  microseconds : int;
  cached : bool;
}

type reader = {
  pending : Buffer.t;
  mutable unread_from : int;
  mutable message : string option;
  mutable echo : string option;
  mutable output : string option;
  on_start : int -> unit;
  on_record : int -> record -> unit;
}

let make_reader ?(on_start = ignore) on_record =
  {
    pending = Buffer.create 1024;
    unread_from = 0;
    message = None;
    echo = None;
    output = None;
    on_start;
    on_record;
  }

let raise_malformed_report text = raise_cannot_build "A test report cannot be read: %s" text

let find_line_end reader =
  let rec scan index =
    if index >= Buffer.length reader.pending then None
    else if Buffer.nth reader.pending index = '\n' then Some index
    else scan (index + 1)
  in
  scan reader.unread_from

let rec drain reader =
  match find_line_end reader with
  | None -> ()
  | Some stop -> (
      let line = Buffer.sub reader.pending reader.unread_from (stop - reader.unread_from) in
      let consume_through last = reader.unread_from <- last + 1 in
      match String.split_on_char ' ' line with
      | [ (("message" | "echo" | "output") as label); count ] ->
          let count =
            match int_of_string_opt count with
            | Some parsed_count -> parsed_count
            | None -> raise_malformed_report line
          in
          if Buffer.length reader.pending >= stop + 1 + count + 1 then begin
            let content = Buffer.sub reader.pending (stop + 1) count in
            (match label with
            | "message" -> reader.message <- Some content
            | "echo" -> reader.echo <- Some content
            | _ -> reader.output <- Some content);
            consume_through (stop + 1 + count);
            drain reader
          end
      | [ "start"; number ] -> (
          match int_of_string_opt number with
          | Some number ->
              consume_through stop;
              reader.on_start number;
              drain reader
          | None -> raise_malformed_report line)
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
                  output = reader.output;
                  microseconds;
                  cached = false;
                }
              in
              reader.message <- None;
              reader.echo <- None;
              reader.output <- None;
              consume_through stop;
              reader.on_record number record;
              drain reader
          | _ -> raise_malformed_report line)
      | _ -> raise_malformed_report line)

let feed reader text =
  Buffer.add_string reader.pending text;
  drain reader;
  if reader.unread_from > 0 then begin
    let unread =
      Buffer.sub reader.pending reader.unread_from
        (Buffer.length reader.pending - reader.unread_from)
    in
    Buffer.clear reader.pending;
    Buffer.add_string reader.pending unread;
    reader.unread_from <- 0
  end

let parse_report text =
  let records = ref [] in
  let reader = make_reader (fun number record -> records := (number, record) :: !records) in
  match
    feed reader text;
    if
      Buffer.length reader.pending > 0
      || reader.message <> None || reader.echo <> None || reader.output <> None
    then raise_malformed_report "it ends partway through a record"
  with
  | () -> Ok (List.map snd (List.sort (fun (left, _) (right, _) -> compare left right) !records))
  | exception Cannot_build message -> Error message

let is_cacheable record =
  record.outcome = Passed && record.message = None && record.echo = None && record.output = None

let find_stored results key =
  Option.map
    (fun microseconds ->
      { outcome = Passed; message = None; echo = None; output = None; microseconds; cached = true })
    (Option.bind (results.find key) int_of_string_opt)

let store results key record = results.add key (string_of_int record.microseconds)

type progress =
  | Lowering
  | Compiling of { compiled : int; total : int }
  | Running of { tests : int }
  | Started of { test : int }
  | Ended of { test : int; record : record }

let make_incomplete_record backend todo_types =
  {
    outcome = Incomplete;
    message =
      Some
        (String.concat "\n"
           (List.map
              (fun path ->
                Printf.sprintf "the type %s is defined as todo\n  at %s" (Path.show path)
                  (show_location backend (locate_todo_type backend.requests path)))
              todo_types));
    echo = None;
    output = None;
    microseconds = 0;
    cached = false;
  }

let run_tests ?(rerun = false) ?(report_progress = ignore) backend ~time_limit_ms tests =
  capture_failure backend @@ fun () ->
  let results = backend.results in
  let roots = List.map make_test_root tests in
  report_progress Lowering;
  let is_keyed test =
    results <> None && not (Interface.Definition.is_external_test backend.requests.interface test)
  in
  let known =
    List.mapi
      (fun index (test, root) ->
        match backend.requests.list_reached_todo_types root with
        | _ :: _ as todo_types ->
            (index, root, None, Some (make_incomplete_record backend todo_types))
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
  let missing =
    Array.of_list (List.filter (fun (_, _, _, known_record) -> known_record = None) known)
  in
  let fresh = Array.make (Array.length missing) None in
  if Array.length missing > 0 then begin
    let roots = Array.to_list (Array.map (fun (_, root, _, _) -> root) missing) in
    let output = make_program_path backend in
    build_test_program backend ~time_limit_ms ~roots ~output ~report_progress:(fun compiled total ->
        report_progress (Compiling { compiled; total }));
    report_progress (Running { tests = Array.length missing });
    let read_test_index number =
      if number < 0 || number >= Array.length missing then
        raise_malformed_report (Printf.sprintf "a test numbered %d" number);
      let index, _, _, _ = missing.(number) in
      index
    in
    let reader =
      make_reader
        ~on_start:(fun number -> report_progress (Started { test = read_test_index number }))
        (fun number record ->
          let index = read_test_index number in
          let _, _, key, _ = missing.(number) in
          fresh.(number) <- Some record;
          (match (results, key) with
          | Some results, Some key when is_cacheable record -> store results key record
          | _ -> ());
          report_progress (Ended { test = index; record }))
    in
    let _, report, errors =
      Fun.protect
        ~finally:(fun () -> try Sys.remove output with Sys_error _ -> ())
        (fun () -> Process.run ~input:"" ~on_output:(feed reader) output [])
    in
    if Array.exists Option.is_none fresh then
      raise_cannot_build "The test program ended before reporting every test:\n%s%s" report errors
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
          | [] -> raise_bug "fewer results than tests"))
    known

let build_supplied_tests backend ~time_limit_ms supplied ~output =
  capture_failure backend @@ fun () ->
  let supplied_env = make_env backend in
  let supplied = List.map (fun make_instance -> make_instance supplied_env) supplied in
  build_test_program backend
    ~supplied:
      (List.map (fun instance -> Emit_c.make_fragment supplied_env (Code instance)) supplied)
    ~time_limit_ms
    ~roots:(List.map Emit_c.Builder.instance_key supplied)
    ~output

type unshippable = {
  failure : [ `Todo | `Echo ];
  file : Path.file;
  line : int;
  column : int;
  way : Path.t list;
}

let make_root_key (root : Path.t) : Instance.key =
  match root with Test _ -> make_test_root root | _ -> Generated (Program_main root)

let rec read_executed_fragment (requests : requests) key =
  match requests.find_lowered key with
  | Some (Ok (Compiled fragment | Folded (_, fragment))) -> Some fragment
  | Some (Ok (Evaluate (path, _))) -> read_executed_fragment requests (Instance.Evaluator path)
  | Some (Error _) | None -> None

let trace_root requests root =
  Emit_c.trace_reachable ~lookup:(read_executed_fragment requests) [ make_root_key root ]

let list_reached_definitions requests root =
  List.sort_uniq Path.compare
    (List.filter_map
       (fun (_, way) ->
         match List.rev way with
         | (Instance.Code { path; _ } | Constant path | Generated (Program_main path)) :: _ ->
             Some path
         | _ -> None)
       (trace_root requests root))

let list_unshippable (requests : requests) ~main =
  let reached = trace_root requests main in
  begin
    let list_definitions keys =
      List.fold_left
        (fun acc (key : Instance.key) ->
          match key with
          | Code { path; _ } | Constant path -> (
              match acc with last :: _ when Path.equal last path -> acc | _ -> path :: acc)
          | _ -> acc)
        [ main ] keys
      |> List.rev
    in
    let reports =
      List.map
        (fun path ->
          let ({ file; line; column } : location) = locate_todo_type requests path in
          { failure = `Todo; file; line; column; way = [ main; path ] })
        (requests.list_reached_todo_types (make_root_key main))
      @ List.concat_map
          (fun (compiled, keys) ->
            List.map
              (fun (failure, site) ->
                let ({ file; line; column } : location) = locate_site requests site in
                {
                  failure = (match failure with Emit_c.Echo -> `Echo | Todo -> `Todo);
                  file;
                  line;
                  column;
                  way = list_definitions keys;
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

let make_program_root backend ~main =
  let root = make_root_key main in
  match backend.requests.list_reached_todo_types root with
  | [] -> root
  | todo_types ->
      raise_cannot_build "%s"
        (String.concat "\n"
           (List.map
              (fun path ->
                Printf.sprintf
                  "%s: the type %s is defined as todo, and `main` can reach it, so the program \
                   cannot be built."
                  (show_location backend (locate_todo_type backend.requests path))
                  (Path.show path))
              todo_types))

let run_program ?input backend ~main ~arguments =
  capture_failure backend @@ fun () ->
  let root = make_program_root backend ~main in
  build_and_run backend ~roots:[ root ]
    ~startup:(Startup.render_program_start (Instance.make_symbol root))
    (fun program -> Process.run ?input program arguments)

let build_program backend ~main ~output =
  capture_failure backend @@ fun () ->
  let root = make_program_root backend ~main in
  build backend ~roots:[ root ]
    ~startup:(Startup.render_program_start (Instance.make_symbol root))
    ~output

let list_reached_todo_types (requests : requests) root =
  requests.list_reached_todo_types (make_root_key root)

let run_template_check backend ~from_template ~literals ~clauses =
  let ran =
    capture_failure backend @@ fun () ->
    run_while_compiling backend
      (Instance.Template_check { from_template; literals; clauses })
      ~read:(fun output ->
        let holds = Encoding.decode_booleans output in
        if List.length holds <> List.length clauses then
          raise_bug "checking a template of %s wrote %d results for %d clauses"
            (Path.show from_template) (List.length holds) (List.length clauses);
        holds)
  in
  match ran with
  | Ok (Ran holds) -> Ok holds
  | Ok Ran_too_long ->
      Error (Printf.sprintf "it ran past the time limit of %d ms" backend.evaluation_time_limit_ms)
  | Ok (Stopped report) | Error report -> Error report

let evaluate_call backend ~function_ ~arguments =
  capture_failure backend @@ fun () ->
  match Interface.Impls.read_signature backend.requests.interface function_ with
  | Some { output = Returns result; _ } ->
      let ty = Monomorphic.ground backend.monomorphic Types.no_substitution result in
      let key = Instance.Call_evaluation { function_; arguments } in
      run_while_compiling backend key ~read:(fun encoded ->
          Encoding.decode (make_env backend) ty encoded)
  | _ -> raise_bug "%s has no result to evaluate" (Path.show function_)

let create ?(show_file = Path.show_file) ?results ?(evaluation_time_limit_ms = 10_000)
    ?(programs = Filename.get_temp_dir_name ())
    ?(is_worked_on = fun package -> package <> Path.standard_package) requests c_compiler profile =
  {
    requests;
    monomorphic = Lower.make_monomorphic_context requests.interface;
    c_compiler;
    profile;
    show_file;
    is_worked_on;
    results;
    evaluation_time_limit_ms;
    programs;
    runs = Hashtbl.create 8;
  }

module For_testing = struct
  let is_folded backend path =
    match read_lowered backend (Instance.Constant path) with
    | Folded _ -> true
    | Evaluate _ -> false
    | Compiled _ -> raise_bug "%s is not a constant" (Path.show path)

  let make_lowered fragment = Compiled fragment

  module Intrinsics = Intrinsics

  let parse_report = parse_report
  let build_supplied_tests = build_supplied_tests
  let compile_fragment = compile_fragment
  let run_program = run_program
  let evaluate_call = evaluate_call
  let drop_and_copy = Drop_and_copy.create
  let is_trivial = Drop_and_copy.is_trivial
  let drop = Drop_and_copy.drop
  let copy = Drop_and_copy.copy
  let copy_signature = Drop_and_copy.For_testing.copy_signature
end
