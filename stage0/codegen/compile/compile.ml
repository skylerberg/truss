module Names = Resolve.Names

type lowering = { target : Memory_layout.target; checks : bool }

let show_lowering lowering =
  Printf.sprintf "%d-bit %s%s" (lowering.target.usize_bytes * 8)
    (Libc.system_name lowering.target.system)
    (if lowering.checks then ", checked" else "")

(* The target as part of a key: a result that depends on the target is
   keyed by all of it. *)
let target_key (target : Memory_layout.target) =
  Cbor.Array
    [
      Cbor.int target.pointer_bytes;
      Cbor.int target.usize_bytes;
      Cbor.Text (Libc.system_name target.system);
    ]

type lowered_outcome =
  | Compiled of Emit_c.fragment
  | Folded of Lowered.data
  | Evaluate of Path.t * Ground.ty

let rec fresh_context lowering database =
  Lower.context ~checks:lowering.checks
    ~constant:(fun _ path ->
      match Query.demand database (Lazy.force lowered) (lowering, Instance.Constant path) with
      | Folded data -> Some data.value
      | Evaluate _ -> None
      | Compiled _ -> Compiler_bug.bug ~stage:"Compile" "%s is not a constant" (Path.show path))
    database lowering.target

(* An instance's C, a constant's data, or a capability's table. *)
and emitted (context : Lower.context) (compiled : Emit_c.compiled) =
  Compiled (Emit_c.fragment (Lower.env context) compiled)

and make (context : Lower.context) (key : Instance.key) : lowered_outcome =
  let glue = Lower.glue context in
  let code instance = emitted context (Code instance) in
  match key with
  | Code _ | Entry _ | Program_main _ | Any_entry _ | Adapter _ | Locked_entry _ ->
      code (Lower.instance context key)
  | Constant path -> (
      match Lower.constant context path with
      | Folded data -> Folded data
      | Run ty -> Evaluate (path, ty))
  | Drop ty -> code (Glue.drop glue ty)
  | Copy ty -> code (Glue.copy glue ty)
  | Debug ty -> code (Glue.debug glue ty)
  | Encode ty -> code (Glue.encode glue ty)
  | Any_drop ty -> code (Glue.any_drop glue ty)
  | Evaluator path -> code (Lower.evaluator context path)
  | Template_check { from_template; texts } ->
      code (Lower.template_check context key ~from_template ~texts)
  | Call_evaluation { function_; arguments } ->
      code (Lower.call_evaluation context key ~function_ ~arguments)
  | Any_table _ -> emitted context (Table (Lower.any_table context key))
  | Table _ -> emitted context (Table (Lower.table context key))
  | Locked_table capability -> emitted context (Table (Lower.locked_table context key ~capability))

and lowered =
  lazy
    (Query.query ~name:"lowered_instance" ~phase:Phases.lowering ~saved:true ~portable:true
       ~show:(fun (lowering, key) -> show_lowering lowering ^ " " ^ Instance.to_string key)
       (fun database (lowering, key) ->
         Compiler_bug.while_doing ~stage:"Compile"
           ("lowering " ^ Instance.to_string key)
           (fun () -> make (fresh_context lowering database) key)))

(* Keys. A test's result is kept under the key of everything its code can
   reach, which is composed from the instances' own keys, so that an edit
   changes the keys of the instances that can reach the edited code and of nothing else. *)

(* Declared when the module is initialized, not when first read: a state
   opened before a query is declared leaves out every result that read
   it. *)
let () = ignore (Lazy.force lowered)
let show_instance (lowering, key) = show_lowering lowering ^ " " ^ Instance.to_string key

(* An instance's references, and the hash of its own code. A constant
   computed by running code refers to its evaluator, whose code determines
   its value. *)
let evaluated_own_hash =
  Blake3.derive_key ~context:"truss 2026-11-12 evaluated constant own hash" ""

let linked =
  Query.query ~name:"linked" ~phase:Phases.linking ~show:show_instance
    (fun database (lowering, key) ->
      let of_fragment fragment = (Reachable.own_hash fragment, Emit_c.references fragment) in
      match Query.demand database (Lazy.force lowered) (lowering, key) with
      | Evaluate (path, _) -> (evaluated_own_hash, [ Instance.Evaluator path ])
      | Compiled fragment -> of_fragment fragment
      | Folded data ->
          let context = fresh_context lowering database in
          of_fragment (Emit_c.fragment (Lower.env context) (Data data)))

let own_hash =
  Query.query ~name:"own_hash" ~phase:Phases.linking ~saved:true ~portable:true ~show:show_instance
    (fun database key -> fst (Query.demand database linked key))

let references =
  Query.query ~name:"references" ~phase:Phases.linking ~saved:true ~portable:true
    ~show:show_instance (fun database key -> snd (Query.demand database linked key))

let roots : (lowering, Instance.key list) Query.input =
  Query.input ~name:"roots" ~show:show_lowering ()

let add_roots database lowering wanted =
  List.sort_uniq Instance.compare
    (wanted @ Option.value (Query.find database roots lowering) ~default:[])

let recursion =
  Query.query ~name:"recursion" ~phase:Phases.recursion ~show:show_lowering
    ~equal:(Reachable.Keys.equal (List.equal Instance.equal))
    (fun database lowering ->
      let wanted = Option.value (Query.find database roots lowering) ~default:[] in
      let edges key =
        match Query.demand database references (lowering, key) with
        | edges -> edges
        | exception (Compiler_bug.Bug _ | Lower.Unsupported _) -> []
      in
      Reachable.groups ~edges wanted)

let group =
  Query.query ~name:"group" ~phase:Phases.keys ~saved:true ~portable:true ~show:show_instance
    (fun database (lowering, key) ->
      Reachable.Keys.find_opt key (Query.demand database recursion lowering))

let rec reach =
  lazy
    (Query.query ~name:"reach" ~phase:Phases.keys ~saved:true ~portable:true ~show:show_instance
       (fun database (lowering, key) ->
         let reach_of other = Query.demand database (Lazy.force reach) (lowering, other) in
         match Query.demand database group (lowering, key) with
         | None ->
             Reachable.unit_key
               ~own:(Query.demand database own_hash (lowering, key))
               (List.map reach_of (Query.demand database references (lowering, key)))
         | Some members ->
             Reachable.group_key
               ~link:(fun member ->
                 ( Query.demand database own_hash (lowering, member),
                   Query.demand database references (lowering, member) ))
               ~deep:reach_of ~members key))

let () = ignore (Lazy.force reach)

type 'a ran = Ran of 'a | Ran_too_long
type results = { find : string -> string option; add : string -> string -> unit }

type t = {
  database : Query.context;
  lowering : lowering;
  want : lowering -> Instance.key list -> unit;
      (** Says which instances' keys are about to be asked for *)
  context : Lower.context;  (** For laying out and emitting the lowered instances *)
  toolchain : Toolchain.t;
  cache : Build.cache;
  settings : Build.settings;
  file_name : Path.file -> string;  (** The file a position names, which the program reports *)
  worked_on : Path.package -> bool;
      (** Whether a package is one of the project's own, whose code a development build never copies
          into another's file *)
  results : results option;
      (** Where the results of runs are kept, by the key of the code that ran *)
  evaluation_time_limit : int;  (** In milliseconds, for each run of code while compiling *)
  programs : string;  (** The directory each built program is written to *)
  runs : (string, string ran) Hashtbl.t;
      (** The output of each run of code while compiling, in this build, by the key of the code that
          ran *)
}

let bug format = Compiler_bug.bug ~stage:"Compile" format
let programs_built = Atomic.make 0

(* A path in the compiler's directory of programs that no other program of
   any process has. *)
let fresh_program compiler =
  Filename.concat compiler.programs
    (Printf.sprintf "program-%d-%d" (Unix.getpid ()) (Atomic.fetch_and_add programs_built 1))

exception Cannot_build of string

let cannot_build format = Printf.ksprintf (fun message -> raise (Cannot_build message)) format

(* The key that the result of a run from [root] is kept under, once [root]
   is wanted. It hashes the key of everything [root] can reach, code
   generation's version, the target, and the build's added C flags. The
   target is part of it because [USize] is a [typedef] in the C, so the C
   can be the same for two widths while [USize.maximum] is not. The flags
   are part of it because a sanitizer can stop a run that passes without
   one. *)
let derive_result_key = Blake3.derive_key ~context:"truss 2026-11-13 result key"

let result_key compiler root =
  derive_result_key
    (Cbor.encode
       (Cbor.Array
          [
            Cbor.int Emit_c.version;
            target_key compiler.lowering.target;
            Bytes (Query.demand compiler.database (Lazy.force reach) (compiler.lowering, root));
            Cbor.Array (List.map (fun flag -> Cbor.Text flag) compiler.settings.extra);
          ]))

let test_key compiler test = result_key compiler (Lower.test_key test)

(* The key a run of code while compiling is kept under. *)
let run_key compiler root =
  compiler.want compiler.lowering [ root ];
  result_key compiler root

let anchor compiler (path : Path.t) : Positions.anchor option =
  match Query.demand compiler.database Interface.Summary.key path with
  | None -> None
  | Some key -> (
      match Query.demand compiler.database Names.base key with
      | None -> None
      | Some (file, base) ->
          let line, _ =
            Source.position (Query.demand compiler.database Packages.source file) base
          in
          Some { definition = path; path = compiler.file_name file; first_line = line })

let decode compiler ty text : Lowered.static_value =
  let env = Lower.env compiler.context in
  let monomorphic = Lower.monomorphic compiler.context in
  let target = Memory_layout.target env in
  let at = ref 0 in
  let take count =
    if !at + count > String.length text then bug "a value written out while compiling ends early";
    let part = String.sub text !at count in
    at := !at + count;
    part
  in
  let unsigned bytes =
    let value = ref Z.zero in
    for index = String.length bytes - 1 downto 0 do
      value := Z.add (Z.shift_left !value 8) (Z.of_int (Char.code bytes.[index]))
    done;
    !value
  in
  let integer (kind : Memory_layout.integer) =
    let size = Memory_layout.integer_size target kind in
    let value = unsigned (take size) in
    match kind with
    | Int8 | Int16 | Int32 | Int64 | ISize ->
        if Z.testbit value ((8 * size) - 1) then Z.sub value (Z.shift_left Z.one (8 * size))
        else value
    | _ -> value
  in
  let rec value ty : Lowered.static_value =
    if Memory_layout.has_zero_size env ty then empty ty
    else
      match Monomorphic.representation monomorphic ty with
      | Handle -> bug "a handle computed while compiling"
      | Shared _ -> bug "a shared value computed while compiling"
      | Storage element ->
          let count = Z.to_int (integer USize) in
          Static_storage
            { element; elements = List.init count (fun _ -> value element); owned = true }
      | Shape (Scalar scalar) -> Static_scalar (scalar_value scalar)
      | Shape (Record members) -> Static_record (fields members)
      | Shape (Array (element, count)) -> Static_array (List.init count (fun _ -> value element))
      | Shape (Sum variants) ->
          let index = Z.to_int (unsigned (take 4)) in
          let variant = List.nth variants index in
          Static_variant (variant.name, fields variant.fields)
  and fields members =
    List.map
      (fun (name, (member : Memory_layout.member)) ->
        match member with
        | Typed field_ty -> (name, value field_ty)
        | Raw _ -> bug "a raw field computed while compiling")
      members
  and scalar_value (scalar : Memory_layout.scalar) : Lowered.constant =
    match scalar with
    | Integer kind -> Integer (kind, integer kind)
    | Float32 -> Float32 (Z.to_int32_unsigned (unsigned (take 4)))
    | Float64 -> Float64 (Z.to_int64_unsigned (unsigned (take 8)))
    | Bool -> Bool (unsigned (take 1) <> Z.zero)
    | Character -> Character (Z.to_int (unsigned (take 4)))
    | _ -> bug "a pointer computed while compiling"
  (* A value of zero size, which is written as nothing. *)
  and empty ty : Lowered.static_value =
    match Monomorphic.shape monomorphic ty with
    | Record members ->
        Static_record (List.map (fun (name, member) -> (name, empty_member member)) members)
    | Sum [ variant ] ->
        Static_variant
          (variant.name, List.map (fun (name, member) -> (name, empty_member member)) variant.fields)
    | Array (element, count) -> Static_array (List.init count (fun _ -> empty element))
    | _ -> bug "%s has no one value of zero size" (Ground.to_string ty)
  and empty_member : Memory_layout.member -> Lowered.static_value = function
    | Typed ty -> empty ty
    | Raw _ -> bug "a raw field of zero size"
  in
  let result = value ty in
  if !at <> String.length text then bug "a value written out while compiling has bytes left over";
  result

(* The small callees emitted beside an instance in a development build, so
   that the C compiler can inline them: functions from source that the
   instance calls, of the standard library or a registry package, with
   little code and no lambdas. Those change only with the toolchain or a
   version in the lock file. The small functions of the project's own
   packages stay calls, so that an edit to one compiles only it again. *)
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

(* The standard library's test runner, which a test program's [main]
   calls. *)
let test_runner : Instance.key = Code { path = Well_known.path Run_tests; type_arguments = [] }

let rec build ?progress ?tests ?in_order ?(supplied = []) compiler ~roots ~startup ~output =
  let supplied =
    List.map (fun instance -> Emit_c.fragment (Lower.env compiler.context) (Code instance)) supplied
  in
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
  let paths = List.sort_uniq Path.compare (List.concat_map Emit_c.anchors units) in
  let anchors = List.filter_map (anchor compiler) paths in
  let target = Memory_layout.target (Lower.env compiler.context) in
  let sources = [ ("startup", startup); ("anchors", Positions.anchors_file target anchors) ] in
  let find key = Reachable.Keys.find_opt key units_by_key in
  let copied =
    match compiler.settings.build with
    | Development -> small_callees ~find ~worked_on:compiler.worked_on
    | Release -> fun _ -> []
  in
  match
    Build.program ?progress ?tests ?in_order ~copied compiler.toolchain compiler.cache
      (Lower.env compiler.context) compiler.settings
      ~files:(List.map (fun unit -> [ unit ]) units)
      ~sources ~output
  with
  | Ok () -> ()
  | Error message -> raise (Cannot_build message)

(* Builds the program that runs the tests at [roots], in that order, with
   the standard library's runner. *)
and build_test_program ?progress ?supplied compiler ~time_limit ~roots ~output =
  build ?progress ?supplied compiler ~tests:true ~roots:(test_runner :: roots)
    ~startup:
      (Startup.tests_calling ~time_limit ~runner:(Instance.symbol test_runner)
         (List.map Instance.symbol roots))
    ~output

(* Builds the instances the roots reach into a program and runs it with
   [arguments], then removes it. *)
and build_and_run ?input ?time_limit ?(in_order = true) compiler ~roots ~startup ~arguments =
  let output = fresh_program compiler in
  (* Code run while compiling starts no threads, so it is linked with the
     in-order runtime unless the caller asks for the threaded one. *)
  build compiler ~in_order ~roots ~startup ~output;
  let result = Process.run ?input ?time_limit output arguments in
  (try Sys.remove output with Sys_error _ -> ());
  result

and run_while_compiling : 'value. t -> Instance.key -> read:(string -> 'value) -> 'value ran =
 fun compiler root ~read ->
  let key = run_key compiler root in
  let ran =
    match Hashtbl.find_opt compiler.runs key with
    | Some ran -> ran
    | None ->
        let ran =
          match Option.bind compiler.results (fun results -> results.find key) with
          | Some output -> Ran output
          | None -> (
              match
                build_and_run compiler ~time_limit:compiler.evaluation_time_limit ~roots:[ root ]
                  ~startup:(Startup.evaluator_calling (Instance.symbol root))
                  ~arguments:[]
              with
              | 0, output, _ ->
                  Option.iter (fun results -> results.add key output) compiler.results;
                  Ran output
              | 137, _, _ ->
                  (* Killed at its time limit. *)
                  Ran_too_long
              | status, _, errors ->
                  cannot_build "Running %s while compiling ended with status %d: %s"
                    (Instance.to_string root) status errors)
        in
        Hashtbl.replace compiler.runs key ran;
        ran
  in
  match ran with Ran output -> Ran (read output) | Ran_too_long -> Ran_too_long

(* An instance's C from the query, or, for a constant the query could not
   fold, the data of the value its evaluator computes. *)
and compiled compiler key =
  let data (data : Lowered.data) = Emit_c.fragment (Lower.env compiler.context) (Data data) in
  let compiled =
    match Query.demand compiler.database (Lazy.force lowered) (compiler.lowering, key) with
    | Compiled fragment -> fragment
    | Folded folded -> data folded
    | Evaluate (path, ty) -> (
        match run_while_compiling compiler (Instance.Evaluator path) ~read:(decode compiler ty) with
        | Ran value -> data { data_key = Constant path; ty; value }
        | Ran_too_long ->
            cannot_build "Evaluating %s ran past the time limit of %d ms." (Path.show path)
              compiler.evaluation_time_limit)
  in
  if not (Instance.equal (Emit_c.key compiled) key) then
    bug "%s compiled to %s" (Instance.to_string key) (Instance.to_string (Emit_c.key compiled));
  compiled

(* A valid program stage0 cannot build yet, as a message with the file and
   line it is at. *)
let unsupported_message compiler (unsupported : Lower.unsupported) =
  let where =
    match unsupported.at with
    | None -> ""
    | Some at -> (
        match anchor compiler at.definition with
        | Some anchor ->
            Printf.sprintf "%s:%d:%d: " anchor.path (anchor.first_line + at.line) at.column
        | None -> "")
  in
  where ^ "Stage0 cannot build this yet: " ^ unsupported.construct ^ "."

(* Runs a step of a build, giving a failure that is not the compiler's as
   its message. A compiler bug is not caught: it is the caller's to report. *)
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

(* Reads the runner's report as it arrives. Each record's blocks come
   before the line that names its test, so a record is whole when its line
   arrives, and is handed to [on_record] with the test's number then. *)
type reader = {
  pending : Buffer.t;  (** Text not yet read as whole lines and blocks *)
  mutable message : string option;
  mutable echo : string option;
  on_start : int -> unit;
  on_record : int -> record -> unit;
}

let reader ?(on_start = ignore) on_record =
  { pending = Buffer.create 1024; message = None; echo = None; on_start; on_record }

let malformed text = cannot_build "A test report cannot be read: %s" text

(* Takes every whole record out of the pending text. *)
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

(* Whether a test is external: it declares [uses], so it gets the real
   implementations of those capabilities, and its result depends on the
   world, so it is never kept and runs every time. *)
let external_test compiler test =
  match Query.demand compiler.database Interface.Environment.interface test with
  | Some (Test_interface uses) when uses <> Types.no_capabilities -> true
  | _ -> false

let run_tests ?(rerun = false) ?(progress = ignore) compiler ~time_limit tests =
  reporting compiler @@ fun () ->
  let results = compiler.results in
  let roots = List.map Lower.test_key tests in
  progress Lowering;
  let keyed test = results <> None && not (external_test compiler test) in
  compiler.want compiler.lowering
    (List.filter_map
       (fun (test, root) -> if keyed test then Some root else None)
       (List.combine tests roots));
  let known =
    List.mapi
      (fun index (test, root) ->
        let key = if keyed test then Some (test_key compiler test) else None in
        let stored_record =
          match (results, key) with
          | Some results, Some key when not rerun -> stored results key
          | _ -> None
        in
        (index, root, key, stored_record))
      (List.combine tests roots)
  in
  (* Kept results are reported first, as ended, so progress counts them, and
     then each test that runs as it ends. *)
  List.iter
    (fun (index, _, _, stored_record) ->
      Option.iter (fun record -> progress (Ended { test = index; record })) stored_record)
    known;
  let missing =
    Array.of_list (List.filter (fun (_, _, _, stored_record) -> stored_record = None) known)
  in
  let fresh = Array.make (Array.length missing) None in
  if Array.length missing > 0 then begin
    let roots = Array.to_list (Array.map (fun (_, root, _, _) -> root) missing) in
    let output = fresh_program compiler in
    build_test_program compiler ~time_limit ~roots ~output ~progress:(fun compiled total ->
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
    (fun (_, _, _, stored_record) ->
      match stored_record with
      | Some record -> record
      | None -> (
          match !fresh with
          | record :: rest ->
              fresh := rest;
              record
          | [] -> bug "fewer results than tests"))
    known

let build_supplied_tests compiler ~time_limit supplied ~output =
  reporting compiler @@ fun () ->
  let supplied = List.map (fun instance -> instance (Lower.env compiler.context)) supplied in
  build_test_program compiler ~supplied ~time_limit
    ~roots:(List.map Emit_c.Builder.instance_key supplied)
    ~output

(* Code that cannot ship: a [todo] or an [echo] a program can reach. *)
type unshippable = {
  failure : [ `Todo | `Echo ];
  file : string;
  line : int;
  column : int;
  way : Path.t list;  (** The definitions from [main] to the one that holds it *)
}

let unshippable compiler ~main =
  reporting compiler @@ fun () ->
  let root = Instance.Program_main main in
  let reached = Reachable.running ~lookup:(compiled compiler) [ root ] in
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
      List.concat_map
        (fun (compiled, keys) ->
          List.filter_map
            (fun (failure, (site : Emit_c.site)) ->
              match anchor compiler site.definition with
              | None -> None
              | Some anchor ->
                  Some
                    {
                      failure = (match failure with Emit_c.Echo -> `Echo | Todo -> `Todo);
                      file = anchor.path;
                      line = anchor.first_line + site.line;
                      column = site.column;
                      way = definitions keys;
                    })
            (Emit_c.failures compiled))
        reached
    in
    (* One report for each place, however many instances hold it. *)
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

let test_keys compiler tests =
  compiler.want compiler.lowering (List.map Lower.test_key tests);
  List.filter_map
    (fun path ->
      match test_key compiler path with
      | key -> Some (path, key)
      | exception (Compiler_bug.Bug _ | Lower.Unsupported _) -> None)
    tests

let run_program ?input ?(in_order = false) compiler ~main ~arguments =
  reporting compiler @@ fun () ->
  let root = Instance.Program_main main in
  build_and_run ?input ~in_order compiler ~roots:[ root ]
    ~startup:(Startup.program_calling (Instance.symbol root))
    ~arguments

let build_program compiler ~main ~output =
  reporting compiler @@ fun () ->
  let root = Instance.Program_main main in
  build compiler ~roots:[ root ] ~startup:(Startup.program_calling (Instance.symbol root)) ~output

let check_template compiler ~from_template ~texts =
  reporting compiler @@ fun () ->
  match Lower.template_checked compiler.context from_template with
  | [] -> Ran []
  | positions ->
      run_while_compiling compiler
        (Instance.Template_check { from_template; texts })
        ~read:(fun output ->
          if String.length output <> List.length positions then
            cannot_build "Checking a template of %s wrote %d results for %d clauses."
              (Path.show from_template) (String.length output) (List.length positions);
          List.mapi (fun index position -> (position, output.[index] <> '\000')) positions)

(* Evaluates a call whose arguments are known, by running it: its result as
   static data, or that it ran past the time limit. *)
let evaluate_call compiler ~function_ ~arguments =
  reporting compiler @@ fun () ->
  match Query.demand compiler.database Interface.Environment.signature function_ with
  | Some { output = Returns result; _ } ->
      let ty = Monomorphic.ground (Lower.monomorphic compiler.context) [] result in
      run_while_compiling compiler
        (Instance.Call_evaluation { function_; arguments })
        ~read:(decode compiler ty)
  | _ -> bug "%s has no result to evaluate" (Path.show function_)

let run_key compiler root = reporting compiler @@ fun () -> run_key compiler root

let create ?(checks = true) ?(file_name = Path.show_file) ?results ?(evaluation_time_limit = 10_000)
    ?(programs = Filename.get_temp_dir_name ()) ~want
    ?(worked_on = fun package -> package <> Path.standard_package) database target toolchain cache
    settings =
  let lowering = { target; checks } in
  {
    database;
    lowering;
    want;
    context = fresh_context lowering database;
    toolchain;
    cache;
    settings;
    file_name;
    worked_on;
    results;
    evaluation_time_limit;
    programs;
    runs = Hashtbl.create 8;
  }

module For_testing = struct
  module Lower = struct
    type context = Lower.context
    type constant = Lower.constant = Folded of Lowered.data | Run of Ground.ty

    let context = Lower.context
    let constant = Lower.constant
    let constant_value = Lower.For_testing.constant_value
  end

  module Intrinsics = Intrinsics

  let parse_report = parse_report
  let build_supplied_tests = build_supplied_tests
  let compiled = compiled
  let run_program = run_program
end
