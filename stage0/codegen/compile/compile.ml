module Names = Resolve.Names

(* Lowering is a query: what each instance compiles to, for a target and
   whether the program checks what the prover would prove, kept current by
   the code database like any other result.

   Each computation makes a lowering context of its own from the query's
   reads, so a layout or a piece of glue worked out on the way is read
   through this query and never cached where another could miss the
   dependency. A pulled method's cursor is a query too. A constant whose value
   must be worked out by running code is the one result a query cannot make,
   since running code is not a function of reads: the query says so, and the
   driver runs its [Evaluator], whose own code is lowered by the query. *)

type lowering = { target : Memory_layout.target; checks : bool }

let show_lowering lowering =
  Printf.sprintf "%d-bit%s" (lowering.target.usize_bytes * 8)
    (if lowering.checks then ", checked" else "")

type lowered_outcome = Compiled of Lir.compiled | Evaluate of Path.t * Ground.ty

let environment (instance : Lir.t) n = instance.nested.(n).environment

let elaborate_code (context : Lower.context) (instance : Lir.t) =
  let needs_drop ty = not (Glue.trivial context.glue ty) in
  let elaborate f = Drops.elaborate context.env ~needs_drop ~environment:(environment instance) f in
  Lir.Code
    (Lir.canonical_instance
       {
         instance with
         main = elaborate instance.main;
         nested = Array.map elaborate instance.nested;
       })

(* A lowering context of its own for one computation, which reads a pulled
   method's cursor and another constant's value through the queries below,
   so that each is made once and what read it is known. *)
let rec fresh_context lowering database =
  let context = Lower.context ~checks:lowering.checks database lowering.target in
  (context.cursor_fields :=
     fun yielding ->
       Yields.cursor_fields context.env
         (fst (Query.demand database (Lazy.force pulled) (lowering, yielding))));
  (context.constant :=
     fun path ->
       match Query.demand database (Lazy.force lowered) (lowering, Instance.Constant path) with
       | Compiled (Data data) -> Some data.value
       | Evaluate _ -> None
       | Compiled _ -> Compiler_bug.bug ~stage:"Compile" "%s is not a constant" (Path.show path));
  context

(* A pulled method's version, with its drops elaborated. *)
and pulled =
  lazy
    (Query.query ~name:"pulled" ~phase:Lowering ~saved:true ~portable:true
       ~show:(fun (lowering, yielding) ->
         show_lowering lowering ^ " " ^ Ground.to_string (Cursor yielding))
       (fun database (lowering, yielding) ->
         Compiler_bug.within ~stage:"Compile"
           ("lowering the pulled form of " ^ Ground.to_string (Cursor yielding))
           (fun () ->
             let context = fresh_context lowering database in
             let f, owned = Lower.pulled context yielding in
             ( Drops.elaborate context.env
                 ~needs_drop:(fun ty -> not (Glue.trivial context.glue ty))
                 ~environment:(fun _ -> [])
                 f,
               owned ))))

and make (context : Lower.context) lowering database (key : Instance.key) : lowered_outcome =
  let glue = context.glue in
  let pulled yielding = Query.demand database (Lazy.force pulled) (lowering, yielding) in
  let code instance = Compiled (elaborate_code context instance) in
  match key with
  | Code _ | Entry _ | Program_main _ | Any_entry _ | Adapter _ -> code (Lower.instance context key)
  | Constant path -> (
      match Lower.constant context path with
      | Folded data -> Compiled (Data data)
      | Run ty -> Evaluate (path, ty))
  | Drop (Cursor yielding as cursor) ->
      let f, owned = pulled yielding in
      Compiled
        (Code
           (Lir.canonical_instance
              { key; main = Yields.cursor_drop context.env ~cursor ~owned f; nested = [||] }))
  | Cursor_next yielding ->
      let f, _ = pulled yielding in
      let cursor = Ground.Cursor yielding in
      let result = Lower.cursor_result context yielding in
      Compiled
        (Code
           (Lir.canonical_instance
              { key; main = Yields.cursor_next context.env ~cursor ~result f; nested = [||] }))
  | Drop ty -> code (Glue.drop glue ty)
  | Copy ty -> code (Glue.copy glue ty)
  | Debug ty -> code (Glue.debug glue ty)
  | Encode ty -> code (Glue.encode glue ty)
  | Any_drop ty -> code (Glue.any_drop glue ty)
  | Evaluator path -> code (Lower.evaluator context path)
  | Template_check { from_template; texts } ->
      code (Lower.template_check context key ~from_template ~texts)
  | Any_table _ -> Compiled (Table (Lower.any_table context key))
  | Table _ -> Compiled (Table (Lower.table context key))
  | Real_evidence capability -> Compiled (Evidence (Lower.real_evidence context capability))

(* What an instance compiles to, or for a constant whose value does not
   fold, that its evaluator is to be run, which no query can do, since
   running code is not a function of what a query reads. *)
and lowered =
  lazy
    (Query.query ~name:"lowered_instance" ~phase:Lowering ~saved:true ~portable:true
       ~show:(fun (lowering, key) -> show_lowering lowering ^ " " ^ Instance.to_string key)
       (fun database (lowering, key) ->
         Compiler_bug.within ~stage:"Compile"
           ("lowering " ^ Instance.to_string key)
           (fun () ->
             let context = fresh_context lowering database in
             let outcome = make context lowering database key in
             (match outcome with
             | Compiled (Code instance) -> Verify.instance context.env instance
             | Compiled _ | Evaluate _ -> ());
             outcome)))

(* Keys. A test's result is kept under the key of everything its code can
   reach, which is composed from the instances' own keys, so that an edit
   changes the keys of what can reach the edited code and of nothing else. *)

let show_instance (lowering, key) = show_lowering lowering ^ " " ^ Instance.to_string key

(* What an instance refers to, and the hash of its own code. A constant
   worked out by running code refers to the evaluator that works it out,
   whose code is what decides its value. *)
let linked =
  Query.query ~name:"linked" ~phase:Linking ~show:show_instance (fun database (lowering, key) ->
      match Query.demand database (Lazy.force lowered) (lowering, key) with
      | Evaluate (path, _) ->
          (Blake3.hash "a constant worked out by its evaluator", [ Instance.Evaluator path ])
      | Compiled compiled ->
          let context = fresh_context lowering database in
          let references = Reachable.compiled_references context.env compiled in
          (Reachable.own_hash ~references compiled, references))

let own_hash =
  Query.query ~name:"own_hash" ~phase:Linking ~saved:true ~portable:true ~show:show_instance
    (fun database key -> fst (Query.demand database linked key))

let references =
  Query.query ~name:"references" ~phase:Linking ~saved:true ~portable:true ~show:show_instance
    (fun database key -> snd (Query.demand database linked key))

(* The tests and programs whose keys have been asked for. The instances
   they reach are those searched for groups that reach each other, so this
   is an input: a driver says what it wants keys for before it asks for
   them, and nothing is lowered for a test nobody asked about. *)
let roots : (lowering, Instance.key list) Query.input =
  Query.input ~name:"roots" ~show:show_lowering ()

(* The groups of instances that reach each other, among what the roots
   reach. It reads what every such instance refers to, and comes out the
   same unless a group forms or changes, so only then does it cost anything
   after it. *)
let recursion =
  Query.query ~name:"recursion" ~phase:Recursion ~show:show_lowering
    ~equal:(Reachable.Keys.equal (List.equal Instance.equal))
    (fun database lowering ->
      let wanted = Option.value (Query.find database roots lowering) ~default:[] in
      let edges key =
        match Query.demand database references (lowering, key) with
        | found -> found
        | exception (Compiler_bug.Bug _ | Compiler_bug.Unsupported _) -> []
      in
      Reachable.groups ~edges wanted)

(* The group an instance is in, if it is in one. *)
let group =
  Query.query ~name:"group" ~phase:Keys ~saved:true ~portable:true ~show:show_instance
    (fun database (lowering, key) ->
      Reachable.Keys.find_opt key (Query.demand database recursion lowering))

(* The key of everything an instance can reach: its own hash and the keys
   of what it refers to, or for an instance of a group, the group as a
   walk from the instance reaches it. *)
let rec reach =
  lazy
    (Query.query ~name:"reach" ~phase:Keys ~saved:true ~portable:true ~show:show_instance
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

(* What a test's result is kept under: the key of everything its code can
   reach, the version of code generation, and the target, since [USize] is
   a [typedef] in the C, so the LIR can be the same for two widths while
   results such as [USize.maximum] are not. *)
let test_key_query =
  Query.query ~name:"test_key" ~phase:Keys ~saved:true ~portable:true
    ~show:(fun (lowering, path) -> show_lowering lowering ^ " " ^ Path.show path)
    (fun database (lowering, path) ->
      Blake3.hash
        (Cbor.encode
           (Cbor.Array
              [
                Text "truss test";
                Cbor.int Lir.version;
                Cbor.Array
                  [ Cbor.int lowering.target.pointer_bytes; Cbor.int lowering.target.usize_bytes ];
                Bytes (Query.demand database (Lazy.force reach) (lowering, Lower.test_key path));
              ])))

type template_check = Ran of (int * bool) list | Ran_too_long

type t = {
  database : Query.context;
  lowering : lowering;
  want : lowering -> Instance.key list -> unit;
      (** Says which instances' keys are about to be asked for *)
  context : Lower.context;  (** For laying out and emitting what the queries lowered *)
  toolchain : Toolchain.t;
  cache : Build.cache;
  settings : Build.settings;
  file_name : Path.module_ -> string;  (** The file a position names, which the program reports *)
  mutable evaluated : (Path.t * Lir.static_value) list;
      (** Each constant worked out by running code, in this build *)
  checked : (string, template_check) Hashtbl.t;
      (** Each template check done in this build, by the key of the code that ran *)
}

let bug format = Compiler_bug.bug ~stage:"Compile" format

(* A build that failed for a reason that is not the compiler's: the C
   compiler or the linker refused, or a program run while compiling did not
   end well. *)
exception Cannot_build of string

let cannot_build format = Printf.ksprintf (fun message -> raise (Cannot_build message)) format

(* A test's key, once it has been said to be wanted. *)
let test_key t test = Query.demand t.database test_key_query (t.lowering, test)

(* The definitions an instance's positions are relative to. *)
let anchored (instance : Lir.t) =
  let of_function (f : Lir.function_) =
    Array.to_list f.blocks
    |> List.concat_map (fun (b : Lir.basic_block) ->
        List.filter_map
          (function Lir.Echo { site; _ } -> Some site.definition | _ -> None)
          b.statements
        @ match b.terminator with Fail { site; _ } -> [ site.definition ] | _ -> [])
  in
  of_function instance.main @ List.concat_map of_function (Array.to_list instance.nested)

let anchor t (path : Path.t) : Positions.anchor option =
  match Query.demand t.database Interface.Summary.key path with
  | None -> None
  | Some key -> (
      match Query.demand t.database Names.base key with
      | None -> None
      | Some (module_, base) ->
          let file = Query.demand t.database Workspace.file module_ in
          let line, _ = Source.position file.source base in
          Some { definition = path; path = t.file_name module_; first_line = line })

(* A value read back from its binary form, as [Glue.encode] writes it, as
   static data. *)
let decode t ty text : Lir.static_value =
  let env = t.context.env in
  let monomorphic = t.context.monomorphic in
  let target = Memory_layout.target env in
  let at = ref 0 in
  let take n =
    if !at + n > String.length text then bug "a value written out while compiling ends early";
    let part = String.sub text !at n in
    at := !at + n;
    part
  in
  let unsigned bytes =
    let value = ref Z.zero in
    for i = String.length bytes - 1 downto 0 do
      value := Z.add (Z.shift_left !value 8) (Z.of_int (Char.code bytes.[i]))
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
  let rec value ty : Lir.static_value =
    if (Memory_layout.of_type env ty).size = 0 then empty ty
    else
      match Monomorphic.kind monomorphic ty with
      | Handle -> bug "a handle worked out while compiling"
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
        | Raw _ -> bug "a raw field worked out while compiling")
      members
  and scalar_value (scalar : Memory_layout.scalar) : Lir.constant =
    match scalar with
    | Integer kind -> Integer (kind, integer kind)
    | Float32 -> Float32 (Z.to_int32_unsigned (unsigned (take 4)))
    | Float64 -> Float64 (Z.to_int64_unsigned (unsigned (take 8)))
    | Bool -> Bool (unsigned (take 1) <> Z.zero)
    | Character -> Character (Z.to_int (unsigned (take 4)))
    | _ -> bug "a pointer worked out while compiling"
  (* A value of zero size, which is written as nothing. *)
  and empty ty : Lir.static_value =
    match Monomorphic.shape monomorphic ty with
    | Record members -> Static_record (List.map (fun (name, m) -> (name, empty_member m)) members)
    | Sum [ variant ] ->
        Static_variant
          (variant.name, List.map (fun (name, m) -> (name, empty_member m)) variant.fields)
    | Array (element, count) -> Static_array (List.init count (fun _ -> empty element))
    | _ -> bug "%s has no one value of zero size" (Ground.to_string ty)
  and empty_member : Memory_layout.member -> Lir.static_value = function
    | Typed ty -> empty ty
    | Raw _ -> bug "a raw field of zero size"
  in
  let result = value ty in
  if !at <> String.length text then bug "a value written out while compiling has bytes left over";
  result

(* Builds what the roots reach into a program at [output], with the given
   startup code, once the instances agree with one another. *)
let rec build ?progress t ~roots ~startup ~output =
  let units = Reachable.reachable t.context.env ~lookup:(compiled t) roots in
  let found =
    List.fold_left
      (fun found unit -> Reachable.Keys.add (Reachable.compiled_key unit) unit found)
      Reachable.Keys.empty units
  in
  List.iter
    (fun unit ->
      Compiler_bug.within ~stage:"Compile"
        ("linking " ^ Instance.to_string (Reachable.compiled_key unit))
        (fun () ->
          Verify.links t.context.env ~find:(fun key -> Reachable.Keys.find_opt key found) unit))
    units;
  let code = List.filter_map (function Lir.Code i -> Some i | _ -> None) units in
  let paths = List.sort_uniq Path.compare (List.concat_map anchored code) in
  let anchors = List.filter_map (anchor t) paths in
  let target = Memory_layout.target t.context.env in
  let sources = [ ("startup", startup); ("anchors", Positions.anchors_file target anchors) ] in
  match
    Build.program ?progress t.toolchain t.cache t.context.env t.settings
      ~files:(List.map (fun unit -> [ unit ]) units)
      ~sources ~output
  with
  | Ok () -> ()
  | Error message -> raise (Cannot_build message)

(* Builds what the roots reach into a temporary program and runs it with
   [arguments], then removes it. *)
and build_and_run ?input ?time_limit t ~roots ~startup ~arguments =
  let output =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "truss-%d-%d" (Unix.getpid ()) (Hashtbl.hash roots))
  in
  build t ~roots ~startup ~output;
  let result = Toolchain.run ?input ?time_limit output arguments in
  (try Sys.remove output with Sys_error _ -> ());
  result

(* Runs a constant's evaluator and reads back its value. *)
and evaluate t path ty =
  let root = Instance.Evaluator path in
  match
    build_and_run t ~roots:[ root ]
      ~startup:(Startup.evaluator_calling (Instance.symbol root))
      ~arguments:[]
  with
  | 0, output, _ -> decode t ty output
  | status, _, errors ->
      cannot_build "Working out %s ended with status %d: %s" (Path.show path) status errors

(* What an instance compiles to, which is what the query lowered, or for a
   constant it could not fold, the value its evaluator works out, once in a
   build. *)
and compiled t key =
  let compiled =
    match Query.demand t.database (Lazy.force lowered) (t.lowering, key) with
    | Compiled compiled -> compiled
    | Evaluate (path, ty) ->
        let value =
          match List.find_opt (fun (p, _) -> Path.equal p path) t.evaluated with
          | Some (_, value) -> value
          | None ->
              let value = evaluate t path ty in
              t.evaluated <- (path, value) :: t.evaluated;
              value
        in
        Data { data_key = Constant path; ty; value }
  in
  if not (Instance.equal (Reachable.compiled_key compiled) key) then
    bug "%s compiled to %s" (Instance.to_string key)
      (Instance.to_string (Reachable.compiled_key compiled));
  compiled

(* A valid program stage0 cannot build yet, as a message with the file and
   line it is at. *)
let unsupported_message t (unsupported : Compiler_bug.unsupported) =
  let where =
    match unsupported.at with
    | None -> ""
    | Some at -> (
        match anchor t at.definition with
        | Some anchor ->
            Printf.sprintf "%s:%d:%d: " anchor.path (anchor.first_line + at.line) at.column
        | None -> "")
  in
  where ^ "Stage0 cannot build this yet: " ^ unsupported.what ^ "."

(* Runs a step of a build, giving a failure that is not the compiler's as
   its message. A compiler bug is not caught: it is the caller's to report. *)
let reporting t f =
  match f () with
  | result -> Ok result
  | exception Cannot_build message -> Error message
  | exception Compiler_bug.Unsupported unsupported -> Error (unsupported_message t unsupported)

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

let show_outcome outcome = fst (List.find (fun (_, o) -> o = outcome) outcomes)

(* One test's result: its outcome, its message and echo output, if any, how
   long it ran, and whether it came from the kept results. *)
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
          let count = match int_of_string_opt count with Some n -> n | None -> malformed line in
          (* The block is its bytes and a newline after the line. *)
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
  let found = ref [] in
  let reader = reader (fun number record -> found := (number, record) :: !found) in
  match
    feed reader text;
    if Buffer.length reader.pending > 0 || reader.message <> None || reader.echo <> None then
      malformed "it ends partway through a record"
  with
  | () -> Ok (List.map snd (List.sort (fun (a, _) (b, _) -> compare a b) !found))
  | exception Cannot_build message -> Error message

(* The results that are kept: a pass with nothing to show. A failure's
   message and any echo give positions, which the key leaves out so that
   moving code keeps its results, and a time limit or a crash may come from
   the machine, so those tests run again. *)
let keep record = record.outcome = Passed && record.message = None && record.echo = None

(* Where test results are kept, by the key of the code each test can run.
   The database keeps them in its store. *)
type results = { find : string -> string option; add : string -> string -> unit }

(* A kept result is [passed] and the microseconds of the run that kept it.
   A result in any other form, such as one an earlier version wrote, counts
   as none, so its test runs again and replaces it. *)
let stored results key =
  match Option.map (String.split_on_char ' ') (results.find key) with
  | Some [ "passed"; microseconds ] ->
      Option.map
        (fun microseconds ->
          { outcome = Passed; message = None; echo = None; microseconds; cached = true })
        (int_of_string_opt microseconds)
  | _ -> None

let store results key record = results.add key (Printf.sprintf "passed %d" record.microseconds)

type progress =
  | Lowering
  | Compiling of { compiled : int; total : int }
  | Running of { tests : int }
  | Started of { test : int }
  | Ended of { test : int; record : record }

(* Whether a test is external: it declares [uses], so it gets the real
   implementations of those capabilities, and its result depends on the
   world, so it is never kept and runs every time. *)
let external_test t test =
  match Query.demand t.database Interface.Environment.interface test with
  | Some (Test_interface (_ :: _)) -> true
  | _ -> false

let run_tests ?results ?(rerun = false) ?(progress = ignore) t ~time_limit tests =
  reporting t @@ fun () ->
  let roots = List.map Lower.test_key tests in
  progress Lowering;
  let keyed test = results <> None && not (external_test t test) in
  t.want t.lowering
    (List.filter_map
       (fun (test, root) -> if keyed test then Some root else None)
       (List.combine tests roots));
  let known =
    List.mapi
      (fun index (test, root) ->
        let key = if keyed test then Some (test_key t test) else None in
        let kept =
          match (results, key) with
          | Some results, Some key when not rerun -> stored results key
          | _ -> None
        in
        (index, root, key, kept))
      (List.combine tests roots)
  in
  (* Kept results are reported first, as ended, so progress counts them, and
     then each test that runs as it ends. *)
  List.iter
    (fun (index, _, _, kept) ->
      Option.iter (fun record -> progress (Ended { test = index; record })) kept)
    known;
  let missing = Array.of_list (List.filter (fun (_, _, _, kept) -> kept = None) known) in
  let fresh = Array.make (Array.length missing) None in
  if Array.length missing > 0 then begin
    let roots = Array.to_list (Array.map (fun (_, root, _, _) -> root) missing) in
    let output =
      Filename.concat (Filename.get_temp_dir_name ())
        (Printf.sprintf "truss-tests-%d" (Unix.getpid ()))
    in
    build t ~roots
      ~startup:(Startup.tests_calling ~time_limit (List.map Instance.symbol roots))
      ~output
      ~progress:(fun compiled total -> progress (Compiling { compiled; total }));
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
          | Some results, Some key when keep record -> store results key record
          | _ -> ());
          progress (Ended { test = index; record }))
    in
    let _, report, errors =
      Fun.protect
        ~finally:(fun () -> try Sys.remove output with Sys_error _ -> ())
        (fun () -> Toolchain.run ~on_output:(feed reader) output [])
    in
    if Array.exists Option.is_none fresh then
      cannot_build "The test program ended before reporting every test:\n%s%s" report errors
  end;
  let fresh = ref (List.filter_map Fun.id (Array.to_list fresh)) in
  List.map
    (fun (_, _, _, kept) ->
      match kept with
      | Some record -> record
      | None -> (
          match !fresh with
          | record :: rest ->
              fresh := rest;
              record
          | [] -> bug "fewer results than tests"))
    known

(* Code that cannot ship: a [todo] or an [echo] a program can reach. *)
type unshippable = {
  failure : [ `Todo | `Echo ];
  file : string;
  line : int;
  column : int;
  way : Path.t list;  (** The definitions from [main] to the one that holds it *)
}

let unshippable t ~main ~echo =
  reporting t @@ fun () ->
  let root = Instance.Program_main main in
  let reached = Reachable.reached t.context.env ~lookup:(compiled t) [ root ] in
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
    let found =
      List.concat_map
        (fun (compiled, keys) ->
          match compiled with
          | Lir.Code instance ->
              let sites =
                List.concat_map
                  (fun (f : Lir.function_) ->
                    Array.to_list f.blocks
                    |> List.concat_map (fun (b : Lir.basic_block) ->
                        (if echo then
                           List.filter_map
                             (function Lir.Echo { site; _ } -> Some (`Echo, site) | _ -> None)
                             b.statements
                         else [])
                        @
                        match b.terminator with
                        | Fail { failure = Todo; site; _ } -> [ (`Todo, site) ]
                        | _ -> []))
                  (instance.main :: Array.to_list instance.nested)
              in
              List.filter_map
                (fun (failure, (site : Lir.site)) ->
                  match anchor t site.definition with
                  | None -> None
                  | Some anchor ->
                      Some
                        {
                          failure;
                          file = anchor.path;
                          line = anchor.first_line + site.line;
                          column = site.column;
                          way = definitions keys;
                        })
                sites
          | _ -> [])
        reached
    in
    (* One report for each place, however many instances hold it. *)
    List.sort_uniq
      (fun a b ->
        compare (a.file, a.line, a.column, a.failure) (b.file, b.line, b.column, b.failure))
      found
    |> List.fold_left
         (fun acc u ->
           match acc with
           | last :: _ when (last.file, last.line, last.column) = (u.file, u.line, u.column) -> acc
           | _ -> u :: acc)
         []
    |> List.rev
  end

let test_keys t tests =
  t.want t.lowering (List.map Lower.test_key tests);
  List.filter_map
    (fun path ->
      match test_key t path with
      | key -> Some (path, key)
      | exception (Compiler_bug.Bug _ | Compiler_bug.Unsupported _) -> None)
    tests

let run_program ?input t ~main ~arguments =
  reporting t @@ fun () ->
  let root = Instance.Program_main main in
  build_and_run ?input t ~roots:[ root ]
    ~startup:(Startup.program_calling (Instance.symbol root))
    ~arguments

let build_program t ~main ~output =
  reporting t @@ fun () ->
  let root = Instance.Program_main main in
  build t ~roots:[ root ] ~startup:(Startup.program_calling (Instance.symbol root)) ~output

(* Works out a tagged template's check: each of the tag's [from_template]'s
   clauses that can run, for a template of these literal texts, by its
   position among the clauses, with whether it holds. Results are kept for
   the compiler's run, and, with [results], under the key of the code that
   ran, as test results are, which the texts are part of. *)
let check_key t root =
  t.want t.lowering [ root ];
  Blake3.hash
    (Cbor.encode
       (Cbor.Array
          [
            Text "truss template check";
            Cbor.int Lir.version;
            Cbor.Array
              [ Cbor.int t.lowering.target.pointer_bytes; Cbor.int t.lowering.target.usize_bytes ];
            Bytes (Query.demand t.database (Lazy.force reach) (t.lowering, root));
          ]))

let check_template ?results t ~time_limit ~from_template ~texts =
  reporting t @@ fun () ->
  match Lower.template_checked t.context from_template with
  | [] -> Ran []
  | positions -> (
      let root = Instance.Template_check { from_template; texts } in
      let key = check_key t root in
      match Hashtbl.find_opt t.checked key with
      | Some found -> found
      | None ->
          let status, output, errors =
            match Option.bind results (fun (results : results) -> results.find key) with
            | Some output -> (0, output, "")
            | None ->
                build_and_run t ~time_limit ~roots:[ root ]
                  ~startup:(Startup.evaluator_calling (Instance.symbol root))
                  ~arguments:[]
          in
          let found =
            match status with
            | 0 when String.length output = List.length positions ->
                Option.iter (fun (results : results) -> results.add key output) results;
                Ran
                  (List.mapi (fun index position -> (position, output.[index] <> '\000')) positions)
            | 137 ->
                (* Killed at its time limit. *)
                Ran_too_long
            | status ->
                cannot_build "Checking a template of %s ended with status %d: %s"
                  (Path.show from_template) status errors
          in
          Hashtbl.replace t.checked key found;
          found)

let no_keys _ _ = bug "keys were asked for, and nothing was given to say which are wanted"

let create ?(checks = true) ?(file_name = Workspace.file_path) ?(want = no_keys) database target
    toolchain cache settings =
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
    evaluated = [];
    checked = Hashtbl.create 8;
  }
