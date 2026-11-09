module Names = Resolve.Names

(* Lowering is a query: what each instance compiles to, for a target and
   whether the program checks what the prover would prove, kept current by
   the code database like any other result. See DATABASE.md, "Exact keys",
   and CODEGEN.md, "Caching".

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

exception Needs_evaluation of Path.t * Ground.ty

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

let rec fresh_context lowering database =
  let context = Lower.context ~checks:lowering.checks database lowering.target in
  (context.cursor_fields :=
     fun yielding ->
       Yields.cursor_fields context.env
         (fst (Query.demand database (Lazy.force pulled) (lowering, yielding))));
  (context.evaluate := fun path ty -> raise (Needs_evaluation (path, ty)));
  context

(* A pulled method's version, with its drops elaborated. *)
and pulled =
  lazy
    (Query.query ~name:"pulled" ~saved:true
       ~show:(fun (lowering, yielding) ->
         show_lowering lowering ^ " " ^ Ground.to_string (Cursor yielding))
       (fun database (lowering, yielding) ->
         let context = fresh_context lowering database in
         let f, owned = Lower.pulled context yielding in
         ( Drops.elaborate context.env
             ~needs_drop:(fun ty -> not (Glue.trivial context.glue ty))
             ~environment:(fun _ -> [])
             f,
           owned )))

let make (context : Lower.context) lowering database (key : Instance.key) : Lir.compiled =
  let glue = context.glue in
  let pulled yielding = Query.demand database (Lazy.force pulled) (lowering, yielding) in
  match key with
  | Code _ -> (
      try elaborate_code context (Lower.instance context key)
      with Invalid_argument message ->
        invalid_arg (message ^ ", lowering " ^ Instance.to_string key))
  | Constant path -> Data (Lower.constant context path)
  | Drop (Cursor yielding as cursor) ->
      let f, owned = pulled yielding in
      Code
        (Lir.canonical_instance
           { key; main = Yields.cursor_drop context.env ~cursor ~owned f; nested = [||] })
  | Cursor_next yielding ->
      let f, _ = pulled yielding in
      let cursor = Ground.Cursor yielding in
      let result = Lower.cursor_result context yielding in
      Code
        (Lir.canonical_instance
           { key; main = Yields.cursor_next context.env ~cursor ~result f; nested = [||] })
  | Drop ty -> elaborate_code context (Glue.drop glue ty)
  | Copy ty -> elaborate_code context (Glue.copy glue ty)
  | Debug ty -> elaborate_code context (Glue.debug glue ty)
  | Encode ty -> elaborate_code context (Glue.encode glue ty)
  | Any_drop ty -> elaborate_code context (Glue.any_drop glue ty)
  | Evaluator path -> elaborate_code context (Lower.evaluator context path)
  | Entry _ | Program_main _ | Any_entry _ | Adapter _ ->
      elaborate_code context (Lower.instance context key)
  | Any_table _ -> Table (Lower.any_table context key)
  | Table _ -> Table (Lower.table context key)
  | Real_evidence capability -> Evidence (Lower.real_evidence context capability)

let lowered =
  Query.query ~name:"lowered_instance" ~saved:true
    ~show:(fun (lowering, key) -> show_lowering lowering ^ " " ^ Instance.to_string key)
    (fun database (lowering, key) ->
      let context = fresh_context lowering database in
      match make context lowering database key with
      | compiled -> Compiled compiled
      | exception Needs_evaluation (path, ty) -> Evaluate (path, ty))

(* What a test's result is kept under: what its code can reach. A constant
   worked out by running code is keyed by the evaluator that works it out,
   whose code is what decides its value. *)
let test_key_query =
  Query.query ~name:"test_key" ~saved:true
    ~show:(fun (lowering, path) -> show_lowering lowering ^ " " ^ Path.show path)
    (fun database (lowering, path) ->
      let context = fresh_context lowering database in
      let rec lookup key =
        match Query.demand database lowered (lowering, key) with
        | Compiled compiled -> compiled
        | Evaluate (path, _) -> lookup (Instance.Evaluator path)
      in
      match Reachable.test_key context.env ~lookup (Lower.test_key path) with
      | key -> Some key
      | exception Invalid_argument _ -> None)

type t = {
  database : Query.context;
  lowering : lowering;
  context : Lower.context;  (** For laying out and emitting what the queries lowered *)
  toolchain : Toolchain.t;
  cache : Build.cache;
  settings : Build.settings;
  file_name : Path.module_ -> string;  (** The file a position names, which the program reports *)
  mutable evaluated : (Path.t * Lir.static_value) list;
      (** Each constant worked out by running code, in this build *)
}

let evaluate_hook : (t -> Path.t -> Ground.ty -> Lir.static_value) ref =
  ref (fun _ _ _ -> invalid_arg "Compile: no evaluator")

let compiled t key =
  match Query.demand t.database lowered (t.lowering, key) with
  | Compiled compiled -> compiled
  | Evaluate (path, ty) ->
      let value =
        match List.find_opt (fun (p, _) -> Path.equal p path) t.evaluated with
        | Some (_, value) -> value
        | None ->
            let value = !evaluate_hook t path ty in
            t.evaluated <- (path, value) :: t.evaluated;
            value
      in
      Data { data_key = Constant path; ty; value }

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

(* Builds what the roots reach into a program at [output], with the given
   startup code. *)
let build ?progress t ~roots ~startup ~output =
  match Reachable.reachable t.context.env ~lookup:(compiled t) roots with
  | exception Invalid_argument message -> Error message
  | units ->
      let code = List.filter_map (function Lir.Code i -> Some i | _ -> None) units in
      let paths = List.sort_uniq Path.compare (List.concat_map anchored code) in
      let anchors = List.filter_map (anchor t) paths in
      let target = Memory_layout.target t.context.env in
      let sources = [ ("startup", startup); ("anchors", Positions.anchors_file target anchors) ] in
      Build.program ?progress t.toolchain t.cache t.context.env t.settings
        ~files:(List.map (fun unit -> [ unit ]) units)
        ~sources ~output

(* Builds what the roots reach into a temporary program and runs it with
   [arguments], then removes it. *)
let build_and_run ?input t ~roots ~startup ~arguments =
  let output =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "truss-%d-%d" (Unix.getpid ()) (Hashtbl.hash roots))
  in
  match build t ~roots ~startup ~output with
  | Error message -> Error message
  | Ok () ->
      let result = Toolchain.run ?input output arguments in
      (try Sys.remove output with Sys_error _ -> ());
      Ok result

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

let malformed text = invalid_arg ("Compile: a test report that cannot be read: " ^ text)

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
  feed reader text;
  if Buffer.length reader.pending > 0 || reader.message <> None || reader.echo <> None then
    malformed "it ends partway through a record";
  List.map snd (List.sort (fun (a, _) (b, _) -> compare a b) !found)

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
  let roots = List.map Lower.test_key tests in
  progress Lowering;
  match
    List.map2
      (fun test root ->
        match results with
        | Some _ when not (external_test t test) -> (
            match Query.demand t.database test_key_query (t.lowering, test) with
            | Some key -> (root, Some key)
            | None -> invalid_arg ("Compile: cannot lower " ^ Path.show test))
        | _ -> (root, None))
      tests roots
  with
  | exception Invalid_argument message -> Error message
  | keyed -> (
      let known =
        List.mapi
          (fun index (root, key) ->
            let kept =
              match (results, key) with
              | Some results, Some key when not rerun -> stored results key
              | _ -> None
            in
            (index, root, key, kept))
          keyed
      in
      (* Kept results are reported first, as ended, so progress counts
         them, and then each test that runs as it ends. *)
      List.iter
        (fun (index, _, _, kept) ->
          Option.iter (fun record -> progress (Ended { test = index; record })) kept)
        known;
      let missing = List.filter (fun (_, _, _, kept) -> kept = None) known in
      let fresh = Array.make (List.length missing) None in
      let ran =
        if missing = [] then Ok ()
        else
          let missing = Array.of_list missing in
          let roots = Array.to_list (Array.map (fun (_, root, _, _) -> root) missing) in
          let output =
            Filename.concat (Filename.get_temp_dir_name ())
              (Printf.sprintf "truss-tests-%d" (Unix.getpid ()))
          in
          let built =
            build t ~roots
              ~startup:(Startup.tests_calling ~time_limit (List.map Instance.symbol roots))
              ~output
              ~progress:(fun compiled total -> progress (Compiling { compiled; total }))
          in
          match built with
          | Error message -> Error message
          | Ok () -> (
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
                    ignore (index_of number);
                    let index, _, key, _ = missing.(number) in
                    fresh.(number) <- Some record;
                    (match (results, key) with
                    | Some results, Some key when keep record -> store results key record
                    | _ -> ());
                    progress (Ended { test = index; record }))
              in
              match Toolchain.run ~on_output:(feed reader) output [] with
              | exception Invalid_argument message ->
                  (try Sys.remove output with Sys_error _ -> ());
                  Error message
              | _, report, errors ->
                  (try Sys.remove output with Sys_error _ -> ());
                  if Array.exists Option.is_none fresh then
                    Error
                      ("Compile: the test program ended before reporting every test:\n" ^ report
                     ^ errors)
                  else Ok ())
      in
      match ran with
      | Error message -> Error message
      | Ok () ->
          let fresh = ref (List.map Option.get (Array.to_list fresh)) in
          Ok
            (List.map
               (fun (_, _, _, kept) ->
                 match kept with
                 | Some record -> record
                 | None -> (
                     match !fresh with
                     | record :: rest ->
                         fresh := rest;
                         record
                     | [] -> invalid_arg "Compile: fewer results than tests"))
               known))

(* Code that cannot ship: a [todo] or an [echo] a program can reach. *)
type unshippable = {
  failure : [ `Todo | `Echo ];
  file : string;
  line : int;
  column : int;
  way : Path.t list;  (** The definitions from [main] to the one that holds it *)
}

let unshippable t ~main ~echo =
  let root = Instance.Program_main main in
  match Reachable.reached t.context.env ~lookup:(compiled t) [ root ] with
  | exception Invalid_argument message -> Error message
  | reached ->
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
      Ok
        (List.sort_uniq
           (fun a b ->
             compare (a.file, a.line, a.column, a.failure) (b.file, b.line, b.column, b.failure))
           found
        |> List.fold_left
             (fun acc u ->
               match acc with
               | last :: _ when (last.file, last.line, last.column) = (u.file, u.line, u.column) ->
                   acc
               | _ -> u :: acc)
             []
        |> List.rev)

let test_keys t tests =
  List.filter_map
    (fun path ->
      Option.map
        (fun key -> (path, key))
        (Query.demand t.database test_key_query (t.lowering, path)))
    tests

let run_program ?input t ~main ~arguments =
  let root = Instance.Program_main main in
  build_and_run ?input t ~roots:[ root ]
    ~startup:(Startup.program_calling (Instance.symbol root))
    ~arguments

let build_program t ~main ~output =
  let root = Instance.Program_main main in
  build t ~roots:[ root ] ~startup:(Startup.program_calling (Instance.symbol root)) ~output

(* A value read back from its binary form, as [Glue.encode] writes it, as
   static data. *)
let decode t ty text : Lir.static_value =
  let env = t.context.env in
  let monomorphic = t.context.monomorphic in
  let target = Memory_layout.target env in
  let at = ref 0 in
  let take n =
    if !at + n > String.length text then
      invalid_arg "Compile: a value written out while compiling ends early";
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
      | Handle -> invalid_arg "Compile: a handle worked out while compiling"
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
        | Raw _ -> invalid_arg "Compile: a raw field worked out while compiling")
      members
  and scalar_value (scalar : Memory_layout.scalar) : Lir.constant =
    match scalar with
    | Integer kind -> Integer (kind, integer kind)
    | Float32 -> Float32 (Z.to_int32_unsigned (unsigned (take 4)))
    | Float64 -> Float64 (Z.to_int64_unsigned (unsigned (take 8)))
    | Bool -> Bool (unsigned (take 1) <> Z.zero)
    | Character -> Character (Z.to_int (unsigned (take 4)))
    | _ -> invalid_arg "Compile: a pointer worked out while compiling"
  (* A value of zero size, which is written as nothing. *)
  and empty ty : Lir.static_value =
    match Monomorphic.shape monomorphic ty with
    | Record members -> Static_record (List.map (fun (name, m) -> (name, empty_member m)) members)
    | Sum [ variant ] ->
        Static_variant
          (variant.name, List.map (fun (name, m) -> (name, empty_member m)) variant.fields)
    | Array (element, count) -> Static_array (List.init count (fun _ -> empty element))
    | _ -> invalid_arg ("Compile: " ^ Ground.to_string ty ^ " has no one value of zero size")
  and empty_member : Memory_layout.member -> Lir.static_value = function
    | Typed ty -> empty ty
    | Raw _ -> invalid_arg "Compile: a raw field of zero size"
  in
  let result = value ty in
  if !at <> String.length text then
    invalid_arg "Compile: a value written out while compiling has bytes left over";
  result

(* Runs a constant's evaluator and reads back its value. *)
let evaluate t path ty =
  let root = Instance.Evaluator path in
  match
    build_and_run t ~roots:[ root ]
      ~startup:(Startup.evaluator_calling (Instance.symbol root))
      ~arguments:[]
  with
  | Error message -> invalid_arg message
  | Ok (0, output, _) -> decode t ty output
  | Ok (status, _, errors) ->
      invalid_arg
        (Printf.sprintf "Compile: working out %s ended with status %d: %s" (Path.show path) status
           errors)

let create ?(checks = true) ?(file_name = Workspace.file_path) database target toolchain cache
    settings =
  let lowering = { target; checks } in
  {
    database;
    lowering;
    context = fresh_context lowering database;
    toolchain;
    cache;
    settings;
    file_name;
    evaluated = [];
  }

let () = evaluate_hook := evaluate
