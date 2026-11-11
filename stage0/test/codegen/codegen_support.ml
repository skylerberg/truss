(* What the codegen tests share: building types, shapes, and LIR by hand,
   compiling and running C, and compiling Truss source with the standard
   library and running it. *)

(* Code generation's tests. Each test gives a small input and states one
   fact about what code generation makes of it. *)

let test = Harness.test
let fail = Harness.fail

let expect_string ~expected actual =
  if not (String.equal expected actual) then fail "expected %S, got %S" expected actual

let contains text part =
  let n = String.length part in
  let rec at i = i + n <= String.length text && (String.sub text i n = part || at (i + 1)) in
  at 0

let expect_int ~expected actual =
  if expected <> actual then fail "expected %d, got %d" expected actual

(* Test records as text, each test's line with its number and outcome, then
   its message and echo blocks, leaving out durations, which differ from run
   to run. *)
let render_records records =
  let block label = function
    | Some content -> Printf.sprintf "%s %d\n%s\n" label (String.length content) content
    | None -> ""
  in
  String.concat ""
    (List.mapi
       (fun i (r : Compile.record) ->
         Printf.sprintf "test %d %s\n" i (Compile.show_outcome r.outcome)
         ^ block "message" r.message ^ block "echo" r.echo)
       records)

(* Types for the tests: a few prelude types and types defined by each test,
   with their shapes. *)

let definition name : Path.t = Top { module_ = { package = "test"; modules = [] }; name }
let named ?(arguments = []) name = Ground.Named { path = definition name; arguments }
let int64 = named "Int64"
let bool = named "Bool"
let character = named "Character"
let unit = named "Unit"
let text = named "Text"
let pair = named "Pair"
let float64 = named "Float64"
let uint8 = named "UInt8"
let option value = named "Option" ~arguments:[ Type value ]
let list element = named "List" ~arguments:[ Type element ]
let array element count = named "Array" ~arguments:[ Type element; Value (Z.of_int count) ]

open Memory_layout

(* The tests build programs and run them, so they build for this system. *)
let host =
  match Libc.host with Some os -> os | None -> failwith "these tests run only on Linux and macOS"

let target_64 = target_64 host
let target_32 = target_32 host
let field name ty = (name, Typed ty)
let variant ?(indirect = false) name fields : variant_shape = { name; indirect; fields }

(* The shapes of the prelude types the tests use, and of [extra], which
   each test defines. *)
let shapes extra (ty : Ground.ty) : shape =
  match ty with
  | Named { path = Top { name = "Int64"; _ }; _ } -> Scalar (Integer Int64)
  | Named { path = Top { name = "UInt8"; _ }; _ } -> Scalar (Integer UInt8)
  | Named { path = Top { name = "UInt64"; _ }; _ } -> Scalar (Integer UInt64)
  | Named { path = Top { name = "USize"; _ }; _ } -> Scalar (Integer USize)
  | Named { path = Top { name = "Float64"; _ }; _ } -> Scalar Float64
  | Named { path = Top { name = "Bool"; _ }; _ } -> Scalar Bool
  | Named { path = Top { name = "Character"; _ }; _ } -> Scalar Character
  | Named { path = Top { name = "Unit"; _ }; _ } -> Record []
  | Never -> Sum []
  | Named { path = Top { name = "Option"; _ }; arguments = [ Type value ] } ->
      Sum [ variant "Some" [ field "value" value ]; variant "None" [] ]
  | Named { path = Top { name = "List"; _ }; arguments = [ Type element ] } ->
      Record
        [
          ("buffer", Raw (Pointer (Data element)));
          field "length" (named "USize");
          field "capacity" (named "USize");
        ]
  | Named { path = Top { name = "Array"; _ }; arguments = [ Type element; Value count ] } ->
      Array (element, Z.to_int count)
  | Named { path = Top { name = "Int32"; _ }; _ } -> Scalar (Integer Int32)
  | Named { path = Top { name = "Storage"; _ }; arguments = [ Type element ] } ->
      Record
        [
          ("buffer", Raw (Pointer (Data element)));
          ("length", Typed (named "USize"));
          ("capacity", Typed (named "USize"));
        ]
  | Function f -> Convention.function_value_shape f
  | _ -> (
      match List.assoc_opt (Ground.to_string ty) extra with
      | Some shape -> shape
      | None -> invalid_arg ("no shape for " ^ Ground.to_string ty))

let layout ?(target = target_64) ?(extra = []) ty =
  of_type (create target ~shape_of:(shapes extra)) ty

let describe ?target ?extra ty = to_string (layout ?target ?extra ty)

(* Building LIR by hand *)

let int32 = named "Int32"
let usize = named "USize"
let local ?name ?(borrowed = false) ty : Lir.local_info = { ty; name; borrowed }
let value ty = Lir.Value ty
let at ?(projections = []) local : Lir.place = { root = Local local; projections }
let copy ?projections local = Lir.Copy (at ?projections local)
let constant_int32 n = Lir.Constant (Integer (Int32, Z.of_int n))
let constant_int64 n = Lir.Constant (Integer (Int64, Z.of_int n))
let block statements terminator : Lir.basic_block = { statements; terminator }

let function_ ?(parameters = []) ?result ?(returns = true) ?(environment = []) locals blocks :
    Lir.function_ =
  {
    parameters;
    written_result = None;
    result;
    returns;
    locals = Array.of_list locals;
    blocks = Array.of_list blocks;
    environment;
  }

let key name = Instance.Code { path = definition name; type_arguments = [] }

let instance ?(nested = []) name main : Lir.t =
  { key = key name; main; nested = Array.of_list nested }

(* [entry] returns an [Int32], which the program exits with. *)
let entry ?nested locals blocks =
  instance ?nested "entry" (function_ ~result:(value int32) locals blocks)

let call name ?(result = Some (value int32)) ?(parameters = []) arguments place : Lir.statement =
  Call
    {
      target =
        Direct
          { function_ = Instance (key name); signature = { parameters; result; returns = true } };
      arguments;
      result = (match place with Some place -> Returned place | None -> Discarded);
    }

(* Compiling and running generated C *)

let shape_env ?(extra = []) () = create target_64 ~shape_of:(shapes extra)
let scratch = lazy (Filename.temp_dir "truss-codegen-tests" "")

let compiler =
  lazy
    (match Toolchain.find () with Ok toolchain -> toolchain | Error message -> failwith message)

(* Generated C must compile with every warning an error, apart from these,
   which are known not to apply to it: parameters a function does not read
   are normal, as for an adapter's environment, and so is a value computed
   and never read, as [let _ = ...] does. *)
let strict =
  [ "-Wall"; "-Wextra"; "-Werror"; "-Wno-unused-parameter"; "-Wno-unused-but-set-variable" ]

let counter = ref 0

(* An object is kept by the text of its C, the compiler, and its flags, so
   with a directory to keep them in, a run compiles only the C that the
   last run did not. *)
let cache =
  lazy
    (Build.cache
       (match Sys.getenv_opt "TRUSS_OBJECT_CACHE" with
       | Some directory when directory <> "" -> directory
       | _ -> Filename.concat (Lazy.force scratch) "objects"))

(* [TRUSS_SANITIZE=1] builds every test's C with AddressSanitizer and
   UndefinedBehaviorSanitizer, as [truss --sanitize] does, and
   [TRUSS_SANITIZE=thread] with ThreadSanitizer, which watches the threads
   that run branches at once; a report is a compiler bug. *)
let sanitizers =
  match Sys.getenv_opt "TRUSS_SANITIZE" with
  | Some "1" ->
      [
        "-fsanitize=address,undefined"; "-fno-sanitize-recover=undefined"; "-fno-omit-frame-pointer";
      ]
  | Some "thread" -> [ "-fsanitize=thread"; "-fno-omit-frame-pointer" ]
  | _ -> []

let settings : Build.settings =
  { build = Development; optimization = O1; extra = strict @ sanitizers }

(* The thread counts that a program on threads is run with. More threads
   than cores makes them interleave more. A sanitizer slows a program
   several times, so under one a program runs once, with a count above the
   number of cores. *)
let worker_counts = if sanitizers = [] then [ 1; 2; 8; 32 ] else [ 8 ]

(* Compiles the instances into a program whose [main] calls [entry], runs
   it, and returns its status, output, and errors. *)
let run_program ?(extra = []) ?env ?(anchors = []) ?input (instances : Lir.t list) =
  incr counter;
  let output = Filename.concat (Lazy.force scratch) (Printf.sprintf "program%d" !counter) in
  let env = match env with Some env -> env | None -> shape_env ~extra () in
  let sources =
    [
      ("main", Startup.main_calling (Instance.symbol (key "entry")));
      ("anchors", Positions.anchors_file target_64 anchors);
    ]
  in
  match
    Build.program (Lazy.force compiler) (Lazy.force cache) env settings
      ~files:[ List.map (fun i -> Lir.Code i) instances ]
      ~sources ~output
  with
  | Ok () -> Toolchain.run ?input output []
  | Error message -> failwith message

let expect_status ?extra ?anchors expected instances =
  let status, _, errors = run_program ?extra ?anchors instances in
  if status <> expected then fail "expected status %d, got %d (%s)" expected status errors

(* Programs from source *)

let example : Path.module_ = { package = "example"; modules = [ "main" ] }

(* The standard library as a fixed base, shared by every test in a run, so
   that it is read and checked once and not for each test. *)
let checked_standard = lazy (Database.Testing.standard_base ())

(* The modules of a package named [example], of Truss source, with the
   standard library, ready to compile. Each must check cleanly. *)
let load_modules modules =
  let database = Engine.context (Engine.create ~bases:[ Lazy.force checked_standard ] ()) in
  Database.load_package (Engine.of_context database) ~name:"example" ~dependencies:[] modules;
  List.iter
    (fun (module_, _) ->
      let source = (Query.demand database Workspace.file module_).source in
      match Type_checker.diagnostics database module_ with
      | [] -> ()
      | diagnostics ->
          fail "the source has diagnostics:\n%s"
            (String.concat "" (List.map (Diagnostic.render source) diagnostics)))
    modules;
  ( database,
    Compile.create
      ~want:(fun lowering wanted ->
        Engine.set (Engine.of_context database) Compile.roots lowering
          (Compile.add_roots (Engine.context (Engine.of_context database)) lowering wanted))
      database target_64 (Lazy.force compiler) (Lazy.force cache) settings )

let load text = load_modules [ (example, text) ]

(* The paths of a module's tests, in order. *)
let tests_in database module_ =
  List.filter_map
    (fun (d : Resolve.Names.declaration) -> match d.path with Test _ -> Some d.path | _ -> None)
    (Query.demand database Resolve.Names.declarations module_)

let tests_of database = tests_in database example

(* Compiles a module of Truss source with the standard library, runs its
   tests, and returns the runner's output. *)
let run_source text =
  let database, compile = load text in
  match Compile.run_tests compile ~time_limit:2000 (tests_of database) with
  | Ok records -> render_records records
  | Error message -> failwith message

let expect_output text expected = expect_string ~expected (run_source text)

(* A test of a module whose one test passes. *)
let passes name source = test name (fun () -> expect_output source "test 0 passed\n")

(* Compiles a module with a [main] and runs it with the arguments. With
   [in_order], the program is linked with the runtime that starts no
   threads, so its tasks and [parallel] branches run sequentially. *)
let run_main ?(arguments = []) ?input ?in_order text =
  let _, compile = load text in
  match
    Compile.run_program ?input ?in_order compile
      ~main:(Top { module_ = example; name = "main" })
      ~arguments
  with
  | Ok result -> result
  | Error message -> failwith message

(* Shapes the drop tests and others use. *)
let drop_shapes =
  [
    ("Text", Record [ ("buffer", Raw (Pointer Opaque)) ]);
    ("Pair", Record [ field "first" text; field "second" text ]);
    ( "Box",
      Sum
        [
          variant "Empty" [];
          variant ~indirect:true "Full" [ field "contents" text; field "count" int32 ];
        ] );
    ("Counter", Record [ ("target", Raw (Pointer (Data int32))) ]);
  ]

(* Ground types and shapes from the standard library *)

let standard_database =
  lazy
    (let database = Engine.context (Engine.create ()) in
     List.iter
       (fun (module_, text) ->
         Engine.set (Engine.of_context database) Workspace.file_text module_ text)
       Standard_library.modules;
     Engine.set (Engine.of_context database) Workspace.packages Path.standard_package
       {
         name = Path.standard_package;
         dependencies = [];
         modules = List.map fst Standard_library.modules;
         usize_bits = 64;
       };
     database)

let standard_context : Monomorphic.context =
  {
    type_interface =
      (fun path ->
        Query.demand (Lazy.force standard_database) Interface.Environment.type_interface path);
    normalize = Fun.id;
    capabilities = (fun _ -> []);
    cursor_fields = (fun _ -> []);
  }

let standard module_ name ?(arguments = []) () =
  Ground.Named { path = Path.standard [ module_ ] name; arguments }

let standard_layout ty =
  Memory_layout.to_string
    (Memory_layout.of_type (create target_64 ~shape_of:(Monomorphic.shape standard_context)) ty)
