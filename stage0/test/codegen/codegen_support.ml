(* Helpers for the codegen tests: building types, shapes, and code by hand,
   compiling and running C, and compiling Truss source with the standard
   library and running it. *)

(* Code generation's tests. Each test gives a small input and states one
   fact about code generation's output. *)

let test = Harness.test
let fail = Harness.fail
let expect_string = Harness.expect_string
let contains = Substring.contains

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
       (fun index (record : Compile.record) ->
         Printf.sprintf "test %d %s\n" index (Compile.show_outcome record.outcome)
         ^ block "message" record.message ^ block "echo" record.echo)
       records)

(* Types for the tests: a few prelude types and types defined by each test,
   with their shapes. *)

let definition name : Path.t =
  Top { module_ = { package = { owner = None; name = "test" }; modules = [] }; name }

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
let target_32 = Memory_layout.For_testing.target_32 host
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
  | Function function_type -> Convention.function_value_shape function_type
  | _ -> (
      match List.assoc_opt (Ground.to_string ty) extra with
      | Some shape -> shape
      | None -> invalid_arg ("no shape for " ^ Ground.to_string ty))

let layout ?(target = target_64) ?(extra = []) ty =
  of_type (create target ~shape_of:(shapes extra)) ty

let describe ?target ?extra ty = Memory_layout.For_testing.to_string (layout ?target ?extra ty)

(* Writing code by hand *)

let int32 = named "Int32"
let usize = named "USize"

(* A function written by hand: its locals and blocks, in the order a
   builder numbers them, block 0 first. *)
type local_info = { ty : Lowered.ty; name : string option }
type block = { statements : Lowered.statement list; terminator : Lowered.terminator }

type function_ = {
  parameters : Lowered.local list;
  result : Lowered.ty option;
  returns : bool;
  environment : (string * Lowered.ty) list;
  locals : local_info list;
  blocks : block list;
}

(* An instance, written as C once the layouts it is printed with are
   known. *)
type instance = Memory_layout.env -> Emit_c.Builder.instance

let local ?name ty = { ty; name }
let value ty = Lowered.Value ty
let at ?(projections = []) local : Lowered.place = { root = Local local; projections }
let copy ?projections local = Lowered.Copy (at ?projections local)
let constant_int32 number = Lowered.Constant (Integer (Int32, Z.of_int number))
let constant_int64 number = Lowered.Constant (Integer (Int64, Z.of_int number))
let block statements terminator = { statements; terminator }

let function_ ?(parameters = []) ?result ?(returns = true) ?(environment = []) locals blocks =
  { parameters; result; returns; environment; locals; blocks }

let key name = Instance.Code { path = definition name; type_arguments = [] }

(* Writes a function with a builder: its locals, then its blocks. *)
let write builder (function_ : function_) =
  let module Builder = Emit_c.Builder in
  List.iter
    (fun (info : local_info) -> ignore (Builder.local builder ?name:info.name info.ty))
    function_.locals;
  List.iter (fun _ -> ignore (Builder.block builder)) function_.blocks;
  List.iteri
    (fun index (block : block) ->
      Builder.start builder index;
      List.iter (Builder.emit builder) block.statements;
      Builder.finish builder block.terminator)
    function_.blocks;
  Builder.build builder ~returns:function_.returns ~parameters:function_.parameters
    ~result:function_.result

let instance ?(nested = []) name main : instance =
 fun env ->
  let builder = Emit_c.Builder.create env ~key:(key name) in
  List.iteri
    (fun index (function_ : function_) ->
      write (Emit_c.Builder.nested builder ~index ~environment:function_.environment) function_)
    nested;
  write builder main;
  Emit_c.Builder.built builder

let printed instance : instance = fun _ -> instance

(* [entry] returns an [Int32], which the program exits with. *)
let entry ?nested locals blocks =
  instance ?nested "entry" (function_ ~result:(value int32) locals blocks)

let call name ?(result = Some (value int32)) ?(parameters = []) arguments place : Lowered.statement
    =
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
let scratch = lazy (Harness.scratch "codegen")

let compiler =
  lazy
    (match Toolchain.find () with Ok toolchain -> toolchain | Error message -> failwith message)

(* Generated C must compile with every warning an error, apart from these,
   which are known not to apply to it: parameters a function does not read
   are normal, as for an adapter's environment, and so is a value computed
   and never read, as [let _ = ...] does. A prototype of the C library's
   table writes a parameter as a pointer where a header writes an array,
   as for [pipe]'s two descriptors. The two are one type in C, and GCC 15
   reports the difference in spelling. [-Wtype-limits] is asked for by
   name: GCC's [-Wextra] has it and Clang's does not, so without it a
   comparison that only GCC rejects passes wherever the tests use Clang.
   A local read before any write is an error, but not a local that the
   compiler finds unwritten on some path: the code can take a path that no
   run takes, such as the code after a [concurrent] block whose every
   branch returns. Each compiler names that warning its own way, and Clang
   rejects GCC's name. *)
let strict =
  lazy
    [
      "-Wall";
      "-Wextra";
      "-Wtype-limits";
      "-Werror";
      "-Wno-unused-parameter";
      "-Wno-unused-but-set-variable";
      "-Wno-array-parameter";
      (if Substring.contains (Lazy.force compiler).identity "clang" then
         "-Wno-sometimes-uninitialized"
       else "-Wno-maybe-uninitialized");
    ]

let counter = ref 0

(* An object is kept in the store by the text of its C, the C compiler,
   and its flags, so a run compiles only the C that no earlier run
   compiled. *)
let cache = lazy (Build.cache (Database.objects_directory ()))

(* The flags in [TRUSS_CFLAGS], as [truss] adds them. CI sets them to a
   sanitizer's, so a report is a compiler bug. *)
let added_flags =
  Toolchain.split_flags (Option.value (Sys.getenv_opt Toolchain.added_flags_variable) ~default:"")

let settings : Build.settings Lazy.t =
  lazy { build = Development; optimization = O1; extra = Lazy.force strict @ added_flags }

(* The thread counts that a program on threads is run with. More threads
   than cores makes them interleave more. A sanitizer slows a program
   several times, so under one a program runs once, with a count above the
   number of cores. *)
let worker_counts =
  if List.exists (String.starts_with ~prefix:"-fsanitize=") added_flags then [ 8 ]
  else [ 1; 2; 8; 32 ]

(* Compiles the instances into a program whose [main] calls [entry], runs
   it, and returns its status, output, and errors. *)
let run_program ?(extra = []) ?env ?(anchors = []) ?input (instances : instance list) =
  incr counter;
  let output = Filename.concat (Lazy.force scratch) (Printf.sprintf "program%d" !counter) in
  let env = match env with Some env -> env | None -> shape_env ~extra () in
  let sources =
    [
      ("main", Startup.For_testing.main_calling (Instance.symbol (key "entry")));
      ("anchors", Positions.anchors_file target_64 anchors);
    ]
  in
  match
    Build.program (Lazy.force compiler) (Lazy.force cache) env (Lazy.force settings)
      ~files:[ List.map (fun instance -> Emit_c.fragment env (Code (instance env))) instances ]
      ~sources ~output
  with
  | Ok () -> Process.run ?input output []
  | Error message -> failwith message

let expect_status ?extra ?anchors expected instances =
  let status, _, errors = run_program ?extra ?anchors instances in
  if status <> expected then fail "expected status %d, got %d (%s)" expected status errors

(* Programs from source *)

let example : Path.module_ = { package = { owner = None; name = "example" }; modules = [] }
let example_file : Path.file = { module_ = example; name = "main" }

(* The standard library as a fixed base, shared by every test in a run, so
   that it is read and checked once and not for each test. *)
let checked_standard = lazy (Database.For_testing.standard_base ())

(* The files of a package named [example], of Truss source, with the
   standard library, ready to compile. Each must check cleanly. *)
let load_files ?results files =
  let database = Engine.context (Engine.create ~bases:[ Lazy.force checked_standard ] ()) in
  Database.load_package (Engine.of_context database)
    ~name:{ owner = None; name = "example" }
    ~dependencies:[] files;
  List.iter
    (fun (file, _) ->
      let source = Query.demand database Packages.source file in
      match Checks.diagnostics database file with
      | [] -> ignore (Core_lint.check_file database file)
      | diagnostics ->
          fail "the source has diagnostics:\n%s"
            (String.concat "" (List.map (Diagnostic.render source) diagnostics)))
    files;
  ( database,
    Compile.create ?results
      ~want:(fun lowering wanted ->
        Engine.set (Engine.of_context database) Compile.roots lowering
          (Compile.add_roots (Engine.context (Engine.of_context database)) lowering wanted))
      database target_64 (Lazy.force compiler) (Lazy.force cache) (Lazy.force settings) )

let load ?results text = load_files ?results [ (example_file, text) ]

(* The paths of a module's tests, in order. *)
let tests_in database module_ =
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      match declaration.path with Test _ -> Some declaration.path | _ -> None)
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
    Compile.For_testing.run_program ?input ?in_order compile
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
     Database.load_standard (Engine.of_context database);
     database)

let standard_context : Monomorphic.context =
  {
    type_interface =
      (fun path ->
        Query.demand (Lazy.force standard_database) Interface.Environment.type_interface path);
    normalize = Fun.id;
    normalize_capabilities = Fun.id;
  }

let standard module_ name ?(arguments = []) () =
  Ground.Named { path = Path.standard [ module_ ] name; arguments }

let standard_layout ty =
  Memory_layout.For_testing.to_string
    (Memory_layout.of_type (create target_64 ~shape_of:(Monomorphic.shape standard_context)) ty)
