let test = Harness.test

let diagnostics pipeline (file : Path.file) =
  Pipeline.check pipeline [ file.module_.package ];
  Pipeline.file_diagnostics pipeline file

let fail = Harness.fail
let expect_string = Harness.expect_string
let contains = Substring.contains

let expect_int ~expected actual =
  if expected <> actual then fail "expected %d, got %d" expected actual

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

let host =
  match Libc.host with Some os -> os | None -> failwith "these tests run only on Linux and macOS"

let field name ty = (name, Typed ty)
let variant ?(indirect = false) name fields : variant_shape = { name; indirect; fields }

let shapes extra (ty : Ground.ty) : shape =
  match ty with
  | Named { path = Top { name = "Int64"; _ }; _ } -> Scalar (Integer Int64)
  | Named { path = Top { name = "UInt8"; _ }; _ } -> Scalar (Integer UInt8)
  | Named { path = Top { name = "UInt64"; _ }; _ } -> Scalar (Integer UInt64)
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
          field "length" (named "UInt64");
          field "capacity" (named "UInt64");
        ]
  | Named { path = Top { name = "Array"; _ }; arguments = [ Type element; Value count ] } ->
      Array (element, Z.to_int count)
  | Named { path = Top { name = "Int32"; _ }; _ } -> Scalar (Integer Int32)
  | Named { path = Top { name = "Storage"; _ }; arguments = [ Type element ] } ->
      Record
        [
          ("buffer", Raw (Pointer (Data element)));
          ("length", Typed (named "UInt64"));
          ("capacity", Typed (named "UInt64"));
        ]
  | Function function_type -> Convention.function_value_shape function_type
  | _ -> (
      match List.assoc_opt (Ground.to_string ty) extra with
      | Some shape -> shape
      | None -> invalid_arg ("no shape for " ^ Ground.to_string ty))

let computed_env system shape_of =
  let rec layout_of ty = Memory_layout.layout ~layout_of ty (shape_of ty) in
  create system ~shape_of ~layout_of

let layout ?(extra = []) ty = of_type (computed_env host (shapes extra)) ty
let describe ?extra ty = Memory_layout.For_testing.to_string (layout ?extra ty)
let int32 = named "Int32"
let uint64 = named "UInt64"

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

let shape_env ?(extra = []) () = computed_env host (shapes extra)
let scratch = lazy (Harness.scratch "codegen")

let compiler =
  lazy
    (match Toolchain.find () with Ok toolchain -> toolchain | Error message -> failwith message)

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
let cache = lazy (Build.cache (Database.objects_directory ()))

let added_flags =
  Toolchain.split_flags (Option.value (Sys.getenv_opt Toolchain.added_flags_variable) ~default:"")

let settings : Build.settings Lazy.t =
  lazy { build = Development; optimization = O1; extra = Lazy.force strict @ added_flags }

let worker_counts =
  if List.exists (String.starts_with ~prefix:"-fsanitize=") added_flags then [ 8 ]
  else [ 1; 2; 8; 32 ]

let run_program ?(extra = []) ?env ?(anchors = []) ?input (instances : instance list) =
  incr counter;
  let output = Filename.concat (Lazy.force scratch) (Printf.sprintf "program%d" !counter) in
  let env = match env with Some env -> env | None -> shape_env ~extra () in
  let sources =
    [
      ("main", Startup.For_testing.main_calling (Instance.symbol (key "entry")));
      ("anchors", Positions.anchors_file anchors);
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

let example : Path.module_ = { package = { owner = None; name = "example" }; modules = [] }
let example_file : Path.file = { module_ = example; name = "main" }
let standard_state = lazy (Database.For_testing.standard_state ())
let pipeline database = Pipeline.create ~loaded:[ Lazy.force standard_state ] database

let example_package files : Project.package list =
  [ { name = { owner = None; name = "example" }; dependencies = []; files } ]

let compile ?results ?evaluation_time_limit_ms pipeline =
  Compile.create ?results ?evaluation_time_limit_ms
    (Pipeline.lowering_requests pipeline [ example.package ])
    (Lazy.force compiler) (Lazy.force cache) (Lazy.force settings)

let load_files ?results ?(roots = []) files =
  let database = example_package files in
  let pipeline = pipeline database in
  List.iter (Pipeline.For_testing.root pipeline) roots;
  List.iter
    (fun ((file : Path.file), text) ->
      let source = Source.create ~path:(Path.show_file file) text in
      match diagnostics pipeline file with
      | [] ->
          ignore
            (Core_lint.check_file
               (Pipeline.interface_lookups pipeline [ file.module_.package ])
               ~core:(fun key ->
                 Option.map
                   (fun (checked : Infer.checked) -> checked.form)
                   (Pipeline.For_testing.checked_body pipeline key))
               file)
      | diagnostics ->
          fail "the source has diagnostics:\n%s"
            (String.concat "" (List.map (Diagnostic.render source) diagnostics)))
    files;
  (pipeline, compile ?results pipeline)

let load ?results ?roots text = load_files ?results ?roots [ (example_file, text) ]

let tests_in pipeline (module_ : Path.module_) =
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      match declaration.path with Test _ -> Some declaration.path | _ -> None)
    ((Pipeline.names pipeline [ module_.package ]).declarations module_)

let tests_of pipeline = tests_in pipeline example

let run_source text =
  let pipeline, compile = load text in
  match Compile.run_tests compile ~time_limit_ms:2000 (tests_of pipeline) with
  | Ok records -> render_records records
  | Error message -> failwith message

let expect_output text expected = expect_string ~expected (run_source text)
let passes name source = test name (fun () -> expect_output source "test 0 passed\n")

let run_main ?(arguments = []) ?input text =
  let _, compile = load text in
  match
    Compile.For_testing.run_program ?input compile
      ~main:(Top { module_ = example; name = "main" })
      ~arguments
  with
  | Ok result -> result
  | Error message -> failwith message

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

let standard_interface = lazy (Pipeline.interface_lookups (pipeline []) [ Path.standard_package ])

let standard_context : Monomorphic.context =
  {
    type_interface =
      (fun path -> Interface.Definition.type_interface (Lazy.force standard_interface) path);
    normalize = Fun.id;
    normalize_capabilities = Fun.id;
  }

let standard module_ name ?(arguments = []) () =
  Ground.Named { path = Path.standard [ module_ ] name; arguments }

let standard_layout ty =
  Memory_layout.For_testing.to_string
    (Memory_layout.of_type (computed_env host (Monomorphic.shape standard_context)) ty)
