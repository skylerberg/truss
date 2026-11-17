let test = Harness.test

let list_diagnostics database (file : Path.file) =
  Database.check database [ file.module_.package ];
  Database.list_file_diagnostics database file

let fail = Harness.fail
let expect_string = Harness.expect_string

let expect_int ~expected actual =
  if expected <> actual then fail "expected %d, got %d" expected actual

let render_records records =
  let render_block label = function
    | Some content -> Printf.sprintf "%s %d\n%s\n" label (String.length content) content
    | None -> ""
  in
  String.concat ""
    (List.mapi
       (fun index (record : Compile.record) ->
         Printf.sprintf "test %d %s\n" index (Compile.show_outcome record.outcome)
         ^ render_block "message" record.message
         ^ render_block "echo" record.echo
         ^ render_block "output" record.output)
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

let host =
  match Libc.host with Some os -> os | None -> failwith "these tests run only on Linux and macOS"

let field name ty = (name, Memory_layout.Typed ty)

let variant ?(indirect = false) name fields : Memory_layout.variant_shape =
  { name; indirect; fields }

let compute_shape extra (ty : Ground.ty) : Memory_layout.shape =
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
  | Function function_type -> Convention.make_function_value_shape function_type
  | _ -> (
      match List.assoc_opt (Ground.to_string ty) extra with
      | Some shape -> shape
      | None -> invalid_arg ("no shape for " ^ Ground.to_string ty))

let lay_out ?(extra = []) ty =
  Memory_layout.of_type (Memory_layout.create host ~compute_shape:(compute_shape extra)) ty

let describe ?extra ty = Memory_layout.For_testing.to_string (lay_out ?extra ty)
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

let function_ ?(parameters = []) ?result ?(environment = []) locals blocks =
  { parameters; result; returns = true; environment; locals; blocks }

let key name =
  Instance.Code { path = definition name; type_arguments = []; capability_arguments = [] }

let write builder (function_ : function_) =
  List.iter
    (fun (info : local_info) ->
      ignore (Emit_c.Builder.allocate_local builder ?name:info.name info.ty))
    function_.locals;
  List.iter (fun _ -> ignore (Emit_c.Builder.allocate_block builder)) function_.blocks;
  List.iteri
    (fun index (block : block) ->
      Emit_c.Builder.start builder index;
      List.iter (Emit_c.Builder.emit builder) block.statements;
      Emit_c.Builder.finish builder block.terminator)
    function_.blocks;
  ({ parameters = function_.parameters; result = function_.result; returns = function_.returns }
    : Emit_c.Builder.prototype)

let instance ?(nested = []) name main : instance =
 fun env ->
  let builder = Emit_c.Builder.create env ~key:(key name) in
  List.iteri
    (fun index (function_ : function_) ->
      Emit_c.Builder.build_nested builder ~index ~environment:function_.environment (fun nested ->
          write nested function_))
    nested;
  Emit_c.Builder.build builder (write builder main)

let make_constant_instance instance : instance = fun _ -> instance

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

let make_shape_env ?(extra = []) () = Memory_layout.create host ~compute_shape:(compute_shape extra)
let scratch = lazy (Harness.make_scratch_directory "codegen")

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
      (if String.includes ~affix:"clang" (Lazy.force compiler).identity then
         "-Wno-sometimes-uninitialized"
       else "-Wno-maybe-uninitialized");
    ]

let counter = ref 0
let cache = lazy (Build.make_cache (Cache.make_objects_directory (Workspace.open_cache ())))

let added_flags =
  Toolchain.split_flags (Option.value (Sys.getenv_opt Toolchain.added_flags_variable) ~default:"")

let settings : Build.settings Lazy.t =
  lazy { build = Development; optimization = O1; extra = Lazy.force strict @ added_flags }

let worker_counts =
  if List.exists (String.starts_with ~prefix:"-fsanitize=") added_flags then [ 8 ]
  else [ 1; 2; 8; 32 ]

let test_position (site : Lowered.site) : Emit_c.position =
  { file = "test.truss"; line = 1; column = site.offset + 1 }

let run_program ?(extra = []) ?env ?input (instances : instance list) =
  incr counter;
  let output = Filename.concat (Lazy.force scratch) (Printf.sprintf "program%d" !counter) in
  let env = match env with Some env -> env | None -> make_shape_env ~extra () in
  let fragments =
    List.map (fun instance -> Emit_c.make_fragment env (Code (instance env))) instances
  in
  let sources =
    [
      ("main", Startup.For_testing.render_main_start (Instance.make_symbol (key "entry")));
      ("sites", Emit_c.render_sites_file ~resolve_position:test_position fragments);
    ]
  in
  match
    Build.build_program (Lazy.force compiler) (Lazy.force cache) env (Lazy.force settings)
      ~files:[ fragments ] ~sources ~output
  with
  | Ok () -> Process.run ?input output []
  | Error message -> failwith message

let expect_status ?extra expected instances =
  let status, _, errors = run_program ?extra instances in
  if status <> expected then fail "expected status %d, got %d (%s)" expected status errors

let example : Path.module_ = { package = { owner = None; name = "example" }; modules = [] }
let example_file : Path.file = { module_ = example; name = "main" }
let standard_package_database = lazy (Workspace.For_testing.load_standard_package_database ())

let make_database ?checks packages =
  Database.create ?checks ~loaded:[ Lazy.force standard_package_database ] packages

let make_example_package files : Project.package list =
  [ { name = { owner = None; name = "example" }; dependencies = []; files } ]

let compile ?results ?evaluation_time_limit_ms database =
  Compile.create ?results ?evaluation_time_limit_ms
    (Database.make_lowering_requests database [ example.package ])
    (Lazy.force compiler) (Lazy.force cache) (Lazy.force settings)

let load_files ?results ?(roots = []) ?checks files =
  let packages = make_example_package files in
  let database = make_database ?checks packages in
  List.iter (Database.For_testing.add_root database) roots;
  List.iter
    (fun ((file : Path.file), text) ->
      let source = Source.create ~path:(Path.show_file file) text in
      match list_diagnostics database file with
      | [] ->
          ignore
            (Core_lint.check_file
               (Database.make_interface_lookups database [ file.module_.package ])
               ~find_core:(fun key ->
                 Option.map
                   (fun (checked : Infer.checked) -> checked.form)
                   (Database.read_checked_body database key))
               file)
      | diagnostics ->
          fail "the source has diagnostics:\n%s"
            (String.concat "" (List.map (Diagnostic.render source) diagnostics)))
    files;
  (database, compile ?results database)

let load ?results ?roots ?checks text = load_files ?results ?roots ?checks [ (example_file, text) ]

let list_tests_in database (module_ : Path.module_) =
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      match declaration.path with Test _ -> Some declaration.path | _ -> None)
    ((Database.make_name_lookups database [ module_.package ]).list_declarations module_)

let list_tests database = list_tests_in database example

let run_source text =
  let database, compile = load text in
  match Compile.run_tests compile ~time_limit_ms:2000 (list_tests database) with
  | Ok records -> render_records records
  | Error message -> failwith message

let expect_output text expected = expect_string ~expected (run_source text)
let expect_pass name source = test name (fun () -> expect_output source "test 0 passed\n")

let run_main ?(arguments = []) ?input ?checks text =
  let _, compile = load ?checks text in
  match
    Compile.For_testing.run_program ?input compile
      ~main:(Top { module_ = example; name = "main" })
      ~arguments
  with
  | Ok result -> result
  | Error message -> failwith message

let drop_shapes =
  [
    ("Text", Memory_layout.Record [ ("buffer", Raw (Pointer Opaque)) ]);
    ("Pair", Record [ field "first" text; field "second" text ]);
    ( "Box",
      Sum
        [
          variant "Empty" [];
          variant ~indirect:true "Full" [ field "contents" text; field "count" int32 ];
        ] );
    ("Counter", Record [ ("target", Raw (Pointer (Data int32))) ]);
  ]

let standard_interface =
  lazy (Database.make_interface_lookups (make_database []) [ Path.standard_package ])

let standard_context : Monomorphic.context =
  {
    find_type_interface =
      (fun path -> Interface.Definition.find_type_interface (Lazy.force standard_interface) path);
    normalize = Fun.id;
    normalize_capabilities = Fun.id;
  }

let make_standard_type module_ name ?(arguments = []) () =
  Ground.Named { path = Path.make_standard_path [ module_ ] name; arguments }

let show_standard_layout ty =
  Memory_layout.For_testing.to_string
    (Memory_layout.of_type
       (Memory_layout.create host ~compute_shape:(Monomorphic.compute_shape standard_context))
       ty)
