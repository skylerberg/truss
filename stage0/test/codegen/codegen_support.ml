let test = Harness.test
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
       (fun index (record : Backend.Test_report.record) ->
         Printf.sprintf "test %d %s\n" index (Backend.Test_report.show_outcome record.outcome)
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
let host = match Libc.host with Ok system -> system | Error message -> failwith message
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
  | Named { path = Top { name = "List" | "Storage"; _ }; arguments = [ Type element ] } ->
      Storage.make_storage_shape element
  | Named { path = Top { name = "Array"; _ }; arguments = [ Type element; Value count ] } ->
      Array (element, Z.to_int count)
  | Named { path = Top { name = "Int32"; _ }; _ } -> Scalar (Integer Int32)
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

type program_fragment = Memory_layout.env -> Emit_c.fragment

let local ?name ty = { ty; name }
let value ty = Lowered.Value ty
let at ?(projections = []) local : Lowered.place = { root = Local local; projections }
let copy ?projections local = Lowered.Copy (at ?projections local)
let constant_int32 number = Lowered.Constant (Integer (Int32, Z.of_int number))
let constant_int64 number = Lowered.Constant (Integer (Int64, Z.of_int number))
let block statements terminator = { statements; terminator }

let function_ ?(parameters = []) ?result ?(environment = []) locals blocks =
  { parameters; result; returns = true; environment; locals; blocks }

let code_item name =
  Lowered.Item.Code { path = definition name; instantiation = Ground.no_instantiation }

let write builder (function_ : function_) =
  List.iter
    (fun (info : local_info) ->
      ignore (Emit_c.Ir_builder.allocate_local builder ?name:info.name info.ty))
    function_.locals;
  List.iter (fun _ -> ignore (Emit_c.Ir_builder.allocate_block builder)) function_.blocks;
  List.iteri
    (fun index (block : block) ->
      Emit_c.Ir_builder.start builder index;
      List.iter (Emit_c.Ir_builder.emit builder) block.statements;
      Emit_c.Ir_builder.finish builder block.terminator)
    function_.blocks;
  ({ parameters = function_.parameters; result = function_.result; returns = function_.returns }
    : Emit_c.Ir_builder.prototype)

let define_function ?(nested = []) name main : program_fragment =
 fun env ->
  let builder = Emit_c.Ir_builder.create env ~item:(code_item name) in
  List.iteri
    (fun index (function_ : function_) ->
      Emit_c.Ir_builder.build_nested builder ~index ~environment:function_.environment
        (fun nested -> write nested function_))
    nested;
  Emit_c.Ir_builder.build builder (write builder main)

let make_program_fragment fragment : program_fragment = fun _ -> fragment

let entry ?nested locals blocks =
  define_function ?nested "entry" (function_ ~result:(value int32) locals blocks)

let call name ?(result = Some (value int32)) ?(parameters = []) arguments place : Lowered.statement
    =
  Call
    {
      target =
        Direct
          { function_ = Item (code_item name); signature = { parameters; result; returns = true } };
      arguments;
      result = (match place with Some place -> Returned place | None -> Discarded);
    }

let make_shape_env ?(extra = []) () = Memory_layout.create host ~compute_shape:(compute_shape extra)
let scratch = lazy (Harness.make_scratch_directory "codegen")

let c_compiler =
  lazy
    (match C_compiler.find ~objects:(Cache.make_objects_directory (Workspace.open_cache ())) with
    | Ok c_compiler -> C_compiler.For_testing.reject_warnings c_compiler
    | Error message -> failwith message)

let counter = ref 0

let make_scratch_path prefix =
  incr counter;
  Filename.concat (Lazy.force scratch) (Printf.sprintf "%s%d" prefix !counter)

let list_worker_counts () =
  if C_compiler.For_testing.has_sanitizer (Lazy.force c_compiler) then [ 8 ] else [ 1; 2; 8; 32 ]

let test_position (site : Lowered.site) : Emit_c.position =
  { file = "test.truss"; line = 1; column = site.offset + 1 }

let run_program ?(extra = []) ?env ?input (program : program_fragment list) =
  let output = make_scratch_path "program" in
  let env = match env with Some env -> env | None -> make_shape_env ~extra () in
  let fragments = List.map (fun program_fragment -> program_fragment env) program in
  match
    C_compiler.build_executable (Lazy.force c_compiler) O1
      ~units:
        [
          ("the runtime", Startup.render_runtime ~tests:false);
          ( "the program",
            Emit_c.render_file env Development
              (List.map (fun fragment -> (fragment, Emit_c.External)) fragments) );
          ("main", Startup.For_testing.render_main_start (Emit_c.make_symbol (code_item "entry")));
          ("sites", Emit_c.render_sites_file ~resolve_position:test_position fragments);
        ]
      ~output
  with
  | Ok () -> Process.run ?input output []
  | Error message -> failwith message

let expect_status ?extra expected program =
  let status, _, errors = run_program ?extra program in
  if status <> expected then fail "expected status %d, got %d (%s)" expected status errors

let example : Path.module_ = { package = { owner = None; name = "example" }; modules = [] }
let example_file : Path.file = { module_ = example; name = "main" }
let example_main : Path.t = Top { module_ = example; name = "main" }
let standard_package_database = lazy (Workspace.For_testing.load_standard_package_database ())

let make_database packages =
  Database.create ~loaded:[ Lazy.force standard_package_database ] packages

let make_example_package files : Project.package list =
  [ { name = { owner = None; name = "example" }; dependencies = []; files } ]

let create_backend ?results ?evaluation_time_limit_ms ?(profile = Backend.Development) ~package
    database =
  Backend.create ?results ?evaluation_time_limit_ms
    (match Database.find_lowered_lookups database [ package ] with
    | Ok lookups -> lookups
    | Error message -> failwith message)
    (Lazy.force c_compiler) profile

let make_backend ?results ?evaluation_time_limit_ms ?profile database =
  create_backend ?results ?evaluation_time_limit_ms ?profile ~package:example.package database

let extend_standard_library files =
  Database.For_testing.extend_package
    ~loaded:[ Lazy.force standard_package_database ]
    ~package:Path.standard_package files

let load_standard_probe ?(roots = []) (file : Path.file) text =
  let database = extend_standard_library [ (file, text) ] in
  List.iter (Database.For_testing.add_root database) roots;
  (match
     Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers database file
   with
  | [] -> ()
  | diagnostics ->
      let source = Source.create ~path:(Path.show_file file) text in
      fail "the source has diagnostics:\n%s"
        (String.concat "" (List.map (Diagnostic.render source) diagnostics)));
  (database, create_backend ~package:Path.standard_package database)

let load_checked ~list_diagnostics ?results ?(roots = []) ?profile files =
  let packages = make_example_package files in
  let database = make_database packages in
  List.iter (Database.For_testing.add_root database) roots;
  List.iter
    (fun ((file : Path.file), text) ->
      let source = Source.create ~path:(Path.show_file file) text in
      match list_diagnostics database file with
      | [] ->
          ignore
            (Core_lint.check_file
               (Database.make_interface_lookups database)
               ~find_core:(fun key ->
                 Option.map
                   (fun (checked : Infer.checked) -> checked.form)
                   (Database.read_checked_body database key))
               file)
      | diagnostics ->
          fail "the source has diagnostics:\n%s"
            (String.concat "" (List.map (Diagnostic.render source) diagnostics)))
    files;
  (database, make_backend ?results ?profile database)

let load_files ?results ?roots ?profile files =
  load_checked ~list_diagnostics:Database.list_file_diagnostics ?results ?roots ?profile files

let load ?results ?roots ?profile text =
  load_checked
    ~list_diagnostics:(Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers)
    ?results ?roots ?profile
    [ (example_file, text) ]

let list_tests_in database (module_ : Path.module_) =
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      match declaration.path with Test _ -> Some declaration.path | _ -> None)
    ((Database.make_name_lookups database).list_declarations module_)

let list_tests database = list_tests_in database example

let run_example_tests database backend =
  match Backend.run_tests backend ~time_limit_ms:2000 (list_tests database) with
  | Ok records -> render_records records
  | Error message -> failwith message

let run_source text =
  let database, backend = load text in
  run_example_tests database backend

let expect_output text expected = expect_string ~expected (run_source text)

let build_program backend ~main =
  let output = make_scratch_path "program" in
  Result.map (fun () -> output) (Backend.build_program backend ~main ~output)

let build_main ?profile text =
  let _, backend = load ?profile text in
  match build_program backend ~main:example_main with
  | Ok program -> program
  | Error message -> failwith message

let run_main ?(arguments = []) ?input text = Process.run ?input (build_main text) arguments

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

let standard_interface = lazy (Database.make_interface_lookups (make_database []))

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
