let app : Path.package = { owner = None; name = "app" }
let make_main_path name = Support.make_top_path "app.main" name

let make_key path : Resolve.Names.key =
  { module_ = Support.parse_module "app.main"; path; ordinal = 0 }

let make_main_key name = make_key (make_main_path name)
let make_method owner name receiver : Path.t = Method { owner; name; receiver }

let make_impl_method ?(module_ = "app.main") ~trait ~for_type name receiver =
  make_method
    (Impl
       {
         module_ = Support.parse_module module_;
         trait = { path = trait; arguments = []; associated = [] };
         for_type;
       })
    name receiver

let make_code_item_of path : Lowered.Item.t =
  Code
    {
      path;
      instantiation = { type_arguments = []; capability_arguments = [] };
      assumes_condition = false;
    }

let make_code_item name = make_code_item_of (make_main_path name)

type part =
  | Parsed of Path.file
  | Declared of Path.module_
  | Resolved of Resolve.Names.key * Resolve.section
  | Import_check of Path.file
  | Interface of Resolve.Names.key
  | Type_facts of Path.t
  | Signature_check of Resolve.Names.key
  | Contract of Resolve.Names.key
  | Checked_body of Resolve.Names.key
  | Body_mir of Resolve.Names.key
  | Generated_mir of Path.t
  | Call_edges of Path.t
  | Recursion_group of Path.t
  | Type_check of Resolve.Names.key
  | Proof of Resolve.Names.key
  | Verdicts of Resolve.Names.key
  | Lowered of Lowered.Item.t
  | Test_key of Lowered.Item.t
  | Unit of Profile.t * Lowered.Item.t

type name =
  | Tree of Resolve.Names.key
  | Text of Resolve.Names.key
  | Place of Resolve.Names.key
  | Impls_of_type of Path.package * Path.t
  | Dependencies of Path.package

type read = Stored of part | Name of name

let locate (part : part) : Database.For_testing.computed =
  let of_key (stage : Database.Kind.stage) key : Database.For_testing.computed =
    { stage; id = Database.For_testing.identify_key key }
  and of_path (stage : Database.Kind.stage) path : Database.For_testing.computed =
    { stage; id = Database.For_testing.identify_path path }
  and of_file (stage : Database.Kind.stage) file : Database.For_testing.computed =
    { stage; id = Database.For_testing.identify_file file }
  and of_item (stage : Database.Kind.stage) item : Database.For_testing.computed =
    { stage; id = Database.For_testing.identify_item item }
  in
  match part with
  | Parsed file -> of_file Parse file
  | Declared module_ -> { stage = Declare; id = Database.For_testing.identify_module module_ }
  | Resolved (key, _) -> of_key Resolve key
  | Import_check file -> of_file Check_imports file
  | Interface key -> of_key Elaborate key
  | Type_facts path -> of_path Compute_type_facts path
  | Signature_check key -> of_key Check_signature key
  | Contract key -> of_key Check_contract key
  | Checked_body key -> of_key Check_body key
  | Body_mir key -> of_key Build_body_mir key
  | Generated_mir path -> of_path Generate_mir path
  | Call_edges path -> of_path List_calls path
  | Recursion_group path -> of_path Group_recursion path
  | Type_check key -> of_key Check_type key
  | Proof key -> of_key Prove key
  | Verdicts key -> of_key Decide key
  | Lowered item -> of_item Lower item
  | Test_key item -> of_item Key_tests item
  | Unit (profile, item) -> of_item (Render profile) item

let list_targets : read -> (Database.Kind.target * int * string) list = function
  | Name (Tree key) -> [ (Lookup Tree, Database.For_testing.identify_key key, "") ]
  | Name (Text key) -> [ (Lookup Text, Database.For_testing.identify_key key, "") ]
  | Name (Place key) -> [ (Lookup Place, Database.For_testing.identify_key key, "") ]
  | Name (Impls_of_type (package, type_)) ->
      [
        (Lookup Impls_of_type, Database.For_testing.identify_path type_, Path.show_package package);
      ]
  | Name (Dependencies package) ->
      [ (Lookup Dependencies, Database.For_testing.identify_package package, "") ]
  | Stored part -> (
      let id = (locate part).id in
      let of_facts facts =
        List.map (fun fact : (Database.Kind.target * int * string) -> (Fact fact, id, "")) facts
      in
      match part with
      | Resolved (_, section) -> of_facts [ Resolved section ]
      | Interface _ -> of_facts [ Interface; Elaboration; Checked_interface ]
      | Type_facts _ -> of_facts [ Type_facts ]
      | Signature_check _ -> of_facts [ Checked_interface ]
      | Contract _ -> of_facts [ Contract ]
      | Checked_body _ -> of_facts [ Body_form; Body_tables; Run_forever; Ownership_modes ]
      | Body_mir _ -> of_facts [ Body_mir ]
      | Generated_mir _ -> of_facts [ Generated_mir ]
      | Call_edges _ -> of_facts [ Call_node; Callees ]
      | Recursion_group _ -> of_facts [ Recursion_group ]
      | Proof _ -> of_facts [ Proof ]
      | Lowered _ -> of_facts [ Lowered ]
      | Test_key _ -> of_facts [ Test_key ]
      | Unit (profile, _) -> of_facts [ Unit profile ]
      | Parsed _ | Declared _ | Import_check _ | Type_check _ | Verdicts _ -> [])

let show_computed ({ stage; id } : Database.For_testing.computed) =
  Printf.sprintf "%s of %d" (Database.Kind.show_stage stage) id

let show_parts computed = String.concat ", " (List.map show_computed computed)
let make_lowered name = Lowered (make_code_item name)
let make_test_key name = Test_key (make_code_item name)
let make_unit profile name = Unit (profile, make_code_item name)

let rec locate_module : Path.t -> Path.module_ = function
  | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ } ->
      module_
  | Method { owner; _ } | Member_constant { owner; _ } -> locate_module owner
  | Derived { type_; _ } -> locate_module type_
  | Unresolved { file; _ } -> file.module_

let list_units_of definitions : Database.For_testing.computed list =
  List.concat_map
    (fun path ->
      let key : Resolve.Names.key = { module_ = locate_module path; path; ordinal = 0 } in
      List.concat_map
        (fun stage : Database.For_testing.computed list ->
          [
            { stage; id = Database.For_testing.identify_key key };
            { stage; id = Database.For_testing.identify_path path };
          ])
        Database.Kind.stages)
    definitions

let is_part_of definitions =
  let units = list_units_of definitions in
  fun computed -> List.mem computed units

let check_text text =
  let database = Support.make_database (Support.setup [ ("app.main", text) ]) in
  (match
     Support.list_codes
       (Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers database
          (Support.parse_file "app.main"))
   with
  | [] -> ()
  | codes -> Harness.fail "the program has diagnostics: %s" (String.concat ", " codes));
  database

let expect_reads database part ~includes ~excludes =
  let computed = locate part in
  let reads = Database.For_testing.list_reads database computed.stage computed.id in
  let is_read read = List.exists (fun target -> List.mem target reads) (list_targets read) in
  List.iteri
    (fun index read ->
      if not (is_read read) then
        Harness.fail "%s does not read the fact %d that it should" (show_computed computed) index)
    includes;
  List.iteri
    (fun index read ->
      if is_read read then
        Harness.fail "%s reads the fact %d that it should not" (show_computed computed) index)
    excludes

let show_differences differences =
  String.concat ", "
    (List.map (fun (table, count) -> Printf.sprintf "%d rows of %s" count table) differences)

let build ?(roots = []) files =
  let database = Support.make_database (Support.setup files) in
  List.iter (fun name -> Database.For_testing.add_root database (make_code_item name)) roots;
  Database.For_testing.propagate database;
  database

let list_changes ~before ~after =
  List.filter_map
    (fun (name, text) ->
      match List.assoc_opt name before with
      | Some previous when previous = text -> None
      | Some _ | None -> Some (Support.parse_file name, Some text))
    after
  @ List.filter_map
      (fun (name, _) ->
        if List.mem_assoc name after then None else Some (Support.parse_file name, None))
      before

let propagate ?roots hot ~before ~after =
  let (), observed =
    Database.For_testing.observe (fun () ->
        Database.update hot (list_changes ~before ~after);
        Database.For_testing.propagate hot)
  in
  (match Database.For_testing.list_differences hot (build ?roots after) with
  | [] -> ()
  | differences ->
      Harness.fail "the propagated database differs from a cold build in %s"
        (show_differences differences));
  observed

let list_linked database profile roots =
  match Database.find_lowered_lookups database [ app ] with
  | Ok lookups -> lookups.list_linked profile roots
  | Error message -> Harness.fail "%s" message

let render_units database roots =
  List.iter
    (fun profile ->
      List.iter
        (function
          | Lowering.Unit _ -> ()
          | Evaluated { item; _ } ->
              Harness.fail "%s is evaluated, and has no unit" (Lowered.Item.to_string item)
          | Unbuildable _ -> Harness.fail "a linked item cannot be built")
        (list_linked database profile (List.map make_code_item roots)))
    [ Profile.Development; Release ]

let list_rendered_after_edit ~roots ~before ~after profile =
  let hot = build ~roots before in
  render_units hot roots;
  let (), observed =
    Database.For_testing.observe (fun () ->
        Database.update hot (list_changes ~before ~after);
        Database.For_testing.propagate hot;
        render_units hot roots)
  in
  let cold = build ~roots after in
  render_units cold roots;
  (match Database.For_testing.list_differences hot cold with
  | [] -> ()
  | differences ->
      Harness.fail "the propagated database differs from a cold build in %s"
        (show_differences differences));
  List.filter
    (fun (computed : Database.For_testing.computed) -> computed.stage = Render profile)
    observed.recomputed

let list_propagated ~before ~after = (propagate (build before) ~before ~after).recomputed

let list_propagated_with_roots ~roots ~before ~after =
  (propagate ~roots (build ~roots before) ~before ~after).recomputed

let expect_recomputed recomputed ~exactly =
  let exactly = List.sort_uniq compare (List.map locate exactly) in
  if recomputed <> exactly then
    Harness.fail "recomputed %s, not %s" (show_parts recomputed) (show_parts exactly)

let expect_same_units recomputed ~as_ =
  if recomputed <> as_ then
    Harness.fail "recomputed %s, not %s" (show_parts recomputed) (show_parts as_)

let expect_untouched recomputed ~is_excluded =
  List.iter
    (fun computed ->
      if is_excluded computed then
        Harness.fail "recomputed %s; it recomputed %s" (show_computed computed)
          (show_parts recomputed))
    recomputed

let expect_included recomputed ~parts =
  List.iter
    (fun part ->
      if not (List.mem (locate part) recomputed) then
        Harness.fail "did not recompute %s; it recomputed %s"
          (show_computed (locate part))
          (show_parts recomputed))
    parts

let standard = lazy (Workspace.For_testing.load_standard_package_database ())

let settle loaded packages =
  let database = Database.create ~loaded:(Lazy.force standard :: loaded) packages in
  Database.For_testing.propagate database;
  database

let lay_out_again ?(loaded = ([], [])) ~before ~after () =
  let hot = settle (fst loaded) before in
  let (), observed =
    Database.For_testing.observe (fun () ->
        Database.relayout hot ~loaded:(Lazy.force standard :: snd loaded) after;
        Database.For_testing.propagate hot)
  in
  (match Database.For_testing.list_differences hot (settle (snd loaded) after) with
  | [] -> ()
  | differences ->
      Harness.fail "the relaid database differs from a cold build in %s"
        (show_differences differences));
  observed.recomputed

let load_package files =
  let path = Filename.concat (Harness.make_scratch_directory "package") "package.sqlite" in
  Database.build_package ~loaded:[ Lazy.force standard ] (List.hd (Support.setup files)) ~into:path;
  path

let compiler = "database tests"

let make_database_path () =
  Filename.concat (Harness.make_scratch_directory "database") "database.sqlite"

let open_saved ?(compiler = compiler) ?(roots = []) path packages =
  let database = Database.open_file path ~compiler ~loaded:[ Lazy.force standard ] packages in
  List.iter (fun name -> Database.For_testing.add_root database (make_code_item name)) roots;
  Database.For_testing.propagate database;
  database

let build_saved ?roots path files = open_saved ?roots path (Support.setup files)

let expect_cold ?roots database files =
  match Database.For_testing.list_differences database (build ?roots files) with
  | [] -> ()
  | differences ->
      Harness.fail "the reopened database differs from a cold build in %s"
        (show_differences differences)

let observe_reopen ?roots path files =
  let database, observed =
    Database.For_testing.observe (fun () -> open_saved ?roots path (Support.setup files))
  in
  expect_cold ?roots database files;
  Database.close database;
  observed

let tool_user =
  [
    ("app.main", "use lib.tools\nfn caller() -> Int64 { tools.helper() }\n");
    ("lib.tools", "public fn helper() -> Int64 { 1 }\n");
  ]

let make_mutual_source body =
  Printf.sprintf
    "fn f(n: Int64) -> Int64\n{ g(n) }\nfn g(n: Int64) -> Int64\n{ %s }\nfn h() -> Int64 { f(1) }\n"
    body

let acyclic = make_mutual_source "n"
let cyclic = make_mutual_source "f(n)"

let stepper =
  "trait Step {\n\
  \  fn step(own self) -> Int64\n\
   }\n\
   fn run(value: own any Step) -> Int64\n\
   {\n\
  \  own value.step()\n\
   }\n\
   type Foo()\n"

let stepper_that_runs =
  stepper
  ^ "impl Step for Foo {\n\
    \  fn step(own self) -> Int64\n\
    \  {\n\
    \    let value: any Step = any self\n\
    \    run(own value)\n\
    \  }\n\
     }\n"

let make_configured_source construction =
  Printf.sprintf
    "type Config(size: Int64 = start())\n\
     fn start() -> Int64\n\
     { make().size }\n\
     fn make() -> Config\n\
     { %s }\n"
    construction

let make_default_source version =
  "type Key(value: Int64)\n\
  \  derives Default\n\
   type Loop(value: Int64)\n\
   impl Default for Loop {\n\
  \  fn default() -> Loop {\n\
  \    Loop(value: check().major.value)\n\
  \  }\n\
   }\n" ^ version
  ^ "fn make[Item: Default]() -> Item\n\
     {\n\
    \  Item.default()\n\
     }\n\
     fn check() -> Version\n\
     {\n\
    \  make[Version]()\n\
     }\n"

let version_deriving_over_a_key =
  make_default_source "type Version(major: Key)\n  derives Default\n"

let version_deriving_over_a_loop =
  make_default_source "type Version(major: Loop)\n  derives Default\n"

let version_with_a_written_default =
  make_default_source
    "type Version(major: Key)\n\
     impl Default for Version {\n\
    \  fn default() -> Version {\n\
    \    check()\n\
    \  }\n\
     }\n"

let default_trait = Support.make_top_path "standard.core" "Default"

let derived_version_default =
  make_method (Derived { type_ = make_main_path "Version"; trait = default_trait }) "default" Static

let expect_recursion_group text ~of_:name ~expected =
  let database = build [ ("app.main", text) ] in
  let group =
    (Database.For_testing.make_proof_lookups database).list_recursion_group (make_main_path name)
  in
  let show_paths paths = String.concat "; " (List.map Path.show paths) in
  if not (List.equal Path.equal group expected) then
    Harness.fail "the recursion group of %s is [%s], not [%s]" name (show_paths group)
      (show_paths expected)

let make_level_source ~height =
  Printf.sprintf
    "trait Level {\n\
    \  fn height(self) -> Int64\n\n\
    \  fn raised(self) -> Int64 {\n\
    \    self.height()\n\
    \  }\n\
     }\n\n\
     type Shelf(height: Int64)\n\n\
     impl Level for Shelf {\n\
    \  fn height(self) -> Int64 {\n\
    \    %s\n\
    \  }\n\
     }\n\n\
     fn floor(shelf: Shelf) -> Int64 {\n\
    \  shelf.raised()\n\
     }\n"
    height

let make_shelf_method name =
  make_impl_method ~trait:(make_main_path "Level") ~for_type:(make_main_path "Shelf") name
    (Instance Read)

let raised_of_shelf = make_shelf_method "raised"

let propagate_with_lib ~before ~after =
  let settle files =
    let database = Support.make_database (Support.setup ~dependencies:[ ("app", "lib") ] files) in
    Database.For_testing.propagate database;
    database
  in
  let hot = settle before in
  let (), observed =
    Database.For_testing.observe (fun () ->
        Database.update hot (list_changes ~before ~after);
        Database.For_testing.propagate hot)
  in
  (match Database.For_testing.list_differences hot (settle after) with
  | [] -> ()
  | differences ->
      Harness.fail "the propagated database differs from a cold build in %s"
        (show_differences differences));
  observed.recomputed

let make_level_library ~provided =
  Printf.sprintf
    "public trait Level {\n\
    \  fn height(self) -> Int64\n\
     %s}\n\n\
     public type Shelf(height: Int64)\n\n\
     impl Level for Shelf {\n\
    \  fn height(self) -> Int64 {\n\
    \    self.height\n\
    \  }\n\
     }\n\n\
     public fn measure[Item: Level](item: Item) -> Int64 {\n\
    \  item.height()\n\
     }\n"
    provided

let level_user = "use lib.tools\nfn caller(shelf: tools.Shelf) -> Int64 { tools.measure(shelf) }\n"

let raised_of_library_shelf =
  make_impl_method ~module_:"lib.tools"
    ~trait:(Support.make_top_path "lib.tools" "Level")
    ~for_type:(Support.make_top_path "lib.tools" "Shelf")
    "raised" (Instance Read)

let make_step_library ~follow =
  Printf.sprintf
    "public trait Step {\n\
    \  fn step(self, node: Node) -> Int64\n\
     }\n\n\
     public type Node(next: any Step)\n\n\
     public fn follow(node: Node) -> Int64 {\n\
    \  %s\n\
     }\n"
    follow

let hop_stepping_through_a_library =
  "use lib.tools\n\n\
   type Hop()\n\n\
   impl tools.Step for Hop {\n\
  \  fn step(self, node: tools.Node) -> Int64 {\n\
  \    tools.follow(node)\n\
  \  }\n\
   }\n"

let step_of_hop =
  make_impl_method
    ~trait:(Support.make_top_path "lib.tools" "Step")
    ~for_type:(make_main_path "Hop") "step" (Instance Read)

let count_termination_obligations database ~of_:path =
  match
    Database.For_testing.find_proof
      (Support.prove database (Support.parse_file "app.main"))
      (make_key path)
  with
  | Some (Value (Obligations outcome)) ->
      List.length
        (List.filter
           (fun (obligation : Prover.Obligation.t) -> obligation.code = Termination)
           outcome.obligations)
  | Some (Value (Unsupported _ | Not_proven_here) | Failed | Blocked) | None ->
      failwith ("the proof of " ^ Path.show path ^ " makes no obligations")

let callee_and_caller =
  "fn callee(x: Int64) -> Int64 { x + 1 }\npublic fn caller() -> Int64 { callee(1) }\n"

let with_helper = [ ("app.main", callee_and_caller); ("app.extra", "fn helper() -> Int64 { 1 }\n") ]

let served_length_program =
  Filename.concat (Filename.dirname Sys.executable_name) "served_length/served_length.exe"

let request_served_length ~key request =
  match Process.run served_length_program [ key; request ] with
  | 0, output, _ -> String.split_on_char '\n' (String.trim output)
  | status, _, errors ->
      Harness.fail "served_length exited with status %d: %s" status (String.trim errors)

let () =
  Harness.test "a client whose background process exits without serving gets an error at once"
    (fun () ->
      Unix.putenv "TRUSS_CACHE" (Harness.make_scratch_directory "unserved-cache");
      let started = Unix.gettimeofday () in
      (match
         (Workspace.For_testing.call_starting ~program:"/usr/bin/false"
            ~key:(Harness.make_scratch_directory "unserved")
            ~report_progress:ignore 0
           : (int, string) result)
       with
      | Error _ -> ()
      | Ok _ -> Harness.fail "answered with no background process");
      let elapsed = Unix.gettimeofday () -. started in
      if elapsed > 2. then Harness.fail "the error took %.1f s" elapsed);
  Harness.test
    "a background process does not listen in a cache that other users can write, where they could \
     replace its socket" (fun () ->
      let cache = Harness.make_scratch_directory "writable-cache" in
      Unix.chmod cache 0o777;
      Unix.putenv "TRUSS_CACHE" cache;
      match Workspace.For_testing.listen ~key:(Harness.make_scratch_directory "refused") with
      | Ok socket ->
          Unix.close socket;
          Harness.fail "listened"
      | Error message ->
          if not (String.includes ~affix:cache message) then Harness.fail "refused with: %s" message);
  Harness.test
    "the files of a background process that ended without removing them are removed, and a running \
     process keeps its own" (fun () ->
      let cache = Harness.make_scratch_directory "ended-servers-cache" in
      Unix.putenv "TRUSS_CACHE" cache;
      let key = Harness.make_scratch_directory "still-served" in
      let wait_for_first_periodic_work () = ignore (request_served_length ~key "two") in
      Fun.protect
        ~finally:(fun () -> ignore (Workspace.stop_servers ()))
        (fun () ->
          ignore (request_served_length ~key "one");
          wait_for_first_periodic_work ();
          let servers = Filename.concat cache "servers" in
          let list_files () =
            List.sort compare
              (List.filter (( <> ) "server.log") (Array.to_list (Sys.readdir servers)))
          in
          let running = list_files () in
          let ended = "0123456789abcdef-0123456789abcdef" in
          List.iter
            (fun suffix ->
              Out_channel.with_open_bin (Filename.concat servers (ended ^ suffix)) ignore)
            [ ".key"; ".lock"; ".start" ];
          Workspace.For_testing.remove_ended_servers ();
          let remaining = list_files () in
          if remaining <> running then
            Harness.fail "kept %s, where the running process has %s" (String.concat ", " remaining)
              (String.concat ", " running);
          if request_served_length ~key "three" <> [ "progress working"; "length 5" ] then
            Harness.fail "the running process stopped answering"));
  Harness.test "a test executable given an argument exits at once instead of running its tests"
    (fun () ->
      Unix.putenv "TRUSS_TEST" "a name that no test has";
      match Process.run Sys.executable_name [ "--help" ] with
      | 2, output, errors ->
          if output <> "" then Harness.fail "printed %S" output;
          if not (String.includes ~affix:"takes no arguments, and was given `--help`" errors) then
            Harness.fail "reported %S" errors
      | status, _, _ -> Harness.fail "exited with status %d" status);
  Harness.test "the background process answers each request and sends its progress" (fun () ->
      Unix.putenv "TRUSS_CACHE" (Harness.make_scratch_directory "served-cache");
      let key = Harness.make_scratch_directory "served" in
      Fun.protect
        ~finally:(fun () -> ignore (Workspace.stop_servers ()))
        (fun () ->
          let answers = List.map (request_served_length ~key) [ "one"; "three"; "four" ] in
          let expected =
            List.map
              (fun length -> [ "progress working"; Printf.sprintf "length %d" length ])
              [ 3; 5; 4 ]
          in
          if answers <> expected then
            Harness.fail "answered %s" (String.concat "; " (List.map (String.concat ", ") answers))))

let () =
  Harness.test "a caller's checked body reads the callee's interface and not its body" (fun () ->
      expect_reads
        (check_text
           "fn callee(x: Int64) -> Int64 { x + 1 }\npublic fn caller() -> Int64 { callee(1) }\n")
        (Checked_body (make_main_key "caller"))
        ~includes:[ Stored (Interface (make_main_key "callee")) ]
        ~excludes:
          [
            Stored (Checked_body (make_main_key "callee"));
            Name (Tree (make_main_key "callee"));
            Stored (Resolved (make_main_key "callee", Body));
          ]);
  Harness.test "a contract reads no resolved names of its body" (fun () ->
      expect_reads
        (check_text "fn f(x: Int64) -> Int64 requires x > 0 { x + 1 }\n")
        (Contract (make_main_key "f"))
        ~includes:[ Stored (Resolved (make_main_key "f", Contract)) ]
        ~excludes:[ Stored (Resolved (make_main_key "f", Body)) ]);
  Harness.test "a checked body reads its callee's signature check" (fun () ->
      expect_reads
        (check_text
           "fn callee(x: Int64) -> Int64 { x + 1 }\npublic fn caller() -> Int64 { callee(1) }\n")
        (Checked_body (make_main_key "caller"))
        ~includes:[ Stored (Signature_check (make_main_key "callee")) ]
        ~excludes:[]);
  Harness.test "a checked body records one read of its callee's interface and signature check"
    (fun () ->
      let database =
        check_text
          "fn callee(x: Int64) -> Int64 { x + 1 }\npublic fn caller() -> Int64 { callee(1) }\n"
      in
      let callee = Database.For_testing.identify_key (make_main_key "callee") in
      let caller = locate (Checked_body (make_main_key "caller")) in
      match
        List.filter
          (fun ((target : Database.Kind.target), id, _) ->
            id = callee
            &&
            match target with
            | Fact fact ->
                List.mem (Database.Kind.show_fact fact) [ "interface"; "signature check" ]
            | Lookup _ | Entity _ | Selection _ -> false)
          (Database.For_testing.list_reads database caller.stage caller.id)
      with
      | [ _ ] -> ()
      | reads -> Harness.fail "recorded %d reads" (List.length reads));
  Harness.test
    "an edit that fails a callee's signature check, and leaves its interface as it was, checks the \
     caller's body again" (fun () ->
      let make_program visibility =
        [
          ( "app.main",
            visibility
            ^ "type Inner(value: Int64)\n\
               public fn callee(count: Int64, inner: Option[Inner] = None) -> Int64 { count }\n\
               public fn caller() -> Int64 { callee(1) }\n" );
        ]
      in
      expect_included
        (list_propagated ~before:(make_program "public ") ~after:(make_program ""))
        ~parts:[ Signature_check (make_main_key "callee"); Checked_body (make_main_key "caller") ]);
  Harness.test "a type's facts read interfaces and type facts, and no signature check" (fun () ->
      expect_reads
        (check_text "type Inner(value: Int64)\ntype Outer(inner: Inner)\n")
        (Type_facts (make_main_path "Outer"))
        ~includes:
          [
            Stored (Interface (make_main_key "Outer")); Stored (Type_facts (make_main_path "Inner"));
          ]
        ~excludes:
          [
            Stored (Signature_check (make_main_key "Outer"));
            Stored (Signature_check (make_main_key "Inner"));
          ]);
  Harness.test "a caller's checked body and proof read no place or text of the callee" (fun () ->
      let database = check_text callee_and_caller in
      ignore (Database.prove database (In_files [ Support.parse_file "app.main" ]));
      List.iter
        (fun part ->
          expect_reads database part ~includes:[]
            ~excludes:
              [ Name (Place (make_main_key "callee")); Name (Text (make_main_key "callee")) ])
        [ Checked_body (make_main_key "caller"); Proof (make_main_key "caller") ]);
  Harness.test "a package check reads no place" (fun () ->
      expect_reads
        (check_text "type Inner(value: Int64)\ntype Outer(inner: Inner)\n")
        (Type_check (make_main_key "Outer"))
        ~includes:[ Name (Tree (make_main_key "Outer")) ]
        ~excludes:[ Name (Place (make_main_key "Outer")); Name (Place (make_main_key "Inner")) ]);
  Harness.test "a reformat inside a definition recomputes only that definition's proof" (fun () ->
      expect_recomputed
        (list_propagated
           ~before:[ ("app.main", callee_and_caller) ]
           ~after:
             [
               ( "app.main",
                 "fn callee(x: Int64) -> Int64 {\n\
                 \  x + 1\n\
                  }\n\
                  public fn caller() -> Int64 { callee(1) }\n" );
             ])
        ~exactly:
          [
            Import_check (Support.parse_file "app.main");
            Declared (Support.parse_module "app.main");
            Parsed (Support.parse_file "app.main");
            Proof (make_main_key "callee");
          ]);
  Harness.test "moving a definition to another file of its module recomputes no definition's part"
    (fun () ->
      expect_recomputed
        (list_propagated
           ~before:[ ("app.main", callee_and_caller); ("app.main/other", "") ]
           ~after:
             [
               ("app.main", "public fn caller() -> Int64 { callee(1) }\n");
               ("app.main/other", "fn callee(x: Int64) -> Int64 { x + 1 }\n");
             ])
        ~exactly:
          [
            Import_check (Support.parse_file "app.main");
            Import_check (Support.parse_file "app.main/other");
            Declared (Support.parse_module "app.main");
            Parsed (Support.parse_file "app.main");
            Parsed (Support.parse_file "app.main/other");
          ]);
  Harness.test "an edit to a body recomputes no part of a caller" (fun () ->
      expect_untouched
        (list_propagated
           ~before:[ ("app.main", callee_and_caller) ]
           ~after:
             [
               ( "app.main",
                 "fn callee(x: Int64) -> Int64 { x + 2 }\n\
                  public fn caller() -> Int64 { callee(1) }\n" );
             ])
        ~is_excluded:(is_part_of [ make_main_path "caller" ]));
  Harness.test "an edit to a signature recomputes the callers" (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app.main", callee_and_caller) ]
          ~after:
            [
              ( "app.main",
                "fn callee(x: Int32) -> Int64 { 1 }\npublic fn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      if not (List.mem (locate (Checked_body (make_main_key "caller"))) recomputed) then
        Harness.fail "recomputed only %s" (show_parts recomputed));
  Harness.test "an edit to an ensures recomputes the callers' proofs and not their checks"
    (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app.main", callee_and_caller) ]
          ~after:
            [
              ( "app.main",
                "fn callee(x: Int64) -> Int64 ensures result == 1 { 1 }\n\
                 public fn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      if not (List.mem (locate (Proof (make_main_key "caller"))) recomputed) then
        Harness.fail "recomputed only %s" (show_parts recomputed);
      expect_untouched recomputed
        ~is_excluded:(( = ) (locate (Checked_body (make_main_key "caller")))));
  Harness.test "an edit to a constant recomputes the contracts whose patterns name it" (fun () ->
      let with_favorite variant =
        "public type Color =\n\
        \  | Red\n\
        \  | Green\n\
        \  derives Equal\n\n\
         public fn pick() -> Color\n\
        \  ensures match result {\n\
        \    app.main.favorite => true\n\
        \    Green => true\n\
        \  }\n\
         {\n\
        \  Color.Red\n\
         }\n\n\
         let favorite: Color = Color." ^ variant ^ "\n"
      in
      expect_included
        (list_propagated
           ~before:[ ("app.main", with_favorite "Red") ]
           ~after:[ ("app.main", with_favorite "Green") ])
        ~parts:[ Contract (make_main_key "pick") ]);
  Harness.test "adding the definition that a call names fixes the call" (fun () ->
      ignore
        (list_propagated
           ~before:[ ("app.main", "public fn caller() -> Int64 { callee(1) }\n") ]
           ~after:[ ("app.main", callee_and_caller) ]));
  Harness.test "saving between an edit and its proofs keeps the call graph whole" (fun () ->
      let with_store name =
        Printf.sprintf
          "fn %s(counts: mut Map[String, UInt64]) {\n\
          \  mut counts.insert(\"key\", value: 1)\n\
           }\n\n\
           public fn run() {\n\
          \  var counts: Map[String, UInt64] = [:]\n\
          \  %s(mut counts)\n\
           }\n"
          name name
      in
      let file = Support.parse_file "app.main" in
      let database = build [ ("app.main", "public fn run() {}\n") ] in
      List.iter
        (fun name ->
          Database.update database [ (file, Some (with_store name)) ];
          ignore (Support.prove database file))
        [ "store"; "put" ];
      match
        Database.For_testing.list_differences database (build [ ("app.main", with_store "put") ])
      with
      | [] -> ()
      | differences ->
          Harness.fail "the database differs from a cold build in %s" (show_differences differences));
  Harness.test "removing a definition deletes its parts and fails its callers" (fun () ->
      expect_untouched
        (list_propagated
           ~before:[ ("app.main", callee_and_caller) ]
           ~after:[ ("app.main", "public fn caller() -> Int64 { callee(1) }\n") ])
        ~is_excluded:(is_part_of [ make_main_path "callee" ]));
  Harness.test "a field that makes a type not plain recomputes the types that hold it" (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app.main", "type Inner(value: Int64)\ntype Outer(inner: Inner)\n") ]
          ~after:[ ("app.main", "type Inner(value: String)\ntype Outer(inner: Inner)\n") ]
      in
      if not (List.mem (locate (Type_facts (make_main_path "Outer"))) recomputed) then
        Harness.fail "recomputed only %s" (show_parts recomputed));
  Harness.test "a body that compares a type reads the impls of the type" (fun () ->
      expect_reads
        (check_text
           "type Box(value: Int64) derives Equal\n\
            fn same(left: Box, right: Box) -> Bool { left == right }\n")
        (Checked_body (make_main_key "same"))
        ~includes:[ Name (Impls_of_type (app, make_main_path "Box")) ]
        ~excludes:[]);
  Harness.test
    "a call that closes a cycle recomputes the proofs of the cycle's members and no other"
    (fun () ->
      let recomputed =
        list_propagated ~before:[ ("app.main", acyclic) ] ~after:[ ("app.main", cyclic) ]
      in
      expect_included recomputed
        ~parts:
          [
            Recursion_group (make_main_path "f");
            Recursion_group (make_main_path "g");
            Proof (make_main_key "f");
            Proof (make_main_key "g");
          ];
      expect_untouched recomputed ~is_excluded:(fun part ->
          is_part_of [ make_main_path "h" ] part || part = locate (Checked_body (make_main_key "f"))));
  Harness.test "removing the call that closes a cycle splits its recursion group" (fun () ->
      let recomputed =
        list_propagated ~before:[ ("app.main", cyclic) ] ~after:[ ("app.main", acyclic) ]
      in
      expect_included recomputed ~parts:[ Proof (make_main_key "f"); Proof (make_main_key "g") ];
      expect_untouched recomputed ~is_excluded:(fun part ->
          is_part_of [ make_main_path "h" ] part || part = locate (Checked_body (make_main_key "f"))));
  Harness.test
    "an impl that closes a cycle through a trait method recomputes the proofs on the cycle"
    (fun () ->
      expect_included
        (list_propagated
           ~before:[ ("app.main", stepper) ]
           ~after:[ ("app.main", stepper_that_runs) ])
        ~parts:[ Recursion_group (make_main_path "run"); Proof (make_main_key "run") ]);
  Harness.test "a function's call edges read the dependencies of no package" (fun () ->
      expect_reads
        (build [ ("app.main", stepper_that_runs) ])
        (Call_edges (make_main_path "run"))
        ~includes:[]
        ~excludes:[ Name (Dependencies app); Name (Dependencies Path.standard_package) ]);
  Harness.test
    "a construction that runs a field default that fails adds no call edge to the default's callee"
    (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app.main", make_configured_source "Config(size: 1)") ]
          ~after:[ ("app.main", make_configured_source "Config()") ]
      in
      expect_included recomputed ~parts:[ Call_edges (make_main_path "make") ];
      expect_untouched recomputed ~is_excluded:(fun computed -> computed.stage = Group_recursion));
  Harness.test "a derived method's call edges read its generated MIR" (fun () ->
      expect_reads
        (build [ ("app.main", version_deriving_over_a_key) ])
        (Call_edges derived_version_default)
        ~includes:[ Stored (Generated_mir derived_version_default) ]
        ~excludes:[]);
  Harness.test "a function that passes a derived impl where a bound needs one has a proof"
    (fun () ->
      let database = check_text version_deriving_over_a_key in
      let file = Support.parse_file "app.main" in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          match Database.For_testing.find_proof (Support.prove database file) declaration.key with
          | Some (Value _) -> ()
          | Some (Failed | Blocked) | None ->
              Harness.fail "%s has no proof" (Path.show declaration.key.path))
        ((Database.make_name_lookups database).list_declarations_in file));
  Harness.test
    "a field's type whose impl calls back joins the recursion group of a function that passes the \
     derived impl where a bound needs one" (fun () ->
      expect_recursion_group version_deriving_over_a_key ~of_:"check" ~expected:[];
      expect_recursion_group version_deriving_over_a_loop ~of_:"check"
        ~expected:
          [
            make_main_path "check";
            make_impl_method ~trait:default_trait ~for_type:(make_main_path "Loop") "default" Static;
            derived_version_default;
          ];
      expect_included
        (list_propagated
           ~before:[ ("app.main", version_deriving_over_a_key) ]
           ~after:[ ("app.main", version_deriving_over_a_loop) ])
        ~parts:
          [
            Call_edges derived_version_default;
            Recursion_group (make_main_path "check");
            Proof (make_main_key "check");
          ]);
  Harness.test
    "a trait leaving a type's `derives` list takes the derived method out of the call graph"
    (fun () ->
      expect_recursion_group version_with_a_written_default ~of_:"check"
        ~expected:
          [
            make_main_path "check";
            make_impl_method ~trait:default_trait ~for_type:(make_main_path "Version") "default"
              Static;
          ];
      expect_included
        (list_propagated
           ~before:[ ("app.main", version_deriving_over_a_key) ]
           ~after:[ ("app.main", version_with_a_written_default) ])
        ~parts:[ Recursion_group (make_main_path "check"); Proof (make_main_key "check") ];
      expect_included
        (list_propagated
           ~before:[ ("app.main", version_with_a_written_default) ]
           ~after:[ ("app.main", version_deriving_over_a_key) ])
        ~parts:[ Call_edges derived_version_default; Proof (make_main_key "check") ]);
  Harness.test "an inherited method's call edges read the MIR of its trait's provided body"
    (fun () ->
      expect_reads
        (build [ ("app.main", make_level_source ~height:"self.height") ])
        (Call_edges raised_of_shelf)
        ~includes:
          [
            Stored
              (Body_mir (make_key (make_method (make_main_path "Level") "raised" (Instance Read))));
          ]
        ~excludes:[]);
  Harness.test
    "an impl's method that calls the caller of a method the impl inherits joins their recursion \
     group" (fun () ->
      expect_recursion_group (make_level_source ~height:"self.height") ~of_:"floor" ~expected:[];
      expect_recursion_group
        (make_level_source ~height:"floor(self)")
        ~of_:"floor"
        ~expected:[ make_main_path "floor"; make_shelf_method "height"; raised_of_shelf ];
      expect_included
        (list_propagated
           ~before:[ ("app.main", make_level_source ~height:"self.height") ]
           ~after:[ ("app.main", make_level_source ~height:"floor(self)") ])
        ~parts:[ Recursion_group raised_of_shelf; Proof (make_main_key "floor") ]);
  Harness.test "removing a function that a function of its package calls matches a cold build"
    (fun () ->
      ignore
        (list_propagated
           ~before:[ ("app.main", callee_and_caller) ]
           ~after:[ ("app.main", "fn caller() -> Int64 { callee(1) }\n") ]));
  Harness.test "removing a function that another package calls matches a cold build" (fun () ->
      ignore
        (propagate_with_lib ~before:tool_user
           ~after:[ List.hd tool_user; ("lib.tools", "public fn other() -> Int64 { 2 }\n") ]));
  Harness.test "removing an impl that a call through `any` reaches matches a cold build" (fun () ->
      ignore
        (list_propagated
           ~before:[ ("app.main", stepper_that_runs) ]
           ~after:[ ("app.main", stepper) ]));
  Harness.test
    "removing a provided method that another package's call graph reaches through an impl matches \
     a cold build" (fun () ->
      let provided = "\n  fn raised(self) -> Int64 {\n    self.height()\n  }\n" in
      let with_raised = [ ("app.main", level_user); ("lib.tools", make_level_library ~provided) ]
      and without_raised =
        [ ("app.main", level_user); ("lib.tools", make_level_library ~provided:"") ]
      in
      expect_included
        (propagate_with_lib ~before:without_raised ~after:with_raised)
        ~parts:[ Call_edges raised_of_library_shelf ];
      ignore (propagate_with_lib ~before:with_raised ~after:without_raised));
  Harness.test
    "a dependency's body that fails reports its error and hides a recursion through it only until \
     the body is fixed" (fun () ->
      let with_follow follow =
        [ ("app.main", hop_stepping_through_a_library); ("lib.tools", make_step_library ~follow) ]
      in
      let failing = with_follow "node.next.step(node) + missing"
      and fixed = with_follow "node.next.step(node)" in
      let settle files =
        Support.make_database (Support.setup ~dependencies:[ ("app", "lib") ] files)
      in
      let with_failing_body = settle failing in
      (match
         Support.list_codes
           (Database.list_file_diagnostics with_failing_body (Support.parse_file "lib.tools"))
       with
      | [ "resolve.unknown_name" ] -> ()
      | codes -> Harness.fail "the dependency reports [%s]" (String.concat ", " codes));
      if count_termination_obligations with_failing_body ~of_:step_of_hop <> 0 then
        Harness.fail "the proof makes a termination obligation while the body fails";
      expect_included
        (propagate_with_lib ~before:failing ~after:fixed)
        ~parts:
          [ Call_edges (Support.make_top_path "lib.tools" "follow"); Proof (make_key step_of_hop) ];
      if count_termination_obligations (settle fixed) ~of_:step_of_hop <> 1 then
        Harness.fail "the proof makes no termination obligation for the recursion");
  Harness.test
    "adding a file and then removing it recomputes no part of the other file's definitions"
    (fun () ->
      let without_helper = [ ("app.main", callee_and_caller) ] in
      let hot = build without_helper in
      List.iter
        (fun (before, after) ->
          expect_untouched (propagate hot ~before ~after).recomputed
            ~is_excluded:(is_part_of [ make_main_path "callee"; make_main_path "caller" ]))
        [ (without_helper, with_helper); (with_helper, without_helper) ]);
  Harness.test "reformatting a callee recomputes no caller's proof" (fun () ->
      expect_recomputed
        (list_propagated
           ~before:
             [
               ( "app.main",
                 "fn callee(x: Int64) -> Int64 requires x > 0 { x }\n\
                  public fn caller() -> Int64 { callee(1) }\n" );
             ]
           ~after:
             [
               ( "app.main",
                 "fn callee(x: Int64) -> Int64\n\
                 \  requires x > 0\n\
                  {\n\
                 \  x\n\
                  }\n\
                  public fn caller() -> Int64 { callee(1) }\n" );
             ])
        ~exactly:
          [
            Import_check (Support.parse_file "app.main");
            Declared (Support.parse_module "app.main");
            Parsed (Support.parse_file "app.main");
          ]);
  Harness.test "an edit to a callee's body recomputes its lowered code and not its caller's"
    (fun () ->
      let recomputed =
        list_propagated_with_roots ~roots:[ "caller" ]
          ~before:[ ("app.main", callee_and_caller) ]
          ~after:
            [
              ( "app.main",
                "fn callee(x: Int64) -> Int64 { x + 2 }\n\
                 public fn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      expect_included recomputed
        ~parts:[ make_lowered "callee"; make_test_key "callee"; make_test_key "caller" ];
      expect_untouched recomputed ~is_excluded:(( = ) (locate (make_lowered "caller"))));
  let edited_callee =
    [
      ( "app.main",
        "fn callee(x: Int64) -> Int64 { x + 2 }\npublic fn caller() -> Int64 { callee(1) }\n" );
      ("app.other", "public fn other() -> Int64 { 1 }\n");
    ]
  and callee_caller_and_other =
    [ ("app.main", callee_and_caller); ("app.other", "public fn other() -> Int64 { 1 }\n") ]
  in
  let other = Unit (Release, make_code_item_of (Support.make_top_path "app.other" "other")) in
  Harness.test
    "an edit to a callee's body renders the callee's development unit and not its caller's"
    (fun () ->
      expect_recomputed
        (list_rendered_after_edit ~roots:[ "caller" ] ~before:callee_caller_and_other
           ~after:edited_callee Development)
        ~exactly:[ make_unit Development "callee" ]);
  Harness.test "an edit to a file renders the release units of that file's items and of no other"
    (fun () ->
      let hot = build ~roots:[ "caller" ] callee_caller_and_other in
      Database.For_testing.add_root hot
        (make_code_item_of (Support.make_top_path "app.other" "other"));
      Database.For_testing.propagate hot;
      let list_release () =
        ignore
          (list_linked hot Release
             [
               make_code_item "caller";
               make_code_item_of (Support.make_top_path "app.other" "other");
             ])
      in
      list_release ();
      let (), observed =
        Database.For_testing.observe (fun () ->
            Database.update hot (list_changes ~before:callee_caller_and_other ~after:edited_callee);
            Database.For_testing.propagate hot;
            list_release ())
      in
      let rendered =
        List.filter
          (fun (computed : Database.For_testing.computed) -> computed.stage = Render Release)
          observed.recomputed
      in
      expect_included rendered ~parts:[ make_unit Release "callee"; make_unit Release "caller" ];
      expect_untouched rendered ~is_excluded:(( = ) (locate other)));
  Harness.test "listing the linked items of a program again renders no unit" (fun () ->
      let files = [ ("app.main", callee_and_caller) ] in
      List.iter
        (fun profile ->
          expect_recomputed
            (list_rendered_after_edit ~roots:[ "caller" ] ~before:files ~after:files profile)
            ~exactly:[])
        [ Profile.Development; Release ]);
  Harness.test "a field added to a type renders the development units that define the type"
    (fun () ->
      let make_program fields =
        [
          ( "app.main",
            "type Pair(" ^ fields
            ^ ")\n\
               fn pass(pair: Pair) -> Pair { pair }\n\
               fn unrelated() -> Int64 { 1 }\n\
               fn caller(pair: Pair) -> Int64 { unrelated() + pass(pair).first }\n" );
        ]
      in
      let rendered =
        list_rendered_after_edit ~roots:[ "caller" ] ~before:(make_program "first: Int64")
          ~after:(make_program "first: Int64, second: Int64")
          Development
      in
      expect_included rendered ~parts:[ make_unit Development "pass" ];
      expect_untouched rendered ~is_excluded:(( = ) (locate (make_unit Development "unrelated"))));
  Harness.test "a callee that leaves a program leaves the development units of the items that stay"
    (fun () ->
      expect_recomputed
        (list_rendered_after_edit ~roots:[ "caller" ]
           ~before:[ ("app.main", callee_and_caller) ]
           ~after:
             [
               ( "app.main",
                 "fn callee(x: Int64) -> Int64 { x + 1 }\npublic fn caller() -> Int64 { 1 }\n" );
             ]
           Development)
        ~exactly:[ make_unit Development "caller" ]);
  Harness.test "a call that is removed with its callee collects the callee's lowered code"
    (fun () ->
      expect_untouched
        (list_propagated_with_roots ~roots:[ "caller" ]
           ~before:[ ("app.main", callee_and_caller) ]
           ~after:[ ("app.main", "fn caller() -> Int64 { 1 }\n") ])
        ~is_excluded:(( = ) (locate (make_lowered "callee"))));
  Harness.test "a removed reference collects exactly the items that only it reached" (fun () ->
      let make_program test =
        [
          ( "app.main",
            "fn shared() -> Int64 { 1 }\n\
             fn only() -> Int64 { shared() + 1 }\n\
             fn kept() -> Int64 { shared() }\n\
             test \"sums\" {\n\
            \  assert " ^ test ^ "\n}\n" );
        ]
      in
      let before = make_program "kept() + only() == 3" in
      let after = make_program "kept() == 1" in
      let observed = propagate (build before) ~before ~after in
      if observed.collected <> [ Database.For_testing.identify_item (make_code_item "only") ] then
        Harness.fail "collected %d items" (List.length observed.collected);
      expect_untouched observed.recomputed ~is_excluded:(fun part ->
          List.mem part (List.map locate [ make_lowered "shared"; make_lowered "kept" ])));
  Harness.test "removing a type collects the items at that type without computing them" (fun () ->
      let make_program shape =
        [
          ( "app.main",
            shape
            ^ "test \"lists\" {\n\
              \  let shapes = [Shape(size: 1)]\n\
              \  assert shapes.length() == 1\n\
               }\n" );
        ]
      in
      let before = make_program "type Shape(size: Int64)\n" and after = make_program "" in
      let hot = build before in
      let items_at_shape =
        List.filter_map
          (fun item ->
            if String.includes ~affix:"[Shape]" (Lowered.Item.to_string item) then
              Some (Database.For_testing.identify_item item)
            else None)
          (Database.For_testing.list_items hot)
      in
      if items_at_shape = [] then Harness.fail "no item is at the type";
      expect_untouched (propagate hot ~before ~after).recomputed ~is_excluded:(fun computed ->
          (computed.stage = Lower || computed.stage = Key_tests)
          && List.mem computed.id items_at_shape));
  Harness.test "the key of an item names every type defined as todo that the item reaches"
    (fun () ->
      let database =
        build ~roots:[ "both" ]
          [
            ( "app.main",
              "type First = todo\n\
               type Second = todo\n\
               fn first() -> Option[First] { None }\n\
               fn second() -> Option[Second] { None }\n\
               fn has_first() -> Bool { first().is_none() }\n\
               fn has_second() -> Bool { second().is_none() }\n\
               fn both() -> Bool { has_first() && has_second() }\n" );
          ]
      in
      match Database.find_lowered_lookups database [ app ] with
      | Error message -> Harness.fail "%s" message
      | Ok lookups -> (
          match lookups.read_test_key (make_code_item "both") with
          | Error (Todo_types types) ->
              Harness.expect_strings
                ~expected:[ "app.main.First"; "app.main.Second" ]
                (List.map Path.show types)
          | Ok _ | Error (Unsupported _) -> Harness.fail "the key names no type defined as todo"));
  Harness.test
    "an edit to a function and to one that it reaches through an unchanged function lowers both"
    (fun () ->
      let make_program ~top ~bottom =
        [
          ( "app.main",
            Printf.sprintf
              "fn bottom() -> Int64 { %s }\n\
               fn middle() -> Int64 { bottom() }\n\
               fn top() -> Int64 { middle() + %s }\n"
              bottom top );
        ]
      in
      let recomputed =
        list_propagated_with_roots ~roots:[ "top" ]
          ~before:(make_program ~top:"1" ~bottom:"1")
          ~after:(make_program ~top:"2" ~bottom:"2")
      in
      expect_included recomputed ~parts:[ make_lowered "top"; make_lowered "bottom" ];
      expect_untouched recomputed ~is_excluded:(( = ) (locate (make_lowered "middle"))));
  Harness.test
    "lowering the code that the tests of one package reach lowers no code of a package that it \
     does not depend on" (fun () ->
      let make_tested package =
        ( package ^ ".main",
          "fn helper() -> Int64 { 1 }\ntest \"helps\" {\n  assert helper() == 1\n}\n" )
      in
      let database =
        Support.make_database (Support.setup [ make_tested "app"; make_tested "far" ])
      in
      let lowered_helper package =
        Lowered (make_code_item_of (Support.make_top_path (package ^ ".main") "helper"))
      in
      let lookups, observed =
        Database.For_testing.observe (fun () -> Database.find_lowered_lookups database [ app ])
      in
      if Result.is_error lookups then Harness.fail "the host builds no code";
      expect_included observed.recomputed ~parts:[ lowered_helper "app" ];
      expect_untouched observed.recomputed ~is_excluded:(( = ) (locate (lowered_helper "far"))));
  Harness.test
    "keying the tests of one package after an edit to a package that it depends on and to a third \
     package keys no item of the third" (fun () ->
      let make_user package body =
        ( package ^ ".main",
          "use lib.tools\nfn helper() -> Int64 { tools.shared() + " ^ body
          ^ " }\ntest \"helps\" {\n  assert helper() == 1\n}\n" )
      in
      let make_packages ~shared ~far =
        [
          ("lib.tools", "public fn shared() -> Int64 { " ^ shared ^ " }\n");
          make_user "app" "0";
          make_user "far" far;
        ]
      in
      let build_packages files =
        let database =
          Support.make_database
            (Support.setup ~dependencies:[ ("app", "lib"); ("far", "lib") ] files)
        in
        Database.For_testing.propagate database;
        database
      in
      let before = make_packages ~shared:"1" ~far:"0"
      and after = make_packages ~shared:"2" ~far:"1" in
      let hot = build_packages before in
      Database.update hot (list_changes ~before ~after);
      let lookups, observed =
        Database.For_testing.observe (fun () -> Database.find_lowered_lookups hot [ app ])
      in
      if Result.is_error lookups then Harness.fail "the host builds no code";
      let helper package = make_code_item_of (Support.make_top_path (package ^ ".main") "helper") in
      expect_included observed.recomputed ~parts:[ Test_key (helper "app") ];
      expect_untouched observed.recomputed ~is_excluded:(( = ) (locate (Test_key (helper "far"))));
      Database.For_testing.propagate hot;
      match Database.For_testing.list_differences hot (build_packages after) with
      | [] -> ()
      | differences ->
          Harness.fail "the propagated database differs from a cold build in %s"
            (show_differences differences));
  Harness.test "defining a type that was todo lowers the code that reaches it again" (fun () ->
      let make_program definition =
        [
          ( "app.main",
            "type Session" ^ definition
            ^ "\n\
               fn none() -> Option[Session] { None }\n\
               test \"reaches\" {\n\
              \  assert none().is_none()\n\
               }\n" );
        ]
      in
      expect_included
        (list_propagated ~before:(make_program " = todo") ~after:(make_program "(id: Int64)"))
        ~parts:[ make_lowered "none" ]);
  Harness.test
    "a type that comes to contain itself in place fails the lowered code that lays it out"
    (fun () ->
      let make_program held =
        [ ("app.main", "type Chain(next: " ^ held ^ ")\nfn size(chain: Chain) -> Int64 { 1 }\n") ]
      in
      expect_included
        (list_propagated_with_roots ~roots:[ "size" ] ~before:(make_program "List[Chain]")
           ~after:(make_program "Option[Chain]"))
        ~parts:[ make_lowered "size" ]);
  Harness.test
    "an edit to a constant recomputes the constants that fold it, which lower no copy of it"
    (fun () ->
      let make_constants first =
        [
          ( "app.main",
            "let first: Int64 = " ^ first
            ^ "\nlet second: Int64 = first + 1\nfn read() -> Int64 { second }\n" );
        ]
      in
      let recomputed =
        list_propagated_with_roots ~roots:[ "read" ] ~before:(make_constants "1")
          ~after:(make_constants "2")
      in
      expect_included recomputed ~parts:[ Lowered (Constant (make_main_path "second")) ];
      expect_untouched recomputed
        ~is_excluded:(( = ) (locate (Lowered (Constant (make_main_path "first"))))));
  Harness.test "adding a dependency to a manifest fixes the dependent's use of it" (fun () ->
      expect_included
        (lay_out_again ~before:(Support.setup tool_user)
           ~after:(Support.setup ~dependencies:[ ("app", "lib") ] tool_user)
           ())
        ~parts:[ Declared (Support.parse_module "app.main"); Checked_body (make_main_key "caller") ]);
  Harness.test "adding a package and then removing it matches a cold build each time" (fun () ->
      let alone = Support.setup [ ("app.main", "fn caller() -> Int64 { 1 }\n") ] in
      let with_lib = Support.setup ~dependencies:[ ("app", "lib") ] tool_user in
      ignore (lay_out_again ~before:alone ~after:with_lib ());
      expect_untouched
        (lay_out_again ~before:with_lib ~after:alone ())
        ~is_excluded:(is_part_of [ Support.make_top_path "lib.tools" "helper" ]));
  Harness.test "a new version of a loaded package recomputes only the readers of what changed"
    (fun () ->
      let make_version second =
        load_package
          [
            ( "lib.tools",
              "public fn first() -> Int64 { 1 }\npublic fn second() -> " ^ second ^ " { 2 }\n" );
          ]
      in
      let app =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [
            ( "app.main",
              "use lib.tools\n\
               fn uses_first() -> Int64 { tools.first() }\n\
               fn uses_second() -> Int64 { 1 }\n\
               fn calls_second() { tools.second() }\n" );
          ]
      in
      let recomputed =
        lay_out_again
          ~loaded:([ make_version "Int64" ], [ make_version "Int32" ])
          ~before:app ~after:app ()
      in
      expect_included recomputed ~parts:[ Checked_body (make_main_key "calls_second") ];
      expect_untouched recomputed
        ~is_excluded:(is_part_of [ make_main_path "uses_first"; make_main_path "uses_second" ]));
  Harness.test
    "reformatting an invariant recomputes the derived Deserialize and none of its readers"
    (fun () ->
      let make_signup invariant =
        [
          ( "app.main",
            "use standard.serialization\ntype Signup(age: UInt32)\n  invariant " ^ invariant
            ^ "\n  derives serialization.Deserialize\n" );
        ]
      in
      expect_recomputed
        (list_propagated ~before:(make_signup "age >= 13") ~after:(make_signup "age  >=\t13"))
        ~exactly:
          [
            Generated_mir
              (make_method
                 (Derived
                    {
                      type_ = make_main_path "Signup";
                      trait = Support.make_top_path "standard.serialization" "Deserialize";
                    })
                 "deserialize" Static);
            Import_check (Support.parse_file "app.main");
            Declared (Support.parse_module "app.main");
            Parsed (Support.parse_file "app.main");
          ])

let make_lowered_program test =
  [
    ( "app.main",
      "type Box(value: Int64) derives Equal\n\
       let base: Int64 = 2\n\
       fn shared() -> Int64 { base }\n\
       fn only() -> Int64 { shared() + 1 }\n\
       fn kept() -> Int64 { shared() }\n\
       fn same(left: Box, right: Box) -> Bool { left == right }\n\
       test \"sums\" {\n\
      \  assert " ^ test ^ "\n}\n" );
    ("app.main/cycle", cyclic);
  ]

let () =
  Harness.test "a database saved after a cold build and reopened recomputes nothing" (fun () ->
      let files = make_lowered_program "kept() + only() == 5" in
      let path = make_database_path () in
      Database.close (build_saved ~roots:[ "same" ] path files);
      expect_recomputed (observe_reopen ~roots:[ "same" ] path files).recomputed ~exactly:[]);
  Harness.test "a database reopened with a changed file recomputes what propagating the change does"
    (fun () ->
      let before = [ ("app.main", callee_and_caller) ] in
      let after =
        [
          ( "app.main",
            "fn callee(x: Int64) -> Int64 { x + 2 }\npublic fn caller() -> Int64 { callee(1) }\n" );
        ]
      in
      let path = make_database_path () in
      Database.close (build_saved path before);
      expect_same_units (observe_reopen path after).recomputed ~as_:(list_propagated ~before ~after));
  Harness.test "a database reopened without a file it saved removes the file's definitions"
    (fun () ->
      let path = make_database_path () in
      Database.close (build_saved path with_helper);
      ignore (observe_reopen path [ ("app.main", callee_and_caller) ]));
  Harness.test "a database saved after a change set reopens as the propagated database" (fun () ->
      let before = make_lowered_program "kept() + only() == 5" in
      let after = make_lowered_program "kept() == 2" in
      let path = make_database_path () in
      let hot = build_saved path before in
      Database.commit hot;
      ignore (propagate hot ~before ~after);
      Database.close hot;
      expect_recomputed (observe_reopen path after).recomputed ~exactly:[]);
  Harness.test "a database saved after a partial drain reopens with its stale parts" (fun () ->
      let before = make_lowered_program "kept() + only() == 5" in
      let after = make_lowered_program "kept() == 2" in
      let path = make_database_path () in
      let hot = build_saved path before in
      Database.update hot (list_changes ~before ~after);
      let (), propagated =
        Database.For_testing.observe (fun () -> Database.For_testing.propagate (Database.copy hot))
      in
      Database.close hot;
      expect_same_units (observe_reopen path after).recomputed ~as_:propagated.recomputed);
  Harness.test
    "a database saved before the call graph drops removed definitions reopens without their \
     recursion groups" (fun () ->
      let before = [ ("app.main", cyclic) ] in
      let after = [ ("app.main", "fn h() -> Int64 { 1 }\n") ] in
      let path = make_database_path () in
      let hot = build_saved path before in
      Database.update hot (list_changes ~before ~after);
      Database.close hot;
      ignore (observe_reopen path after));
  Harness.test "a database saved after a package is removed reopens without the package" (fun () ->
      let with_lib = Support.setup ~dependencies:[ ("app", "lib") ] tool_user in
      let alone = [ ("app.main", "fn caller() -> Int64 { 1 }\n") ] in
      let path = make_database_path () in
      let hot = open_saved path with_lib in
      Database.relayout hot ~loaded:[ Lazy.force standard ] (Support.setup alone);
      Database.For_testing.propagate hot;
      Database.close hot;
      expect_recomputed (observe_reopen path alone).recomputed ~exactly:[]);
  Harness.test
    "a database closed before a change set commits reopens as it was before the change set"
    (fun () ->
      let before = [ ("app.main", callee_and_caller) ] in
      let after = [ ("app.main", "fn h() -> Int64 { 1 }\n") ] in
      let path = make_database_path () in
      let hot = build_saved path before in
      Database.commit hot;
      Database.update hot (list_changes ~before ~after);
      Database.close_uncommitted hot;
      expect_recomputed (observe_reopen path before).recomputed ~exactly:[]);
  Harness.test "a database written by another compiler is rebuilt" (fun () ->
      let packages = Support.setup [ ("app.main", callee_and_caller) ] in
      let path = make_database_path () in
      Database.close (open_saved ~compiler:"another compiler" path packages);
      let database, observed = Database.For_testing.observe (fun () -> open_saved path packages) in
      Database.close database;
      expect_included observed.recomputed ~parts:[ Checked_body (make_main_key "caller") ]);
  Harness.test "a database file that SQLite cannot read is rebuilt" (fun () ->
      let packages = Support.setup [ ("app.main", callee_and_caller) ] in
      let path = make_database_path () in
      Database.close (open_saved path packages);
      File_system.write path "not a database";
      let database, observed = Database.For_testing.observe (fun () -> open_saved path packages) in
      Database.close database;
      expect_included observed.recomputed ~parts:[ Checked_body (make_main_key "caller") ])

let project files =
  let root = Harness.make_scratch_directory "project" in
  Harness.write_files root
    (("truss.toml", "[package]\nname = \"app\"\ntruss = \"0.1\"\n")
    :: List.map (fun (path, text) -> (path ^ ".truss", text)) files);
  root

let open_workspace root =
  match Workspace.take_snapshot root with
  | Ok (snapshot, _) -> snapshot
  | Error message -> failwith message

let settle_on_disk root =
  let (snapshot, database), observed =
    Database.For_testing.observe (fun () ->
        let snapshot = open_workspace root in
        let database = Workspace.open_database snapshot in
        Database.For_testing.propagate database;
        (snapshot, database))
  in
  let cold = Workspace.For_testing.build_cold_database snapshot in
  Database.For_testing.propagate cold;
  (match Database.For_testing.list_differences database cold with
  | [] -> ()
  | differences ->
      Harness.fail "the database in .truss differs from a cold build in %s"
        (show_differences differences));
  observed.recomputed

let edited_body =
  "fn callee(x: Int64) -> Int64 { x + 2 }\npublic fn caller() -> Int64 { callee(1) }\n"

let () =
  Harness.test "a database written to .truss and reopened recomputes nothing" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settle_on_disk root);
      Workspace.flush ();
      expect_recomputed (settle_on_disk root) ~exactly:[];
      Workspace.flush ());
  Harness.test "a copy of a project with a changed file recomputes what propagating the change does"
    (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settle_on_disk root);
      Workspace.flush ();
      let copy = Harness.make_scratch_directory "copy" in
      if Sys.command (Filename.quote_command "cp" [ "-R"; root ^ "/."; copy ]) <> 0 then
        Harness.fail "cannot copy %s" root;
      Harness.write_files copy [ ("main/main.truss", edited_body) ];
      let copied = settle_on_disk copy in
      Workspace.flush ();
      ignore (open_workspace root);
      Harness.write_files root [ ("main/main.truss", edited_body) ];
      let propagated = settle_on_disk root in
      Workspace.flush ();
      expect_same_units copied ~as_:propagated)

let expect_cold_snapshot database snapshot =
  let cold = Workspace.For_testing.build_cold_database snapshot in
  Database.For_testing.propagate cold;
  match Database.For_testing.list_differences database cold with
  | [] -> ()
  | differences ->
      Harness.fail "the database differs from a cold build in %s" (show_differences differences)

let () =
  let follow_overlay_and_return name changes ~check_overlay =
    Harness.test name (fun () ->
        let root = project [ ("main/main", callee_and_caller) ] in
        let snapshot = open_workspace root in
        let worktree = Workspace.open_database snapshot in
        Database.For_testing.propagate worktree;
        let overlay = Workspace.make_overlay snapshot changes in
        let database, observed =
          Database.For_testing.observe (fun () ->
              let database = Workspace.open_database overlay in
              Database.For_testing.propagate database;
              database)
        in
        if database != worktree then Harness.fail "the overlay has a database of its own";
        check_overlay observed.Database.For_testing.recomputed;
        expect_cold_snapshot database overlay;
        let saved = Workspace.open_database snapshot in
        Database.For_testing.propagate saved;
        expect_cold_snapshot saved snapshot;
        Workspace.flush ())
  in
  follow_overlay_and_return
    "the worktree's database follows an overlay of its files, and then the saved files again"
    [ ("main/main.truss", Some edited_body) ]
    ~check_overlay:(fun recomputed ->
      expect_included recomputed ~parts:[ Checked_body (make_main_key "callee") ];
      expect_untouched recomputed ~is_excluded:(is_part_of [ make_main_path "caller" ]));
  follow_overlay_and_return
    "the worktree's database follows an overlay that renames the package, and then the saved files \
     again"
    [ ("truss.toml", Some "[package]\nname = \"tool\"\ntruss = \"0.1\"\n") ]
    ~check_overlay:ignore;
  Harness.test "a second overlay keeps the proofs that the first computed" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      let snapshot = open_workspace root in
      let prove text =
        (snd
           (Database.For_testing.observe (fun () ->
                ignore
                  (Database.prove
                     (Workspace.open_database
                        (Workspace.make_overlay snapshot [ ("main/main.truss", Some text) ]))
                     (In_files [ Support.parse_file "app.main" ])))))
          .recomputed
      in
      expect_included (prove edited_body) ~parts:[ Proof (make_main_key "caller") ];
      expect_untouched
        (prove (edited_body ^ "\n"))
        ~is_excluded:(fun computed -> computed.stage = Prove);
      Workspace.flush ());
  Harness.test "a database that holds an overlay is closed without a commit" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settle_on_disk root);
      Workspace.flush ();
      let snapshot = open_workspace root in
      let overlay = Workspace.make_overlay snapshot [ ("main/main.truss", Some edited_body) ] in
      Database.For_testing.propagate (Workspace.open_database overlay);
      Workspace.flush ();
      expect_recomputed (settle_on_disk root) ~exactly:[];
      Workspace.flush ());
  Harness.test "an overlay whose files equal the saved files is committed as the saved files"
    (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      let snapshot = open_workspace root in
      let overlay =
        Workspace.make_overlay snapshot [ ("main/main.truss", Some callee_and_caller) ]
      in
      Database.For_testing.propagate (Workspace.open_database overlay);
      Workspace.flush ();
      expect_recomputed (settle_on_disk root) ~exactly:[];
      Workspace.flush ())

let show_counts (counts : Database.counts) =
  Printf.sprintf "%s: computed %d, unchanged %d, writes %d, reads %d, distinct reads %d" counts.kind
    counts.computed counts.unchanged counts.writes counts.reads counts.distinct_reads

let extract_counts counts kind =
  Option.value
    (List.find_opt (fun (counts : Database.counts) -> counts.kind = kind) counts)
    ~default:{ kind; computed = 0; unchanged = 0; writes = 0; reads = 0; distinct_reads = 0 }

let count_propagation hot ~before ~after =
  snd
    (Database.count (fun () ->
         Database.update hot (list_changes ~before ~after);
         Database.For_testing.propagate hot))

let count_cold_build files =
  snd
    (Database.count (fun () ->
         Database.For_testing.propagate (Support.make_database (Support.setup files))))

let () =
  Harness.test "a propagation with no stale part counts no work" (fun () ->
      let database = build [ ("app.main", callee_and_caller) ] in
      match snd (Database.count (fun () -> Database.For_testing.propagate database)) with
      | [] -> ()
      | counts -> Harness.fail "counted %s" (String.concat "; " (List.map show_counts counts)));
  Harness.test
    "a computed part whose value comes out unchanged is counted as unchanged, not written"
    (fun () ->
      let before = [ ("app.main", callee_and_caller) ] in
      let after =
        [
          ( "app.main",
            "fn callee(x: Int64) -> Int64 {\n\
            \  x + 1\n\
             }\n\
             public fn caller() -> Int64 { callee(1) }\n" );
        ]
      in
      let import_check =
        extract_counts (count_propagation (build before) ~before ~after) "import check"
      in
      if (import_check.computed, import_check.unchanged, import_check.writes) <> (1, 1, 0) then
        Harness.fail "counted %s" (show_counts import_check));
  Harness.test "a lookup that a computation repeats is a read and not another distinct read"
    (fun () ->
      let count_checked_bodies reader_body =
        extract_counts
          (count_cold_build
             [
               ( "app.main",
                 "type Point(x: Int64, y: Int64)\nfn reader(point: Point) -> Int64 { " ^ reader_body
                 ^ " }\n" );
             ])
          "checked body"
      in
      let once = count_checked_bodies "point.x + point.y"
      and twice = count_checked_bodies "point.x + point.y + point.x" in
      if twice.distinct_reads <> once.distinct_reads || twice.reads <= once.reads then
        Harness.fail "counted %s with two field reads and %s with three" (show_counts once)
          (show_counts twice));
  Harness.test "removing a definition counts the removal of its checked body as a write" (fun () ->
      let before = [ ("app.main", "fn unused() -> Int64 { 1 }\nfn kept() -> Int64 { 2 }\n") ] in
      let after = [ ("app.main", "fn kept() -> Int64 { 2 }\n") ] in
      let checked_bodies =
        extract_counts (count_propagation (build before) ~before ~after) "checked body"
      in
      if (checked_bodies.computed, checked_bodies.writes) <> (0, 1) then
        Harness.fail "counted %s" (show_counts checked_bodies));
  Harness.test "counting an operation counts the work of a database that the operation copies"
    (fun () ->
      let before = [ ("app.main", callee_and_caller) ] in
      let after = [ ("app.main", edited_body) ] in
      let hot = build before in
      let _, counts =
        Database.count (fun () ->
            let trial = Database.copy hot in
            Database.update trial (list_changes ~before ~after);
            Database.For_testing.propagate trial)
      in
      let checked_bodies = extract_counts counts "checked body" in
      if checked_bodies.computed <> 1 then Harness.fail "counted %s" (show_counts checked_bodies))

let () =
  Harness.test "a module whose declarations come out unchanged is counted as unchanged, not written"
    (fun () ->
      let before = [ ("app.main", callee_and_caller) ] in
      let after = [ ("app.main", callee_and_caller ^ "\n") ] in
      let declarations =
        extract_counts (count_propagation (build before) ~before ~after) "declarations"
      in
      if (declarations.computed, declarations.unchanged, declarations.writes) <> (1, 1, 0) then
        Harness.fail "counted %s" (show_counts declarations))

let () =
  Harness.test "adding a file to a module recomputes the namespace, which reads the files"
    (fun () ->
      expect_included
        (list_propagated
           ~before:[ ("app.main", "fn first() -> Int64 { 1 }\n") ]
           ~after:
             [
               ("app.main", "fn first() -> Int64 { 1 }\n");
               ("app.main/second", "fn second() -> Int64 { first() }\n");
             ])
        ~parts:[ Declared (Support.parse_module "app.main"); Checked_body (make_main_key "second") ]);
  Harness.test "adding the module that a use names matches a cold build" (fun () ->
      let user = ("app.main", "use app.tools\n\nfn caller() -> Int64 {\n  tools.helper()\n}\n") in
      expect_included
        (list_propagated ~before:[ user ]
           ~after:[ user; ("app.tools", "public fn helper() -> Int64 { 1 }\n") ])
        ~parts:[ Checked_body (make_main_key "caller") ]);
  let tools_user = ("app.main", "use app.tools\n\nfn caller() -> Int64 {\n  tools.helper()\n}\n") in
  let tools = ("app.tools", "public fn helper() -> Int64 { 1 }\n") in
  let extra = ("app.extra", "public fn unused() -> Int64 { 2 }\n") in
  let is_main_resolution computed = computed = locate (Resolved (make_main_key "caller", Body)) in
  Harness.test "adding a module re-resolves no definition that does not name it" (fun () ->
      expect_untouched
        (list_propagated ~before:[ tools_user; tools ] ~after:[ tools_user; tools; extra ])
        ~is_excluded:is_main_resolution);
  Harness.test "removing a module re-resolves no definition that does not name it" (fun () ->
      expect_untouched
        (list_propagated ~before:[ tools_user; tools; extra ] ~after:[ tools_user; tools ])
        ~is_excluded:is_main_resolution);
  Harness.test "removing the module that a use names re-resolves the user" (fun () ->
      expect_included
        (list_propagated ~before:[ tools_user; tools ] ~after:[ tools_user ])
        ~parts:[ Resolved (make_main_key "caller", Body) ]);
  let read_callee_ownership database =
    Database.For_testing.read_ownership database (make_main_key "callee")
  in
  let propagate_with_failing_callee () =
    let database = build [ ("app.main", callee_and_caller) ] in
    Database.For_testing.with_failing_unit Check_ownership
      (Database.For_testing.identify_key (make_main_key "callee"))
      (fun () ->
        Database.update ~on_bug:ignore database
          [
            ( Support.parse_file "app.main",
              Some "fn callee(x: Int64) -> Int64 { x + 2 }\nfn caller() -> Int64 { callee(1) }\n" );
          ]);
    database
  in
  Harness.test "a read of a part whose computation raised a compiler bug raises that bug" (fun () ->
      match read_callee_ownership (propagate_with_failing_callee ()) with
      | _ -> Harness.fail "the part was read"
      | exception Compiler_bug.Bug bug when String.includes ~affix:"fails for a test" bug.message ->
          ()
      | exception Compiler_bug.Bug bug -> Harness.fail "raised %s" (Compiler_bug.to_string bug));
  Harness.test "a part whose computation raised a compiler bug is computed at the next input"
    (fun () ->
      let database = propagate_with_failing_callee () in
      Database.update database [];
      match read_callee_ownership database with
      | Value _ -> ()
      | Failed | Blocked -> Harness.fail "the part did not compute");
  Harness.test
    "a part whose computation raised an exception that is no compiler bug is computed at the next \
     input" (fun () ->
      let before = [ ("app.main", callee_and_caller) ] in
      let after =
        [
          ( "app.main",
            "fn callee(x: Int64) -> Int64 { x + 2 }\npublic fn caller() -> Int64 { callee(1) }\n" );
        ]
      in
      let database = build before in
      (match
         Database.For_testing.with_failing_unit ~raising:Exit Check_body
           (Database.For_testing.identify_key (make_main_key "callee"))
           (fun () -> Database.update database (list_changes ~before ~after))
       with
      | () -> Harness.fail "the exception did not escape the update"
      | exception Exit -> ());
      Database.update database [];
      Database.For_testing.propagate database;
      match Database.For_testing.list_differences database (build after) with
      | [] -> ()
      | differences ->
          Harness.fail "the database differs from a cold build in %s" (show_differences differences));
  Harness.test "a request that reads a fact computes nothing" (fun () ->
      let database = build [ ("app.main", callee_and_caller) ] in
      match
        snd
          (Database.count (fun () ->
               ignore (Database.read_checked_body database (make_main_key "caller"))))
      with
      | [] -> ()
      | counts -> Harness.fail "counted %s" (String.concat "; " (List.map show_counts counts)));
  Harness.test
    "listing a file's diagnostics runs as many statements for twenty definitions as for one"
    (fun () ->
      let count_statements definitions =
        let database =
          build
            [
              ( "app.main",
                String.concat ""
                  (List.init definitions (fun index ->
                       Printf.sprintf "fn caller_%d() -> Int64 { \"one\" }\n" index)) );
            ]
        in
        let diagnostics, statements =
          Database.count_statements (fun () ->
              Database.list_file_diagnostics database (Support.parse_file "app.main"))
        in
        if List.length diagnostics <> definitions then
          Harness.fail "listed %d diagnostics for %d definitions" (List.length diagnostics)
            definitions;
        List.fold_left
          (fun total (count : Database.statement_count) -> total + count.runs)
          0 statements
      in
      let for_one = count_statements 1 and for_twenty = count_statements 20 in
      if for_one <> for_twenty then
        Harness.fail "ran %d statements for one definition and %d for twenty" for_one for_twenty);
  let make_part index body =
    ( Printf.sprintf "app.part%d" index,
      Printf.sprintf
        "public fn first%d() -> Int64 { %s }\npublic fn second%d() -> Int64 { first%d() }\n" index
        body index index )
  in
  let first_part = Support.parse_file "app.part0" in
  let first_of_first_part = Support.make_top_path "app.part0" "first0" in
  let total read counts =
    List.fold_left (fun total (count : Database.statement_count) -> total + read count) 0 counts
  in
  let count_runs (count : Database.statement_count) = count.runs
  and count_steps (count : Database.statement_count) = count.steps in
  let make_tested_part index body =
    let name, text = make_part index body in
    (name, Printf.sprintf "%stest \"part %d\" {\n  assert second%d() > 0\n}\n" text index index)
  in
  let expect_the_same_work_at_two_sizes name ?(make_part = make_part) ?(shared = []) ?(body = "1")
      ?(prepare = ignore) ?(is_counted = fun _ -> true) ask =
    Harness.test (name ^ " costs the same in forty modules as in four") (fun () ->
        let count_statements modules =
          let database = build (shared @ List.init modules (fun index -> make_part index body)) in
          prepare database;
          List.filter is_counted (snd (Database.count_statements (fun () -> ask database)))
        in
        let for_four = count_statements 4 and for_forty = count_statements 40 in
        if total count_runs for_four <> total count_runs for_forty then
          Harness.fail "ran %d statements for four modules and %d for forty"
            (total count_runs for_four) (total count_runs for_forty);
        if 10 * total count_steps for_forty > 11 * total count_steps for_four then
          Harness.fail "ran %d steps for four modules and %d for forty" (total count_steps for_four)
            (total count_steps for_forty))
  in
  Harness.test "no statement of a build from nothing grows faster than the project" (fun () ->
      let count_statements modules =
        snd
          (Database.count_statements (fun () ->
               ignore (build (List.init modules (fun index -> make_part index "1")))))
      in
      let for_four = count_statements 4 and for_forty = count_statements 40 in
      List.iter
        (fun (count : Database.statement_count) ->
          let steps_for_four =
            total count_steps
              (List.filter
                 (fun (other : Database.statement_count) -> other.statement = count.statement)
                 for_four)
          in
          if count.steps > 3000 && count.steps > 12 * steps_for_four then
            Harness.fail "ran %d steps for four modules and %d for forty: %s" steps_for_four
              count.steps count.statement)
        for_forty);
  expect_the_same_work_at_two_sizes "an edit to one body" (fun database ->
      Database.update database [ (first_part, Some (snd (make_part 0 "1 + 1"))) ];
      Database.For_testing.propagate database);
  let make_helped_part index body =
    ( Printf.sprintf "app.part%d" index,
      Printf.sprintf
        "fn helper%d() -> Int64 { 3 }\n\
         public fn first%d() -> Int64 { %s }\n\
         public fn second%d() -> Int64 { helper%d() }\n"
        index index body index index )
  in
  let edit_first_part make_part body database =
    Database.update database [ (first_part, Some (snd (make_part 0 body))) ]
  in
  expect_the_same_work_at_two_sizes "adding a function that nothing uses" (fun database ->
      Database.update database
        [ (first_part, Some (snd (make_part 0 "1") ^ "fn spare() -> Int64 { 4 }\n")) ]);
  expect_the_same_work_at_two_sizes "an edit that adds a use of an unexported function"
    ~make_part:make_helped_part
    (edit_first_part make_helped_part "helper0()");
  expect_the_same_work_at_two_sizes "an edit that removes the last use of an unexported function"
    ~make_part:make_helped_part (fun database ->
      Database.update database
        [
          ( first_part,
            Some
              "fn helper0() -> Int64 { 3 }\n\
               public fn first0() -> Int64 { 1 }\n\
               public fn second0() -> Int64 { 2 }\n" );
        ]);
  expect_the_same_work_at_two_sizes "an edit that leaves a body with a type error"
    ~make_part:make_helped_part
    (edit_first_part make_helped_part "\"one\"");
  expect_the_same_work_at_two_sizes "an edit that fixes a body's type error"
    ~make_part:make_helped_part
    ~prepare:(edit_first_part make_helped_part "\"one\"")
    (edit_first_part make_helped_part "1");
  expect_the_same_work_at_two_sizes "adding a test" ~make_part:make_tested_part (fun database ->
      Database.update database
        [ (first_part, Some (snd (make_tested_part 0 "1") ^ "test \"another\" {\n}\n")) ]);
  let lower_tested_code database =
    match Database.find_lowered_lookups database [ app ] with
    | Ok _ -> ()
    | Error message -> Harness.fail "%s" message
  in
  expect_the_same_work_at_two_sizes "lowering the code that the tests reach without a change"
    ~make_part:make_tested_part lower_tested_code;
  expect_the_same_work_at_two_sizes
    "lowering the code that the tests reach after an edit to one body" ~make_part:make_tested_part
    ~prepare:(fun database ->
      Database.update database [ (first_part, Some (snd (make_tested_part 0 "1 + 1"))) ])
    lower_tested_code;
  let make_hub_caller index body =
    ( Printf.sprintf "app.part%d" index,
      Printf.sprintf
        "use app.hub\n\
         public fn first%d() -> Int64 { %s }\n\
         public fn second%d() -> Int64 { first%d() }\n\
         test \"part %d\" {\n\
        \  assert second%d() > 0\n\
         }\n"
        index body index index index index )
  in
  expect_the_same_work_at_two_sizes
    "lowering the code that the tests reach after an edit that removes one call to a function that \
     every module calls"
    ~make_part:make_hub_caller
    ~shared:[ ("app.hub", "public fn shared() -> Int64 { 1 }\npublic fn other() -> Int64 { 2 }\n") ]
    ~body:"hub.shared()"
    ~prepare:(fun database ->
      Database.update database [ (first_part, Some (snd (make_hub_caller 0 "hub.other()"))) ])
    lower_tested_code;
  expect_the_same_work_at_two_sizes
    "asking whether a claim names a function that every module calls, after an edit that removes \
     one call to it,"
    ~make_part:make_hub_caller
    ~shared:[ ("app.hub", "public fn shared() -> Int64 { 1 }\npublic fn other() -> Int64 { 2 }\n") ]
    ~body:"hub.shared()"
    ~prepare:(fun database ->
      Database.update database [ (first_part, Some (snd (make_hub_caller 0 "hub.other()"))) ])
    ~is_counted:(fun count -> String.includes ~affix:"FROM main.edge c" count.statement)
    lower_tested_code;
  Harness.test
    "listing the linked items of a program after an edit to one body runs as many statements for \
     forty modules as for four, and renders the edited unit in as many steps" (fun () ->
      let count_listing_work modules =
        let roots =
          List.init modules (fun index ->
              make_code_item_of
                (Support.make_top_path
                   (Printf.sprintf "app.part%d" index)
                   (Printf.sprintf "second%d" index)))
        in
        let database =
          Support.make_database
            (Support.setup (List.init modules (fun index -> make_part index "1")))
        in
        List.iter (Database.For_testing.add_root database) roots;
        Database.For_testing.propagate database;
        let list_linked () =
          match Database.find_lowered_lookups database [ app ] with
          | Ok lookups -> lookups.list_linked Development roots
          | Error message -> Harness.fail "%s" message
        in
        if List.length (list_linked ()) <> 2 * modules then
          Harness.fail "the program of %d modules does not link two items of each" modules;
        Database.update database [ (first_part, Some (snd (make_part 0 "1 + 1"))) ];
        Database.For_testing.propagate database;
        let (_, observed), statements =
          Database.count_statements (fun () -> Database.For_testing.observe list_linked)
        in
        expect_recomputed
          (List.filter
             (fun (computed : Database.For_testing.computed) -> computed.stage = Render Development)
             observed.recomputed)
          ~exactly:[ Unit (Development, make_code_item_of first_of_first_part) ];
        let _, statements_without_a_change = Database.count_statements list_linked in
        ( total count_runs statements,
          total count_steps statements - total count_steps statements_without_a_change )
      in
      let runs_for_four, rendering_steps_for_four = count_listing_work 4
      and runs_for_forty, rendering_steps_for_forty = count_listing_work 40 in
      if runs_for_four <> runs_for_forty then
        Harness.fail "ran %d statements for four modules and %d for forty" runs_for_four
          runs_for_forty;
      if 10 * rendering_steps_for_forty > 11 * rendering_steps_for_four then
        Harness.fail "rendering the unit added %d steps for four modules and %d for forty"
          rendering_steps_for_four rendering_steps_for_forty);
  expect_the_same_work_at_two_sizes "listing the diagnostics of one file" (fun database ->
      ignore (Database.list_file_diagnostics database first_part));
  expect_the_same_work_at_two_sizes "listing the readers of one module" (fun database ->
      ignore (Database.list_readers_of_module database first_part.module_));
  Harness.test "the readers of a module are the definitions and the files that name it" (fun () ->
      let database =
        build
          [
            ("app.util", "public fn one() -> Int64 { 1 }\n");
            ("app.full", "fn by_path() -> Int64 { app.util.one() }\n");
            ("app.used", "use app.util\nfn by_import() -> Int64 { util.one() }\n");
            ("app.other", "fn unrelated() -> Int64 { 2 }\n");
          ]
      in
      let definitions, files =
        Database.list_readers_of_module database (Support.parse_file "app.util").module_
      in
      let names path =
        List.exists (fun (key : Resolve.Names.key) -> Path.equal key.path path) definitions
      in
      if not (names (Support.make_top_path "app.full" "by_path")) then
        Harness.fail "the definition that names the module by its full path is not listed";
      if names (Support.make_top_path "app.other" "unrelated") then
        Harness.fail "a definition that does not name the module is listed";
      if files <> [ Support.parse_file "app.used" ] then
        Harness.fail "listed %d files that import the module" (List.length files));
  expect_the_same_work_at_two_sizes "listing the dependents of one definition" (fun database ->
      ignore (Database.list_dependents database [ first_of_first_part ]));
  expect_the_same_work_at_two_sizes "listing the dependencies of one definition" (fun database ->
      ignore (Database.list_dependencies database [ Support.make_top_path "app.part0" "second0" ]));
  expect_the_same_work_at_two_sizes "listing the definitions that name one definition"
    (fun database -> ignore (Database.list_definitions_naming database first_of_first_part));
  expect_the_same_work_at_two_sizes "proving and deciding one file" (fun database ->
      ignore (Support.list_proof_states database first_part));
  expect_the_same_work_at_two_sizes "proving and deciding one file again without a change"
    ~prepare:(fun database -> ignore (Support.list_proof_states database first_part))
    (fun database -> ignore (Support.list_proof_states database first_part));
  let decide_package database = Support.decide database (In_packages [ app ]) in
  expect_the_same_work_at_two_sizes "deciding a package again, after every proof is decided,"
    ~prepare:decide_package decide_package;
  Harness.test "listing a file's diagnostics reads no part" (fun () ->
      let database = build [ ("app.main", "fn caller() -> Int64 { \"one\" }\n") ] in
      match
        Database.count (fun () ->
            Database.list_file_diagnostics database (Support.parse_file "app.main"))
      with
      | [ _ ], [] -> ()
      | diagnostics, counts ->
          Harness.fail "listed %d diagnostics and counted %s" (List.length diagnostics)
            (String.concat "; " (List.map show_counts counts)))

let () =
  let count_reports database file code =
    List.length
      (List.filter (String.equal code)
         (Support.list_codes (Database.list_file_diagnostics database (Support.parse_file file))))
  in
  let expect_reports_after_edits name ~code steps =
    Harness.test name (fun () ->
        match steps with
        | [] -> Harness.fail "no step"
        | (first, _) :: _ ->
            let hot = build first in
            ignore
              (List.fold_left
                 (fun before (after, counts) ->
                   ignore (propagate hot ~before ~after);
                   List.iter
                     (fun (file, count) ->
                       let reported = count_reports hot file code in
                       if reported <> count then
                         Harness.fail "%s holds %d reports of %s, and not %d" file reported code
                           count)
                     counts;
                   after)
                 first steps))
  in
  let expect_unused_after_edits name texts =
    expect_reports_after_edits name ~code:"usage.unused_function"
      (List.map (fun (text, count) -> ([ ("app.main", text) ], [ ("app.main", count) ])) texts)
  in
  let helper = "internal fn helper() -> Int64 { 1 }\n" in
  let helper_and_user = helper ^ "public fn top() -> Int64 { helper() }\n" in
  let helper_alone = helper ^ "public fn top() -> Int64 { 2 }\n" in
  expect_unused_after_edits
    "an unexported function is reported while no body uses it, and at no other time"
    [ (helper_and_user, 0); (helper_alone, 1); (helper_and_user, 0) ];
  let make_chain top =
    "internal fn leaf() -> Int64 { 1 }\ninternal fn middle() -> Int64 { leaf() }\n" ^ top
  in
  expect_unused_after_edits
    "the functions that only an unused function reaches are reported with it"
    [
      (make_chain "public fn top() -> Int64 { middle() }\n", 0);
      (make_chain "public fn top() -> Int64 { 2 }\n", 2);
      (make_chain "public fn top() -> Int64 { middle() }\n", 0);
    ];
  let make_cycle top =
    "internal fn ping(depth: Int64) -> Int64 { pong(depth) }\n\
     internal fn pong(depth: Int64) -> Int64 { ping(depth) }\n" ^ top
  in
  expect_unused_after_edits
    "functions that call each other are reported once no other body calls them"
    [
      (make_cycle "public fn top() -> Int64 { ping(1) }\n", 0);
      (make_cycle "public fn top() -> Int64 { 2 }\n", 2);
      (make_cycle "public fn top() -> Int64 { pong(1) }\n", 0);
    ];
  expect_unused_after_edits
    "a function that becomes unexported and unused is reported with the functions that only it uses"
    [
      (helper_and_user, 0);
      (helper ^ "internal fn top() -> Int64 { helper() }\n", 2);
      (helper_and_user, 0);
    ];
  let make_dead_chain top = make_chain "internal fn upper() -> Int64 { middle() }\n" ^ top in
  expect_unused_after_edits
    "a use of the middle of an unused chain leaves the function above it unused"
    [
      (make_dead_chain "public fn top() -> Int64 { 2 }\n", 3);
      (make_dead_chain "public fn top() -> Int64 { middle() }\n", 1);
      (make_dead_chain "public fn top() -> Int64 { 2 }\n", 3);
    ];
  expect_unused_after_edits
    "no unexported function is reported while a body of its package fails to check"
    [
      (helper_and_user, 0);
      (helper ^ "public fn top() -> Int64 { \"one\" }\n", 0);
      (helper_alone, 1);
      (helper ^ "public fn top() -> Int64 { helper() + \"one\" }\n", 0);
      (helper_and_user, 0);
    ];
  expect_unused_after_edits
    "an unexported function whose definition has a syntax error after its name is not reported"
    [
      ("public fn top() -> Int64 { 2 }\ninternal fn helper( -> Int64 { 1 }\n", 0); (helper_alone, 1);
    ];
  let expect_linear_work name ~affix make_definition =
    Harness.test (name ^ " cost in proportion to their number") (fun () ->
        let count_steps length =
          let text = String.concat "" (List.init length make_definition) in
          List.fold_left
            (fun steps (count : Database.statement_count) ->
              if String.includes ~affix count.statement then steps + count.steps else steps)
            0
            (snd (Database.count_statements (fun () -> ignore (build [ ("app.main", text) ]))))
        in
        let for_ten = count_steps 10 and for_forty = count_steps 40 in
        if for_ten = 0 || for_forty > 5 * for_ten then
          Harness.fail "ran %d steps for ten definitions and %d for forty" for_ten for_forty)
  in
  expect_linear_work "unused functions that call each other in a chain" ~affix:"ON d.id = e.source"
    (fun index ->
      Printf.sprintf "fn link%d() -> Int64 { %s }\n" index
        (if index = 0 then "1" else Printf.sprintf "link%d()" (index - 1)));
  expect_linear_work "tests added together" ~affix:"AND member = ?2 AND kind = ?3" (fun index ->
      Printf.sprintf "test \"case %d\" {\n}\n" index);
  expect_linear_work "generic functions whose calls grow in a chain" ~affix:"ON d.path = e.target"
    (fun index ->
      Printf.sprintf "fn wrap%d[Element](value: own Element) -> Int64 {\n  %s\n}\n\n" index
        (if index = 0 then "1" else Printf.sprintf "wrap%d(Some(own value))" (index - 1)));
  let adds = "test \"adds\" {\n}\n" in
  expect_reports_after_edits "a test is reported while an earlier test of its package has its name"
    ~code:"package.duplicate_test"
    [
      ([ ("app.main", adds) ], [ ("app.main", 0) ]);
      ([ ("app.main", adds); ("app.other", adds) ], [ ("app.main", 0); ("app.other", 1) ]);
      ([ ("app.other", adds) ], [ ("app.other", 0) ]);
    ];
  let make_generic_pair pong_body =
    Printf.sprintf
      "fn ping[Element](value: own Element) -> Int64 {\n\
      \  pong(Some(own value))\n\
       }\n\n\
       fn pong[Element](value: own Element) -> Int64 {\n\
      \  %s\n\
       }\n"
      pong_body
  in
  expect_reports_after_edits
    "generic code is reported when an edit to its callee closes a cycle that grows"
    ~code:"package.instantiation_cycle"
    (List.map
       (fun (pong_body, count) ->
         ([ ("app.main", make_generic_pair pong_body) ], [ ("app.main", count) ]))
       [ ("1", 0); ("ping(own value)", 1); ("1", 0) ]);
  expect_reports_after_edits
    "a function is reported once it becomes generic and instantiates itself with a growing type"
    ~code:"package.instantiation_cycle"
    (List.map
       (fun (text, count) -> ([ ("app.main", text) ], [ ("app.main", count) ]))
       [
         ("fn grow(value: Int64) -> Int64 {\n  1\n}\n", 0);
         ("fn grow[Element](value: own Element) -> Int64 {\n  grow(Some(own value))\n}\n", 1);
         ("fn grow(value: Int64) -> Int64 {\n  1\n}\n", 0);
       ]);
  Harness.test "a dependency is reported while no body of its package uses it" (fun () ->
      let settle files =
        let database =
          Support.make_database (Support.setup ~dependencies:[ ("app", "lib") ] files)
        in
        Database.For_testing.propagate database;
        database
      in
      let lib = List.nth tool_user 1 in
      let unused = [ ("app.main", "fn caller() -> Int64 { 1 }\n"); lib ] in
      let hot = settle tool_user in
      ignore
        (List.fold_left
           (fun before (after, is_reported) ->
             Database.update hot (list_changes ~before ~after);
             Database.For_testing.propagate hot;
             (match Database.For_testing.list_differences hot (settle after) with
             | [] -> ()
             | differences ->
                 Harness.fail "the propagated database differs from a cold build in %s"
                   (show_differences differences));
             (match (Database.list_manifest_problems hot app, is_reported) with
             | [], false | [ Unused_dependency { owner = None; name = "lib" } ], true -> ()
             | problems, _ -> Harness.fail "reported %d problems" (List.length problems));
             after)
           tool_user
           [ (tool_user, false); (unused, true); (tool_user, false) ]))

let () =
  Harness.test "a blocked proof in a package with no error is a compiler bug" (fun () ->
      let database = build [ ("app.main", "public fn one() -> Int64 { 1 }\n") ] in
      let main = Support.parse_file "app.main" in
      ignore (Support.prove database main);
      Database.For_testing.block_proof database
        { module_ = main.module_; path = Support.make_top_path "app.main" "one"; ordinal = 0 };
      List.iter
        (fun (scope : Database.proof_scope) ->
          match Database.prove database scope with
          | _ -> Harness.fail "no bug is raised"
          | exception Compiler_bug.Bug bug when String.includes ~affix:"is blocked" bug.message ->
              ()
          | exception Compiler_bug.Bug bug -> Harness.fail "raised %s" (Compiler_bug.to_string bug))
        [ In_packages [ app ]; In_files [ main ] ]);
  Harness.test "every kind of written definition has a proof" (fun () ->
      let packages =
        Support.setup [ ("app.main", Fixtures.Capabilities.package_of_every_kind_of_definition) ]
      in
      let proofs = Database.prove (Support.make_database packages) (In_packages [ app ]) in
      let declarations = Support.list_declarations packages (Support.parse_module "app.main") in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          match Database.For_testing.find_proof proofs declaration.key with
          | Some (Value _) -> ()
          | Some (Failed | Blocked) ->
              Harness.fail "the proof of %s is blocked" (Resolve.Names.show_key declaration.key)
          | None -> Harness.fail "%s has no proof" (Resolve.Names.show_key declaration.key))
        declarations;
      List.iter
        (fun (kind : Resolve.Names.kind) ->
          if
            not
              (List.exists
                 (fun (declaration : Resolve.Names.declaration) -> declaration.kind = kind)
                 declarations)
          then Harness.fail "the package lacks %s" (Resolve.Names.show_kind kind))
        [
          Function;
          Type;
          Trait;
          Capability;
          Constant;
          Theorem;
          Method;
          Member_constant;
          Impl;
          Test;
          Law_proof;
        ])

let () =
  Harness.test "a package build writes no edge that only records a read" (fun () ->
      let package =
        List.hd
          (Support.setup
             [
               ( "lib.tools",
                 "public fn first() -> Int64 { 1 }\npublic fn second() -> Int64 { first() }\n" );
             ])
      in
      let loaded = [ Lazy.force standard ] in
      let count_edge_steps build =
        List.fold_left
          (fun steps (count : Database.statement_count) ->
            if String.includes ~affix:"INTO main.edge" count.statement then steps + count.steps
            else steps)
          0
          (snd (Database.count_statements build))
      in
      let steps_as_package =
        count_edge_steps (fun () ->
            Database.build_package ~loaded package
              ~into:(Filename.concat (Harness.make_scratch_directory "package") "package.sqlite"))
      and steps_as_project =
        count_edge_steps (fun () -> ignore (Database.create ~loaded [ package ]))
      in
      if 4 * steps_as_package > steps_as_project then
        Harness.fail "wrote its edges in %d steps as a package and in %d as a project"
          steps_as_package steps_as_project);
  Harness.test "a package database records the diagnostics of its package, and none when it checks"
    (fun () ->
      let clean = load_package [ ("lib.tools", "public fn first() -> Int64 { 1 }\n") ] in
      let broken = load_package [ ("lib.tools", "public fn first() -> Int64 { \"one\" }\n") ] in
      let lib : Path.package = { owner = None; name = "lib" } in
      if Database.list_package_diagnostics clean lib <> [] then
        Harness.fail "the package that checks records diagnostics";
      match Database.list_package_diagnostics broken lib with
      | [ (_, _ :: _) ] -> ()
      | failed -> Harness.fail "the broken package records %d files" (List.length failed))

let shapes_and_tools =
  [
    ( "app.main",
      "use app.tools\n\
       trait Shape {\n\
      \  fn side(self) -> Int64\n\
      \  fn doubled(self) -> Int64 {\n\
      \    self.side() + self.side()\n\
      \  }\n\
       }\n\
       type Square(side: Int64)\n\
       impl Shape for Square {\n\
      \  fn side(self) -> Int64 {\n\
      \    self.side\n\
      \  }\n\
       }\n\
       fn Square.grow(self) -> Int64 { tools.helper() }\n\
       fn caller() -> Int64 { 1 }\n" );
    ("app.tools", "public fn helper() -> Int64 { 1 }\nconst limit: Int64 = 3\n");
  ]

let expect_propagation_equals_cold name ~before ~after =
  Harness.test ("a propagated database equals one built from nothing: " ^ name) (fun () ->
      let hot = Support.make_database (Support.setup before) in
      Database.update hot
        (List.map (fun (file, text) -> (Support.parse_file file, Some text)) after
        @ List.filter_map
            (fun (file, _) ->
              if List.mem_assoc file after then None else Some (Support.parse_file file, None))
            before);
      match
        Database.For_testing.list_differences hot (Support.make_database (Support.setup after))
      with
      | [] -> ()
      | differences ->
          Harness.fail "the tables differ: %s"
            (String.concat ", "
               (List.map
                  (fun (table, count) -> Printf.sprintf "%s in %d rows" table count)
                  differences)))

let replace_in ~sub ~by files =
  List.map
    (fun (file, text) ->
      match String.find_first ~sub text with
      | Some start ->
          ( file,
            String.sub text 0 start ^ by
            ^ String.sub text
                (start + String.length sub)
                (String.length text - start - String.length sub) )
      | None -> (file, text))
    files

let () =
  let before = shapes_and_tools in
  expect_propagation_equals_cold "no change" ~before ~after:before;
  expect_propagation_equals_cold "an edited body" ~before
    ~after:(replace_in ~sub:"fn caller() -> Int64 { 1 }" ~by:"fn caller() -> Int64 { 2 }" before);
  expect_propagation_equals_cold "a body that gains a call" ~before
    ~after:
      (replace_in ~sub:"fn caller() -> Int64 { 1 }" ~by:"fn caller() -> Int64 { tools.helper() }"
         before);
  expect_propagation_equals_cold "a body that becomes recursive" ~before
    ~after:
      (replace_in ~sub:"fn caller() -> Int64 { 1 }" ~by:"fn caller() -> Int64 { caller() }" before);
  expect_propagation_equals_cold "an edited signature" ~before
    ~after:
      (replace_in ~sub:"public fn helper() -> Int64 { 1 }" ~by:"public fn helper() -> Int32 { 1 }"
         before);
  expect_propagation_equals_cold "an added definition" ~before
    ~after:(replace_in ~sub:"const limit" ~by:"fn extra() -> Int64 { limit }\nconst limit" before);
  expect_propagation_equals_cold "a removed definition" ~before
    ~after:(replace_in ~sub:"fn caller() -> Int64 { 1 }\n" ~by:"" before);
  expect_propagation_equals_cold "a removed impl" ~before
    ~after:
      (replace_in
         ~sub:"impl Shape for Square {\n  fn side(self) -> Int64 {\n    self.side\n  }\n}\n"
         ~by:"" before);
  expect_propagation_equals_cold "a removed import" ~before
    ~after:
      (replace_in ~sub:"tools.helper()" ~by:"1" (replace_in ~sub:"use app.tools\n" ~by:"" before));
  expect_propagation_equals_cold "an unresolved name" ~before
    ~after:
      (replace_in ~sub:"fn caller() -> Int64 { 1 }" ~by:"fn caller() -> Int64 { missing }" before);
  expect_propagation_equals_cold "a repaired name"
    ~before:
      (replace_in ~sub:"fn caller() -> Int64 { 1 }" ~by:"fn caller() -> Int64 { missing }" before)
    ~after:before;
  expect_propagation_equals_cold "an added file" ~before
    ~after:(before @ [ ("app.more", "public fn more() -> Int64 { 4 }\n") ]);
  expect_propagation_equals_cold "a removed file"
    ~before:(before @ [ ("app.more", "public fn more() -> Int64 { 4 }\n") ])
    ~after:before;
  let duplicated =
    replace_in ~sub:"fn caller() -> Int64 { 1 }\n"
      ~by:"fn caller() -> Int64 { 1 }\nfn caller() -> Int64 { 1 }\n" before
  in
  expect_propagation_equals_cold "a duplicated definition" ~before ~after:duplicated;
  expect_propagation_equals_cold "a duplicate removed" ~before:duplicated ~after:before;
  let make_labelled kind =
    [
      ( "app.main",
        kind
        ^ " Labelled {\n\
          \  fn label(self) -> Int64\n\
           }\n\
           type Box(value: Int64)\n\
           fn read(box: Box) -> Int64 { box.label() }\n" );
    ]
  in
  expect_propagation_equals_cold "a capability that becomes a trait"
    ~before:(make_labelled "capability") ~after:(make_labelled "trait");
  expect_propagation_equals_cold "a trait that becomes a capability" ~before:(make_labelled "trait")
    ~after:(make_labelled "capability")

let () =
  Harness.test "two databases built from different files differ in their rows" (fun () ->
      let edited =
        replace_in ~sub:"fn caller() -> Int64 { 1 }" ~by:"fn caller() -> Int64 { 2 }"
          shapes_and_tools
      in
      match
        Database.For_testing.list_differences
          (Support.make_database (Support.setup shapes_and_tools))
          (Support.make_database (Support.setup edited))
      with
      | [] -> Harness.fail "no table differs"
      | differences ->
          List.iter
            (fun table ->
              if not (List.mem_assoc table differences) then
                Harness.fail "the table %s does not differ" table)
            [ "file"; "syntax"; "body" ])

let bounded_and_unbounded =
  "fn bounded(count: UInt8) -> UInt8\n\
  \  requires count < 255\n\
   {\n\
  \  count + 1\n\
   }\n\n\
   fn unbounded(count: UInt8) -> UInt8 {\n\
  \  count + 1\n\
   }\n"

let () =
  let file = Support.parse_file "app.main" in
  let build_decided () =
    let database = Support.make_database (Support.setup [ ("app.main", bounded_and_unbounded) ]) in
    (database, Support.list_proof_states database file)
  in
  let observe_deciding database =
    let states, (observed : Database.For_testing.observed) =
      Database.For_testing.observe (fun () -> Support.list_proof_states database file)
    in
    ( states,
      List.filter
        (fun (computed : Database.For_testing.computed) -> computed.stage = Decide)
        observed.recomputed )
  in
  let list_overflows states =
    List.filter (fun (state : Database.proof_state) -> state.site.code = "prover.overflow") states
  in
  Harness.test "a verdict says whether the solver proved its obligation" (fun () ->
      match list_overflows (snd (build_decided ())) with
      | [ bounded; unbounded ] ->
          if (not bounded.is_proven) || unbounded.is_proven then
            Harness.fail "the addition under the requires is proven: %b; the other: %b"
              bounded.is_proven unbounded.is_proven
      | states -> Harness.fail "%d overflow states" (List.length states));
  Harness.test "deciding a file again without a change decides no definition" (fun () ->
      let database, _ = build_decided () in
      match snd (observe_deciding database) with
      | [] -> ()
      | decided -> Harness.fail "decided %s" (show_parts decided));
  Harness.test "an edit to one body decides that definition and no other" (fun () ->
      let database, _ = build_decided () in
      Database.update database
        [
          ( file,
            Some
              (String.concat "count + 2"
                 (String.split_on_char '|'
                    "fn bounded(count: UInt8) -> UInt8\n\
                    \  requires count < 255\n\
                     {\n\
                    \  count + 1\n\
                     }\n\n\
                     fn unbounded(count: UInt8) -> UInt8 {\n\
                    \  |\n\
                     }\n")) );
        ];
      expect_same_units
        (snd (observe_deciding database))
        ~as_:[ locate (Verdicts (make_main_key "unbounded")) ]);
  Harness.test "a database decided again after an edit equals one decided from nothing" (fun () ->
      let edited =
        "\n" ^ bounded_and_unbounded ^ "\nfn added(count: UInt8) -> UInt8 { count + 3 }\n"
      in
      let hot, _ = build_decided () in
      Database.update hot [ (file, Some edited) ];
      ignore (Support.list_proof_states hot file);
      let cold = Support.make_database (Support.setup [ ("app.main", edited) ]) in
      ignore (Support.list_proof_states cold file);
      match Database.For_testing.list_differences hot cold with
      | [] -> ()
      | differences ->
          Harness.fail "the tables differ: %s"
            (String.concat ", "
               (List.map
                  (fun (table, count) -> Printf.sprintf "%s in %d rows" table count)
                  differences)));
  Harness.test "an edit above a definition decides it no further, and its states move with it"
    (fun () ->
      let database, states_before = build_decided () in
      Database.update database [ (file, Some ("\n" ^ bounded_and_unbounded)) ];
      let states, decided = observe_deciding database in
      if decided <> [] then Harness.fail "decided %s" (show_parts decided);
      if
        List.map (fun (state : Database.proof_state) -> state.site.span.start) states
        <> List.map (fun (state : Database.proof_state) -> state.site.span.start + 1) states_before
      then Harness.fail "the states did not move by the one byte added above them")
