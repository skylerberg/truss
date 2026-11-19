let app : Path.package = { owner = None; name = "app" }
let make_main_path name = Support.make_top_path "app::main" name

let make_key path : Resolve.Names.key =
  { module_ = Support.parse_module "app::main"; path; ordinal = 0 }

let make_main_key name = make_key (make_main_path name)
let make_method owner name receiver : Path.t = Method { owner; name; receiver }

let make_impl_method ?(module_ = "app::main") ~trait ~for_type name receiver =
  make_method
    (Impl
       {
         module_ = Support.parse_module module_;
         trait = { path = trait; arguments = []; associated = [] };
         for_type;
       })
    name receiver

let make_code_item name : Lowered.Item.t =
  Code
    {
      path = make_main_path name;
      instantiation = { type_arguments = []; capability_arguments = [] };
    }

let make_lowered name : Database.Part.any = Any (Lowered (make_code_item name))
let make_test_key name : Database.Part.any = Any (Test_key (make_code_item name))
let show_part part = Database.Part.show (Stored part)
let show_parts parts = String.concat ", " (List.map show_part parts)

let is_part_of definitions part =
  match Database.Part.find_definition (Stored part) with
  | Some path -> List.exists (Path.equal path) definitions
  | None -> false

let check_text text =
  let database = Support.make_database (Support.setup [ ("app::main", text) ]) in
  (match
     Support.list_codes
       (Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers database
          (Support.parse_file "app::main"))
   with
  | [] -> ()
  | codes -> Harness.fail "the program has diagnostics: %s" (String.concat ", " codes));
  database

let expect_reads database part ~includes ~excludes =
  let reads = Database.For_testing.list_reads database part in
  List.iter
    (fun read ->
      if not (List.mem read reads) then
        Harness.fail "%s does not read %s; it reads %s" (show_part part) (Database.Part.show read)
          (String.concat ", " (List.map Database.Part.show reads)))
    includes;
  List.iter
    (fun read ->
      if List.mem read reads then
        Harness.fail "%s reads %s" (show_part part) (Database.Part.show read))
    excludes

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
  | parts ->
      Harness.fail "the propagated database differs from a cold build in %s" (show_parts parts));
  observed

let list_propagated ~before ~after = (propagate (build before) ~before ~after).recomputed

let list_propagated_with_roots ~roots ~before ~after =
  (propagate ~roots (build ~roots before) ~before ~after).recomputed

let expect_recomputed recomputed ~exactly =
  if recomputed <> List.sort_uniq compare exactly then
    Harness.fail "recomputed %s, not %s" (show_parts recomputed) (show_parts exactly)

let expect_untouched recomputed ~is_excluded =
  List.iter
    (fun part ->
      if is_excluded part then
        Harness.fail "recomputed %s; it recomputed %s" (show_part part) (show_parts recomputed))
    recomputed

let expect_included recomputed ~parts =
  List.iter
    (fun part ->
      if not (List.mem part recomputed) then
        Harness.fail "did not recompute %s; it recomputed %s" (show_part part)
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
  | parts -> Harness.fail "the relaid database differs from a cold build in %s" (show_parts parts));
  observed.recomputed

let load_package files =
  Database.build_package_database ~loaded:[ Lazy.force standard ] (List.hd (Support.setup files))

let list_saved database =
  let entries = Database.list_unsaved database in
  Database.mark_saved database;
  entries

let commit log entries =
  List.fold_left (fun log (key, value) -> (key, value) :: List.remove_assoc key log) log entries

let list_live log =
  List.filter_map (fun (key, value) -> Option.map (fun value -> (key, value)) value) log

let reopen log files =
  let packages = Support.setup files in
  let find_text (file : Path.file) =
    List.find_map (fun (package : Project.package) -> List.assoc_opt file package.files) packages
  in
  let database =
    Database.restore
      ~saved:[ Lazy.force standard ]
      ~find_text
      ~loaded:[ Lazy.force standard ]
      packages (list_live log)
  in
  database

let expect_cold ?roots database files =
  match Database.For_testing.list_differences database (build ?roots files) with
  | [] -> ()
  | parts -> Harness.fail "the reopened database differs from a cold build in %s" (show_parts parts)

let remove_rebuilt_on_reopen recomputed =
  List.filter
    (function Database.Part.Any (Namespace _ | Recursion_group _) -> false | _ -> true)
    recomputed

let observe_reopen ?roots log files =
  let database, observed =
    Database.For_testing.observe (fun () ->
        let database = reopen log files in
        Database.For_testing.propagate database;
        database)
  in
  expect_cold ?roots database files;
  { observed with recomputed = remove_rebuilt_on_reopen observed.recomputed }

let tool_user =
  [
    ("app::main", "use lib::tools\nfn caller() -> Int64 { tools::helper() }\n");
    ("lib::tools", "public fn helper() -> Int64 { 1 }\n");
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

let default_trait = Support.make_top_path "standard::core" "Default"

let derived_version_default =
  make_method (Derived { type_ = make_main_path "Version"; trait = default_trait }) "default" Static

let expect_recursion_group text ~of_:name ~expected =
  let database = build [ ("app::main", text) ] in
  let group = (Database.make_proof_lookups database).list_recursion_group (make_main_path name) in
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
  make_impl_method ~trait:(make_main_path "Level") ~for_type:(make_main_path "Shelf") name Read

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
  | parts ->
      Harness.fail "the propagated database differs from a cold build in %s" (show_parts parts));
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

let level_user =
  "use lib::tools\nfn caller(shelf: tools::Shelf) -> Int64 { tools::measure(shelf) }\n"

let raised_of_library_shelf =
  make_impl_method ~module_:"lib::tools"
    ~trait:(Support.make_top_path "lib::tools" "Level")
    ~for_type:(Support.make_top_path "lib::tools" "Shelf")
    "raised" Read

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
  "use lib::tools\n\n\
   type Hop()\n\n\
   impl tools::Step for Hop {\n\
  \  fn step(self, node: tools::Node) -> Int64 {\n\
  \    tools::follow(node)\n\
  \  }\n\
   }\n"

let step_of_hop =
  make_impl_method
    ~trait:(Support.make_top_path "lib::tools" "Step")
    ~for_type:(make_main_path "Hop") "step" Read

let count_termination_obligations database ~of_:path =
  match
    Database.For_testing.find_proof
      (Support.prove database (Support.parse_file "app::main"))
      (make_key path)
  with
  | Some (Value (Obligations outcome)) ->
      List.length
        (List.filter
           (fun (obligation : Prover.Obligation.t) -> obligation.code = Termination)
           outcome.obligations)
  | Some (Value (Unsupported _ | Not_proven_here) | Failed _ | Blocked) | None ->
      failwith ("the proof of " ^ Path.show path ^ " makes no obligations")

let callee_and_caller =
  "fn callee(x: Int64) -> Int64 { x + 1 }\npublic fn caller() -> Int64 { callee(1) }\n"

let with_helper =
  [ ("app::main", callee_and_caller); ("app::extra", "fn helper() -> Int64 { 1 }\n") ]

let served_length_program =
  Filename.concat (Filename.dirname Sys.executable_name) "served_length/served_length.exe"

let request_served_length ~key request =
  match Process.run served_length_program [ key; request ] with
  | 0, output, _ -> String.split_on_char '\n' (String.trim output)
  | status, _, errors ->
      Harness.fail "served_length exited with status %d: %s" status (String.trim errors);
      []

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
        (Any (Checked_body (make_main_key "caller")))
        ~includes:[ Stored (Any (Interface (make_main_key "callee"))) ]
        ~excludes:
          [
            Stored (Any (Checked_body (make_main_key "callee")));
            Name (Tree (make_main_key "callee"));
            Stored (Any (Resolved (make_main_key "callee", Body)));
          ]);
  Harness.test "a contract reads no resolved names of its body" (fun () ->
      expect_reads
        (check_text "fn f(x: Int64) -> Int64 requires x > 0 { x + 1 }\n")
        (Any (Contract (make_main_key "f")))
        ~includes:[ Stored (Any (Resolved (make_main_key "f", Contract))) ]
        ~excludes:[ Stored (Any (Resolved (make_main_key "f", Body))) ]);
  Harness.test "a checked body reads its callee's signature check" (fun () ->
      expect_reads
        (check_text
           "fn callee(x: Int64) -> Int64 { x + 1 }\npublic fn caller() -> Int64 { callee(1) }\n")
        (Any (Checked_body (make_main_key "caller")))
        ~includes:[ Stored (Any (Signature_check (make_main_key "callee"))) ]
        ~excludes:[]);
  Harness.test "a type's facts read interfaces and type facts, and no signature check" (fun () ->
      expect_reads
        (check_text "type Inner(value: Int64)\ntype Outer(inner: Inner)\n")
        (Any (Type_facts (make_main_path "Outer")))
        ~includes:
          [
            Stored (Any (Interface (make_main_key "Outer")));
            Stored (Any (Type_facts (make_main_path "Inner")));
          ]
        ~excludes:
          [
            Stored (Any (Signature_check (make_main_key "Outer")));
            Stored (Any (Signature_check (make_main_key "Inner")));
          ]);
  Harness.test "a caller's checked body and proof read no place or text of the callee" (fun () ->
      let database = check_text callee_and_caller in
      ignore (Database.prove database [ Support.parse_file "app::main" ]);
      List.iter
        (fun part ->
          expect_reads database part ~includes:[]
            ~excludes:
              [ Name (Place (make_main_key "callee")); Name (Text (make_main_key "callee")) ])
        [ Any (Checked_body (make_main_key "caller")); Any (Proof (make_main_key "caller")) ]);
  Harness.test "a package check reads no place" (fun () ->
      expect_reads
        (check_text "type Inner(value: Int64)\ntype Outer(inner: Inner)\n")
        (Any (Package_check (app, Type (make_main_key "Outer"))))
        ~includes:[ Name (Tree (make_main_key "Outer")) ]
        ~excludes:[ Name (Place (make_main_key "Outer")); Name (Place (make_main_key "Inner")) ]);
  Harness.test "a reformat inside a definition recomputes only that definition's proof" (fun () ->
      expect_recomputed
        (list_propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 {\n\
                 \  x + 1\n\
                  }\n\
                  public fn caller() -> Int64 { callee(1) }\n" );
             ])
        ~exactly:
          [
            Any (Import_check (Support.parse_file "app::main"));
            Any (Namespace app);
            Any (Parsed (Support.parse_file "app::main"));
            Any (Proof (make_main_key "callee"));
          ]);
  Harness.test "moving a definition to another file of its module recomputes no definition's part"
    (fun () ->
      expect_recomputed
        (list_propagated
           ~before:[ ("app::main", callee_and_caller); ("app::main/other", "") ]
           ~after:
             [
               ("app::main", "public fn caller() -> Int64 { callee(1) }\n");
               ("app::main/other", "fn callee(x: Int64) -> Int64 { x + 1 }\n");
             ])
        ~exactly:
          [
            Any (Import_check (Support.parse_file "app::main"));
            Any (Import_check (Support.parse_file "app::main/other"));
            Any (Namespace app);
            Any (Parsed (Support.parse_file "app::main"));
            Any (Parsed (Support.parse_file "app::main/other"));
          ]);
  Harness.test "an edit to a body recomputes no part of a caller" (fun () ->
      expect_untouched
        (list_propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 { x + 2 }\n\
                  public fn caller() -> Int64 { callee(1) }\n" );
             ])
        ~is_excluded:(is_part_of [ make_main_path "caller" ]));
  Harness.test "an edit to a signature recomputes the callers" (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app::main", callee_and_caller) ]
          ~after:
            [
              ( "app::main",
                "fn callee(x: Int32) -> Int64 { 1 }\npublic fn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      if not (List.mem (Database.Part.Any (Checked_body (make_main_key "caller"))) recomputed) then
        Harness.fail "recomputed only %s" (show_parts recomputed));
  Harness.test "an edit to an ensures recomputes the callers' proofs and not their checks"
    (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app::main", callee_and_caller) ]
          ~after:
            [
              ( "app::main",
                "fn callee(x: Int64) -> Int64 ensures result == 1 { 1 }\n\
                 public fn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      if not (List.mem (Database.Part.Any (Proof (make_main_key "caller"))) recomputed) then
        Harness.fail "recomputed only %s" (show_parts recomputed);
      expect_untouched recomputed
        ~is_excluded:(( = ) (Database.Part.Any (Checked_body (make_main_key "caller")))));
  Harness.test "adding the definition that a call names fixes the call" (fun () ->
      ignore
        (list_propagated
           ~before:[ ("app::main", "public fn caller() -> Int64 { callee(1) }\n") ]
           ~after:[ ("app::main", callee_and_caller) ]));
  Harness.test "removing a definition deletes its parts and fails its callers" (fun () ->
      expect_untouched
        (list_propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:[ ("app::main", "public fn caller() -> Int64 { callee(1) }\n") ])
        ~is_excluded:(is_part_of [ make_main_path "callee" ]));
  Harness.test "a field that makes a type not plain recomputes the types that hold it" (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app::main", "type Inner(value: Int64)\ntype Outer(inner: Inner)\n") ]
          ~after:[ ("app::main", "type Inner(value: String)\ntype Outer(inner: Inner)\n") ]
      in
      if not (List.mem (Database.Part.Any (Type_facts (make_main_path "Outer"))) recomputed) then
        Harness.fail "recomputed only %s" (show_parts recomputed));
  Harness.test "a body that compares a type reads its impls and not the impl index" (fun () ->
      expect_reads
        (check_text
           "type Box(value: Int64) derives Equal\n\
            fn same(left: Box, right: Box) -> Bool { left == right }\n")
        (Any (Checked_body (make_main_key "same")))
        ~includes:[ Name (Impls_of_type (app, make_main_path "Box")) ]
        ~excludes:[ Name (Impl_index app); Name (Impl_index Path.standard_package) ]);
  Harness.test
    "a call that closes a cycle recomputes the proofs of the cycle's members and no other"
    (fun () ->
      let recomputed =
        list_propagated ~before:[ ("app::main", acyclic) ] ~after:[ ("app::main", cyclic) ]
      in
      expect_included recomputed
        ~parts:
          [
            Any (Recursion_group (make_main_path "f"));
            Any (Recursion_group (make_main_path "g"));
            Any (Proof (make_main_key "f"));
            Any (Proof (make_main_key "g"));
          ];
      expect_untouched recomputed ~is_excluded:(fun part ->
          is_part_of [ make_main_path "h" ] part || part = Any (Checked_body (make_main_key "f"))));
  Harness.test "removing the call that closes a cycle splits its recursion group" (fun () ->
      let recomputed =
        list_propagated ~before:[ ("app::main", cyclic) ] ~after:[ ("app::main", acyclic) ]
      in
      expect_included recomputed
        ~parts:[ Any (Proof (make_main_key "f")); Any (Proof (make_main_key "g")) ];
      expect_untouched recomputed ~is_excluded:(fun part ->
          is_part_of [ make_main_path "h" ] part || part = Any (Checked_body (make_main_key "f"))));
  Harness.test
    "an impl that closes a cycle through a trait method recomputes the proofs on the cycle"
    (fun () ->
      expect_included
        (list_propagated
           ~before:[ ("app::main", stepper) ]
           ~after:[ ("app::main", stepper_that_runs) ])
        ~parts:
          [
            Any (Call_edges (make_method (make_main_path "Step") "step" Own, app));
            Any (Proof (make_main_key "run"));
          ]);
  Harness.test "only a trait method's call edges read the dependencies of the calling package"
    (fun () ->
      let database = build [ ("app::main", stepper_that_runs) ] in
      let dependencies : Database.Part.t list =
        [ Input (Dependencies app); Input (Dependencies Path.standard_package) ]
      in
      expect_reads database
        (Any (Call_edges (make_method (make_main_path "Step") "step" Own, app)))
        ~includes:dependencies ~excludes:[];
      expect_reads database
        (Any (Call_edges (make_main_path "run", app)))
        ~includes:[] ~excludes:dependencies);
  Harness.test
    "a construction that runs a field default that fails adds no call edge to the default's callee"
    (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app::main", make_configured_source "Config(size: 1)") ]
          ~after:[ ("app::main", make_configured_source "Config()") ]
      in
      expect_included recomputed ~parts:[ Any (Mir_call_edges (make_main_path "make")) ];
      expect_untouched recomputed ~is_excluded:(function
        | Any (Recursion_group _) -> true
        | _ -> false));
  Harness.test "a derived method's MIR call edges read its generated MIR" (fun () ->
      expect_reads
        (build [ ("app::main", version_deriving_over_a_key) ])
        (Any (Mir_call_edges derived_version_default))
        ~includes:[ Stored (Any (Generated_mir derived_version_default)) ]
        ~excludes:[]);
  Harness.test "a function that passes a derived impl where a bound needs one has a proof"
    (fun () ->
      let database = check_text version_deriving_over_a_key in
      let file = Support.parse_file "app::main" in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          match Database.For_testing.find_proof (Support.prove database file) declaration.key with
          | Some (Value _) -> ()
          | Some (Failed _ | Blocked) | None ->
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
           ~before:[ ("app::main", version_deriving_over_a_key) ]
           ~after:[ ("app::main", version_deriving_over_a_loop) ])
        ~parts:
          [
            Any (Mir_call_edges derived_version_default);
            Any (Recursion_group (make_main_path "check"));
            Any (Proof (make_main_key "check"));
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
           ~before:[ ("app::main", version_deriving_over_a_key) ]
           ~after:[ ("app::main", version_with_a_written_default) ])
        ~parts:
          [ Any (Recursion_group (make_main_path "check")); Any (Proof (make_main_key "check")) ];
      expect_included
        (list_propagated
           ~before:[ ("app::main", version_with_a_written_default) ]
           ~after:[ ("app::main", version_deriving_over_a_key) ])
        ~parts:
          [
            Any (Mir_call_edges derived_version_default);
            Any (Call_edges (derived_version_default, app));
            Any (Proof (make_main_key "check"));
          ]);
  Harness.test "an inherited method's MIR call edges read the MIR of its trait's provided body"
    (fun () ->
      expect_reads
        (build [ ("app::main", make_level_source ~height:"self.height") ])
        (Any (Mir_call_edges raised_of_shelf))
        ~includes:
          [
            Stored (Any (Body_mir (make_key (make_method (make_main_path "Level") "raised" Read))));
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
           ~before:[ ("app::main", make_level_source ~height:"self.height") ]
           ~after:[ ("app::main", make_level_source ~height:"floor(self)") ])
        ~parts:[ Any (Recursion_group raised_of_shelf); Any (Proof (make_main_key "floor")) ]);
  Harness.test "removing a function that a function of its package calls matches a cold build"
    (fun () ->
      ignore
        (list_propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:[ ("app::main", "fn caller() -> Int64 { callee(1) }\n") ]));
  Harness.test "removing a function that another package calls matches a cold build" (fun () ->
      ignore
        (propagate_with_lib ~before:tool_user
           ~after:[ List.hd tool_user; ("lib::tools", "public fn other() -> Int64 { 2 }\n") ]));
  Harness.test "removing an impl that a call through `any` reaches matches a cold build" (fun () ->
      ignore
        (list_propagated
           ~before:[ ("app::main", stepper_that_runs) ]
           ~after:[ ("app::main", stepper) ]));
  Harness.test
    "removing a provided method that another package's call graph reaches through an impl matches \
     a cold build" (fun () ->
      let provided = "\n  fn raised(self) -> Int64 {\n    self.height()\n  }\n" in
      let with_raised = [ ("app::main", level_user); ("lib::tools", make_level_library ~provided) ]
      and without_raised =
        [ ("app::main", level_user); ("lib::tools", make_level_library ~provided:"") ]
      in
      expect_included
        (propagate_with_lib ~before:without_raised ~after:with_raised)
        ~parts:[ Any (Call_edges (raised_of_library_shelf, app)) ];
      expect_included
        (propagate_with_lib ~before:with_raised ~after:without_raised)
        ~parts:[ Any (Call_edges (raised_of_library_shelf, app)) ]);
  Harness.test
    "a dependency's body that fails reports its error and hides a recursion through it only until \
     the body is fixed" (fun () ->
      let with_follow follow =
        [ ("app::main", hop_stepping_through_a_library); ("lib::tools", make_step_library ~follow) ]
      in
      let failing = with_follow "node.next.step(node) + missing"
      and fixed = with_follow "node.next.step(node)" in
      let settle files =
        Support.make_database (Support.setup ~dependencies:[ ("app", "lib") ] files)
      in
      let with_failing_body = settle failing in
      (match
         Support.list_codes
           (Database.list_file_diagnostics with_failing_body (Support.parse_file "lib::tools"))
       with
      | [ "resolve.unknown_name" ] -> ()
      | codes -> Harness.fail "the dependency reports [%s]" (String.concat ", " codes));
      if count_termination_obligations with_failing_body ~of_:step_of_hop <> 0 then
        Harness.fail "the proof makes a termination obligation while the body fails";
      expect_included
        (propagate_with_lib ~before:failing ~after:fixed)
        ~parts:
          [
            Any (Call_edges (Support.make_top_path "lib::tools" "follow", app));
            Any (Proof (make_key step_of_hop));
          ];
      if count_termination_obligations (settle fixed) ~of_:step_of_hop <> 1 then
        Harness.fail "the proof makes no termination obligation for the recursion");
  Harness.test
    "adding a file and then removing it recomputes no part of the other file's definitions"
    (fun () ->
      let without_helper = [ ("app::main", callee_and_caller) ] in
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
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 requires x > 0 { x }\n\
                  public fn caller() -> Int64 { callee(1) }\n" );
             ]
           ~after:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64\n\
                 \  requires x > 0\n\
                  {\n\
                 \  x\n\
                  }\n\
                  public fn caller() -> Int64 { callee(1) }\n" );
             ])
        ~exactly:
          [
            Any (Import_check (Support.parse_file "app::main"));
            Any (Namespace app);
            Any (Parsed (Support.parse_file "app::main"));
          ]);
  Harness.test "an edit to a callee's body recomputes its lowered code and not its caller's"
    (fun () ->
      let recomputed =
        list_propagated_with_roots ~roots:[ "caller" ]
          ~before:[ ("app::main", callee_and_caller) ]
          ~after:
            [
              ( "app::main",
                "fn callee(x: Int64) -> Int64 { x + 2 }\n\
                 public fn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      expect_included recomputed
        ~parts:[ make_lowered "callee"; make_test_key "callee"; make_test_key "caller" ];
      expect_untouched recomputed ~is_excluded:(( = ) (make_lowered "caller")));
  Harness.test "a call that is removed with its callee collects the callee's lowered code"
    (fun () ->
      expect_untouched
        (list_propagated_with_roots ~roots:[ "caller" ]
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:[ ("app::main", "fn caller() -> Int64 { 1 }\n") ])
        ~is_excluded:(( = ) (make_lowered "callee")));
  Harness.test "a removed reference collects exactly the items that only it reached" (fun () ->
      let make_program test =
        [
          ( "app::main",
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
      if observed.collected <> List.sort compare [ make_lowered "only"; make_test_key "only" ] then
        Harness.fail "collected %s" (show_parts observed.collected);
      expect_untouched observed.recomputed ~is_excluded:(fun part ->
          List.mem part [ make_lowered "shared"; make_lowered "kept" ]));
  Harness.test "removing a type collects the items at that type without computing them" (fun () ->
      let make_program shape =
        [
          ( "app::main",
            shape
            ^ "test \"lists\" {\n\
              \  let shapes = [Shape(size: 1)]\n\
              \  assert shapes.length() == 1\n\
               }\n" );
        ]
      in
      expect_untouched
        (list_propagated
           ~before:(make_program "type Shape(size: Int64)\n")
           ~after:(make_program ""))
        ~is_excluded:(function
          | Any (Lowered item | Test_key item) ->
              String.includes ~affix:"[Shape]" (Lowered.Item.to_string item)
          | _ -> false));
  Harness.test "a test that reaches a type defined as todo is blocked until the type is defined"
    (fun () ->
      let make_program definition =
        [
          ( "app::main",
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
        [ ("app::main", "type Chain(next: " ^ held ^ ")\nfn size(chain: Chain) -> Int64 { 1 }\n") ]
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
          ( "app::main",
            "let first: Int64 = " ^ first
            ^ "\nlet second: Int64 = first + 1\nfn read() -> Int64 { second }\n" );
        ]
      in
      let recomputed =
        list_propagated_with_roots ~roots:[ "read" ] ~before:(make_constants "1")
          ~after:(make_constants "2")
      in
      expect_included recomputed ~parts:[ Any (Lowered (Constant (make_main_path "second"))) ];
      expect_untouched recomputed
        ~is_excluded:(( = ) (Database.Part.Any (Lowered (Constant (make_main_path "first"))))));
  Harness.test "adding a dependency to a manifest fixes the dependent's use of it" (fun () ->
      expect_included
        (lay_out_again ~before:(Support.setup tool_user)
           ~after:(Support.setup ~dependencies:[ ("app", "lib") ] tool_user)
           ())
        ~parts:[ Any (Namespace app); Any (Checked_body (make_main_key "caller")) ]);
  Harness.test "adding a package and then removing it matches a cold build each time" (fun () ->
      let alone = Support.setup [ ("app::main", "fn caller() -> Int64 { 1 }\n") ] in
      let with_lib = Support.setup ~dependencies:[ ("app", "lib") ] tool_user in
      ignore (lay_out_again ~before:alone ~after:with_lib ());
      expect_untouched (lay_out_again ~before:with_lib ~after:alone ()) ~is_excluded:(fun part ->
          Database.Part.locate_package part = { Path.owner = None; name = "lib" }));
  Harness.test "a new version of a loaded package recomputes only the readers of what changed"
    (fun () ->
      let make_version second =
        load_package
          [
            ( "lib::tools",
              "public fn first() -> Int64 { 1 }\npublic fn second() -> " ^ second ^ " { 2 }\n" );
          ]
      in
      let app =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [
            ( "app::main",
              "use lib::tools\n\
               fn uses_first() -> Int64 { tools::first() }\n\
               fn uses_second() -> Int64 { 1 }\n\
               fn calls_second() { tools::second() }\n" );
          ]
      in
      let recomputed =
        lay_out_again
          ~loaded:([ make_version "Int64" ], [ make_version "Int32" ])
          ~before:app ~after:app ()
      in
      expect_included recomputed ~parts:[ Any (Checked_body (make_main_key "calls_second")) ];
      expect_untouched recomputed
        ~is_excluded:(is_part_of [ make_main_path "uses_first"; make_main_path "uses_second" ]));
  Harness.test
    "reformatting an invariant recomputes the derived Deserialize and none of its readers"
    (fun () ->
      let make_signup invariant =
        [
          ( "app::main",
            "use standard::serialization\ntype Signup(age: UInt32)\n  invariant " ^ invariant
            ^ "\n  derives serialization::Deserialize\n" );
        ]
      in
      expect_recomputed
        (list_propagated ~before:(make_signup "age >= 13") ~after:(make_signup "age  >=\t13"))
        ~exactly:
          [
            Any
              (Generated_mir
                 (make_method
                    (Derived
                       {
                         type_ = make_main_path "Signup";
                         trait = Support.make_top_path "standard::serialization" "Deserialize";
                       })
                    "deserialize" Static));
            Any (Import_check (Support.parse_file "app::main"));
            Any (Namespace app);
            Any (Package_check (app, Type (make_main_key "Signup")));
            Any (Parsed (Support.parse_file "app::main"));
          ])

let make_lowered_program test =
  [
    ( "app::main",
      "type Box(value: Int64) derives Equal\n\
       let base: Int64 = 2\n\
       fn shared() -> Int64 { base }\n\
       fn only() -> Int64 { shared() + 1 }\n\
       fn kept() -> Int64 { shared() }\n\
       fn same(left: Box, right: Box) -> Bool { left == right }\n\
       test \"sums\" {\n\
      \  assert " ^ test ^ "\n}\n" );
    ("app::main/cycle", cyclic);
  ]

let () =
  Harness.test "a database saved after a cold build and reopened recomputes nothing" (fun () ->
      let files = make_lowered_program "kept() + only() == 5" in
      let log = commit [] (list_saved (build ~roots:[ "same" ] files)) in
      expect_recomputed (observe_reopen ~roots:[ "same" ] log files).recomputed ~exactly:[]);
  Harness.test "a database reopened with a changed file recomputes what propagating the change does"
    (fun () ->
      let before = [ ("app::main", callee_and_caller) ] in
      let after =
        [
          ( "app::main",
            "fn callee(x: Int64) -> Int64 { x + 2 }\npublic fn caller() -> Int64 { callee(1) }\n" );
        ]
      in
      let log = commit [] (list_saved (build before)) in
      expect_recomputed (observe_reopen log after).recomputed
        ~exactly:(remove_rebuilt_on_reopen (list_propagated ~before ~after)));
  Harness.test "a database reopened without a file it saved removes the file's definitions"
    (fun () ->
      let log = commit [] (list_saved (build with_helper)) in
      ignore (observe_reopen log [ ("app::main", callee_and_caller) ]));
  Harness.test "a database saved after a change set reopens as the propagated database" (fun () ->
      let before = make_lowered_program "kept() + only() == 5" in
      let after = make_lowered_program "kept() == 2" in
      let hot = build before in
      let log = commit [] (list_saved hot) in
      ignore (propagate hot ~before ~after);
      let log = commit log (list_saved hot) in
      expect_recomputed (observe_reopen log after).recomputed ~exactly:[]);
  Harness.test "a database saved after a partial drain reopens with its stale parts" (fun () ->
      let before = make_lowered_program "kept() + only() == 5" in
      let after = make_lowered_program "kept() == 2" in
      let hot = build before in
      let log = commit [] (list_saved hot) in
      Database.update hot (list_changes ~before ~after);
      let log = commit log (list_saved hot) in
      let (), propagated =
        Database.For_testing.observe (fun () -> Database.For_testing.propagate hot)
      in
      expect_recomputed (observe_reopen log after).recomputed
        ~exactly:(remove_rebuilt_on_reopen propagated.recomputed));
  Harness.test "a database saved after a package is removed reopens without the package" (fun () ->
      let with_lib = Support.setup ~dependencies:[ ("app", "lib") ] tool_user in
      let alone = [ ("app::main", "fn caller() -> Int64 { 1 }\n") ] in
      let hot = settle [] with_lib in
      let log = commit [] (list_saved hot) in
      Database.relayout hot ~loaded:[ Lazy.force standard ] (Support.setup alone);
      Database.For_testing.propagate hot;
      let log = commit log (list_saved hot) in
      expect_recomputed (observe_reopen log alone).recomputed ~exactly:[])

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
  | parts ->
      Harness.fail "the database in .truss differs from a cold build in %s" (show_parts parts));
  remove_rebuilt_on_reopen observed.recomputed

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
      expect_recomputed copied ~exactly:propagated);
  Harness.test "an interrupted commit leaves the database as it was before the change set"
    (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settle_on_disk root);
      Workspace.flush ();
      Harness.write_files root [ ("main/main.truss", edited_body) ];
      ignore (settle_on_disk root);
      Workspace.For_testing.interrupt_commit (Workspace.locate_root (open_workspace root));
      Harness.write_files root [ ("main/main.truss", callee_and_caller) ];
      expect_recomputed (settle_on_disk root) ~exactly:[];
      Workspace.flush ());
  Harness.test "a database written by another compiler is rebuilt" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settle_on_disk root);
      Workspace.flush ();
      let list = Filename.concat root ".truss/list" in
      let digest = Workspace.For_testing.compiler_digest in
      (match String.split_first ~sep:digest (File_system.read list) with
      | Some (before, after) ->
          File_system.write list (before ^ String.make (String.length digest) '0' ^ after)
      | None -> Harness.fail "the list does not name the compiler");
      expect_included (settle_on_disk root) ~parts:[ Any (Checked_body (make_main_key "caller")) ];
      Workspace.flush ());
  Harness.test "a database whose list is in the earlier text format is rebuilt" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      ignore (settle_on_disk root);
      Workspace.flush ();
      File_system.write
        (Filename.concat root ".truss/list")
        ("truss database\nheader compiler " ^ Workspace.For_testing.compiler_digest ^ "\n");
      expect_included (settle_on_disk root) ~parts:[ Any (Checked_body (make_main_key "caller")) ];
      Workspace.flush ())

let expect_cold database snapshot =
  let cold = Workspace.For_testing.build_cold_database snapshot in
  Database.For_testing.propagate cold;
  match Database.For_testing.list_differences database cold with
  | [] -> ()
  | parts -> Harness.fail "the database differs from a cold build in %s" (show_parts parts)

let () =
  Harness.test "a trial is a copy of the database, propagated with the files that differ" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      let snapshot = open_workspace root in
      let worktree = Workspace.open_database snapshot in
      Database.For_testing.propagate worktree;
      let trial = Workspace.make_trial snapshot [ ("main/main.truss", Some edited_body) ] in
      let database, observed =
        Database.For_testing.observe (fun () ->
            let database = Workspace.open_database trial in
            Database.For_testing.propagate database;
            database)
      in
      let recomputed = observed.recomputed in
      expect_included recomputed ~parts:[ Any (Checked_body (make_main_key "callee")) ];
      expect_untouched recomputed ~is_excluded:(is_part_of [ make_main_path "caller" ]);
      expect_cold database trial;
      expect_cold worktree snapshot;
      Workspace.flush ());
  Harness.test "a trial that renames the package leaves the worktree's database as it was"
    (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      let snapshot = open_workspace root in
      let worktree = Workspace.open_database snapshot in
      Database.For_testing.propagate worktree;
      let trial =
        Workspace.make_trial snapshot
          [ ("truss.toml", Some "[package]\nname = \"tool\"\ntruss = \"0.1\"\n") ]
      in
      let database = Workspace.open_database trial in
      Database.For_testing.propagate database;
      expect_cold database trial;
      expect_cold worktree snapshot;
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
      let database = build [ ("app::main", callee_and_caller) ] in
      match snd (Database.count (fun () -> Database.For_testing.propagate database)) with
      | [] -> ()
      | counts -> Harness.fail "counted %s" (String.concat "; " (List.map show_counts counts)));
  Harness.test
    "a computed part whose value comes out unchanged is counted as unchanged, not written"
    (fun () ->
      let before = [ ("app::main", callee_and_caller) ] in
      let after =
        [
          ( "app::main",
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
      let count_checked_bodies caller_body =
        extract_counts
          (count_cold_build
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 { x + 1 }\nfn caller() -> Int64 { " ^ caller_body
                 ^ " }\n" );
             ])
          "checked body"
      in
      let once = count_checked_bodies "callee(1)"
      and twice = count_checked_bodies "callee(callee(1))" in
      if twice.distinct_reads <> once.distinct_reads || twice.reads <= once.reads then
        Harness.fail "counted %s with one call and %s with two" (show_counts once)
          (show_counts twice));
  Harness.test "removing a definition counts the removal of its checked body as a write" (fun () ->
      let before = [ ("app::main", "fn unused() -> Int64 { 1 }\nfn kept() -> Int64 { 2 }\n") ] in
      let after = [ ("app::main", "fn kept() -> Int64 { 2 }\n") ] in
      let checked_bodies =
        extract_counts (count_propagation (build before) ~before ~after) "checked body"
      in
      if (checked_bodies.computed, checked_bodies.writes) <> (0, 1) then
        Harness.fail "counted %s" (show_counts checked_bodies));
  Harness.test "counting an operation counts the work of a database that the operation copies"
    (fun () ->
      let before = [ ("app::main", callee_and_caller) ] in
      let after = [ ("app::main", edited_body) ] in
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
  Harness.test "a namespace whose names come out unchanged is counted as unchanged, not written"
    (fun () ->
      let before = [ ("app::main", callee_and_caller) ] in
      let after = [ ("app::main", callee_and_caller ^ "\n") ] in
      let namespaces =
        extract_counts (count_propagation (build before) ~before ~after) "namespace"
      in
      if (namespaces.computed, namespaces.unchanged, namespaces.writes) <> (1, 1, 0) then
        Harness.fail "counted %s" (show_counts namespaces));
  Harness.test "a new version of a loaded package counts a write of each part that differs"
    (fun () ->
      let make_version second =
        load_package
          [
            ( "lib::tools",
              "public fn first() -> Int64 { 1 }\npublic fn second() -> " ^ second ^ " { 2 }\n" );
          ]
      in
      let app =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [ ("app::main", "use lib::tools\nfn calls_second() { tools::second() }\n") ]
      in
      let hot = settle [ make_version "Int64" ] app in
      let newer = make_version "Int32" in
      let _, counts =
        Database.count (fun () ->
            Database.relayout hot ~loaded:[ Lazy.force standard; newer ] app;
            Database.For_testing.propagate hot)
      in
      let interfaces = extract_counts counts "interface" in
      if (interfaces.computed, interfaces.writes) <> (0, 1) then
        Harness.fail "counted %s" (show_counts interfaces))

let () =
  Harness.test "adding a file to a module recomputes the namespace, which reads the files"
    (fun () ->
      expect_included
        (list_propagated
           ~before:[ ("app::main", "fn first() -> Int64 { 1 }\n") ]
           ~after:
             [
               ("app::main", "fn first() -> Int64 { 1 }\n");
               ("app::main/second", "fn second() -> Int64 { first() }\n");
             ])
        ~parts:[ Any (Namespace app); Any (Checked_body (make_main_key "second")) ]);
  Harness.test "adding the module that a use names matches a cold build" (fun () ->
      let user =
        ("app::main", "use app::tools\n\nfn caller() -> Int64 {\n  tools::helper()\n}\n")
      in
      expect_included
        (list_propagated ~before:[ user ]
           ~after:[ user; ("app::tools", "public fn helper() -> Int64 { 1 }\n") ])
        ~parts:[ Any (Checked_body (make_main_key "caller")) ]);
  let read_callee_ownership database =
    Database.For_testing.read_ownership database (make_main_key "callee")
  in
  let propagate_with_failing_callee () =
    let database = build [ ("app::main", callee_and_caller) ] in
    Database.For_testing.with_failing_part
      (Any (Ownership (make_main_key "callee")))
      (fun () ->
        Database.update ~on_bug:ignore database
          [
            ( Support.parse_file "app::main",
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
      | Failed _ | Blocked -> Harness.fail "the part did not compute");
  Harness.test "a request's reads are counted as untracked, and the request computes nothing"
    (fun () ->
      let database = build [ ("app::main", callee_and_caller) ] in
      match
        snd
          (Database.count (fun () ->
               ignore (Database.list_file_diagnostics database (Support.parse_file "app::main"))))
      with
      | [ { kind = "untracked"; computed = 0; writes = 0; reads; _ } ] when reads > 0 -> ()
      | counts -> Harness.fail "counted %s" (String.concat "; " (List.map show_counts counts)))

let () =
  Harness.test "a package database records the diagnostics of its package, and none when it checks"
    (fun () ->
      let clean = load_package [ ("lib::tools", "public fn first() -> Int64 { 1 }\n") ] in
      let broken = load_package [ ("lib::tools", "public fn first() -> Int64 { \"one\" }\n") ] in
      if Database.list_package_diagnostics clean <> [] then
        Harness.fail "the package that checks records diagnostics";
      match Database.list_package_diagnostics broken with
      | [ (_, _ :: _) ] -> ()
      | failed -> Harness.fail "the broken package records %d files" (List.length failed))
