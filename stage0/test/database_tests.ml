let () =
  match Sys.argv with
  | [| _; "__serve"; key |] ->
      Workspace.serve ~key ~handle:(fun ~report_progress (request : string) ->
          report_progress "working";
          String.length request);
      Unix._exit 0
  | _ -> ()

let check_text text =
  let database = Support.make_database (Support.setup [ ("app::main", text) ]) in
  (match
     Support.list_codes (Support.list_diagnostics database (Support.parse_file "app::main"))
   with
  | [] -> ()
  | codes -> Harness.fail "the program has diagnostics: %s" (String.concat ", " codes));
  database

let expect_reads database part ~includes ~excludes =
  let reads = Database.For_testing.list_reads database part in
  List.iter
    (fun read ->
      if not (List.mem read reads) then
        Harness.fail "%s does not read %s; it reads %s" part read (String.concat ", " reads))
    includes;
  List.iter (fun read -> if List.mem read reads then Harness.fail "%s reads %s" part read) excludes

let show_lowered name = "lowered app::main::" ^ name
let test_key name = "test key app::main::" ^ name

let build ?(roots = []) files =
  let database = Support.make_database (Support.setup files) in
  List.iter
    (fun name ->
      Database.For_testing.add_root database
        (Code
           {
             path = Top { module_ = Support.parse_module "app::main"; name };
             instantiation = { type_arguments = []; capability_arguments = [] };
           }))
    roots;
  Database.propagate database;
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
  let observed =
    Database.For_testing.observe (fun () ->
        Database.update hot (list_changes ~before ~after);
        Database.propagate hot)
  in
  (match Database.For_testing.list_differences hot (build ?roots after) with
  | [] -> ()
  | parts ->
      Harness.fail "the propagated database differs from a cold build in %s"
        (String.concat ", " parts));
  observed

let list_propagated ~before ~after = (propagate (build before) ~before ~after).recomputed

let list_propagated_with_roots ~roots ~before ~after =
  (propagate ~roots (build ~roots before) ~before ~after).recomputed

let expect_recomputed recomputed ~exactly =
  if recomputed <> exactly then
    Harness.fail "recomputed %s, not %s" (String.concat ", " recomputed)
      (String.concat ", " exactly)

let expect_untouched recomputed ~names =
  List.iter
    (fun part ->
      if List.exists (fun name -> String.includes ~affix:name part) names then
        Harness.fail "recomputed %s; it recomputed %s" part (String.concat ", " recomputed))
    recomputed

let expect_included recomputed ~parts =
  List.iter
    (fun part ->
      if not (List.mem part recomputed) then
        Harness.fail "did not recompute %s; it recomputed %s" part (String.concat ", " recomputed))
    parts

let standard = lazy (Workspace.For_testing.load_standard_package_database ())

let settle loaded packages =
  let database = Database.create ~loaded:(Lazy.force standard :: loaded) packages in
  Database.propagate database;
  database

let lay_out_again ?(loaded = ([], [])) ~before ~after () =
  let hot = settle (fst loaded) before in
  let observed =
    Database.For_testing.observe (fun () ->
        Database.relayout hot ~loaded:(Lazy.force standard :: snd loaded) after;
        Database.propagate hot)
  in
  (match Database.For_testing.list_differences hot (settle (snd loaded) after) with
  | [] -> ()
  | parts ->
      Harness.fail "the relaid database differs from a cold build in %s" (String.concat ", " parts));
  observed.recomputed

let load_package files =
  let packages = Support.setup files in
  Database.read_package_database
    (Database.create ~loaded:[ Lazy.force standard ] packages)
    (List.hd packages).name

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
  let database = Database.restore ~loaded:[ Lazy.force standard ] ~find_text (list_live log) in
  Database.relayout database ~loaded:[ Lazy.force standard ] packages;
  database

let expect_cold ?roots database files =
  match Database.For_testing.list_differences database (build ?roots files) with
  | [] -> ()
  | parts ->
      Harness.fail "the reopened database differs from a cold build in %s"
        (String.concat ", " parts)

let observe_reopen ?roots log files =
  let database = reopen log files in
  let observed = Database.For_testing.observe (fun () -> Database.propagate database) in
  expect_cold ?roots database files;
  observed

let tool_user =
  [
    ("app::main", "use lib::tools\nfn caller() -> Int64 { tools::helper() }\n");
    ("lib::tools", "public fn helper() -> Int64 { 1 }\n");
  ]

let make_mutual_source body =
  Printf.sprintf
    "fn f(n: Int64) -> Int64\n\
    \  cost time finite\n\
     { g(n) }\n\
     fn g(n: Int64) -> Int64\n\
    \  cost time finite\n\
     { %s }\n\
     fn h() -> Int64 { f(1) }\n"
    body

let acyclic = make_mutual_source "n"
let cyclic = make_mutual_source "f(n)"

let stepper =
  "trait Step {\n\
  \  fn step(own self) -> Int64\n\
  \    cost time finite\n\
   }\n\
   fn run(value: own any Step) -> Int64\n\
  \  cost time finite\n\
   {\n\
  \  own value.step()\n\
   }\n\
   type Foo()\n"

let stepper_that_runs =
  stepper
  ^ "impl Step for Foo {\n\
    \  fn step(own self) -> Int64\n\
    \    cost time finite\n\
    \  {\n\
    \    let value: any Step = any self\n\
    \    run(own value)\n\
    \  }\n\
     }\n"

let make_configured_source construction =
  Printf.sprintf
    "type Config(size: Int64 = start())\n\
     fn start() -> Int64\n\
    \  cost time finite\n\
     { make().size }\n\
     fn make() -> Config\n\
    \  cost time finite\n\
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
    \  cost time finite\n\
     {\n\
    \  Item.default()\n\
     }\n\
     fn check() -> Version\n\
    \  cost time finite\n\
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

let derived_version_default = "derived standard::core::Default for app::main::Version.default"

let expect_recursion_group text ~of_:name ~expected =
  let database = build [ ("app::main", text) ] in
  let group =
    List.map Path.show
      ((Database.make_proof_lookups database).list_recursion_group
         (Support.make_top_path "app::main" name))
  in
  if group <> expected then
    Harness.fail "the recursion group of %s is [%s], not [%s]" name (String.concat "; " group)
      (String.concat "; " expected)

let make_level_source ~height =
  Printf.sprintf
    "trait Level {\n\
    \  fn height(self) -> Int64\n\
    \    cost time finite\n\n\
    \  fn raised(self) -> Int64\n\
    \    cost time finite\n\
    \  {\n\
    \    self.height()\n\
    \  }\n\
     }\n\n\
     type Shelf(height: Int64)\n\n\
     impl Level for Shelf {\n\
    \  fn height(self) -> Int64 {\n\
    \    %s\n\
    \  }\n\
     }\n\n\
     fn floor(shelf: Shelf) -> Int64\n\
    \  cost time finite\n\
     {\n\
    \  shelf.raised()\n\
     }\n"
    height

let raised_of_shelf = "app::main::impl app::main::Level for app::main::Shelf.raised"

let callee_and_caller =
  "fn callee(x: Int64) -> Int64 { x + 1 }\nfn caller() -> Int64 { callee(1) }\n"

let with_helper =
  [ ("app::main", callee_and_caller); ("app::extra", "fn helper() -> Int64 { 1 }\n") ]

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
      let program = Unix.realpath Sys.executable_name in
      let measure_served request =
        match Workspace.For_testing.call_starting ~program ~key ~report_progress:ignore request with
        | Ok (length : int) -> length
        | Error message ->
            Harness.fail "%s" message;
            -1
      in
      let wait_for_first_periodic_work () = ignore (measure_served "two") in
      Fun.protect
        ~finally:(fun () -> ignore (Workspace.stop_servers ()))
        (fun () ->
          ignore (measure_served "one");
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
          if measure_served "three" <> 5 then Harness.fail "the running process stopped answering"));
  Harness.test "the background process answers each request and sends its progress" (fun () ->
      Unix.putenv "TRUSS_CACHE" (Harness.make_scratch_directory "served-cache");
      let key = Harness.make_scratch_directory "served" in
      let program = Unix.realpath Sys.executable_name in
      let progressed = ref false in
      let measure_served request =
        match
          Workspace.For_testing.call_starting ~program ~key
            ~report_progress:(fun text -> if text = "working" then progressed := true)
            request
        with
        | Ok (length : int) -> length
        | Error message ->
            Harness.fail "%s" message;
            -1
      in
      Fun.protect
        ~finally:(fun () -> ignore (Workspace.stop_servers ()))
        (fun () ->
          let lengths = List.map measure_served [ "one"; "three"; "four" ] in
          if lengths <> [ 3; 5; 4 ] then
            Harness.fail "answered %s" (String.concat ", " (List.map string_of_int lengths));
          if not !progressed then Harness.fail "sent no progress"))

let () =
  Harness.test "a caller's checked body reads the callee's interface and not its body" (fun () ->
      expect_reads
        (check_text "fn callee(x: Int64) -> Int64 { x + 1 }\nfn caller() -> Int64 { callee(1) }\n")
        "checked body app::main::caller" ~includes:[ "interface app::main::callee" ]
        ~excludes:
          [
            "checked body app::main::callee";
            "tree app::main::callee";
            "resolved body app::main::callee";
          ]);
  Harness.test "a contract reads no resolved names of its body" (fun () ->
      expect_reads
        (check_text "fn f(x: Int64) -> Int64 requires x > 0 { x + 1 }\n")
        "contract app::main::f"
        ~includes:[ "resolved contract app::main::f" ]
        ~excludes:[ "resolved body app::main::f" ]);
  Harness.test "a checked body reads its callee's signature check" (fun () ->
      expect_reads
        (check_text "fn callee(x: Int64) -> Int64 { x + 1 }\nfn caller() -> Int64 { callee(1) }\n")
        "checked body app::main::caller"
        ~includes:[ "signature check app::main::callee" ]
        ~excludes:[]);
  Harness.test "a type's facts read interfaces and type facts, and no signature check" (fun () ->
      expect_reads
        (check_text "type Inner(value: Int64)\ntype Outer(inner: Inner)\n")
        "type facts app::main::Outer"
        ~includes:[ "interface app::main::Outer"; "type facts app::main::Inner" ]
        ~excludes:[ "signature check app::main::Outer"; "signature check app::main::Inner" ]);
  Harness.test "a caller's checked body and proof read no place or text of the callee" (fun () ->
      let database = check_text callee_and_caller in
      ignore (Database.prove database [ Support.parse_file "app::main" ]);
      List.iter
        (fun part ->
          expect_reads database part ~includes:[]
            ~excludes:[ "place app::main::callee"; "text app::main::callee" ])
        [ "checked body app::main::caller"; "proof app::main::caller" ]);
  Harness.test "a package check reads no place" (fun () ->
      expect_reads
        (check_text "type Inner(value: Int64)\ntype Outer(inner: Inner)\n")
        "package check app type app::main::Outer" ~includes:[ "tree app::main::Outer" ]
        ~excludes:[ "place app::main::Outer"; "place app::main::Inner" ]);
  Harness.test "a reformat inside a definition recomputes only that definition's proof" (fun () ->
      expect_recomputed
        (list_propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 {\n  x + 1\n}\nfn caller() -> Int64 { callee(1) }\n"
               );
             ])
        ~exactly:
          [
            "import check app/main/main.truss";
            "namespace app";
            "parsed app/main/main.truss";
            "proof app::main::callee";
          ]);
  Harness.test "moving a definition to another file of its module recomputes no definition's part"
    (fun () ->
      expect_recomputed
        (list_propagated
           ~before:[ ("app::main", callee_and_caller); ("app::main/other", "") ]
           ~after:
             [
               ("app::main", "fn caller() -> Int64 { callee(1) }\n");
               ("app::main/other", "fn callee(x: Int64) -> Int64 { x + 1 }\n");
             ])
        ~exactly:
          [
            "import check app/main/main.truss";
            "import check app/main/other.truss";
            "namespace app";
            "parsed app/main/main.truss";
            "parsed app/main/other.truss";
          ]);
  Harness.test "an edit to a body recomputes no part of a caller" (fun () ->
      expect_untouched
        (list_propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 { x + 2 }\nfn caller() -> Int64 { callee(1) }\n" );
             ])
        ~names:[ "caller" ]);
  Harness.test "an edit to a signature recomputes the callers" (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app::main", callee_and_caller) ]
          ~after:
            [
              ( "app::main",
                "fn callee(x: Int32) -> Int64 { 1 }\nfn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      if not (List.mem "checked body app::main::caller" recomputed) then
        Harness.fail "recomputed only %s" (String.concat ", " recomputed));
  Harness.test "an edit to an ensures recomputes the callers' proofs and not their checks"
    (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app::main", callee_and_caller) ]
          ~after:
            [
              ( "app::main",
                "fn callee(x: Int64) -> Int64 ensures result == 1 { 1 }\n\
                 fn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      if not (List.mem "proof app::main::caller" recomputed) then
        Harness.fail "recomputed only %s" (String.concat ", " recomputed);
      expect_untouched recomputed ~names:[ "checked body app::main::caller" ]);
  Harness.test "adding the definition that a call names fixes the call" (fun () ->
      ignore
        (list_propagated
           ~before:[ ("app::main", "fn caller() -> Int64 { callee(1) }\n") ]
           ~after:[ ("app::main", callee_and_caller) ]));
  Harness.test "removing a definition deletes its parts and fails its callers" (fun () ->
      expect_untouched
        (list_propagated
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:[ ("app::main", "fn caller() -> Int64 { callee(1) }\n") ])
        ~names:[ "app::main::callee" ]);
  Harness.test "a field that makes a type not plain recomputes the types that hold it" (fun () ->
      let recomputed =
        list_propagated
          ~before:[ ("app::main", "type Inner(value: Int64)\ntype Outer(inner: Inner)\n") ]
          ~after:[ ("app::main", "type Inner(value: String)\ntype Outer(inner: Inner)\n") ]
      in
      if not (List.mem "type facts app::main::Outer" recomputed) then
        Harness.fail "recomputed only %s" (String.concat ", " recomputed));
  Harness.test "a body that compares a type reads its impls and not the impl index" (fun () ->
      expect_reads
        (check_text
           "type Box(value: Int64) derives Equal\n\
            fn same(left: Box, right: Box) -> Bool { left == right }\n")
        "checked body app::main::same"
        ~includes:[ "impls of type app app::main::Box" ]
        ~excludes:[ "impl index app"; "impl index standard" ]);
  Harness.test
    "a call that closes a cycle recomputes the proofs of the cycle's members and no other"
    (fun () ->
      let recomputed =
        list_propagated ~before:[ ("app::main", acyclic) ] ~after:[ ("app::main", cyclic) ]
      in
      expect_included recomputed
        ~parts:
          [
            "recursion group app::main::f";
            "recursion group app::main::g";
            "proof app::main::f";
            "proof app::main::g";
          ];
      expect_untouched recomputed ~names:[ "app::main::h"; "checked body app::main::f" ]);
  Harness.test "removing the call that closes a cycle splits its recursion group" (fun () ->
      let recomputed =
        list_propagated ~before:[ ("app::main", cyclic) ] ~after:[ ("app::main", acyclic) ]
      in
      expect_included recomputed ~parts:[ "proof app::main::f"; "proof app::main::g" ];
      expect_untouched recomputed ~names:[ "app::main::h"; "checked body app::main::f" ]);
  Harness.test
    "an impl that closes a cycle through a trait method recomputes the proofs on the cycle"
    (fun () ->
      expect_included
        (list_propagated
           ~before:[ ("app::main", stepper) ]
           ~after:[ ("app::main", stepper_that_runs) ])
        ~parts:[ "call edges app app::main::Step.step(own self)"; "proof app::main::run" ]);
  Harness.test "only a trait method's call edges read the dependencies of the calling package"
    (fun () ->
      let database = build [ ("app::main", stepper_that_runs) ] in
      let dependencies = [ "dependencies app"; "dependencies standard" ] in
      expect_reads database "call edges app app::main::Step.step(own self)" ~includes:dependencies
        ~excludes:[];
      expect_reads database "call edges app app::main::run" ~includes:[] ~excludes:dependencies);
  Harness.test
    "a construction that runs a field default joins the recursion group of the default's callee"
    (fun () ->
      expect_included
        (list_propagated
           ~before:[ ("app::main", make_configured_source "Config(size: 1)") ]
           ~after:[ ("app::main", make_configured_source "Config()") ])
        ~parts:
          [
            "MIR call edges app::main::make";
            "recursion group app::main::make";
            "recursion group app::main::start";
            "proof app::main::start";
          ]);
  Harness.test "a derived method's MIR call edges read its generated MIR" (fun () ->
      expect_reads
        (build [ ("app::main", version_deriving_over_a_key) ])
        ("MIR call edges " ^ derived_version_default)
        ~includes:[ "generated mir " ^ derived_version_default ]
        ~excludes:[]);
  Harness.test "a function that passes a derived impl where a bound needs one has a proof"
    (fun () ->
      let database = check_text version_deriving_over_a_key in
      let file = Support.parse_file "app::main" in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          match
            Database.For_testing.find_proof (Support.prove database file)
              (Resolve.Names.make_key declaration)
          with
          | Some (Value _) -> ()
          | Some (Failed _ | Blocked) | None ->
              Harness.fail "%s has no proof" (Path.show declaration.path))
        ((Database.make_name_lookups database [ file.module_.package ]).list_declarations_in file));
  Harness.test
    "a field's type whose impl calls back joins the recursion group of a function that passes the \
     derived impl where a bound needs one" (fun () ->
      expect_recursion_group version_deriving_over_a_key ~of_:"check" ~expected:[];
      expect_recursion_group version_deriving_over_a_loop ~of_:"check"
        ~expected:
          [
            "app::main::check";
            "app::main::impl standard::core::Default for app::main::Loop.default";
            derived_version_default;
          ];
      expect_included
        (list_propagated
           ~before:[ ("app::main", version_deriving_over_a_key) ]
           ~after:[ ("app::main", version_deriving_over_a_loop) ])
        ~parts:
          [
            "MIR call edges " ^ derived_version_default;
            "recursion group app::main::check";
            "proof app::main::check";
          ]);
  Harness.test
    "a trait leaving a type's `derives` list takes the derived method out of the call graph"
    (fun () ->
      expect_recursion_group version_with_a_written_default ~of_:"check"
        ~expected:
          [
            "app::main::check";
            "app::main::impl standard::core::Default for app::main::Version.default";
          ];
      expect_included
        (list_propagated
           ~before:[ ("app::main", version_deriving_over_a_key) ]
           ~after:[ ("app::main", version_with_a_written_default) ])
        ~parts:[ "recursion group app::main::check"; "proof app::main::check" ];
      expect_included
        (list_propagated
           ~before:[ ("app::main", version_with_a_written_default) ]
           ~after:[ ("app::main", version_deriving_over_a_key) ])
        ~parts:
          [
            "MIR call edges " ^ derived_version_default;
            "call edges app " ^ derived_version_default;
            "proof app::main::check";
          ]);
  Harness.test "an inherited method's MIR call edges read the MIR of its trait's provided body"
    (fun () ->
      expect_reads
        (build [ ("app::main", make_level_source ~height:"self.height") ])
        ("MIR call edges " ^ raised_of_shelf)
        ~includes:[ "body mir app::main::Level.raised" ]
        ~excludes:[]);
  Harness.test
    "an impl's method that calls the caller of a method the impl inherits joins their recursion \
     group" (fun () ->
      expect_recursion_group (make_level_source ~height:"self.height") ~of_:"floor" ~expected:[];
      expect_recursion_group
        (make_level_source ~height:"floor(self)")
        ~of_:"floor"
        ~expected:
          [
            "app::main::floor";
            "app::main::impl app::main::Level for app::main::Shelf.height";
            raised_of_shelf;
          ];
      expect_included
        (list_propagated
           ~before:[ ("app::main", make_level_source ~height:"self.height") ]
           ~after:[ ("app::main", make_level_source ~height:"floor(self)") ])
        ~parts:[ "recursion group " ^ raised_of_shelf; "proof app::main::floor" ]);
  Harness.test
    "adding a file and then removing it recomputes no part of the other file's definitions"
    (fun () ->
      let without_helper = [ ("app::main", callee_and_caller) ] in
      let hot = build without_helper in
      List.iter
        (fun (before, after) ->
          expect_untouched (propagate hot ~before ~after).recomputed ~names:[ "app::main::" ])
        [ (without_helper, with_helper); (with_helper, without_helper) ]);
  Harness.test "reformatting a callee recomputes no caller's proof" (fun () ->
      expect_recomputed
        (list_propagated
           ~before:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64 requires x > 0 { x }\n\
                  fn caller() -> Int64 { callee(1) }\n" );
             ]
           ~after:
             [
               ( "app::main",
                 "fn callee(x: Int64) -> Int64\n\
                 \  requires x > 0\n\
                  {\n\
                 \  x\n\
                  }\n\
                  fn caller() -> Int64 { callee(1) }\n" );
             ])
        ~exactly:
          [ "import check app/main/main.truss"; "namespace app"; "parsed app/main/main.truss" ]);
  Harness.test "an edit to a callee's body recomputes its lowered code and not its caller's"
    (fun () ->
      let recomputed =
        list_propagated_with_roots ~roots:[ "caller" ]
          ~before:[ ("app::main", callee_and_caller) ]
          ~after:
            [
              ( "app::main",
                "fn callee(x: Int64) -> Int64 { x + 2 }\nfn caller() -> Int64 { callee(1) }\n" );
            ]
      in
      expect_included recomputed
        ~parts:[ show_lowered "callee"; test_key "callee"; test_key "caller" ];
      expect_untouched recomputed ~names:[ show_lowered "caller" ]);
  Harness.test "a call that is removed with its callee collects the callee's lowered code"
    (fun () ->
      expect_untouched
        (list_propagated_with_roots ~roots:[ "caller" ]
           ~before:[ ("app::main", callee_and_caller) ]
           ~after:[ ("app::main", "fn caller() -> Int64 { 1 }\n") ])
        ~names:[ show_lowered "callee" ]);
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
      if observed.collected <> [ show_lowered "only"; test_key "only" ] then
        Harness.fail "collected %s" (String.concat ", " observed.collected);
      expect_untouched observed.recomputed ~names:[ show_lowered "shared"; show_lowered "kept" ]);
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
        ~names:[ "[Shape]" ]);
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
        ~parts:[ show_lowered "none" ]);
  Harness.test
    "a type that comes to contain itself in place fails the lowered code that lays it out"
    (fun () ->
      let make_program held =
        [ ("app::main", "type Chain(next: " ^ held ^ ")\nfn size(chain: Chain) -> Int64 { 1 }\n") ]
      in
      expect_included
        (list_propagated_with_roots ~roots:[ "size" ] ~before:(make_program "List[Chain]")
           ~after:(make_program "Option[Chain]"))
        ~parts:[ show_lowered "size" ]);
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
      expect_included recomputed ~parts:[ show_lowered "second" ];
      expect_untouched recomputed ~names:[ show_lowered "first" ]);
  Harness.test "adding a dependency to a manifest fixes the dependent's use of it" (fun () ->
      expect_included
        (lay_out_again ~before:(Support.setup tool_user)
           ~after:(Support.setup ~dependencies:[ ("app", "lib") ] tool_user)
           ())
        ~parts:[ "namespace app"; "checked body app::main::caller" ]);
  Harness.test "adding a package and then removing it matches a cold build each time" (fun () ->
      let alone = Support.setup [ ("app::main", "fn caller() -> Int64 { 1 }\n") ] in
      let with_lib = Support.setup ~dependencies:[ ("app", "lib") ] tool_user in
      ignore (lay_out_again ~before:alone ~after:with_lib ());
      expect_untouched
        (List.filter
           (fun part -> not (String.starts_with ~prefix:"call edges app " part))
           (lay_out_again ~before:with_lib ~after:alone ()))
        ~names:[ "lib::" ]);
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
      expect_included recomputed ~parts:[ "checked body app::main::calls_second" ];
      expect_untouched recomputed ~names:[ "app::main::uses_first"; "app::main::uses_second" ]);
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
            "generated mir derived standard::serialization::Deserialize for \
             app::main::Signup.deserialize";
            "import check app/main/main.truss";
            "namespace app";
            "package check app type app::main::Signup";
            "parsed app/main/main.truss";
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
            "fn callee(x: Int64) -> Int64 { x + 2 }\nfn caller() -> Int64 { callee(1) }\n" );
        ]
      in
      let log = commit [] (list_saved (build before)) in
      expect_recomputed (observe_reopen log after).recomputed
        ~exactly:(list_propagated ~before ~after));
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
      Database.check hot [ (Support.parse_module "app::main").package ];
      let log = commit log (list_saved hot) in
      let propagated =
        (Database.For_testing.observe (fun () -> Database.propagate hot)).recomputed
      in
      expect_recomputed (observe_reopen log after).recomputed ~exactly:propagated);
  Harness.test "a database saved after a package is removed reopens without the package" (fun () ->
      let with_lib = Support.setup ~dependencies:[ ("app", "lib") ] tool_user in
      let alone = [ ("app::main", "fn caller() -> Int64 { 1 }\n") ] in
      let hot = settle [] with_lib in
      let log = commit [] (list_saved hot) in
      Database.relayout hot ~loaded:[ Lazy.force standard ] (Support.setup alone);
      Database.propagate hot;
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
  let snapshot = open_workspace root in
  let database = Workspace.open_database snapshot in
  let observed = Database.For_testing.observe (fun () -> Database.propagate database) in
  let cold = Workspace.For_testing.build_cold_database snapshot in
  Database.propagate cold;
  (match Database.For_testing.list_differences database cold with
  | [] -> ()
  | parts ->
      Harness.fail "the database in .truss differs from a cold build in %s"
        (String.concat ", " parts));
  observed.recomputed

let edited_body = "fn callee(x: Int64) -> Int64 { x + 2 }\nfn caller() -> Int64 { callee(1) }\n"

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
      File_system.write list
        (String.concat "\n"
           (List.map
              (fun line ->
                if String.starts_with ~prefix:"header compiler " line then "header compiler other"
                else line)
              (String.split_on_char '\n' (File_system.read list))));
      expect_included (settle_on_disk root)
        ~parts:[ "namespace app"; "checked body app::main::caller" ];
      Workspace.flush ())

let expect_cold database snapshot =
  let cold = Workspace.For_testing.build_cold_database snapshot in
  Database.propagate cold;
  match Database.For_testing.list_differences database cold with
  | [] -> ()
  | parts -> Harness.fail "the database differs from a cold build in %s" (String.concat ", " parts)

let () =
  Harness.test "a trial is a copy of the database, propagated with the files that differ" (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      let snapshot = open_workspace root in
      let worktree = Workspace.open_database snapshot in
      Database.propagate worktree;
      let trial = Workspace.make_trial snapshot [ ("main/main.truss", Some edited_body) ] in
      let database = Workspace.open_database trial in
      let recomputed =
        (Database.For_testing.observe (fun () -> Database.propagate database)).recomputed
      in
      expect_included recomputed ~parts:[ "checked body app::main::callee" ];
      expect_untouched recomputed ~names:[ "app::main::caller" ];
      expect_cold database trial;
      expect_cold worktree snapshot;
      Workspace.flush ());
  Harness.test "a trial that renames the package leaves the worktree's database as it was"
    (fun () ->
      let root = project [ ("main/main", callee_and_caller) ] in
      let snapshot = open_workspace root in
      let worktree = Workspace.open_database snapshot in
      Database.propagate worktree;
      let trial =
        Workspace.make_trial snapshot
          [ ("truss.toml", Some "[package]\nname = \"tool\"\ntruss = \"0.1\"\n") ]
      in
      let database = Workspace.open_database trial in
      Database.propagate database;
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
         Database.propagate hot))

let count_cold_build files =
  let database = Support.make_database (Support.setup files) in
  snd (Database.count (fun () -> Database.propagate database))

let () =
  Harness.test "a propagation with no stale part counts no work" (fun () ->
      let database = build [ ("app::main", callee_and_caller) ] in
      match snd (Database.count (fun () -> Database.propagate database)) with
      | [] -> ()
      | counts -> Harness.fail "counted %s" (String.concat "; " (List.map show_counts counts)));
  Harness.test
    "a computed part whose value comes out unchanged is counted as unchanged, not written"
    (fun () ->
      let before = [ ("app::main", callee_and_caller) ] in
      let after =
        [
          ( "app::main",
            "fn callee(x: Int64) -> Int64 {\n  x + 1\n}\nfn caller() -> Int64 { callee(1) }\n" );
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
            Database.propagate trial)
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
            Database.propagate hot)
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
        ~parts:[ "namespace app"; "checked body app::main::second" ]);
  Harness.test "a request that reads a name whose namespace is stale is a compiler bug" (fun () ->
      let database = build [ ("app::main", callee_and_caller) ] in
      Database.update database
        [ (Support.parse_file "app::main/extra", Some "fn extra() -> Int64 { 3 }\n") ];
      let names = Database.make_name_lookups database [] in
      match names.list_declarations (Support.parse_module "app::main") with
      | _ -> Harness.fail "the stale namespace was read"
      | exception Compiler_bug.Bug _ -> ());
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
