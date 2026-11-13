(* The tests of the code database's sessions: a session's findings, the
   results a restart or a new worktree computes again, dependencies, comparing
   with a commit, overlaps between worktrees, and the background process. *)

open Harness

let fresh = scratch
let counter = ref 0

let write directory file text =
  write_files directory [ (file, text) ];
  (* A rewrite within one second must still look changed. *)
  incr counter;
  let now = Unix.gettimeofday () in
  Unix.utimes (Filename.concat directory file) now (now +. float_of_int !counter)

let manifest name = Printf.sprintf "[package]\nname = \"%s\"\ntruss = \"0.1\"\n" name
let project = "[project]\n"
let program = Fixtures.Database.doubling

(* A store that holds the standard library's checked state and nothing
   else, as any store does once Truss has run. Checking the standard
   library and writing its state is most of a new store's cost, and it
   comes out the same for each, so it is done once. *)
let store_with_standard =
  lazy
    (let directory = fresh "standard" in
     Database.reset ();
     Unix.putenv "TRUSS_CACHE" directory;
     Database.For_testing.prepare_store ();
     Database.flush_store ();
     Database.reset ();
     directory)

(* Every test starts as a new process would, with a store of its own. With
   [~empty:true] the store holds nothing, as on a machine where Truss has
   never run, and the process checks the standard library itself. *)
let fresh_store ?(empty = false) () =
  let standard = if empty then None else Some (Lazy.force store_with_standard) in
  Database.reset ();
  let directory = fresh "cache" in
  Option.iter
    (fun standard ->
      if
        Sys.command
          (Printf.sprintf "cp -R %s/. %s" (Filename.quote standard) (Filename.quote directory))
        <> 0
      then failwith "could not copy the store")
    standard;
  Unix.putenv "TRUSS_CACHE" directory;
  Database.For_testing.logging := true

let package () =
  let directory = fresh "package" in
  write directory "truss.toml" (manifest "app");
  write directory "main.truss" program;
  directory

let session directory =
  match Database.open_session directory with
  | Ok (session, packages) -> (session, packages)
  | Error message -> failwith message

(* A session's diagnostics and problems, as a count, after it is saved, as
   a command would leave it. *)
let errors directory =
  let session, packages = session directory in
  let actual =
    List.concat_map
      (fun (_, name) ->
        List.concat_map (Database.diagnostics session) (Database.package_files session name))
      packages
  in
  Database.save_session session;
  List.length actual + List.length (Database.problems session)

let executed directory =
  match Database.For_testing.session_engine directory with
  | Some engine -> Engine.For_testing.executed engine
  | None -> []

let computed directory query =
  match Database.For_testing.session_engine directory with
  | Some engine -> Engine.For_testing.computed engine query
  | None -> []

let checked directory = computed directory Infer.type_check_result
let top = Support.top_key

let shapes_method name : Resolve.Names.key =
  let module_ = Support.module_of "app" in
  {
    module_;
    path =
      Method
        {
          owner =
            Impl { module_; trait = "Shape"; for_type = { type_name = "Square"; generics = [] } };
          name;
          receiver = Read;
        };
    ordinal = 0;
  }

let clear directory =
  Option.iter Engine.For_testing.clear_log (Database.For_testing.session_engine directory)

let contains = Substring.contains

let expect_errors directory count =
  let actual = errors directory in
  if actual <> count then fail "%d errors, expected %d" actual count

(* The background process, first, since a process cannot fork once a
   build has started domains *)

let () =
  test "running git leaves the process able to start the background process" (fun () ->
      (match Process.output "git" [ "--version" ] with
      | 0, _ -> ()
      | status, _ -> fail "git --version exited with %d" status);
      match Unix.fork () with 0 -> Unix._exit 0 | child -> ignore (Unix.waitpid [] child));
  test "the background process answers requests and sees every earlier write" (fun () ->
      fresh_store ();
      let directory = package () in
      match Unix.fork () with
      | 0 ->
          (* A request is a directory, and the answer its count of errors, or
             [-1] to stop. *)
          Database.serve ~key:(Database.server_key directory) ~handle:(fun ~progress request ->
              let directory = request in
              progress "working";
              if directory = "stop" then begin
                Database.stop ();
                -1
              end
              else errors directory);
          Unix._exit 0
      | child ->
          let progressed = ref false in
          let call request =
            match
              Database.call ~program:"/nonexistent" ~key:(Database.server_key directory)
                ~progress:(fun text -> if text = "working" then progressed := true)
                request
            with
            | Ok (count : int) -> count
            | Error message ->
                fail "%s" message;
                -2
          in
          if call directory <> 0 then fail "found errors";
          if not !progressed then fail "sent no progress";
          write directory "main.truss"
            Fixtures.Database.background_process_answers_requests_and_sees_every;
          if call directory <> 1 then fail "missed the error";
          (match Database.open_session directory with
          | Error _ -> ()
          | Ok _ -> fail "opened a session the background process holds");
          ignore (call "stop");
          ignore (Unix.waitpid [] child))

let () =
  test "a session of a package with no errors finds none" (fun () ->
      fresh_store ();
      expect_errors (package ()) 0);
  test "a session finds an error, and none once it is fixed" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "main.truss"
        Fixtures.Database.session_finds_an_error_and_none_once_it_is_fixed;
      expect_errors directory 1;
      write directory "main.truss" program;
      expect_errors directory 0);
  test "a session after a restart computes nothing" (fun () ->
      fresh_store ();
      let directory = package () in
      expect_errors directory 0;
      Database.reset ();
      expect_errors directory 0;
      let again = executed directory in
      if again <> [] then fail "computed [%s]" (String.concat "; " again));
  test "a change made while no process ran is seen after a restart" (fun () ->
      fresh_store ();
      let directory = package () in
      expect_errors directory 0;
      Database.reset ();
      write directory "main.truss"
        Fixtures.Database.change_made_while_no_process_ran_is_seen_after_a;
      expect_errors directory 1);
  test "editing one function's body checks only that body again" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "other.truss"
        Fixtures.Database.editing_one_functions_body_checks_only_that_body;
      expect_errors directory 0;
      clear directory;
      write directory "main.truss"
        (program ^ Fixtures.Database.editing_one_functions_body_checks_only_that_body_2);
      write directory "main.truss" program;
      write directory "other.truss"
        Fixtures.Database.editing_one_functions_body_checks_only_that_body_3;
      expect_errors directory 0;
      let again = checked directory in
      if List.mem (top "app" "double") again then fail "checked double again";
      if not (List.mem (top "app" "triple") again) then fail "did not check triple");
  test "reordering a type's fields checks no reader of the type again" (fun () ->
      fresh_store ();
      let directory = package () in
      let point fields = "internal type Point(" ^ fields ^ ")\n" in
      write directory "point/point.truss" (point "x: Int64, y: Int64");
      write directory "reader/reader.truss"
        Fixtures.Database.reordering_a_types_fields_checks_no_reader_of_the;
      expect_errors directory 0;
      let width = top "app::reader" "width" in
      let lowered directory = computed directory Interface.Environment.lowered_interface in
      if not (List.mem width (checked directory)) then fail "never checked width";
      if not (List.mem width (lowered directory)) then fail "never lowered width's interface";
      clear directory;
      write directory "point/point.truss" (point "y: Int64, x: Int64");
      expect_errors directory 0;
      if List.mem width (checked directory) then fail "checked width again";
      if List.mem width (lowered directory) then fail "lowered width's interface again");
  test "editing one method's body checks only that method again" (fun () ->
      fresh_store ();
      let directory = package () in
      let shapes area =
        "trait Shape {\n\
        \  fn area(self) -> Int64\n\
        \  fn sides(self) -> Int64\n\
         }\n\n\
         type Square(side: Int64)\n\n\
         impl Shape for Square {\n\
        \  fn area(self) -> Int64 {\n\
        \    " ^ area ^ "\n  }\n\n  fn sides(self) -> Int64 {\n    4\n  }\n}\n"
      in
      write directory "shapes.truss" (shapes "1");
      expect_errors directory 0;
      clear directory;
      (* The change moves [sides], which is the same method where it is. *)
      write directory "shapes.truss" (shapes "10 + 2");
      expect_errors directory 0;
      let again = checked directory in
      if not (List.mem (shapes_method "area") again) then fail "did not check area";
      if List.mem (shapes_method "sides") again then fail "checked sides again");
  test "a removed module is gone from the package" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "broken.truss" Fixtures.Database.removed_module_is_gone_from_the_package;
      expect_errors directory 1;
      Sys.remove (Filename.concat directory "broken.truss");
      expect_errors directory 0);
  test "a package renamed in its manifest keeps its modules' text" (fun () ->
      fresh_store ();
      let directory = package () in
      expect_errors directory 0;
      write directory "truss.toml" (manifest "renamed");
      expect_errors directory 0;
      Database.reset ();
      expect_errors directory 0);
  test "a file that cannot be read is not there, and a change beside it is still seen" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "other.truss"
        Fixtures.Database.file_that_cannot_be_read_is_not_there_and_a_change;
      expect_errors directory 0;
      write directory "main.truss"
        Fixtures.Database.file_that_cannot_be_read_is_not_there_and_a_change_2;
      Unix.chmod (Filename.concat directory "other.truss") 0;
      let unreadable = errors directory in
      Unix.chmod (Filename.concat directory "other.truss") 0o644;
      if unreadable = 0 then fail "the change beside the unreadable file was not seen";
      if errors directory = 0 then fail "the change was lost once the file could be read");
  test "a trial sees its changed, added, and removed files, and the session does not" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "other.truss"
        Fixtures.Database.trial_sees_its_changed_added_and_removed_files_and;
      expect_errors directory 0;
      let session, _ = session directory in
      let trial =
        Database.trial session
          [
            ( "main.truss",
              Some Fixtures.Database.trial_sees_its_changed_added_and_removed_files_and_2 );
            ( "added.truss",
              Some Fixtures.Database.trial_sees_its_changed_added_and_removed_files_and_3 );
            ("other.truss", None);
          ]
      in
      let files session =
        List.sort compare (Database.package_files session { owner = None; name = "app" })
      in
      let named name : Path.file =
        { module_ = { package = { owner = None; name = "app" }; modules = [] }; name }
      in
      if files trial <> [ named "added"; named "main" ] then fail "the trial's files";
      if Database.diagnostics trial (named "main") = [] then fail "the trial did not see the change";
      if files session <> [ named "main"; named "other" ] then fail "the session's files changed";
      if Database.diagnostics session (named "main") <> [] then fail "the session saw the change");
  test "a manifest added below a package gives the files under it to a new package" (fun () ->
      fresh_store ();
      let directory = fresh "project" in
      write directory "truss.toml" (project ^ manifest "app");
      write directory "main.truss" program;
      write directory "tools/helper.truss"
        Fixtures.Database.manifest_added_below_a_package_gives_the_files;
      expect_errors directory 0;
      let before, _ = session directory in
      if List.length (Database.package_modules before { owner = None; name = "app" }) <> 2 then
        fail "the package does not have both modules";
      write directory "tools/truss.toml" (manifest "tools");
      expect_errors directory 0;
      let after, _ = session directory in
      if
        Database.package_modules after { owner = None; name = "app" }
        <> [ { package = { owner = None; name = "app" }; modules = [] } ]
      then fail "the first package still has the file";
      if
        Database.package_modules after { owner = None; name = "tools" }
        <> [ { package = { owner = None; name = "tools" }; modules = [] } ]
      then fail "the new package does not have the file");
  test "a malformed manifest is a problem, at its line" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "truss.toml" "[package]\nname = \n";
      let session, _ = session directory in
      if
        not
          (List.exists (fun problem -> contains problem "truss.toml:2") (Database.problems session))
      then fail "problems: [%s]" (String.concat "; " (Database.problems session)));
  test "a package cannot depend on one that runs only on 64-bit targets unless it does too"
    (fun () ->
      fresh_store ();
      let root = fresh "project" in
      write root "truss.toml" project;
      write root "wide/truss.toml" (manifest "wide" ^ "usize_bits = 64\n");
      write root "wide/main.truss" program;
      write root "app/truss.toml" (manifest "app" ^ "\n[dependencies]\nwide = []\n");
      write root "app/main.truss" program;
      let session, _ = session root in
      if
        not
          (List.exists
             (fun problem -> contains problem "runs only on 64-bit targets")
             (Database.problems session))
      then fail "problems: [%s]" (String.concat "; " (Database.problems session)));
  test "a session opened in a package's directory is about that package alone" (fun () ->
      fresh_store ();
      let root = fresh "project" in
      write root "truss.toml" project;
      write root "good/truss.toml" (manifest "good");
      write root "good/main.truss" program;
      write root "bad/truss.toml" (manifest "bad");
      write root "bad/main.truss" Fixtures.Database.session_opened_in_a_packages_directory_is_about;
      expect_errors (Filename.concat root "good") 0;
      expect_errors (Filename.concat root "bad") 1;
      expect_errors root 1);
  test "a new worktree starts from the nearest saved state" (fun () ->
      fresh_store ();
      let first = package () in
      expect_errors first 0;
      let second = package () in
      write second "main.truss"
        (program ^ Fixtures.Database.new_worktree_starts_from_the_nearest_saved_state);
      expect_errors second 0;
      let again = checked second in
      if List.mem (top "app" "double") again then fail "checked double again";
      if not (List.mem (top "app" "extra") again) then fail "did not check extra");
  test "a new worktree's state is a difference over the state it started from" (fun () ->
      fresh_store ~empty:true ();
      (* Eight modules, of which the second worktree changes one. *)
      let module_text index =
        Printf.sprintf
          "fn first_%d(value: Int64) -> Int64 {\n\
          \  value + %d\n\
           }\n\n\
           fn second_%d(value: Int64) -> Int64 {\n\
          \  first_%d(value) * 2\n\
           }\n"
          index index index index
      in
      let worktree () =
        let directory = fresh "package" in
        write directory "truss.toml" (manifest "app");
        for index = 1 to 8 do
          write directory (Printf.sprintf "part_%d.truss" index) (module_text index)
        done;
        directory
      in
      let first = worktree () in
      expect_errors first 0;
      let second = worktree () in
      write second "part_3.truss"
        (module_text 3 ^ Fixtures.Database.new_worktrees_state_is_a_difference_over_the_state);
      expect_errors second 0;
      match
        (Database.For_testing.session_engine first, Database.For_testing.session_engine second)
      with
      | Some whole, Some difference ->
          let own = Engine.For_testing.count difference
          and all = List.length (Engine.nodes whole) in
          if own * 2 >= all then
            fail "the second holds %d nodes of its own, and the first state has %d" own all
      | _ -> fail "no sessions")

let double : Path.t =
  Top { module_ = { package = { owner = None; name = "app" }; modules = [] }; name = "double" }

let doubling : Path.t =
  Test { module_ = { package = { owner = None; name = "app" }; modules = [] }; name = "doubling" }

let test_body_reads_signature : Graph_types.edge =
  {
    dependent = doubling;
    dependent_part = "body";
    dependency = double;
    dependency_part = "signature";
  }

let () =
  test "a definition's dependents are found part by part" (fun () ->
      fresh_store ();
      let session, _ = session (package ()) in
      ignore (errors (Database.root session));
      if not (List.mem test_body_reads_signature (Database.dependents session [ double ])) then
        fail "the test's body does not read double's signature");
  test "a definition's dependencies are found part by part" (fun () ->
      fresh_store ();
      let session, _ = session (package ()) in
      ignore (errors (Database.root session));
      if not (List.mem test_body_reads_signature (Database.dependencies session [ doubling ])) then
        fail "the test's body does not read double's signature");
  test "a definition does not depend on standard-library types it does not use" (fun () ->
      fresh_store ();
      let directory = fresh "package" in
      write directory "truss.toml" (manifest "app");
      write directory "main.truss" Fixtures.Database.moving_a_string;
      let session, _ = session directory in
      ignore (errors directory);
      let keep : Path.t =
        Top { module_ = { package = { owner = None; name = "app" }; modules = [] }; name = "keep" }
      in
      let dependencies = Database.dependencies session [ keep ] in
      if dependencies = [] then fail "keep depends on nothing";
      List.iter
        (fun (edge : Graph_types.edge) ->
          if contains (Path.show edge.dependency) "standard::html" then
            fail "keep depends on %s" (Path.show edge.dependency))
        dependencies);
  test "a root reaches its dependencies and itself" (fun () ->
      fresh_store ();
      let session, _ = session (package ()) in
      ignore (errors (Database.root session));
      match Database.reachable session [ doubling; double ] with
      | [ from_test; from_double ] ->
          if not (Path.Set.mem double from_test && Path.Set.mem doubling from_test) then
            fail "the test does not reach double and itself";
          if Path.Set.mem doubling from_double then fail "double reaches the test that calls it"
      | _ -> fail "not one set for each root");
  test "a name finds the definitions whose path ends with it" (fun () ->
      fresh_store ();
      let session, _ = session (package ()) in
      if Database.find_definitions session "double" <> [ double ] then fail "found otherwise")

(* With git *)

let git = Harness.git

let repository () =
  let root = fresh "repository" in
  git root [ "init"; "-q"; "-b"; "main" ];
  write root "truss.toml" (manifest "app");
  write root "main.truss" program;
  git root [ "add"; "-A" ];
  git root [ "commit"; "-q"; "-m"; "base" ];
  root

let change_interface root = write root "main.truss" Fixtures.Database.change_interface
let add_caller root = write root "main.truss" (program ^ Fixtures.Database.add_caller)

let base_of session =
  match Database.base_commit session None with
  | None ->
      fail "no base commit";
      None
  | Some commit -> (
      match Database.open_commit_of session commit with
      | Ok base -> Some base
      | Error message ->
          fail "%s" message;
          None)

let () =
  test "a worktree that a background process serves is compared through a snapshot of its state"
    (fun () ->
      fresh_store ();
      let root = repository () in
      let other = fresh "served" in
      git root [ "worktree"; "add"; "-q"; other; "-b"; "served" ];
      add_caller other;
      let key = Database.server_key other in
      match Unix.fork () with
      | 0 ->
          Database.serve ~key ~handle:(fun ~progress:_ request ->
              if request = "stop" then begin
                Database.stop ();
                -1
              end
              else errors request);
          Unix._exit 0
      | child ->
          let call request =
            match Database.call ~program:"/nonexistent" ~key ~progress:ignore request with
            | Ok (count : int) -> count
            | Error message ->
                fail "%s" message;
                -2
          in
          ignore (call other);
          change_interface root;
          let mine, _ = session root in
          (match Database.other_worktrees mine with
          | [ actual ] when Database.root actual = Unix.realpath other -> (
              match Database.overlap_with mine actual with
              | Error message -> fail "%s" message
              | Ok [] -> fail "found no overlap"
              | Ok _ -> ())
          | actual -> fail "compared with [%s]" (String.concat "; " (List.map Database.root actual)));
          ignore (call "stop");
          ignore (Unix.waitpid [] child))

let () =
  test "comparing with the base finds the changed signature" (fun () ->
      fresh_store ();
      let root = repository () in
      change_interface root;
      let session, _ = session root in
      match base_of session with
      | None -> ()
      | Some base ->
          if
            not
              (List.exists
                 (fun (path, part, difference) ->
                   Path.equal path double && part = Some "signature"
                   && difference = Graph_types.Changed)
                 (Database.changes session base))
          then
            fail "double's signature is not changed: %s"
              (String.concat "; "
                 (List.map
                    (fun (path, part, digest) ->
                      Printf.sprintf "%s %s %s" (Path.show path) (Option.value part ~default:"-")
                        (match digest with
                        | Graph_types.Changed -> "changed"
                        | Added -> "added"
                        | Same -> "same"))
                    (Database.changes session base))));
  test "overlap finds a new call to a function another worktree changes" (fun () ->
      fresh_store ();
      let root = repository () in
      let other = fresh "other" in
      git root [ "worktree"; "add"; "-q"; other; "-b"; "other" ];
      change_interface root;
      add_caller other;
      let mine, _ = session root in
      let theirs, _ = session other in
      match Database.overlap_with theirs mine with
      | Error message -> fail "%s" message
      | Ok overlaps ->
          let quadruple : Path.t =
            Top
              {
                module_ = { package = { owner = None; name = "app" }; modules = [] };
                name = "quadruple";
              }
          in
          if
            not
              (List.exists
                 (function
                   | Graph_types.Reads { this_worktree = true; change; reads } ->
                       change.path = Some quadruple && reads.path = Some double
                   | _ -> false)
                 overlaps)
          then
            fail "no overlap found: %s"
              (String.concat "; "
                 (List.map
                    (function
                      | Graph_types.Both_change problem -> "both " ^ problem.label
                      | Reads { this_worktree; change; reads } ->
                          Printf.sprintf "%b %s %s" this_worktree change.label reads.label)
                    overlaps)));
  test "a project below the top of its worktree is compared with itself in another worktree"
    (fun () ->
      fresh_store ();
      let top = fresh "repository" in
      git top [ "init"; "-q"; "-b"; "main" ];
      let root = Filename.concat top "services/app" in
      write root "truss.toml" (manifest "app");
      write root "main.truss" program;
      write top "tools/truss.toml" (manifest "tools");
      write top "tools/main.truss" program;
      git top [ "add"; "-A" ];
      git top [ "commit"; "-q"; "-m"; "base" ];
      let other_top = fresh "nested" in
      git top [ "worktree"; "add"; "-q"; other_top; "-b"; "other" ];
      let other = Filename.concat other_top "services/app" in
      change_interface root;
      add_caller other;
      let mine, _ = session root in
      let theirs, _ = session other in
      let _ = session (Filename.concat top "tools") in
      (match Database.other_worktrees theirs with
      | [ actual ] when Database.root actual = Unix.realpath root -> ()
      | actual -> fail "compared with [%s]" (String.concat "; " (List.map Database.root actual)));
      (match Database.overlap_with theirs mine with
      | Error message -> fail "%s" message
      | Ok overlaps ->
          if
            not
              (List.exists
                 (function
                   | Graph_types.Reads { this_worktree = true; reads; _ } ->
                       reads.path = Some double
                   | _ -> false)
                 overlaps)
          then fail "no overlap found");
      match Database.merge_preview mine theirs with
      | Error message -> fail "%s" message
      | Ok actual ->
          if not (List.exists (fun (file, _, _) -> file = "main.truss") actual) then
            fail "no error found in the merge");
  test "a merge preview finds the errors the merge would have" (fun () ->
      fresh_store ();
      let root = repository () in
      let other = fresh "merge" in
      git root [ "worktree"; "add"; "-q"; other; "-b"; "merged" ];
      change_interface root;
      write other "caller.truss" Fixtures.Database.merge_preview_finds_the_errors_the_merge_would;
      let mine, _ = session root in
      let theirs, _ = session other in
      match Database.merge_preview mine theirs with
      | Error message -> fail "%s" message
      | Ok actual ->
          if
            not
              (List.exists
                 (fun (file, code, _) -> file = "caller.truss" && code = "types.missing_argument")
                 actual)
          then fail "no error found")

(* The layers stay apart *)

let library_file name : Path.file =
  { module_ = { package = Path.standard_package; modules = [ name ] }; name }

let library_function name =
  Printf.sprintf "internal fn %s(value: Int64) -> Int64 {\n  value\n}\n" name

let open_library files =
  match Database.For_testing.open_library ~files "tests" with
  | Ok library -> library
  | Error message -> failwith message

let check_library library files =
  List.iter
    (fun (file, _) ->
      ignore (Engine.get (Database.For_testing.engine library) Type_checker.file_diagnostics file))
    files;
  Database.save_session library

let () =
  test "a library state opened again after an edit recomputes only the edit's dependents" (fun () ->
      fresh_store ~empty:true ();
      let first = (library_file "first", library_function "first") in
      let second = (library_file "second", library_function "second") in
      check_library (open_library [ first; second ]) [ first; second ];
      Database.reset ();
      let second = (library_file "second", library_function "other") in
      let library = open_library [ first; second ] in
      let engine = Database.For_testing.engine library in
      Engine.For_testing.clear_log engine;
      check_library library [ first; second ];
      let checked = Engine.For_testing.computed engine Infer.type_check_result in
      let in_module ((file : Path.file), _) =
        List.exists (fun (key : Resolve.Names.key) -> key.module_ = file.module_) checked
      in
      if not (in_module second) then fail "the edited module was not checked again";
      if in_module first then fail "the unchanged module was checked again");
  test "a library state drops the text of a file that is gone from the sources" (fun () ->
      fresh_store ~empty:true ();
      let first = (library_file "first", library_function "first") in
      let second = (library_file "second", library_function "second") in
      check_library (open_library [ first; second ]) [ first; second ];
      Database.reset ();
      let library = open_library [ first ] in
      let context = Engine.context (Database.For_testing.engine library) in
      if Query.demand context Project.file_text (fst second) <> None then
        fail "the file's text is still set";
      if
        List.mem (fst second).module_ (Query.demand context Workspace.modules Path.standard_package)
      then fail "the package still has the module")

let () =
  test "a query cannot be declared once the database has opened its store" (fun () ->
      fresh_store ();
      ignore (session (package ()));
      match
        Query.query ~name:"declared_late" ~phase:Phases.syntax ~show:Fun.id (fun _ key -> key)
      with
      | _ -> fail "it was declared"
      | exception Invalid_argument _ -> ())
