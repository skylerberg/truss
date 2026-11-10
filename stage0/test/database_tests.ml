(* The tests of the code database's sessions: what a session finds, what a
   restart or a new worktree computes again, what reads what, comparing
   with a commit, overlaps between worktrees, and the background process. *)

open Harness

let scratch =
  lazy
    (let directory =
       Filename.concat (Filename.get_temp_dir_name ())
         (Printf.sprintf "truss-database-tests-%d" (Unix.getpid ()))
     in
     ignore (Sys.command ("rm -rf " ^ Filename.quote directory));
     Unix.mkdir directory 0o755;
     at_exit (fun () -> ignore (Sys.command ("rm -rf " ^ Filename.quote directory)));
     directory)

let counter = ref 0

let fresh name =
  incr counter;
  let path = Filename.concat (Lazy.force scratch) (Printf.sprintf "%s-%d" name !counter) in
  Unix.mkdir path 0o755;
  path

let write directory file text =
  let path = Filename.concat directory file in
  let rec make dir =
    if not (Sys.file_exists dir) then begin
      make (Filename.dirname dir);
      Unix.mkdir dir 0o755
    end
  in
  make (Filename.dirname path);
  Out_channel.with_open_bin path (fun out -> output_string out text);
  (* A rewrite within one second must still look changed. *)
  let now = Unix.gettimeofday () in
  Unix.utimes path now (now +. float_of_int !counter)

let manifest name = Printf.sprintf "[package]\nname = \"%s\"\n" name

let program =
  {|internal fn double(value: Int64) -> Int64 {
  value * 2
}

test "doubling" {
  assert double(2) == 4
}
|}

(* Every test starts as a new process would, with a store of its own. *)
let fresh_store () =
  Database.reset ();
  Unix.putenv "TRUSS_CACHE" (fresh "cache");
  Database.logging := true

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
  let found =
    List.concat_map
      (fun (_, name) ->
        List.concat_map (Database.diagnostics session) (Database.package_modules session name))
      packages
  in
  Database.save_session session;
  List.length found + List.length (Database.problems session)

let computed directory =
  match Database.session_engine directory with Some engine -> Engine.executed engine | None -> []

let clear directory = Option.iter Engine.clear_log (Database.session_engine directory)

let contains text part =
  let n = String.length part and l = String.length text in
  let rec at i = i + n <= l && (String.sub text i n = part || at (i + 1)) in
  at 0

let expect_errors directory count =
  let found = errors directory in
  if found <> count then fail "%d errors, expected %d" found count

(* The background process, first, since a process cannot fork once a
   build has started domains *)

let () =
  test "the background process answers requests and sees every earlier write" (fun () ->
      fresh_store ();
      let directory = package () in
      match Unix.fork () with
      | 0 ->
          (* A request is a directory, and the answer its count of errors, or
             [-1] to stop. *)
          Database.serve ~handle:(fun ~progress directory ->
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
              Database.call ~program:"/nonexistent"
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
          write directory "main.truss" "fn broken() -> Int64 {\n  true\n}\n";
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
      write directory "main.truss" "fn broken() -> Int64 {\n  true\n}\n";
      expect_errors directory 1;
      write directory "main.truss" program;
      expect_errors directory 0);
  test "a session after a restart computes nothing" (fun () ->
      fresh_store ();
      let directory = package () in
      expect_errors directory 0;
      Database.reset ();
      expect_errors directory 0;
      let again = computed directory in
      if again <> [] then fail "computed [%s]" (String.concat "; " again));
  test "a change made while no process ran is seen after a restart" (fun () ->
      fresh_store ();
      let directory = package () in
      expect_errors directory 0;
      Database.reset ();
      write directory "main.truss" "fn broken() -> Int64 {\n  true\n}\n";
      expect_errors directory 1);
  test "editing one function's body checks only that body again" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "other.truss" "fn triple(value: Int64) -> Int64 {\n  value * 3\n}\n";
      expect_errors directory 0;
      clear directory;
      write directory "main.truss" (program ^ "\nfn unused() -> Int64 {\n  1\n}\n");
      write directory "main.truss" program;
      write directory "other.truss" "fn triple(value: Int64) -> Int64 {\n  value * 4\n}\n";
      expect_errors directory 0;
      let again = computed directory in
      if List.mem "checked(app::main::double)" again then fail "checked double again";
      if not (List.mem "checked(app::other::triple)" again) then fail "did not check triple");
  test "a removed module is gone from the package" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "broken.truss" "fn broken() -> Int64 {\n  true\n}\n";
      expect_errors directory 1;
      Sys.remove (Filename.concat directory "broken.truss");
      expect_errors directory 0);
  test "a malformed manifest is a problem, at its line" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "truss.toml" "[package]\nname = \n";
      let session, _ = session directory in
      if not (List.exists (fun p -> contains p "truss.toml:2") (Database.problems session)) then
        fail "problems: [%s]" (String.concat "; " (Database.problems session)));
  test "a package cannot depend on one that runs only on 64-bit targets unless it does too"
    (fun () ->
      fresh_store ();
      let root = fresh "worktree" in
      write root "wide/truss.toml" "[package]\nname = \"wide\"\nusize_bits = 64\n";
      write root "wide/main.truss" program;
      write root "app/truss.toml"
        "[package]\nname = \"app\"\n\n[dependencies]\nwide = { version = \"1\" }\n";
      write root "app/main.truss" program;
      let session, _ = session root in
      if
        not
          (List.exists
             (fun p -> contains p "wide runs only on 64-bit targets")
             (Database.problems session))
      then fail "no problem");
  test "a session opened in a package's directory is about that package alone" (fun () ->
      fresh_store ();
      let root = fresh "worktree" in
      write root "good/truss.toml" (manifest "good");
      write root "good/main.truss" program;
      write root "bad/truss.toml" (manifest "bad");
      write root "bad/main.truss" "fn broken() -> Int64 {\n  true\n}\n";
      expect_errors (Filename.concat root "good") 0;
      expect_errors (Filename.concat root "bad") 1;
      expect_errors root 1);
  test "a new worktree starts from the nearest saved state" (fun () ->
      fresh_store ();
      let first = package () in
      expect_errors first 0;
      let second = package () in
      write second "main.truss" (program ^ "\nfn extra() -> Int64 {\n  1\n}\n");
      expect_errors second 0;
      let again = computed second in
      if List.mem "checked(app::main::double)" again then fail "checked double again";
      if not (List.mem "checked(app::main::extra)" again) then fail "did not check extra");
  test "a new worktree's state is a difference over the state it started from" (fun () ->
      fresh_store ();
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
      write second "part_3.truss" (module_text 3 ^ "\nfn extra() -> Int64 {\n  1\n}\n");
      expect_errors second 0;
      match (Database.session_engine first, Database.session_engine second) with
      | Some whole, Some difference ->
          let own = Engine.count difference and all = List.length (Engine.nodes whole) in
          if own * 2 >= all then
            fail "the second holds %d nodes of its own, and the first state has %d" own all
      | _ -> fail "no sessions")

let double : Path.t = Top { module_ = { package = "app"; modules = [ "main" ] }; name = "double" }

let doubling : Path.t =
  Test { module_ = { package = "app"; modules = [ "main" ] }; name = "doubling" }

let () =
  test "what reads a definition is found part by part" (fun () ->
      fresh_store ();
      let session, _ = session (package ()) in
      ignore (errors (Database.root session));
      let readers = Database.readers (Database.dependencies session) double in
      if not (List.mem (doubling, "body", "signature") readers) then
        fail "the test's body does not read double's signature");
  test "what a definition reads is found part by part" (fun () ->
      fresh_store ();
      let session, _ = session (package ()) in
      ignore (errors (Database.root session));
      let reads = Database.reads (Database.dependencies session) doubling in
      if not (List.mem (double, "body", "signature") reads) then
        fail "the test's body does not read double's signature");
  test "a name finds the definitions whose path ends with it" (fun () ->
      fresh_store ();
      let session, _ = session (package ()) in
      if Database.find_definitions session "double" <> [ double ] then fail "found otherwise")

(* With git *)

let git directory arguments =
  let command =
    String.concat " "
      (List.map Filename.quote
         ([ "git"; "-C"; directory; "-c"; "user.name=test"; "-c"; "user.email=test@example.com" ]
         @ arguments))
  in
  if Sys.command (command ^ " >/dev/null 2>&1") <> 0 then
    fail "git %s failed" (String.concat " " arguments)

let repository () =
  let root = fresh "repository" in
  git root [ "init"; "-q"; "-b"; "main" ];
  write root "truss.toml" (manifest "app");
  write root "main.truss" program;
  git root [ "add"; "-A" ];
  git root [ "commit"; "-q"; "-m"; "base" ];
  root

let change_interface root =
  write root "main.truss"
    {|internal fn double(value: Int64, times: Int64) -> Int64 {
  value * times
}

test "doubling" {
  assert double(2, times: 2) == 4
}
|}

let add_caller root =
  write root "main.truss"
    (program ^ {|
fn quadruple(value: Int64) -> Int64 {
  double(double(value))
}
|})

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
                   && difference = Database.Changed)
                 (Database.changes session base))
          then
            fail "double's signature is not changed: %s"
              (String.concat "; "
                 (List.map
                    (fun (path, part, d) ->
                      Printf.sprintf "%s %s %s" (Path.show path) (Option.value part ~default:"-")
                        (match d with
                        | Database.Changed -> "changed"
                        | Added -> "added"
                        | Same -> "same"))
                    (Database.changes session base))));
  test "overlap finds a new call to a function another worktree changes" (fun () ->
      fresh_store ();
      let root = repository () in
      let other = Filename.concat (Lazy.force scratch) (Printf.sprintf "other-%d" !counter) in
      git root [ "worktree"; "add"; "-q"; other; "-b"; "other" ];
      change_interface root;
      add_caller other;
      let mine, _ = session root in
      let theirs, _ = session other in
      match Database.overlap_with theirs mine with
      | Error message -> fail "%s" message
      | Ok overlaps ->
          let quadruple : Path.t =
            Top { module_ = { package = "app"; modules = [ "main" ] }; name = "quadruple" }
          in
          if
            not
              (List.exists
                 (function
                   | Database.Reads { this_worktree = true; change; reads } ->
                       change.path = Some quadruple && reads.path = Some double
                   | _ -> false)
                 overlaps)
          then
            fail "no overlap found: %s"
              (String.concat "; "
                 (List.map
                    (function
                      | Database.Both_change p -> "both " ^ p.label
                      | Reads { this_worktree; change; reads } ->
                          Printf.sprintf "%b %s %s" this_worktree change.label reads.label)
                    overlaps)));
  test "a merge preview finds the errors the merge would have" (fun () ->
      fresh_store ();
      let root = repository () in
      let other = Filename.concat (Lazy.force scratch) (Printf.sprintf "merge-%d" !counter) in
      git root [ "worktree"; "add"; "-q"; other; "-b"; "merged" ];
      change_interface root;
      write other "caller.truss"
        "use app::main\n\n\
         fn quadruple(value: Int64) -> Int64 {\n\
        \  main::double(main::double(value))\n\
         }\n";
      let mine, _ = session root in
      let theirs, _ = session other in
      match Database.merge_preview mine theirs with
      | Error message -> fail "%s" message
      | Ok found ->
          if
            not
              (List.exists
                 (fun (file, code, _) -> file = "caller.truss" && code = "types.missing_argument")
                 found)
          then fail "no error found")

(* The layers stay apart *)

let rec dune_files directory =
  Array.to_list (Sys.readdir directory)
  |> List.concat_map (fun entry ->
      let path = Filename.concat directory entry in
      if Sys.is_directory path then dune_files path else if entry = "dune" then [ path ] else [])

let () =
  test "no compiler stage lists the engine, the store, or the database" (fun () ->
      let root = "../../stage0" in
      let outside_stages =
        [ "incremental"; "query"; "engine"; "store"; "database"; "cli"; "bin"; "test"; "tools" ]
      in
      List.iter
        (fun path ->
          let parts = String.split_on_char '/' path in
          let stage = List.nth parts 3 in
          if not (List.mem stage outside_stages) then
            let text = In_channel.with_open_bin path In_channel.input_all in
            let words =
              String.split_on_char ' '
                (String.map (fun c -> if c = '\n' || c = '(' || c = ')' then ' ' else c) text)
            in
            List.iter
              (fun layer -> if List.mem layer words then fail "%s lists %s" path layer)
              [ "engine"; "store"; "database"; "incremental" ])
        (dune_files root);
      if not (List.mem "../../stage0/infer/dune" (dune_files root)) then
        fail "found no stage's dune file")

let () = finish ()
