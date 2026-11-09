(* The tests of the code database's sessions and requests: what a check
   finds, what a restart or a new worktree computes again, the questions
   about dependencies, overlaps between worktrees, and the background
   process. See DATABASE.md, "Sessions", "Requests", and "Parallel work". *)

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

let request ?(json = false) directory command = Database.handle { directory; command; json }

let package () =
  let directory = fresh "package" in
  write directory "truss.toml" (manifest "app");
  write directory "main.truss" program;
  directory

let computed directory =
  match Database.session_engine directory with Some engine -> Engine.executed engine | None -> []

let clear directory = Option.iter Engine.clear_log (Database.session_engine directory)

let expect_status (response : Database.response) status =
  if response.status <> status then
    fail "status %d, expected %d: %s%s" response.status status response.output response.errors

let contains text part =
  let n = String.length part and l = String.length text in
  let rec at i = i + n <= l && (String.sub text i n = part || at (i + 1)) in
  at 0

let expect_contains (response : Database.response) part =
  let all = response.output ^ response.errors in
  if not (contains all part) then fail "expected %S in:\n%s" part all

(* The background process, first, since a process cannot fork once a
   build has started domains *)

let () =
  test "the background process answers requests and sees every earlier write" (fun () ->
      fresh_store ();
      let directory = package () in
      match Unix.fork () with
      | 0 ->
          Database.serve ();
          Unix._exit 0
      | child ->
          let call command =
            Database.call ~program:"/nonexistent" { directory; command; json = false }
          in
          expect_status (call Check) 0;
          write directory "main.truss" "fn broken() -> Int64 {\n  true\n}\n";
          expect_status (call Check) 1;
          let busy = request directory Check in
          expect_status busy 2;
          expect_status (call Stop) 0;
          ignore (Unix.waitpid [] child))

let () =
  test "a check of a package with no errors succeeds" (fun () ->
      fresh_store ();
      expect_status (request (package ()) Check) 0);
  test "a check reports an error, and none once it is fixed" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "main.truss" "fn broken() -> Int64 {\n  true\n}\n";
      let response = request directory Check in
      expect_status response 1;
      expect_contains response "main.truss:2:3";
      write directory "main.truss" program;
      expect_status (request directory Check) 0);
  test "a check after a restart computes nothing" (fun () ->
      fresh_store ();
      let directory = package () in
      expect_status (request directory Check) 0;
      Database.reset ();
      expect_status (request directory Check) 0;
      let again = computed directory in
      if again <> [] then fail "computed [%s]" (String.concat "; " again));
  test "a change made while no process ran is seen after a restart" (fun () ->
      fresh_store ();
      let directory = package () in
      expect_status (request directory Check) 0;
      Database.reset ();
      write directory "main.truss" "fn broken() -> Int64 {\n  true\n}\n";
      expect_status (request directory Check) 1);
  test "editing one function's body checks only that body again" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "other.truss" "fn triple(value: Int64) -> Int64 {\n  value * 3\n}\n";
      expect_status (request directory Check) 0;
      clear directory;
      write directory "main.truss" (program ^ "\nfn unused() -> Int64 {\n  1\n}\n");
      write directory "main.truss" program;
      write directory "other.truss" "fn triple(value: Int64) -> Int64 {\n  value * 4\n}\n";
      expect_status (request directory Check) 0;
      let again = computed directory in
      if List.mem "checked(app::main::double)" again then fail "checked double again";
      if not (List.mem "checked(app::other::triple)" again) then fail "did not check triple");
  test "a removed module is gone from the package" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "broken.truss" "fn broken() -> Int64 {\n  true\n}\n";
      expect_status (request directory Check) 1;
      Sys.remove (Filename.concat directory "broken.truss");
      expect_status (request directory Check) 0);
  test "a malformed manifest is reported" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "truss.toml" "[package]\nname = \n";
      let response = request directory Check in
      expect_status response 1;
      expect_contains response "truss.toml:2");
  test "a package cannot depend on one that runs only on 64-bit targets unless it does too"
    (fun () ->
      fresh_store ();
      let root = fresh "worktree" in
      write root "wide/truss.toml" "[package]\nname = \"wide\"\nusize_bits = 64\n";
      write root "wide/main.truss" program;
      write root "app/truss.toml"
        "[package]\nname = \"app\"\n\n[dependencies]\nwide = { version = \"1\" }\n";
      write root "app/main.truss" program;
      let response = request root Check in
      expect_status response 1;
      expect_contains response "wide runs only on 64-bit targets");
  test "a check in a package's directory checks only that package" (fun () ->
      fresh_store ();
      let root = fresh "worktree" in
      write root "good/truss.toml" (manifest "good");
      write root "good/main.truss" program;
      write root "bad/truss.toml" (manifest "bad");
      write root "bad/main.truss" "fn broken() -> Int64 {\n  true\n}\n";
      expect_status (request (Filename.concat root "good") Check) 0;
      expect_status (request (Filename.concat root "bad") Check) 1;
      expect_status (request root Check) 1);
  test "a new worktree starts from the nearest session" (fun () ->
      fresh_store ();
      let first = package () in
      expect_status (request first Check) 0;
      let fresh_work = List.length (computed first) in
      let second = package () in
      write second "main.truss" (program ^ "\nfn extra() -> Int64 {\n  1\n}\n");
      expect_status (request second Check) 0;
      let work = List.length (computed second) in
      if work * 2 >= fresh_work then fail "computed %d of %d" work fresh_work)

let () =
  test "holes are listed with their type, the names in scope, and what they block" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "main.truss"
        "fn parse(text: String) -> Int64 {\n\
        \  let trimmed = text.trim()\n\
        \  todo\n\
         }\n\n\
         test \"parsing\" {\n\
        \  assert parse(\"1\") == 1\n\
         }\n";
      let response = request directory Holes in
      expect_status response 0;
      expect_contains response "main.truss:3:3: a hole of type Int64";
      expect_contains response "text: String";
      expect_contains response "trimmed";
      expect_contains response "blocks: app::main::test \"parsing\"");
  test "references name what reads a definition" (fun () ->
      fresh_store ();
      let response = request (package ()) (References { name = "double" }) in
      expect_status response 0;
      expect_contains response
        "app::main::test \"doubling\": its body reads the signature of app::main::double");
  test "dependencies name what a definition reads" (fun () ->
      fresh_store ();
      let response = request (package ()) (Dependencies { name = "test \"doubling\"" }) in
      expect_status response 0;
      expect_contains response "reads the signature of app::main::double");
  test "explaining a name gives its meaning and the signature it refers to" (fun () ->
      fresh_store ();
      let directory = package () in
      let response =
        request directory
          (Explain { file = Filename.concat directory "main.truss"; line = 6; column = 10 })
      in
      expect_status response 0;
      expect_contains response "app::main::double";
      expect_contains response "fn double(value: Int64) -> Int64")

(* Lowering is kept too *)

let lowered directory =
  List.filter (fun label -> contains label "lowered_instance(") (computed directory)

let () =
  test "a test run after a restart lowers nothing" (fun () ->
      fresh_store ();
      let directory = package () in
      expect_status (request directory (Test { sanitize = false })) 0;
      Database.reset ();
      expect_status (request directory (Test { sanitize = false })) 0;
      match lowered directory with
      | [] -> ()
      | found -> fail "lowered [%s]" (String.concat "; " found));
  test "editing one function lowers that function again, and not the others" (fun () ->
      fresh_store ();
      let directory = package () in
      write directory "other.truss"
        "internal fn triple(value: Int64) -> Int64 {\n\
        \  value * 3\n\
         }\n\n\
         test \"tripling\" {\n\
        \  assert triple(1) == 3\n\
         }\n";
      expect_status (request directory (Test { sanitize = false })) 0;
      clear directory;
      write directory "other.truss"
        "internal fn triple(value: Int64) -> Int64 {\n\
        \  value * 4 - value\n\
         }\n\n\
         test \"tripling\" {\n\
        \  assert triple(1) == 3\n\
         }\n";
      expect_status (request directory (Test { sanitize = false })) 0;
      let again = lowered directory in
      if List.exists (fun label -> contains label "double") again then
        fail "lowered double again: [%s]" (String.concat "; " again);
      if not (List.exists (fun label -> contains label "triple") again) then
        fail "did not lower triple: [%s]" (String.concat "; " again))

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

let () =
  test "impact lists what changed since the base, and the signatures to review" (fun () ->
      fresh_store ();
      let root = repository () in
      change_interface root;
      let response = request root (Impact { base = None }) in
      expect_status response 0;
      expect_contains response "Changed:";
      expect_contains response "app::main::double";
      expect_contains response "Signatures to review:";
      expect_contains response "fn double(value: Int64, times: Int64) -> Int64");
  test "overlap finds a new call to a function another worktree changes" (fun () ->
      fresh_store ();
      let root = repository () in
      let other = Filename.concat (Lazy.force scratch) (Printf.sprintf "other-%d" !counter) in
      git root [ "worktree"; "add"; "-q"; other; "-b"; "other" ];
      change_interface root;
      add_caller other;
      expect_status (request root Check) 0;
      let response = request other Check in
      expect_status response 0;
      expect_contains response
        "this worktree's change to the body of app::main::quadruple reads the signature of \
         app::main::double, which the other changes");
  test "overlap with a merge finds the errors the merge would have" (fun () ->
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
      expect_status (request root Check) 0;
      expect_status (request other Check) 0;
      let response = request root (Overlap { other = None; merge = true }) in
      expect_status response 0;
      expect_contains response "merged: caller.truss: types.missing_argument")

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
        [ "incremental"; "query"; "engine"; "store"; "database"; "bin"; "test"; "tools" ]
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
