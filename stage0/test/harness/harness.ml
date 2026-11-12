let failures = ref 0
let count = ref 0
let current_test = ref ""

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      Printf.printf "FAIL %s: %s\n" !current_test message)
    format

(* Every engine a test makes is audited when the test ends: each result it
   holds is computed again in a new engine with the same inputs, and must
   come out the same. So every test of every stage also tests that the
   code database kept each result current. *)
let () = Engine.auditing := true

(* With [TRUSS_TEST] set, only the tests whose names contain it run, for
   working on one. *)
let wanted =
  match Sys.getenv_opt "TRUSS_TEST" with
  | None | Some "" -> fun _ -> true
  | Some part ->
      fun name ->
        let length = String.length part in
        let rec from start =
          start + length <= String.length name
          && (String.sub name start length = part || from (start + 1))
        in
        from 0

let always name body =
  incr count;
  current_test := name;
  (match body () with
  | () -> ()
  | exception exception_ ->
      (* With OCAMLRUNPARAM=b, the backtrace says where. *)
      fail "raised %s%s" (Printexc.to_string exception_) (Printexc.get_backtrace ()));
  match Engine.audit_all () with
  | problems ->
      List.iter (fun problem -> fail "the code database kept a stale result: %s" problem) problems
  | exception exception_ -> fail "auditing raised %s" (Printexc.to_string exception_)

let test name body = if wanted name then always name body

let expect_not_recomputed engine ~first ~again query keys =
  let computed step =
    Engine.clear_log engine;
    step ();
    Engine.computed engine query
  in
  let before = computed first in
  let after = computed again in
  List.iter
    (fun key ->
      if not (List.mem key before) then fail "%s was never computed" (Engine.result_label query key)
      else if List.mem key after then fail "%s was computed again" (Engine.result_label query key))
    keys

(* The workspace root: the nearest directory above the executable that
   holds [dune-project]. The executable is built under [_build/default],
   which has no copy of it. *)
let workspace_root =
  lazy
    (let rec up directory =
       if Sys.file_exists (Filename.concat directory "dune-project") then directory
       else
         let parent = Filename.dirname directory in
         if parent = directory then failwith "no dune-project above the test executable"
         else up parent
     in
     let executable =
       if Filename.is_relative Sys.executable_name then
         Filename.concat (Sys.getcwd ()) Sys.executable_name
       else Sys.executable_name
     in
     up (Filename.dirname executable))

let workspace_path path = Filename.concat (Lazy.force workspace_root) path

let () =
  at_exit (fun () ->
      if !failures > 0 then begin
        Printf.printf "%d failures in %d tests\n" !failures !count;
        exit 1
      end
      else Printf.printf "%d tests pass\n" !count)

let scratch_root =
  lazy
    (let root = Filename.temp_dir "truss-tests" "" in
     at_exit (fun () -> try File_system.remove root with Sys_error _ | Unix.Unix_error _ -> ());
     root)

let scratch_count = ref 0

let scratch name =
  incr scratch_count;
  let directory =
    Filename.concat (Lazy.force scratch_root) (Printf.sprintf "%s-%d" name !scratch_count)
  in
  File_system.make_directory directory;
  directory

let write_files root files =
  List.iter
    (fun (path, text) ->
      let path = Filename.concat root path in
      File_system.make_directory (Filename.dirname path);
      File_system.write path text)
    files

let git directory arguments =
  match
    Process.output "git"
      ([ "-C"; directory; "-c"; "user.name=test"; "-c"; "user.email=test@example.com" ] @ arguments)
  with
  | 0, _ -> ()
  | _ -> fail "git %s failed" (String.concat " " arguments)

let markdown_documents () =
  Sys.readdir (workspace_path ".")
  |> Array.to_list
  |> List.filter (fun name -> Filename.check_suffix name ".md")
  |> List.sort compare

let expect_string ~expected actual =
  if not (String.equal expected actual) then fail "expected %S, got %S" expected actual

let expect_strings ~expected actual =
  if expected <> actual then
    fail "expected [%s], got [%s]" (String.concat "; " expected) (String.concat "; " actual)
