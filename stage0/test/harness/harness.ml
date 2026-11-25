let suite = Filename.remove_extension (Filename.basename Sys.executable_name)

let () =
  match Array.to_list Sys.argv with
  | _ :: (_ :: _ as arguments) ->
      Printf.eprintf
        "%s takes no arguments, and was given %s. Set TRUSS_TEST to run only the tests whose names \
         contain its value.\n"
        suite
        (String.concat " " (List.map (Printf.sprintf "`%s`") arguments));
      exit 2
  | [] | [ _ ] -> ()

let () =
  match Sys.getenv_opt "TRUSS_SKIP_SUITES" with
  | Some names when List.mem suite (String.split_on_char ',' names) ->
      print_endline ("skipped: TRUSS_SKIP_SUITES names " ^ suite);
      exit 0
  | _ -> ()

let share =
  match Sys.getenv_opt "TRUSS_TEST_SHARE" with
  | None | Some "" -> None
  | Some text -> (
      match List.map int_of_string_opt (String.split_on_char '/' text) with
      | [ Some index; Some count ] when 0 <= index && index < count -> Some (index, count)
      | _ ->
          prerr_endline ("TRUSS_TEST_SHARE is `index/count`, such as `0/2`, not `" ^ text ^ "`.");
          exit 2)

let failures = ref 0
let count = ref 0
let current_test = ref ""
let running_depth = ref 0

exception Test_failed of string

let report_failure test message =
  incr failures;
  Printf.printf "FAIL %s: %s\n" test message

let fail format =
  Printf.ksprintf
    (fun message ->
      if !running_depth > 0 then raise (Test_failed message)
      else begin
        report_failure "outside a test" message;
        exit 1
      end)
    format

let is_wanted =
  match Sys.getenv_opt "TRUSS_TEST" with
  | None | Some "" -> fun _ -> true
  | Some affix -> String.includes ~affix

let read_environment () =
  List.filter_map (String.split_first ~sep:"=") (Array.to_list (Unix.environment ()))

let restore_environment saved =
  let current = read_environment () in
  List.iter (fun (name, _) -> if not (List.mem_assoc name saved) then Unix.unsetenv name) current;
  List.iter
    (fun (name, value) -> if List.assoc_opt name current <> Some value then Unix.putenv name value)
    saved

let slow_test_seconds = 0.5

let test_always name body =
  incr count;
  let enclosing_test = !current_test in
  current_test := name;
  incr running_depth;
  let environment = read_environment () in
  let started = Unix.gettimeofday () in
  (match body () with
  | () -> ()
  | exception Test_failed message -> report_failure name message
  | exception exception_ ->
      report_failure name
        (Printf.sprintf "raised %s%s" (Printexc.to_string exception_) (Printexc.get_backtrace ())));
  let elapsed = Unix.gettimeofday () -. started in
  if elapsed > slow_test_seconds then Printf.printf "slow: %.2f s: %s\n%!" elapsed name;
  decr running_depth;
  current_test := enclosing_test;
  restore_environment environment

let is_in_share name =
  match share with Some (index, count) -> Hashtbl.hash name mod count = index | None -> true

let test name body = if is_wanted name && is_in_share name then test_always name body

let workspace_root =
  lazy
    (let rec search_upward directory =
       if Sys.file_exists (Filename.concat directory "dune-project") then directory
       else
         let parent = Filename.dirname directory in
         if parent = directory then failwith "no dune-project above the test executable"
         else search_upward parent
     in
     let executable =
       if Filename.is_relative Sys.executable_name then
         Filename.concat (Sys.getcwd ()) Sys.executable_name
       else Sys.executable_name
     in
     search_upward (Filename.dirname executable))

let make_workspace_path path = Filename.concat (Lazy.force workspace_root) path

let () =
  at_exit (fun () ->
      if !failures > 0 then begin
        Printf.printf "%d failures in %d tests\n" !failures !count;
        exit 1
      end
      else Printf.printf "%d tests pass\n" !count)

let scratch_root =
  lazy
    (let root = Filename.temp_dir ~temp_dir:"/tmp" "truss-tests" "" in
     at_exit (fun () -> try File_system.remove root with Sys_error _ | Unix.Unix_error _ -> ());
     root)

let scratch_count = ref 0

let make_scratch_directory name =
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

let list_markdown_documents () =
  Sys.readdir (make_workspace_path ".")
  |> Array.to_list
  |> List.filter (fun name -> Filename.check_suffix name ".md")
  |> List.sort compare

let expect_string ~expected actual =
  if not (String.equal expected actual) then fail "expected %S, got %S" expected actual

let expect_strings ~expected actual =
  if expected <> actual then
    fail "expected [%s], got [%s]" (String.concat "; " expected) (String.concat "; " actual)
