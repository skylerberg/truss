let () =
  let suite = Filename.remove_extension (Filename.basename Sys.executable_name) in
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

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      Printf.printf "FAIL %s: %s\n" !current_test message)
    format

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
  match body () with
  | () -> ()
  | exception exception_ ->
      fail "raised %s%s" (Printexc.to_string exception_) (Printexc.get_backtrace ())

let ordinal = ref 0

let test name body =
  if wanted name then begin
    let is_mine =
      match share with Some (index, count) -> !ordinal mod count = index | None -> true
    in
    incr ordinal;
    if is_mine then always name body
  end

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
    (let root = Filename.temp_dir ~temp_dir:"/tmp" "truss-tests" "" in
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

let rec files_under ~suffix directory =
  Sys.readdir (workspace_path directory)
  |> Array.to_list
  |> List.concat_map (fun name ->
      let path = Filename.concat directory name in
      if Sys.is_directory (workspace_path path) then files_under ~suffix path
      else if Filename.check_suffix name suffix then [ path ]
      else [])

let markdown_documents () =
  Sys.readdir (workspace_path ".")
  |> Array.to_list
  |> List.filter (fun name -> Filename.check_suffix name ".md")
  |> List.sort compare

let truss_files () =
  List.sort compare
    (files_under ~suffix:".truss" "standard" @ files_under ~suffix:".truss" "stage0/test/fixtures")

let expect_string ~expected actual =
  if not (String.equal expected actual) then fail "expected %S, got %S" expected actual

let expect_strings ~expected actual =
  if expected <> actual then
    fail "expected [%s], got [%s]" (String.concat "; " expected) (String.concat "; " actual)
