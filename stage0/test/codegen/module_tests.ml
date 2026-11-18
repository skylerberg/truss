let root = Harness.make_workspace_path "stage0/test/codegen/modules"
let list_entries directory = List.sort compare (Array.to_list (Sys.readdir directory))

let exit_with_usage () =
  prerr_endline
    "usage: module_tests.exe [INDEX/COUNT], such as 0/4, to run one share of the modules";
  exit 2

let share_index, share_count =
  match Sys.argv with
  | [| _ |] -> (0, 1)
  | [| _; share |] -> (
      match List.map int_of_string_opt (String.split_on_char '/' share) with
      | [ Some index; Some count ] when 0 <= index && index < count -> (index, count)
      | _ -> exit_with_usage ())
  | _ -> exit_with_usage ()

let files =
  List.concat_map
    (fun topic ->
      List.filter_map
        (fun entry ->
          if Filename.check_suffix entry ".truss" then
            Some (topic, Filename.chop_suffix entry ".truss")
          else None)
        (list_entries (Filename.concat root topic)))
    (list_entries root)
  |> List.filteri (fun position _ -> position mod share_count = share_index)
  |> List.map (fun (topic, name) ->
      let file_path : Path.file =
        { module_ = { Codegen_support.example with modules = [ topic; name ] }; name }
      in
      ( file_path,
        In_channel.with_open_bin
          (Filename.concat (Filename.concat root topic) (name ^ ".truss"))
          In_channel.input_all ))

let name_of (path : Path.t) =
  match path with
  | Test { module_; name } -> Printf.sprintf "%s: %s" (String.concat "::" module_.modules) name
  | _ -> Path.show path

let fail_unbuilt message =
  Harness.test_always "the modules' tests build" (fun () -> Codegen_support.fail "%s" message)

let find_expected_panic (path : Path.t) =
  match path with
  | Test { module_ = { modules = [ "library"; "panics" ]; _ }; name } -> Some name
  | _ -> None

let () =
  let loaded = ref None in
  let load () = loaded := Some (Codegen_support.load_files files) in
  let checking = "the modules check cleanly" in
  if Harness.is_wanted checking then Codegen_support.test checking load else load ();
  match !loaded with
  | None -> ()
  | Some (database, backend) -> (
      let tests =
        List.concat_map
          (fun ((file : Path.file), _) -> Codegen_support.list_tests_in database file.module_)
          files
        |> List.filter (fun path -> Harness.is_wanted (name_of path))
      in
      match Backend.run_tests backend ~time_limit_ms:10000 tests with
      | exception Compiler_bug.Bug bug -> fail_unbuilt (Compiler_bug.to_string bug)
      | Error message -> fail_unbuilt message
      | Ok records ->
          List.iter2
            (fun path (record : Backend.Test_report.record) ->
              Codegen_support.test (name_of path) (fun () ->
                  match (find_expected_panic path, record.outcome, record.message) with
                  | None, Passed, _ -> ()
                  | Some expected, Panicked, Some message
                    when String.includes ~affix:expected message ->
                      ()
                  | _, outcome, message ->
                      Codegen_support.fail "%s%s"
                        (Backend.Test_report.show_outcome outcome)
                        (match message with Some message -> ": " ^ message | None -> "")))
            tests records)
