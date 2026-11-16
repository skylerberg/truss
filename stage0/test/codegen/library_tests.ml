let directory = Harness.workspace_path "stage0/test/codegen/library"

let files =
  Sys.readdir directory |> Array.to_list
  |> List.filter (fun file -> Filename.check_suffix file ".truss")
  |> List.sort compare
  |> List.map (fun file ->
      let name = Filename.chop_suffix file ".truss" in
      let file_path : Path.file =
        { module_ = { package = { owner = None; name = "example" }; modules = [ name ] }; name }
      in
      (file_path, In_channel.with_open_bin (Filename.concat directory file) In_channel.input_all))

let name_of (path : Path.t) =
  match path with
  | Test { module_; name } -> Printf.sprintf "%s: %s" (String.concat "::" module_.modules) name
  | _ -> Path.show path

let not_built message =
  Harness.always "the library's tests build" (fun () -> Codegen_support.fail "%s" message)

let expected_panic (path : Path.t) =
  match path with Test { module_ = { modules = [ "panics" ]; _ }; name } -> Some name | _ -> None

let () =
  let loaded = ref None in
  let load () = loaded := Some (Codegen_support.load_files files) in
  let checking = "the library's test modules check cleanly" in
  if Harness.wanted checking then Codegen_support.test checking load else load ();
  match !loaded with
  | None -> ()
  | Some (database, compile) -> (
      let tests =
        List.concat_map
          (fun ((file : Path.file), _) -> Codegen_support.tests_in database file.module_)
          files
        |> List.filter (fun path -> Harness.wanted (name_of path))
      in
      match Compile.run_tests compile ~time_limit_ms:10000 tests with
      | exception Compiler_bug.Bug bug -> not_built (Compiler_bug.to_string bug)
      | Error message -> not_built message
      | Ok records ->
          List.iter2
            (fun path (record : Compile.record) ->
              Codegen_support.test (name_of path) (fun () ->
                  match (expected_panic path, record.outcome, record.message) with
                  | None, Passed, _ -> ()
                  | Some expected, Panicked, Some message
                    when Codegen_support.contains message expected ->
                      ()
                  | _, outcome, message ->
                      Codegen_support.fail "%s%s" (Compile.show_outcome outcome)
                        (match message with Some message -> ": " ^ message | None -> "")))
            tests records)
