(* The standard library's tests, written in Truss. Each file of [library]
   is a module of one package, and the tests of all of them are built into
   one program and run, so a test costs its own code and no build of its
   own. With [TRUSS_TEST] set, only the tests it names are built. *)

open Harness
open Codegen_support

let directory = "library"

let modules =
  Sys.readdir directory |> Array.to_list
  |> List.filter (fun file -> Filename.check_suffix file ".truss")
  |> List.sort compare
  |> List.map (fun file ->
      let module_ : Path.module_ =
        { package = "example"; modules = [ Filename.chop_suffix file ".truss" ] }
      in
      (module_, In_channel.with_open_bin (Filename.concat directory file) In_channel.input_all))

let name_of (path : Path.t) =
  match path with
  | Test { module_; name } -> Printf.sprintf "%s: %s" (String.concat "::" module_.modules) name
  | _ -> Path.show path

let () =
  let loaded = ref None in
  test "the library's test modules check cleanly" (fun () -> loaded := Some (load_modules modules));
  match !loaded with
  | None -> ()
  | Some (database, compile) -> (
      let tests =
        List.concat_map (fun (module_, _) -> tests_in database module_) modules
        |> List.filter (fun path -> wanted (name_of path))
      in
      match Compile.run_tests compile ~time_limit:10000 tests with
      | Error message -> test "the library's tests build" (fun () -> fail "%s" message)
      | Ok records ->
          List.iter2
            (fun path (record : Compile.record) ->
              test (name_of path) (fun () ->
                  match record.outcome with
                  | Passed -> ()
                  | outcome ->
                      fail "%s%s" (Compile.show_outcome outcome)
                        (match record.message with Some message -> ": " ^ message | None -> "")))
            tests records)

let () = finish ()
