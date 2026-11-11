(* The standard library's tests, written in Truss. Each file of [library]
   is a module of one package, and the tests of all of them are built into
   one program and run, so a test costs its own code and no build of its
   own. With [TRUSS_TEST] set, only the tests it names are built.

   A test of the module [panics] must panic, with a message that contains
   the test's name. Every other test must pass. *)

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

(* The tests could not be built. This is reported whatever [TRUSS_TEST]
   names, since none of the tests it names can run. *)
let not_built message = always "the library's tests build" (fun () -> fail "%s" message)

let expected_panic (path : Path.t) =
  match path with Test { module_ = { modules = [ "panics" ]; _ }; name } -> Some name | _ -> None

let () =
  let loaded = ref None in
  let load () = loaded := Some (load_modules modules) in
  let checking = "the library's test modules check cleanly" in
  if wanted checking then test checking load else load ();
  match !loaded with
  | None -> ()
  | Some (database, _)
    when List.exists (fun (module_, _) -> Type_checker.diagnostics database module_ <> []) modules
    ->
      ()
  | Some (database, compile) -> (
      let tests =
        List.concat_map (fun (module_, _) -> tests_in database module_) modules
        |> List.filter (fun path -> wanted (name_of path))
      in
      match Compile.run_tests compile ~time_limit:10000 tests with
      | exception Compiler_bug.Bug bug -> not_built (Compiler_bug.to_string bug)
      | Error message -> not_built message
      | Ok records ->
          List.iter2
            (fun path (record : Compile.record) ->
              test (name_of path) (fun () ->
                  match (expected_panic path, record.outcome, record.message) with
                  | None, Passed, _ -> ()
                  | Some expected, Panicked, Some message when contains message expected -> ()
                  | _, outcome, message ->
                      fail "%s%s" (Compile.show_outcome outcome)
                        (match message with Some message -> ": " ^ message | None -> "")))
            tests records)

let () = finish ()
