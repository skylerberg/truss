(* The [truss] command: [truss test DIRECTORY] builds a package's tests and
   runs them, and [truss run DIRECTORY ARGUMENTS...] builds its program and
   runs it. A package is a directory with a [truss.toml] manifest naming
   it; each [.truss] file under the directory is one of its modules. *)

let usage () =
  prerr_endline "usage: truss test DIRECTORY\n       truss run DIRECTORY [ARGUMENTS...]";
  exit 2

let fail format =
  Printf.ksprintf
    (fun message ->
      prerr_endline message;
      exit 2)
    format

(* The package in a directory, loaded with the standard library, and its
   modules. *)
let load directory =
  let manifest_path = Filename.concat directory "truss.toml" in
  if not (Sys.file_exists manifest_path) then fail "%s: no truss.toml." directory;
  let manifest =
    try Type_checker.Manifest.parse (In_channel.with_open_bin manifest_path In_channel.input_all)
    with Type_checker.Manifest.Malformed (line, expected) ->
      fail "%s:%d: expected %s." manifest_path line expected
  in
  let database = Query.create () in
  let modules = Type_checker.read_directory ~package:manifest.name directory in
  Type_checker.load_standard database;
  Type_checker.load_package database ~name:manifest.name ~dependencies:manifest.dependencies modules;
  (database, List.map fst modules)

(* Every diagnostic in the package, each an error, which stops the build. *)
let check database modules =
  let found =
    List.concat_map
      (fun module_ ->
        let source = (Query.demand database Workspace.file module_).source in
        List.map
          (fun diagnostic -> Diagnostic.render source diagnostic)
          (Diagnostic.shown (Type_checker.diagnostics database module_)))
      modules
  in
  List.iter prerr_string found;
  if found <> [] then exit 1

let compiler database =
  match Toolchain.find () with
  | Error message -> fail "%s" message
  | Ok toolchain ->
      let home = Option.value (Sys.getenv_opt "HOME") ~default:(Filename.get_temp_dir_name ()) in
      let cache = Build.cache (Filename.concat home ".cache/truss/objects") in
      Compile.create database Memory_layout.target_64 toolchain cache
        { build = Development; optimization = O1; extra = [] }

let () =
  match Array.to_list Sys.argv with
  | _ :: "test" :: [ directory ] -> (
      let database, modules = load directory in
      check database modules;
      let tests =
        List.concat_map
          (fun module_ ->
            List.filter_map
              (fun (d : Resolve.Names.declaration) ->
                match d.path with Test _ -> Some d.path | _ -> None)
              (Query.demand database Resolve.Names.declarations module_))
          modules
      in
      match Compile.run_tests (compiler database) ~time_limit:10_000 tests with
      | Error message ->
          prerr_endline message;
          exit 1
      | Ok (status, output) ->
          let names = Array.of_list (List.map Path.show tests) in
          String.split_on_char '\n' output
          |> List.iter (fun line ->
              match String.split_on_char ' ' line with
              | [ "test"; index; outcome ] ->
                  Printf.printf "%s: %s\n" names.(int_of_string index) outcome
              | _ -> if line <> "" then print_endline line);
          exit status)
  | _ :: "run" :: directory :: arguments -> (
      let database, modules = load directory in
      check database modules;
      let main =
        List.find_map
          (fun module_ ->
            List.find_map
              (fun (d : Resolve.Names.declaration) ->
                match d.path with Top { name = "main"; _ } -> Some d.path | _ -> None)
              (Query.demand database Resolve.Names.declarations module_))
          modules
      in
      match main with
      | None -> fail "%s: the package has no main." directory
      | Some main -> (
          (* The program runs on this terminal, so it can prompt and read. *)
          let output = Filename.temp_file "truss-run-" "" in
          match Compile.build_program (compiler database) ~main ~output with
          | Error message ->
              prerr_endline message;
              exit 1
          | Ok () ->
              let status = Toolchain.run_attached output arguments in
              (try Sys.remove output with Sys_error _ -> ());
              exit status))
  | _ -> usage ()
