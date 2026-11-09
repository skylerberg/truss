(* The [truss] command: [truss test DIRECTORY] builds a package's tests and
   runs them, [truss run DIRECTORY ARGUMENTS...] builds its program and
   runs it, and [truss prove DIRECTORY] proves its obligations. A package is a directory with a [truss.toml] manifest naming
   it; each [.truss] file under the directory is one of its modules. *)

let usage () =
  prerr_endline
    "usage: truss test [--sanitize] DIRECTORY\n\
    \       truss run [--sanitize] DIRECTORY [ARGUMENTS...]\n\
    \       truss prove DIRECTORY";
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

(* [--sanitize], right after the command, builds with AddressSanitizer and
   UndefinedBehaviorSanitizer, for testing the compiler: a report from
   either is a bug in it. *)
let sanitize, arguments =
  match Array.to_list Sys.argv with
  | program :: command :: "--sanitize" :: rest -> (true, program :: command :: rest)
  | all -> (false, all)

let sanitizers =
  [ "-fsanitize=address,undefined"; "-fno-sanitize-recover=undefined"; "-fno-omit-frame-pointer" ]

let home = Option.value (Sys.getenv_opt "HOME") ~default:(Filename.get_temp_dir_name ())

(* Where test results are kept, by the key of the code each can run. A
   sanitized build keeps none, since it checks what a plain one does not. *)
let results = if sanitize then None else Some (Filename.concat home ".cache/truss/results")

let compiler database =
  match Toolchain.find () with
  | Error message -> fail "%s" message
  | Ok toolchain ->
      let cache = Build.cache (Filename.concat home ".cache/truss/objects") in
      Compile.create database Memory_layout.target_64 toolchain cache
        { build = Development; optimization = O1; extra = (if sanitize then sanitizers else []) }

let () =
  match arguments with
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
      match Compile.run_tests ?results (compiler database) ~time_limit:10_000 tests with
      | Error message ->
          prerr_endline message;
          exit 1
      | Ok (status, output) ->
          (* Each test's name and outcome, with its message and its echo
             output indented under it, then a count of each outcome. *)
          let indented text =
            String.split_on_char '\n' text
            |> List.filter (( <> ) "")
            |> List.iter (fun line -> print_endline ("    " ^ line))
          in
          let records = Compile.parse_report output in
          List.iter2
            (fun test (record : Compile.record) ->
              Printf.printf "%s: %s\n" (Path.show test) record.outcome;
              Option.iter indented record.message;
              Option.iter indented record.echo)
            tests records;
          let count outcome =
            List.length (List.filter (fun (r : Compile.record) -> r.outcome = outcome) records)
          in
          let failed = List.length records - count "passed" in
          Printf.printf "\n%d passed, %d did not pass\n" (count "passed") failed;
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
  | _ :: "prove" :: [ directory ] -> (
      let database, modules = load directory in
      check database modules;
      match Solver.find ~cache:(Filename.concat home ".cache/truss/proofs") () with
      | Error message -> fail "%s" message
      | Ok solver ->
          let found =
            List.concat_map
              (fun module_ ->
                let source = (Query.demand database Workspace.file module_).source in
                List.map (Diagnostic.render source)
                  (Diagnostic.shown (Prover.diagnostics database solver module_)))
              modules
          in
          List.iter prerr_string found;
          (* Holes are not errors, but what reaches one is not proven. *)
          let holes =
            List.concat_map
              (fun module_ ->
                let source = (Query.demand database Workspace.file module_).source in
                List.map
                  (fun (span : Source.span) ->
                    let line, column = Source.position source span.start in
                    Printf.sprintf "%s:%d:%d: hole: this `todo` leaves the proof unfinished.\n"
                      (Source.path source) line column)
                  (Prover.holes database module_))
              modules
          in
          List.iter prerr_string holes;
          if found <> [] || holes <> [] then exit 1)
  | _ -> usage ()
