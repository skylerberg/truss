(* The [truss] command: [truss test DIRECTORY] builds a package's tests and
   runs them, and [truss run DIRECTORY ARGUMENTS...] builds its program and
   runs it. A package is a directory with a [truss.toml] manifest naming
   it; each [.truss] file under the directory is one of its modules. *)

let usage () =
  prerr_endline "usage: truss test DIRECTORY\n       truss run DIRECTORY [ARGUMENTS...]";
  exit 2

(* The package's name, from its manifest's [name = "..."] line. *)
let package_name directory =
  let manifest = Filename.concat directory "truss.toml" in
  if not (Sys.file_exists manifest) then begin
    Printf.eprintf "%s has no truss.toml\n" directory;
    exit 2
  end;
  let lines = String.split_on_char '\n' (In_channel.with_open_bin manifest In_channel.input_all) in
  match
    List.find_map
      (fun line ->
        match String.split_on_char '=' line with
        | [ key; value ] when String.trim key = "name" ->
            let value = String.trim value in
            if String.length value >= 2 && value.[0] = '"' then
              Some (String.sub value 1 (String.length value - 2))
            else None
        | _ -> None)
      lines
  with
  | Some name -> name
  | None ->
      Printf.eprintf "%s names no package\n" manifest;
      exit 2

(* Every [.truss] file under the directory, as a module and its text. *)
let rec modules package directory relative =
  Sys.readdir (Filename.concat directory (String.concat Filename.dir_sep relative))
  |> Array.to_list |> List.sort compare
  |> List.concat_map (fun entry ->
      let path =
        Filename.concat directory (String.concat Filename.dir_sep (relative @ [ entry ]))
      in
      if Sys.is_directory path then modules package directory (relative @ [ entry ])
      else if Filename.check_suffix entry ".truss" then
        [
          ( { Path.package; modules = relative @ [ Filename.chop_suffix entry ".truss" ] },
            In_channel.with_open_bin path In_channel.input_all );
        ]
      else [])

let load directory =
  let name = package_name directory in
  let own = modules name directory [] in
  let database = Query.create () in
  List.iter
    (fun (module_, text) -> Query.set database Workspace.file_text module_ text)
    (Standard_library.modules @ own);
  Query.set database Workspace.packages Standard_library.package
    {
      name = Standard_library.package;
      dependencies = [];
      modules = List.map fst Standard_library.modules;
    };
  Query.set database Workspace.packages name { name; dependencies = []; modules = List.map fst own };
  (database, List.map fst own)

(* Every error in the package, reported with its source, which stops the
   build. *)
let check database modules =
  let errors =
    List.concat_map
      (fun module_ ->
        let file = Query.demand database Workspace.file module_ in
        let diagnostics =
          file.diagnostics
          @ Resolve.diagnostics database module_
          @ Interface.diagnostics database module_
          @ Infer.diagnostics database module_
        in
        List.map (fun diagnostic -> Diagnostic.render file.source diagnostic) diagnostics)
      modules
  in
  List.iter prerr_endline errors;
  if errors <> [] then exit 1

let compiler database =
  match Toolchain.find () with
  | Error message ->
      prerr_endline message;
      exit 2
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
      | None ->
          prerr_endline "the package has no main";
          exit 2
      | Some main -> (
          match Compile.run_program (compiler database) ~main ~arguments with
          | Error message ->
              prerr_endline message;
              exit 1
          | Ok (status, output, errors) ->
              print_string output;
              prerr_string errors;
              exit status))
  | _ -> usage ()
