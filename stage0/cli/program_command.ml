(* [truss run] and [truss build]: build the package's program from its
   [main]. [truss run] is [truss build] followed by running the program,
   except that it builds for development unless told to build for
   release. *)

(* A package's program starts at the [main] of its root module, the
   package's top directory. *)
let main_of (project : Project.t) (package : Project.package) =
  let module_ : Path.module_ = { package = package.name; modules = [] } in
  if not (List.mem module_ (Project.modules project)) then None
  else
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        match declaration.path with
        | Top { name = "main"; _ } when declaration.kind = Function && declaration.ordinal = 0 ->
            Some declaration.path
        | _ -> None)
      (Query.demand project.context Resolve.Names.declarations module_)

let mains (project : Project.t) = List.filter_map (main_of project) project.packages

(* The package's [main]. A package without one is a library, which is not
   an error in its code, so the command exits with 2. *)
let main (project : Project.t) =
  let package = Project.package project in
  match main_of project package with
  | Some main -> main
  | None ->
      Project.cannot_run
        "The package %s has no `main` in its root module, a file in its top directory, so it has \
         no program."
        (Path.show_package package.name)

(* Rejects a program whose [main] can reach a [todo] or an [echo] in code,
   or a hole in a proof, and lists each in order of position with the
   definitions from [main] to the one that holds it. *)
let refuse_unshippable project compile main =
  let in_code =
    match Compile.unshippable compile ~main with
    | Error message -> Project.cannot_run "%s" message
    | Ok unshippable ->
        List.map
          (fun ({ failure; file; line; column; way } : Compile.unshippable) ->
            ( Project.shown_workspace_path project file,
              line,
              column,
              (failure :> [ `Todo | `Echo | `Proof_hole ]),
              way ))
          unshippable
  in
  let in_proofs =
    List.map
      (fun (definition, file, line, column) -> (file, line, column, `Proof_hole, [ definition ]))
      (Proofs.holes_reached project main)
  in
  match List.sort_uniq compare (in_code @ in_proofs) with
  | [] -> ()
  | refusals ->
      let kind = function `Todo -> "todo" | `Echo -> "echo" | `Proof_hole -> "proof hole" in
      let shown = function
        | `Todo -> "`todo`"
        | `Echo -> "`echo`"
        | `Proof_hole -> "`todo` in a proof"
      in
      if Output.json () then
        Json.print
          (Json.document ~diagnostics:[]
             [
               ( "unshippable",
                 Json.List
                   (List.map
                      (fun (file, line, column, failure, way) ->
                        Json.Object
                          [
                            ("kind", Json.String (kind failure));
                            ("file", Json.String file);
                            ("line", Json.Int line);
                            ("column", Json.Int column);
                            ( "way",
                              Json.List (List.map (fun path -> Json.String (Path.show path)) way) );
                          ])
                      refusals) );
             ])
      else
        List.iter
          (fun (file, line, column, failure, way) ->
            Output.eprintf
              "%s:%d:%d: %s can be reached from `main`, so the program cannot be built.\n    %s\n"
              file line column (shown failure)
              (String.concat " -> " (List.map Path.show way)))
          refusals;
      raise (Outcome.Stop 1)

(* Builds the package's program to [output], or else to a fresh path in
   the store's directory of programs, and returns its path. A release build requires
   every obligation to be proven, so it omits the run-time checks that the
   proofs replace, and it refuses a program that can reach unfinished
   code. A development build skips the prover and keeps the checks; a
   [todo] it reaches stops the program, and an [echo] writes to standard
   error. *)
let build_program ?output (project : Project.t) (build : Compiler.build) =
  let is_release = build = Release in
  let report = Report.gather ~proofs:is_release project in
  if not (Report.clean report) then raise (Report.Errors report);
  let main = main project in
  let compile = Compiler.create ~checks:(not is_release) project build in
  if is_release then refuse_unshippable project compile main;
  let output = Option.value output ~default:(Compile.fresh_program compile) in
  match Compile.build_program compile ~main ~output with
  | Error message -> Project.cannot_run "%s" message
  | Ok () -> output

(* [truss run]: builds the command's one package, and returns the program
   for the client to run on its terminal with the arguments, so it can
   prompt and read input. *)
let run ~release ~arguments =
  let program = build_program (Project.current ()) (if release then Release else Development) in
  Outcome.Run_program { program; arguments }

(* [truss build]: builds for release to [output], or else to a file named
   after the package in the current directory. *)
let build ~output =
  let project = Project.current () in
  let package = Project.package project in
  let output = Project.normalize (Option.value output ~default:(Path.show_package package.name)) in
  ignore (build_program project Release ~output);
  if Output.json () then
    Json.print (Json.document ~diagnostics:[] [ ("output", Json.String (Project.shown output)) ])
  else Output.printf "Built %s.\n" (Project.shown output);
  Outcome.Exit 0
