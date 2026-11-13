(* [truss run] and [truss build]: build the package's program from its
   [main]. *)

exception Stop of int
(** The command has reported why it stopped, and exits with this status. *)

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

let stop_at_diagnostics ?proofs ~json project =
  let report = Report.gather ?proofs project in
  if not (Report.clean report) then begin
    if json then Json.print (Report.document report []) else Report.print report;
    raise (Stop 1)
  end

let keyword = function `Todo -> "`todo`" | `Echo -> "`echo`"

let unshippable_json project (unshippable : Compile.unshippable) =
  Json.Object
    [
      ("kind", Json.String (match unshippable.failure with `Todo -> "todo" | `Echo -> "echo"));
      ("file", Json.String (Project.shown_workspace_path project unshippable.file));
      ("line", Json.Int unshippable.line);
      ("column", Json.Int unshippable.column);
      ("way", Json.List (List.map (fun path -> Json.String (Path.show path)) unshippable.way));
    ]

(* Rejects a program whose [main] reaches a [todo], or with [echo], an
   [echo], and lists each with its call path from [main]. *)
let refuse_unshippable ~json ~echo (project : Project.t) compile main =
  match Compile.unshippable compile ~main ~echo with
  | Error message -> Project.cannot_run "%s" message
  | Ok [] -> ()
  | Ok unshippable ->
      if json then
        Json.print
          (Json.document ~diagnostics:[]
             [ ("unshippable", Json.List (List.map (unshippable_json project) unshippable)) ])
      else
        List.iter
          (fun (unshippable : Compile.unshippable) ->
            Output.eprintf
              "%s:%d:%d: %s can be reached from `main`, so the program cannot be built.\n    %s\n"
              (Project.shown_workspace_path project unshippable.file)
              unshippable.line unshippable.column (keyword unshippable.failure)
              (String.concat " -> " (List.map Path.show unshippable.way)))
          unshippable;
      raise (Stop 1)

(* Rejects a program whose [main] reaches a definition with a hole in its
   proofs, and names each definition. *)
let refuse_holes ~json (project : Project.t) main =
  match Proofs.holes_reached project main with
  | [] -> ()
  | holes ->
      if json then
        Json.print
          (Json.document ~diagnostics:[]
             [
               ( "unshippable",
                 Json.List
                   (List.map
                      (fun path ->
                        Json.Object
                          [
                            ("kind", Json.String "proof hole");
                            ("definition", Json.String (Path.show path));
                          ])
                      holes) );
             ])
      else
        List.iter
          (fun path ->
            Output.eprintf
              "`%s` has a `todo` in a proof and can be reached from `main`, so the program cannot \
               be built.\n"
              (Path.show path))
          holes;
      raise (Stop 1)

let catching work = try work () with Stop status -> Outcome.Exit status

(* [truss run]: builds the command's one package for development, or with
   [release] for release, and returns the program for the client to run on
   its terminal with the arguments, so it can prompt and read input. A
   [todo] is rejected even here, since reaching one would be a failure that
   the signature does not show. [echo] writes to standard error, except
   that a release build rejects it as [truss build] does. *)
let run ~directory ~release ~sanitize ~arguments =
  catching (fun () ->
      let project = Project.load directory in
      ignore (Project.package project);
      stop_at_diagnostics ~json:false project;
      let main = main project in
      let compile = Compiler.create ~sanitize project (if release then Release else Development) in
      refuse_unshippable ~json:false ~echo:release project compile main;
      let program =
        Filename.concat (Database.programs_directory ())
          (Printf.sprintf "program-%d-%d" (Unix.getpid ())
             (int_of_float (Unix.gettimeofday () *. 1e6)))
      in
      match Compile.build_program compile ~main ~output:program with
      | Error message -> Project.cannot_run "%s" message
      | Ok () -> Outcome.Run_program { program; arguments })

(* [truss build]: builds for release to [output], or else to a file named
   after the package in the current directory. *)
let build ~directory ~output ~json =
  catching (fun () ->
      let project = Project.load directory in
      let package = Project.package project in
      (* A program is built only once its obligations are proven. *)
      stop_at_diagnostics ~proofs:true ~json project;
      let main = main project in
      refuse_holes ~json project main;
      (* Every obligation the program reaches is proven, including the
         standard library's, so the build omits the run-time checks they
         replace. *)
      let compile = Compiler.create ~checks:false project Release in
      refuse_unshippable ~json ~echo:true project compile main;
      let output =
        Project.normalize (Option.value output ~default:(Path.show_package package.name))
      in
      match Compile.build_program compile ~main ~output with
      | Error message -> Project.cannot_run "%s" message
      | Ok () ->
          if json then
            Json.print
              (Json.document ~diagnostics:[] [ ("output", Json.String (Project.shown output)) ])
          else Output.printf "Built %s.\n" (Project.shown output);
          Outcome.Exit 0)
