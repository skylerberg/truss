(* [truss run] and [truss build]: the package's program, built from its
   [main]. *)

exception Stop of int
(** The command reported why it stopped, and exits with this status. *)

(* A package's program starts at the [main] of its [main] module. *)
let main_of (project : Project.t) (package : Project.package) =
  let module_ : Path.module_ = { package = package.name; modules = [ "main" ] } in
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

(* The package's [main]. A package with none is a library, which is not a
   problem in its code, so the command stops with 2. *)
let main (project : Project.t) =
  let package = Project.package project in
  match main_of project package with
  | Some main -> main
  | None ->
      Project.cannot_run "The package %s has no `main` in a `main` module, so it has no program."
        (Path.show_package package.name)

let stop_at_diagnostics ?proofs ~json project =
  let report = Report.gather ?proofs project in
  if not (Report.clean report) then begin
    if json then Json.print (Report.document report []) else Report.print report;
    raise (Stop 1)
  end

let what = function `Todo -> "`todo`" | `Echo -> "`echo`"

let unshippable_json project (unshippable : Compile.unshippable) =
  Json.Object
    [
      ("kind", Json.String (match unshippable.failure with `Todo -> "todo" | `Echo -> "echo"));
      ("file", Json.String (Project.shown_workspace_path project unshippable.file));
      ("line", Json.Int unshippable.line);
      ("column", Json.Int unshippable.column);
      ("way", Json.List (List.map (fun path -> Json.String (Path.show path)) unshippable.way));
    ]

(* Refuses a program whose [main] can reach a [todo], or with [echo], an
   [echo], listing each with the way from [main] to it. *)
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
              unshippable.line unshippable.column (what unshippable.failure)
              (String.concat " -> " (List.map Path.show unshippable.way)))
          unshippable;
      raise (Stop 1)

(* Refuses a program whose [main] can reach a definition whose proofs have
   a hole, naming each. *)
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

(* [truss run]: a development build, unless [release], of the one package
   the directory is about, which the client runs on its own terminal with
   the arguments, so it can prompt and read. A [todo] is refused even here,
   since reaching one would be a failure its signature does not show;
   [echo] writes to standard error, except in a release build, which
   refuses it as [truss build] does. *)
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

(* [truss build]: a release build at [output], or else at a file named after
   the package in the current directory. *)
let build ~directory ~output ~json =
  catching (fun () ->
      let project = Project.load directory in
      let package = Project.package project in
      (* A program is built only once its proofs are done. *)
      stop_at_diagnostics ~proofs:true ~json project;
      let main = main project in
      refuse_holes ~json project main;
      (* Every proof the program reaches is done, the standard library's
         included, so what they show is not checked again at run time. *)
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
