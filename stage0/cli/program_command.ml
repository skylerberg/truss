(* [truss run] and [truss build]: build the package's program from its
   [main]. [truss run] is [truss build] followed by running the program,
   except that it builds for development unless told to build for
   release. *)

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

let stop_at_diagnostics ~proofs ~json project =
  let report = Report.gather ~proofs project in
  if not (Report.clean report) then begin
    if json then Json.print (Report.document report []) else Report.print report;
    raise (Stop 1)
  end

(* What a release build refuses and [main] can reach: a [todo] or an [echo]
   in code, with the definitions from [main] to the one that holds it, or
   a hole in the proofs of a definition. *)
type refusal = {
  failure : [ `Todo of Path.t list | `Echo of Path.t list | `Proof_hole of Path.t ];
  file : string;  (** As the current directory shows it *)
  line : int;
  column : int;
}

let refusals project compile main =
  let in_code =
    match Compile.unshippable compile ~main with
    | Error message -> Project.cannot_run "%s" message
    | Ok unshippable ->
        List.map
          (fun (unshippable : Compile.unshippable) ->
            {
              failure =
                (match unshippable.failure with
                | `Todo -> `Todo unshippable.way
                | `Echo -> `Echo unshippable.way);
              file = Project.shown_workspace_path project unshippable.file;
              line = unshippable.line;
              column = unshippable.column;
            })
          unshippable
  in
  let in_proofs =
    List.map
      (fun (hole : Proofs.hole) ->
        let source = Project.source project hole.file in
        let line, column = Source.position source hole.offset in
        {
          failure = `Proof_hole hole.definition;
          file = Project.shown (Source.path source);
          line;
          column;
        })
      (Proofs.holes_reached project main)
  in
  List.sort_uniq
    (fun left right ->
      compare
        (left.file, left.line, left.column, left.failure)
        (right.file, right.line, right.column, right.failure))
    (in_code @ in_proofs)

let refusal_json refusal =
  let kind, detail =
    match refusal.failure with
    | `Todo way ->
        ("todo", ("way", Json.List (List.map (fun path -> Json.String (Path.show path)) way)))
    | `Echo way ->
        ("echo", ("way", Json.List (List.map (fun path -> Json.String (Path.show path)) way)))
    | `Proof_hole definition -> ("proof hole", ("definition", Json.String (Path.show definition)))
  in
  Json.Object
    [
      ("kind", Json.String kind);
      ("file", Json.String refusal.file);
      ("line", Json.Int refusal.line);
      ("column", Json.Int refusal.column);
      detail;
    ]

let print_refusal refusal =
  let position = Printf.sprintf "%s:%d:%d" refusal.file refusal.line refusal.column in
  let way path = String.concat " -> " (List.map Path.show path) in
  match refusal.failure with
  | `Todo path ->
      Output.eprintf
        "%s: `todo` can be reached from `main`, so the program cannot be built.\n    %s\n" position
        (way path)
  | `Echo path ->
      Output.eprintf
        "%s: `echo` can be reached from `main`, so the program cannot be built.\n    %s\n" position
        (way path)
  | `Proof_hole definition ->
      Output.eprintf
        "%s: `%s` has a hole in its proofs and can be reached from `main`, so the program cannot \
         be built.\n"
        position (Path.show definition)

(* Rejects a program whose [main] reaches a [todo], an [echo], or a hole in
   a proof, and lists each in order of position. *)
let refuse_unshippable ~json project compile main =
  match refusals project compile main with
  | [] -> ()
  | refusals ->
      if json then
        Json.print
          (Json.document ~diagnostics:[]
             [ ("unshippable", Json.List (List.map refusal_json refusals)) ])
      else List.iter print_refusal refusals;
      raise (Stop 1)

(* Builds the package's program to [output]. A release build requires
   every obligation to be proven, so it omits the run-time checks that the
   proofs replace, and it refuses a program that can reach unfinished
   code. A development build skips the prover and keeps the checks; a
   [todo] it reaches stops the program, and an [echo] writes to standard
   error. *)
let build_program ~json (project : Project.t) (build : Compiler.build) ~output =
  let is_release = build = Release in
  stop_at_diagnostics ~proofs:is_release ~json project;
  let main = main project in
  let compile = Compiler.create ~checks:(not is_release) project build in
  if is_release then refuse_unshippable ~json project compile main;
  match Compile.build_program compile ~main ~output with
  | Error message -> Project.cannot_run "%s" message
  | Ok () -> ()

let catching work = try work () with Stop status -> Outcome.Exit status

(* [truss run]: builds the command's one package, and returns the program
   for the client to run on its terminal with the arguments, so it can
   prompt and read input. *)
let run ~directory ~release ~arguments =
  catching (fun () ->
      let project = Project.load directory in
      ignore (Project.package project);
      let program =
        Filename.concat (Database.programs_directory ())
          (Printf.sprintf "program-%d-%d" (Unix.getpid ())
             (int_of_float (Unix.gettimeofday () *. 1e6)))
      in
      build_program ~json:false project (if release then Release else Development) ~output:program;
      Outcome.Run_program { program; arguments })

(* [truss build]: builds for release to [output], or else to a file named
   after the package in the current directory. *)
let build ~directory ~output ~json =
  catching (fun () ->
      let project = Project.load directory in
      let package = Project.package project in
      let output =
        Project.normalize (Option.value output ~default:(Path.show_package package.name))
      in
      build_program ~json project Release ~output;
      if json then
        Json.print
          (Json.document ~diagnostics:[] [ ("output", Json.String (Project.shown output)) ])
      else Output.printf "Built %s.\n" (Project.shown output);
      Outcome.Exit 0)
