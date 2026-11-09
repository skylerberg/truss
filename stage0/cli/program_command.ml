(* [truss run] and [truss build]: the package's program, built from its
   [main]. See CLI.md, "Running and building". *)

exception Stop of int
(** The command reported why it stopped, and exits with this status. *)

let mains (project : Project.t) =
  List.concat_map
    (fun module_ ->
      List.filter_map
        (fun (declaration : Resolve.Names.declaration) ->
          match declaration.path with
          | Top { name = "main"; _ } when declaration.kind = Function && declaration.ordinal = 0 ->
              Some declaration.path
          | _ -> None)
        (Query.demand project.database Resolve.Names.declarations module_))
    (Project.modules project)

(* The package's [main]. A package with none has no program, which is not a
   problem in its code, so it stops with 2; one with several does have a
   problem, and stops with 1. *)
let main (project : Project.t) =
  match mains project with
  | [ main ] -> main
  | [] ->
      Project.cannot_run "The package %s has no `main`, so it has no program." project.manifest.name
  | several ->
      Printf.eprintf "The package has more than one `main`: %s.\n%!"
        (String.concat ", " (List.map (fun path -> "`" ^ Path.show path ^ "`") several));
      raise (Stop 1)

let stop_at_diagnostics ~json project =
  match Report.gather project with
  | [] -> ()
  | files ->
      if json then Json.print (Json.document ~diagnostics:(Report.to_json files) [])
      else Report.print files;
      raise (Stop 1)

let what = function `Todo -> "`todo`" | `Echo -> "`echo`"

let unshippable_json project (u : Compile.unshippable) =
  Json.Object
    [
      ("kind", Json.String (match u.failure with `Todo -> "todo" | `Echo -> "echo"));
      ("file", Json.String (Project.shown_workspace_path project u.file));
      ("line", Json.Int u.line);
      ("column", Json.Int u.column);
      ("way", Json.List (List.map (fun p -> Json.String (Path.show p)) u.way));
    ]

(* Refuses a program whose [main] can reach a [todo], or with [echo], an
   [echo], listing each with the way from [main] to it. *)
let refuse_unshippable ~json ~echo (project : Project.t) compile main =
  match Compile.unshippable compile ~main ~echo with
  | Error message -> Project.cannot_run "%s" message
  | Ok [] -> ()
  | Ok found ->
      if json then
        Json.print
          (Json.document ~diagnostics:[]
             [ ("unshippable", Json.List (List.map (unshippable_json project) found)) ])
      else
        List.iter
          (fun (u : Compile.unshippable) ->
            Printf.eprintf
              "%s:%d:%d: %s can be reached from `main`, so the program cannot be built.\n    %s\n"
              (Project.shown_workspace_path project u.file)
              u.line u.column (what u.failure)
              (String.concat " -> " (List.map Path.show u.way)))
          found;
      flush stderr;
      raise (Stop 1)

let catching f = try f () with Stop status -> status

(* [truss run]: a development build, unless [release], run on this
   terminal with the arguments. A [todo] is refused even here, since
   reaching one would be a failure its signature does not show; [echo]
   writes to standard error, except in a release build, which refuses it
   as [truss build] does. *)
let run ~directory ~release ~sanitize ~arguments =
  catching (fun () ->
      let project = Project.load directory in
      stop_at_diagnostics ~json:false project;
      let main = main project in
      let compile = Compiler.create ~sanitize project (if release then Release else Development) in
      refuse_unshippable ~json:false ~echo:release project compile main;
      let output = Filename.temp_file "truss-run-" "" in
      Fun.protect
        ~finally:(fun () -> try Sys.remove output with Sys_error _ -> ())
        (fun () ->
          match Compile.build_program compile ~main ~output with
          | Error message -> Project.cannot_run "%s" message
          | Ok () -> Toolchain.run_attached output arguments))

(* [truss build]: a release build at [output], or else at a file named after
   the package in the current directory. *)
let build ~directory ~output ~json =
  catching (fun () ->
      let project = Project.load directory in
      stop_at_diagnostics ~json project;
      let main = main project in
      let compile = Compiler.create project Release in
      refuse_unshippable ~json ~echo:true project compile main;
      let output = Project.normalize (Option.value output ~default:project.manifest.name) in
      match Compile.build_program compile ~main ~output with
      | Error message -> Project.cannot_run "%s" message
      | Ok () ->
          if json then
            Json.print
              (Json.document ~diagnostics:[] [ ("output", Json.String (Project.shown output)) ])
          else Printf.printf "Built %s.\n%!" (Project.shown output);
          0)
