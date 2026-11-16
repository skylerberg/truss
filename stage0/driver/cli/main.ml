let common =
  let directory =
    Cmdliner.Arg.(
      value & opt dir "."
      & info [ "C" ] ~docv:"DIRECTORY"
          ~doc:"Run as if from $(docv): find the packages and resolve paths from there.")
  and json =
    Cmdliner.Arg.(
      value & flag
      & info [ "json" ]
          ~doc:
            "Write one JSON document to standard output instead of the report for people, with \
             every diagnostic and the command's own fields.")
  in
  Cmdliner.Term.(
    const (fun directory json ->
        Sys.chdir directory;
        Output.set_json json)
    $ directory $ json)

let make_paths_argument items =
  Cmdliner.Arg.(
    value & pos_all string []
    & info [] ~docv:"FILE_OR_DIRECTORY"
        ~doc:("Select only the " ^ items ^ " in these files and directories."))

let exits =
  [
    Cmdliner.Cmd.Exit.info 0 ~doc:"when the command succeeded and the code has no error.";
    Cmdliner.Cmd.Exit.info 1
      ~doc:
        "when the code has an error: a diagnostic, a test that did not pass, or a rejected build.";
    Cmdliner.Cmd.Exit.info 2 ~doc:"when the command could not run.";
  ]

let make_command name ~doc ?(man = []) term =
  Cmdliner.Cmd.v (Cmdliner.Cmd.info name ~doc ~man ~exits) term

let check =
  let fix =
    Cmdliner.Arg.(
      value & flag
      & info [ "fix" ]
          ~doc:
            "Apply every fix that is its diagnostic's only fix, check again, and repeat until no \
             such fix remains, then report the remaining diagnostics.")
  in
  let no_proofs =
    Cmdliner.Arg.(
      value & flag
      & info [ "no-proofs" ]
          ~doc:"Skip the prover: report every other diagnostic, without the pinned solver.")
  in
  make_command "check"
    ~doc:"Report every diagnostic of the packages and of the project's packages they depend on."
    Cmdliner.Term.(
      const (fun () fix no_proofs -> Outcome.Exit (Check_command.run ~fix ~proofs:(not no_proofs)))
      $ common $ fix $ no_proofs)

let test =
  let match_ =
    Cmdliner.Arg.(
      value
      & opt (some string) None
      & info [ "match" ] ~docv:"TEXT" ~doc:"Run only the tests whose names contain $(docv).")
  in
  let timings =
    Cmdliner.Arg.(
      value & flag
      & info [ "timings" ]
          ~doc:
            "After the report, list every selected test with its duration, slowest first. A cached \
             test shows the duration from the run that produced its result.")
  in
  let rerun =
    Cmdliner.Arg.(
      value & flag
      & info [ "rerun" ]
          ~doc:"Run every selected test without reading cached results, and cache the new ones.")
  in
  make_command "test" ~doc:"Check the packages, then run the tests without a cached result."
    Cmdliner.Term.(
      const (fun () paths match_ timings rerun ->
          Outcome.Exit (Test_command.run ~paths ~match_ ~timings ~rerun))
      $ common $ make_paths_argument "tests" $ match_ $ timings $ rerun)

let make_release_flag doc = Cmdliner.Arg.(value & flag & info [ "release" ] ~doc)

let run =
  let arguments =
    Cmdliner.Arg.(
      value & pos_all string [] & info [] ~docv:"ARGUMENT" ~doc:"The program's arguments.")
  in
  make_command "run"
    ~doc:"Check the package, build its program for development, and run it with the arguments."
    ~man:
      [
        `S Cmdliner.Manpage.s_description;
        `P
          "The first argument that is not an option starts the program's arguments, and $(b,--) \
           marks the start when the first one begins with $(b,-).";
      ]
    Cmdliner.Term.(
      const (fun () release arguments -> Program_command.run ~release ~arguments)
      $ common
      $ make_release_flag "Build as $(b,truss build) does, then run the program."
      $ arguments)

let build =
  let output =
    Cmdliner.Arg.(
      value
      & opt (some string) None
      & info [ "o"; "output" ] ~docv:"PATH"
          ~doc:
            "Write the program to $(docv) instead of a file named after the package in the current \
             directory.")
  in
  make_command "build"
    ~doc:
      "Check the package and build its program for release, rejecting a program whose $(b,main) \
       reaches a $(b,todo) or an $(b,echo)."
    Cmdliner.Term.(const (fun () output -> Program_command.build ~output) $ common $ output)

let holes =
  make_command "holes"
    ~doc:
      "List every $(b,todo) with its expected type, the bindings in scope, and the tests and \
       $(b,main) that reach it."
    Cmdliner.Term.(
      const (fun () paths -> Outcome.Exit (Holes_command.run ~paths))
      $ common $ make_paths_argument "holes")

let show =
  let paths =
    Cmdliner.Arg.(
      non_empty & pos_all string []
      & info [] ~docv:"PATH"
          ~doc:
            "A package, module, type, definition, or method, such as $(b,weather), \
             $(b,weather::forecast), $(b,weather::forecast::parse), or \
             $(b,weather::forecast::Forecast.summary).")
  in
  let body = Cmdliner.Arg.(value & flag & info [ "body" ] ~doc:"Print whole definitions.") in
  make_command "show" ~doc:"Print the signatures of a package, module, type, or definition."
    Cmdliner.Term.(
      const (fun () paths body -> Outcome.Exit (Show_command.run ~paths ~body))
      $ common $ paths $ body)

let explain =
  let position =
    Cmdliner.Arg.(
      required
      & pos 0 (some string) None
      & info [] ~docv:"FILE:LINE:COLUMN" ~doc:"A position, written as diagnostics write it.")
  in
  make_command "explain"
    ~doc:
      "Describe the name or expression at a position: its meaning, its type, and the signature of \
       its definition."
    Cmdliner.Term.(
      const (fun () position -> Outcome.Exit (Explain_command.run ~position)) $ common $ position)

let name_argument =
  Cmdliner.Arg.(
    required
    & pos 0 (some string) None
    & info [] ~docv:"NAME"
        ~doc:
          "A definition: its full path, or a suffix of one, such as $(b,parse) or \
           $(b,Forecast.summary).")

let dependents =
  make_command "dependents"
    ~doc:"List the parts of other definitions that read a part of a definition, by kind of part."
    Cmdliner.Term.(
      const (fun () name -> Outcome.Exit (Graph_command.run ~direction:Dependents ~name))
      $ common $ name_argument)

let dependencies =
  make_command "dependencies"
    ~doc:"List the parts of other definitions that a definition's parts read, by kind of part."
    Cmdliner.Term.(
      const (fun () name -> Outcome.Exit (Graph_command.run ~direction:Dependencies ~name))
      $ common $ name_argument)

let rename =
  let from_ = Cmdliner.Arg.(required & pos 0 (some string) None & info [] ~docv:"FROM") in
  let to_ = Cmdliner.Arg.(required & pos 1 (some string) None & info [] ~docv:"TO") in
  make_command "rename"
    ~doc:
      "Rename a definition, method, or module, and every reference to it in the project's packages."
    Cmdliner.Term.(
      const (fun () from_ to_ -> Outcome.Exit (Rename_command.run ~from_ ~to_))
      $ common $ from_ $ to_)

let make_packages_argument ~doc =
  Cmdliner.Arg.(value & pos_all string [] & info [] ~docv:"PACKAGE" ~doc)

let add =
  make_command "add"
    ~doc:
      "Add registry packages as dependencies of the package, each granted nothing, at the version \
       written after $(b,@) or the newest."
    Cmdliner.Term.(
      const (fun () names -> Outcome.Exit (Add_command.run ~names))
      $ common
      $ make_packages_argument
          ~doc:"A package, such as $(b,acme::geometry) or $(b,acme::geometry@1.4.2).")

let upgrade =
  make_command "upgrade"
    ~doc:
      "Change the project's registry packages, or only the named ones, to their newest versions or \
       the version written after $(b,@), and report the effect."
    Cmdliner.Term.(
      const (fun () names -> Outcome.Exit (Upgrade_command.run ~names))
      $ common
      $ make_packages_argument
          ~doc:"A package, such as $(b,acme::geometry) or $(b,acme::geometry@1.4.2).")

let publish =
  make_command "publish"
    ~doc:
      "Publish the package to the registry as its next version, if it is complete and compatible \
       with its previous version."
    Cmdliner.Term.(const (fun () -> Outcome.Exit (Publish_command.run ())) $ common)

let new_ =
  let name = Cmdliner.Arg.(required & pos 0 (some string) None & info [] ~docv:"NAME") in
  make_command "new" ~doc:"Create a package in a directory named $(i,NAME)."
    Cmdliner.Term.(const (fun () name -> Outcome.Exit (New_command.run ~name)) $ common $ name)

let status =
  make_command "status"
    ~doc:"List the package databases that the background processes of this build of truss hold."
    Cmdliner.Term.(
      const (fun () ->
          List.iter Output.print_line (Workspace.list_package_databases ());
          Outcome.Exit 0)
      $ common)

let stop =
  let all =
    Cmdliner.Arg.(
      value & flag
      & info [ "all" ] ~doc:"Stop the background processes of every project, not only this one.")
  in
  make_command "stop" ~doc:"Stop the background processes of every build of truss for the project."
    Cmdliner.Term.(
      const (fun all () ->
          let directory = Sys.getcwd () in
          match (all, Workspace.find_project_root directory) with
          | true, _ ->
              if not (Workspace.stop_servers ()) then
                Output.eprint_line "No background process is running.";
              Outcome.Exit 0
          | false, None ->
              Output.eprintf
                "No `truss.toml` in %s or any directory above it, so it is in no project. To stop \
                 the background processes of every project, use --all.\n"
                directory;
              Outcome.Exit 2
          | false, Some root ->
              if not (Workspace.stop_servers ~key:root ()) then
                Output.eprintf "No background process serves %s.\n" root;
              Outcome.Exit 0)
      $ all $ common)

let clean =
  make_command "clean"
    ~doc:
      "Stop the background processes of every project and every build of truss, then delete the \
       cache directory."
    ~man:
      [
        `S Cmdliner.Manpage.s_description;
        `P
          "The cache directory is $(b,TRUSS_CACHE), else $(b,XDG_CACHE_HOME)/truss, else \
           ~/.cache/truss.";
      ]
    Cmdliner.Term.(
      const (fun () ->
          ignore (Workspace.stop_servers ());
          Workspace.reset ();
          match Cache.locate_default_directory () with
          | Error message -> raise (Outcome.Cannot_run message)
          | Ok directory -> (
              match File_system.remove directory with
              | () -> Outcome.Exit 0
              | exception Unix.Unix_error (error, _, path) ->
                  Outcome.raise_cannot_run "Cannot delete %s: %s" path (Unix.error_message error)
              | exception Sys_error message -> Outcome.raise_cannot_run "Cannot delete %s" message))
      $ const ())

let database_counts_variable = "TRUSS_DATABASE_COUNTS"

let version =
  Printf.sprintf "stage0 (Truss %s, code generation %d, Unicode %s)" Manifest.truss_version
    Emit_c.version Unicode.version

let truss =
  Cmdliner.Cmd.group
    (Cmdliner.Cmd.info "truss" ~version ~exits
       ~man:
         [
           `S Cmdliner.Manpage.s_environment;
           `P
             "$(b,TRUSS_NO_SERVER=1), or $(b,--no-server) before or after the command, runs the \
              command in its own process, and not in the background process.";
           `P
             ("$(b," ^ database_counts_variable
            ^ "=1) writes a table to standard error after the command. The table has a row for \
               each kind of part that the database computed or wrote during the command. A row \
               counts the parts computed, the computed parts whose value came out unchanged, the \
               writes, the reads that the computations made, and the distinct parts that each \
               computation read. A write is a changed value or a removed part. A last row, \
               untracked, counts the reads that no part records: the command's own reads of the \
               database, and the reads that order the parts of a stage. The table omits the work \
               that the background process did before the command, such as propagating a saved \
               file.");
         ]
       ~doc:"Check, test, build, and change Truss code.")
    [
      check;
      test;
      run;
      build;
      holes;
      show;
      dependents;
      dependencies;
      explain;
      rename;
      add;
      upgrade;
      publish;
      new_;
      status;
      stop;
      clean;
    ]

let print_database_counts (counts : Database.counts list) =
  let total =
    List.fold_left
      (fun (total : Database.counts) (counts : Database.counts) ->
        {
          total with
          computed = total.computed + counts.computed;
          unchanged = total.unchanged + counts.unchanged;
          writes = total.writes + counts.writes;
          reads = total.reads + counts.reads;
          distinct_reads = total.distinct_reads + counts.distinct_reads;
        })
      { kind = "total"; computed = 0; unchanged = 0; writes = 0; reads = 0; distinct_reads = 0 }
      counts
  in
  let rows =
    List.map
      (fun (counts : Database.counts) ->
        ( counts.kind,
          List.map string_of_int
            [
              counts.computed; counts.unchanged; counts.writes; counts.reads; counts.distinct_reads;
            ] ))
      (counts @ [ total ])
  in
  let heading = ("kind", [ "computed"; "unchanged"; "writes"; "reads"; "distinct reads" ]) in
  let kind_width, cell_widths =
    List.fold_left
      (fun (kind_width, cell_widths) (kind, cells) ->
        ( max kind_width (String.length kind),
          List.map2 (fun width cell -> max width (String.length cell)) cell_widths cells ))
      (0, List.map (fun _ -> 0) (snd heading))
      (heading :: rows)
  in
  List.iter
    (fun (kind, cells) ->
      Output.eprint_line
        (String.concat "  "
           (Printf.sprintf "%-*s" kind_width kind
           :: List.map2 (fun width cell -> Printf.sprintf "%*s" width cell) cell_widths cells)))
    (heading :: rows)

let with_database_counts run =
  if Sys.getenv_opt database_counts_variable = Some "1" then begin
    let outcome, counts = Database.count run in
    print_database_counts counts;
    outcome
  end
  else run ()

let evaluate arguments =
  Output.set_json false;
  let buffer_out = Buffer.create 256 and buffer_err = Buffer.create 256 in
  let help = Format.formatter_of_buffer buffer_out
  and err = Format.formatter_of_buffer buffer_err in
  let run () =
    match arguments with
    | "__check-buffers" :: rest -> Outcome.Exit (Lsp_command.check_buffers rest)
    | _ -> (
        match
          Cmdliner.Cmd.eval_value ~help ~err ~catch:false
            ~argv:(Array.of_list ("truss" :: arguments))
            truss
        with
        | Ok (`Ok outcome) -> outcome
        | Ok (`Version | `Help) -> Outcome.Exit 0
        | Error (`Parse | `Term | `Exn) -> Outcome.Exit 2)
  in
  let outcome =
    with_database_counts (fun () ->
        match
          Compiler_bug.run_while_doing ~stage:"Command"
            ("running `truss " ^ String.concat " " arguments ^ "`")
            run
        with
        | outcome -> outcome
        | exception Outcome.Stop status -> Outcome.Exit status
        | exception Report.Errors report ->
            if Output.json () then Json.print (Report.make_document report [])
            else Report.print report;
            Outcome.Exit 1
        | exception (Outcome.Cannot_run message | Workspace.Unusable_cache message) ->
            Output.eprint_line message;
            Outcome.Exit 2
        | exception Compiler_bug.Bug bug ->
            Output.eprint_line
              ("The compiler has a bug, and cannot continue. Please report it.\n  "
             ^ Compiler_bug.to_string bug);
            Outcome.Exit 2)
  in
  Format.pp_print_flush help ();
  Format.pp_print_flush err ();
  Output.print (Buffer.contents buffer_out);
  Output.eprint (Buffer.contents buffer_err);
  outcome

let run_command_line ?(directory = Sys.getcwd ()) arguments =
  let previous = Sys.getcwd () in
  Fun.protect
    ~finally:(fun () -> try Sys.chdir previous with Sys_error _ -> ())
    (fun () ->
      Sys.chdir directory;
      match evaluate arguments with
      | outcome -> outcome
      | exception exception_ ->
          Output.eprintf "The compiler failed: %s\n" (Printexc.to_string exception_);
          Outcome.Exit 2)

let forwarded =
  [
    Registry.Index.variable;
    Toolchain.added_flags_variable;
    "TRUSS_CC";
    "TRUSS_KEEP_C";
    "TRUSS_Z3";
    "TRUSS_CACHE_SIZE";
    "TRUSS_WORKERS";
    database_counts_variable;
  ]

type request = {
  arguments : string list;
  directory : string;
  environment : (string * string) list;
  terminal : bool;
  columns : int option;
}

type response = { output : string; outcome : Outcome.t }

let handle ~report_progress request =
  let buffer = Buffer.create 1024 in
  List.iter (fun (name, value) -> Unix.putenv name value) request.environment;
  let outcome =
    Output.with_
      {
        print_out = Buffer.add_string buffer;
        print_err = report_progress;
        terminal = request.terminal;
        columns = request.columns;
        json = false;
      }
      (fun () -> run_command_line ~directory:request.directory request.arguments)
  in
  { output = Buffer.contents buffer; outcome }

let serve key = Workspace.serve ~key ~handle

let find_command arguments =
  List.find_opt (fun argument -> not (String.starts_with ~prefix:"-" argument)) arguments

let finish (outcome : Outcome.t) =
  match outcome with
  | Exit status -> status
  | Run_program { program; arguments } ->
      Fun.protect
        ~finally:(fun () -> try Sys.remove program with Sys_error _ -> ())
        (fun () -> Process.run_attached program arguments)

let make_request arguments =
  {
    arguments;
    directory = Sys.getcwd ();
    environment =
      List.map (fun name -> (name, Option.value (Sys.getenv_opt name) ~default:"")) forwarded;
    terminal = Output.terminal ();
    columns = Output.columns ();
  }

let locate_directory arguments =
  let rec find_name = function
    | "-C" :: directory :: _ -> Some directory
    | option :: _ when String.length option > 2 && String.starts_with ~prefix:"-C" option ->
        Some (String.drop_first 2 option)
    | _ :: rest -> find_name rest
    | [] -> None
  in
  match find_name arguments with
  | Some directory when Filename.is_relative directory -> Filename.concat (Sys.getcwd ()) directory
  | Some directory -> directory
  | None -> Sys.getcwd ()

let run_language_server ~no_server =
  let check ~root encoding buffers =
    let request =
      { (make_request (Lsp_command.check_arguments ~root encoding buffers)) with directory = root }
    in
    let response =
      match Workspace.find_project_root root with
      | Some project_root when not no_server ->
          Workspace.call ~key:project_root ~report_progress:ignore request
      | Some _ | None ->
          let response = handle ~report_progress:ignore request in
          Workspace.flush ();
          Ok response
    in
    match response with Ok { output; outcome = Exit 0 } -> Some output | Ok _ | Error _ -> None
  in
  Lsp_command.serve ~input:stdin ~output:stdout ~check

let run_client argv =
  let arguments = List.tl (Arguments.prepare argv) in
  let no_server = List.mem "--no-server" arguments || Sys.getenv_opt "TRUSS_NO_SERVER" = Some "1" in
  let arguments = List.filter (( <> ) "--no-server") arguments in
  let run_locally () =
    let outcome = run_command_line arguments in
    Workspace.flush ();
    finish outcome
  in
  match find_command arguments with
  | Some "lsp" -> run_language_server ~no_server
  | None | Some ("new" | "stop" | "clean") -> run_locally ()
  | _ when no_server -> run_locally ()
  | Some "status" -> (
      match Workspace.list_servers () with
      | [] ->
          Output.eprint_line "No background process of this build of truss is running.";
          0
      | keys ->
          List.fold_left
            (fun status key ->
              match
                (Workspace.call ~start_server:false ~key ~report_progress:Output.eprint
                   (make_request arguments)
                  : (response, string) result)
              with
              | Ok response ->
                  Output.print response.output;
                  max status (finish response.outcome)
              | Error message ->
                  Output.eprint_line message;
                  status)
            0 keys)
  | Some _ -> (
      match Workspace.find_project_root (locate_directory arguments) with
      | None -> run_locally ()
      | Some project_root -> (
          match
            (Workspace.call ~key:project_root ~report_progress:Output.eprint
               (make_request arguments)
              : (response, string) result)
          with
          | Ok response ->
              Output.print response.output;
              finish response.outcome
          | Error message ->
              Output.eprint_line message;
              2))

module For_testing = struct
  let run_command_line = run_command_line
end
