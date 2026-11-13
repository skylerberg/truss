(* The [truss] command line: its commands and arguments, and the process
   that runs each command.

   A command that reads code runs in the process that holds its worktree's
   session: the background process, which keeps sessions between commands
   and starts when a command first needs it, or with [--no-server] or
   [TRUSS_NO_SERVER=1], the client's own process. Both run the same code to
   parse the arguments and run the command, so the result is the same. *)

open Cmdliner

(* The options of every command, which apply before it runs: [-C] changes
   to a directory, as in git, and [--json] selects JSON output. *)
let common =
  let directory =
    Arg.(
      value & opt dir "."
      & info [ "C" ] ~docv:"DIRECTORY"
          ~doc:"Run as if from $(docv): find the packages and resolve paths from there.")
  and json =
    Arg.(
      value & flag
      & info [ "json" ]
          ~doc:
            "Write one JSON document to standard output instead of the report for people, with \
             every diagnostic and the command's own fields.")
  in
  Term.(
    const (fun directory json ->
        Sys.chdir directory;
        Output.set_json json)
    $ directory $ json)

let paths items =
  Arg.(
    value & pos_all string []
    & info [] ~docv:"FILE_OR_DIRECTORY"
        ~doc:("Select only the " ^ items ^ " in these files and directories."))

let exits =
  [
    Cmd.Exit.info 0 ~doc:"when the command succeeded and the code has no error.";
    Cmd.Exit.info 1
      ~doc:
        "when the code has an error: a diagnostic, a test that did not pass, or a rejected build.";
    Cmd.Exit.info 2 ~doc:"when the command could not run.";
  ]

let command name ~doc ?(man = []) term = Cmd.v (Cmd.info name ~doc ~man ~exits) term

let check =
  let fix =
    Arg.(
      value & flag
      & info [ "fix" ]
          ~doc:
            "Apply every fix that is its diagnostic's only fix, check again, and repeat until no \
             such fix remains, then report the remaining diagnostics.")
  in
  let no_proofs =
    Arg.(
      value & flag
      & info [ "no-proofs" ]
          ~doc:"Skip the prover: report every other diagnostic, without the pinned solver.")
  in
  command "check"
    ~doc:"Report every diagnostic of the packages and of the project's packages they depend on."
    Term.(
      const (fun () fix no_proofs -> Outcome.Exit (Check_command.run ~fix ~proofs:(not no_proofs)))
      $ common $ fix $ no_proofs)

let test =
  let match_ =
    Arg.(
      value
      & opt (some string) None
      & info [ "match" ] ~docv:"TEXT" ~doc:"Run only the tests whose names contain $(docv).")
  in
  let timings =
    Arg.(
      value & flag
      & info [ "timings" ]
          ~doc:
            "After the report, list every selected test with its duration, slowest first. A cached \
             test shows the duration from the run that produced its result.")
  in
  let rerun =
    Arg.(
      value & flag
      & info [ "rerun" ]
          ~doc:"Run every selected test without reading cached results, and cache the new ones.")
  in
  command "test" ~doc:"Check the packages, then run the tests without a cached result."
    Term.(
      const (fun () paths match_ timings rerun ->
          Outcome.Exit (Test_command.run ~paths ~match_ ~timings ~rerun))
      $ common $ paths "tests" $ match_ $ timings $ rerun)

let release_flag doc = Arg.(value & flag & info [ "release" ] ~doc)

let run =
  let arguments =
    Arg.(value & pos_all string [] & info [] ~docv:"ARGUMENT" ~doc:"The program's arguments.")
  in
  command "run"
    ~doc:"Check the package, build its program for development, and run it with the arguments."
    ~man:
      [
        `S Manpage.s_description;
        `P
          "The first argument that is not an option starts the program's arguments, and $(b,--) \
           marks the start when the first one begins with $(b,-).";
      ]
    Term.(
      const (fun () release arguments -> Program_command.run ~release ~arguments)
      $ common
      $ release_flag "Build as $(b,truss build) does, then run the program."
      $ arguments)

let build =
  let output =
    Arg.(
      value
      & opt (some string) None
      & info [ "o"; "output" ] ~docv:"PATH"
          ~doc:
            "Write the program to $(docv) instead of a file named after the package in the current \
             directory.")
  in
  command "build"
    ~doc:
      "Check the package and build its program for release, rejecting a program whose $(b,main) \
       reaches a $(b,todo) or an $(b,echo)."
    Term.(const (fun () output -> Program_command.build ~output) $ common $ output)

let holes =
  command "holes"
    ~doc:
      "List every $(b,todo) with its expected type, the bindings in scope, and the tests and \
       $(b,main) that reach it."
    Term.(const (fun () paths -> Outcome.Exit (Holes_command.run ~paths)) $ common $ paths "holes")

let show =
  let paths =
    Arg.(
      non_empty & pos_all string []
      & info [] ~docv:"PATH"
          ~doc:
            "A package, module, type, definition, or method, such as $(b,weather), \
             $(b,weather::forecast), $(b,weather::forecast::parse), or \
             $(b,weather::forecast::Forecast.summary).")
  in
  let body = Arg.(value & flag & info [ "body" ] ~doc:"Print whole definitions.") in
  command "show" ~doc:"Print the signatures of a package, module, type, or definition."
    Term.(
      const (fun () paths body -> Outcome.Exit (Show_command.run ~paths ~body))
      $ common $ paths $ body)

let impact =
  let base =
    Arg.(
      value
      & opt (some string) None
      & info [ "base" ] ~docv:"REVISION"
          ~doc:"Compare with the commit $(docv) instead of the merge base with the default branch.")
  in
  command "impact"
    ~doc:"List the definitions that the worktree changes since a base commit, and their dependents."
    Term.(const (fun () base -> Outcome.Exit (Impact_command.run ~base)) $ common $ base)

let name_argument =
  Arg.(
    required
    & pos 0 (some string) None
    & info [] ~docv:"NAME"
        ~doc:
          "A definition: its full path, or a suffix of one, such as $(b,parse) or \
           $(b,Forecast.summary).")

let references =
  command "references" ~doc:"List the dependents of a definition, by part."
    Term.(
      const (fun () name -> Outcome.Exit (Graph_command.run ~direction:References ~name))
      $ common $ name_argument)

let dependencies =
  command "dependencies" ~doc:"List the dependencies of a definition, by part."
    Term.(
      const (fun () name -> Outcome.Exit (Graph_command.run ~direction:Dependencies ~name))
      $ common $ name_argument)

let explain =
  let position =
    Arg.(
      required
      & pos 0 (some string) None
      & info [] ~docv:"FILE:LINE:COLUMN" ~doc:"A position, written as diagnostics write it.")
  in
  command "explain"
    ~doc:
      "Describe the name or expression at a position: its meaning, its type, and the signature of \
       its definition."
    Term.(
      const (fun () position -> Outcome.Exit (Explain_command.run ~position)) $ common $ position)

let overlap =
  let with_ =
    Arg.(
      value
      & opt (some string) None
      & info [ "with" ] ~docv:"BRANCH"
          ~doc:"Compare with $(docv) instead of the other open worktrees.")
  in
  let merge =
    Arg.(
      value & flag
      & info [ "merge" ] ~doc:"Also check the merge result and list the diagnostics only it has.")
  in
  command "overlap"
    ~doc:"List where this worktree's changes overlap those of other worktrees or of a branch."
    Term.(
      const (fun () with_ merge -> Outcome.Exit (Overlap_command.run ~with_ ~merge))
      $ common $ with_ $ merge)

let rename =
  let from_ = Arg.(required & pos 0 (some string) None & info [] ~docv:"FROM") in
  let to_ = Arg.(required & pos 1 (some string) None & info [] ~docv:"TO") in
  command "rename"
    ~doc:
      "Rename a definition, method, or module, and every reference to it in the project's packages."
    Term.(
      const (fun () from_ to_ -> Outcome.Exit (Rename_command.run ~from_ ~to_))
      $ common $ from_ $ to_)

let packages_argument ~doc = Arg.(value & pos_all string [] & info [] ~docv:"PACKAGE" ~doc)

let add =
  command "add"
    ~doc:
      "Add registry packages as dependencies of the package, each granted nothing, at the version \
       written after $(b,@) or the newest."
    Term.(
      const (fun () names -> Outcome.Exit (Add_command.run ~names))
      $ common
      $ packages_argument
          ~doc:"A package, such as $(b,acme::geometry) or $(b,acme::geometry@1.4.2).")

let upgrade =
  command "upgrade"
    ~doc:
      "Change the project's registry packages, or only the named ones, to their newest versions or \
       the version written after $(b,@), and report the effect."
    Term.(
      const (fun () names -> Outcome.Exit (Upgrade_command.run ~names))
      $ common
      $ packages_argument
          ~doc:"A package, such as $(b,acme::geometry) or $(b,acme::geometry@1.4.2).")

let publish =
  command "publish"
    ~doc:
      "Publish the package to the registry as its next version, if it is complete and compatible \
       with its previous version."
    Term.(const (fun () -> Outcome.Exit (Publish_command.run ())) $ common)

let new_ =
  let name = Arg.(required & pos 0 (some string) None & info [] ~docv:"NAME") in
  command "new" ~doc:"Create a package in a directory named $(i,NAME)."
    Term.(const (fun () name -> Outcome.Exit (New_command.run ~name)) $ common $ name)

let sync =
  command "sync" ~doc:"Update the project's session from its files, and do nothing else."
    Term.(
      const (fun () ->
          ignore (Command_packages.current ());
          Outcome.Exit 0)
      $ common)

let status =
  command "status" ~doc:"List the background process's sessions."
    Term.(
      const (fun () ->
          List.iter
            (fun (name, nodes) -> Output.printf "%s: %d results\n" name nodes)
            (Database.sessions ());
          Outcome.Exit 0)
      $ common)

let stop =
  command "stop" ~doc:"Stop the background process."
    Term.(
      const (fun () ->
          Database.stop ();
          Outcome.Exit 0)
      $ common)

let clean =
  command "clean" ~doc:"Stop the background process and delete the store, which costs only time."
    Term.(const (fun () -> Outcome.Exit 0) $ common)

(* The help of [truss lsp]. The client runs the language server itself,
   since the server reads standard input for as long as the editor is
   open. *)
let lsp =
  command "lsp"
    ~doc:
      "Run the language server on standard input and output, for an editor. It reports each open \
       file's diagnostics, the prover's included, and the state of each obligation."
    Term.(const (fun () -> Outcome.Exit 2) $ common)

let version =
  Printf.sprintf "stage0 (Truss %s, code generation %d, Unicode %s)" Manifest.truss_version
    Lir.version Unicode.version

let truss =
  Cmd.group
    (Cmd.info "truss" ~version ~exits
       ~man:
         [
           `S Manpage.s_environment;
           `P
             "$(b,TRUSS_NO_SERVER=1), or $(b,--no-server) before or after the command, runs the \
              command in its own process, and not in the background process.";
         ]
       ~doc:"Check, test, build, and change Truss code.")
    [
      check;
      test;
      run;
      build;
      holes;
      show;
      impact;
      references;
      dependencies;
      explain;
      overlap;
      rename;
      add;
      upgrade;
      publish;
      new_;
      sync;
      status;
      stop;
      clean;
      lsp;
    ]

(* Parses the arguments and runs the command, writing to [Output]'s current
   streams. Code with errors exits with 1, after its report. A command that
   cannot run, or a compiler bug, exits with 2; the bug's message names the
   compiler's step when it failed. The command's sessions and the store are
   saved when it ends, so another process can reuse their results. *)
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
          Cmd.eval_value ~help ~err ~catch:false ~argv:(Array.of_list ("truss" :: arguments)) truss
        with
        | Ok (`Ok outcome) -> outcome
        | Ok (`Version | `Help) -> Outcome.Exit 0
        | Error (`Parse | `Term | `Exn) -> Outcome.Exit 2)
  in
  let outcome =
    match
      Compiler_bug.while_doing ~stage:"Command"
        ("running `truss " ^ String.concat " " arguments ^ "`")
        run
    with
    | outcome -> outcome
    | exception Outcome.Stop status -> Outcome.Exit status
    | exception Report.Errors report ->
        if Output.json () then Json.print (Report.document report []) else Report.print report;
        Outcome.Exit 1
    | exception Outcome.Cannot_run message ->
        Output.eprint_line message;
        Outcome.Exit 2
    | exception Compiler_bug.Bug bug ->
        Output.eprint_line
          ("The compiler has a bug, and cannot continue. Please report it.\n  "
         ^ Compiler_bug.to_string bug);
        Outcome.Exit 2
  in
  Format.pp_print_flush help ();
  Format.pp_print_flush err ();
  Output.print (Buffer.contents buffer_out);
  Output.eprint (Buffer.contents buffer_err);
  Database.save_opened ();
  outcome

(* Runs a command line from [directory], or else from the current directory,
   which it is in again afterwards. If another process evicted an input of a
   session that the command reads, the command runs again from the files. A
   system failure, such as an unreadable file, exits with 2. *)
let run_command_line ?(directory = Sys.getcwd ()) arguments =
  let previous = Sys.getcwd () in
  Fun.protect
    ~finally:(fun () -> try Sys.chdir previous with Sys_error _ -> ())
    (fun () ->
      Sys.chdir directory;
      match Database.recovering (fun () -> evaluate arguments) with
      | outcome -> outcome
      | exception exception_ ->
          Output.eprintf "The compiler failed: %s\n" (Printexc.to_string exception_);
          Outcome.Exit 2)

(* The environment variables a command reads, which the background process
   is given from each client. [TRUSS_CACHE] is not among them: it names the
   store, and each store has its own background process. *)
let forwarded =
  [
    Registry.Index.variable;
    Toolchain.added_flags_variable;
    "TRUSS_CC";
    "TRUSS_KEEP_C";
    "TRUSS_Z3";
    "TRUSS_CACHE_SIZE";
    "TRUSS_WORKERS";
  ]

type request = {
  arguments : string list;
  directory : string;  (** The client's current directory *)
  environment : (string * string) list;
      (** The client's value of each forwarded variable, empty where it is not set *)
  terminal : bool;
  columns : int option;
}

type response = { output : string; outcome : Outcome.t }

(* The background process's response to a request: it runs the command
   from the client's directory and with the client's environment, as the
   client would, and sends standard error as progress, so it appears while
   the command runs. *)
let handle ~progress request =
  let buffer = Buffer.create 1024 in
  List.iter (fun (name, value) -> Unix.putenv name value) request.environment;
  let outcome =
    Output.with_
      {
        out = Buffer.add_string buffer;
        err = progress;
        terminal = request.terminal;
        columns = request.columns;
        json = false;
      }
      (fun () -> run_command_line ~directory:request.directory request.arguments)
  in
  { output = Buffer.contents buffer; outcome }

let serve key = Database.serve ~key ~handle

(* The command name: the first argument that is not an option. *)
let command_of arguments =
  List.find_opt (fun argument -> not (String.starts_with ~prefix:"-" argument)) arguments

let finish (outcome : Outcome.t) =
  match outcome with
  | Exit status -> status
  | Run_program { program; arguments } ->
      (* The program runs on the client's terminal, so it can prompt and read
         input. *)
      Fun.protect
        ~finally:(fun () -> try Sys.remove program with Sys_error _ -> ())
        (fun () -> Process.run_attached program arguments)

let request arguments =
  {
    arguments;
    directory = Sys.getcwd ();
    environment =
      List.map (fun name -> (name, Option.value (Sys.getenv_opt name) ~default:"")) forwarded;
    terminal = Output.terminal ();
    columns = Output.columns ();
  }

(* Asks each running background process, and starts none. *)
let ask_running arguments : (response, string) result list =
  List.map
    (fun key -> Database.call ~start_server:false ~key ~progress:Output.eprint (request arguments))
    (Database.servers ())

(* [truss clean]: stops every background process, since each holds the
   store open, and deletes the store. *)
let clean_store () =
  ignore (ask_running [ "stop" ]);
  Database.reset ();
  let directory = Database.store_directory () in
  match File_system.remove directory with
  | () -> 0
  | exception Unix.Unix_error (error, _, _) ->
      Output.eprintf "Cannot delete %s: %s\n" directory (Unix.error_message error);
      2

(* The command line's directory: the directory that [-C] names, relative to
   the current directory, or else the current directory. Its project's
   background process answers the command. *)
let directory_of arguments =
  let rec named = function
    | "-C" :: directory :: _ -> Some directory
    | option :: _ when String.length option > 2 && String.starts_with ~prefix:"-C" option ->
        Some (String.sub option 2 (String.length option - 2))
    | _ :: rest -> named rest
    | [] -> None
  in
  match named arguments with
  | Some directory when Filename.is_relative directory -> Filename.concat (Sys.getcwd ()) directory
  | Some directory -> directory
  | None -> Sys.getcwd ()

(* [truss lsp]: runs the language server in the client's process. It checks
   the open files in the process where every other command runs. *)
let language_server ~no_server =
  let check ~root encoding buffers =
    let request =
      { (request (Lsp_command.check_arguments ~root encoding buffers)) with directory = root }
    in
    let response =
      if no_server then Ok (handle ~progress:ignore request)
      else Database.call ~key:(Database.server_key root) ~progress:ignore request
    in
    match response with Ok { output; outcome = Exit 0 } -> Some output | Ok _ | Error _ -> None
  in
  Lsp_command.serve ~input:stdin ~output:stdout ~check

(* Runs a command line as the client: the command in its own process, or
   in the background process. *)
let client argv =
  let arguments = List.tl (Arguments.prepare argv) in
  let no_server = List.mem "--no-server" arguments || Sys.getenv_opt "TRUSS_NO_SERVER" = Some "1" in
  let arguments = List.filter (( <> ) "--no-server") arguments in
  let local () = finish (run_command_line arguments) in
  match command_of arguments with
  | Some "clean" -> clean_store ()
  | Some "lsp" -> language_server ~no_server
  | None | Some "new" -> local ()
  | _ when no_server -> local ()
  | Some ("status" | "stop") -> (
      match ask_running arguments with
      | [] ->
          Output.eprint_line "No background process is running.";
          0
      | answers ->
          List.fold_left
            (fun status answer ->
              match answer with
              | Ok response ->
                  Output.print response.output;
                  max status (finish response.outcome)
              | Error message ->
                  Output.eprint_line message;
                  status)
            0 answers)
  | Some _ -> (
      match
        (Database.call
           ~key:(Database.server_key (directory_of arguments))
           ~progress:Output.eprint (request arguments)
          : (response, string) result)
      with
      | Ok response ->
          Output.print response.output;
          finish response.outcome
      | Error message ->
          Output.eprint_line message;
          2)

module For_testing = struct
  let run_command_line = run_command_line
end
