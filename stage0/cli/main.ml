(* The [truss] command line: its commands and arguments, and where each
   command runs.

   A command that reads code runs where its worktree's session is: in the
   background process, which keeps sessions between commands and starts
   when a command first needs it, or, with [--no-server] or
   [TRUSS_NO_SERVER=1], in the command's own process. Either way the same
   code below parses the arguments and runs the command, so the answer is
   the same. *)

open Cmdliner

let directory =
  Arg.(
    value & opt dir "."
    & info [ "C" ] ~docv:"DIRECTORY"
        ~doc:"Run as if from $(docv): find the packages from there, and read paths from there.")

let json =
  Arg.(
    value & flag
    & info [ "json" ]
        ~doc:
          "Write one JSON document to standard output in place of the report for people, with \
           every diagnostic and the command's own fields.")

let paths what =
  Arg.(
    value & pos_all string []
    & info [] ~docv:"FILE_OR_DIRECTORY"
        ~doc:("Look only at the " ^ what ^ " in these files and directories."))

(* Hidden from the commands' help: for testing the compiler. *)
let sanitize =
  Arg.(
    value & flag
    & info [ "sanitize" ] ~docs:Manpage.s_none
        ~doc:
          "Build with AddressSanitizer and UndefinedBehaviorSanitizer, and keep no test results. A \
           report from either is a bug in the compiler.")

let exits =
  [
    Cmd.Exit.info 0 ~doc:"when the command did what was asked and the code had no problem.";
    Cmd.Exit.info 1
      ~doc:"when the code has a problem: a diagnostic, a test that did not pass, a refused build.";
    Cmd.Exit.info 2 ~doc:"when the command could not do its job.";
  ]

let command name ~doc ?(man = []) term = Cmd.v (Cmd.info name ~doc ~man ~exits) term

let check =
  let fix =
    Arg.(
      value & flag
      & info [ "fix" ]
          ~doc:
            "Apply every fix that is the only fix its diagnostic offers, check again, and repeat \
             until none is left, then report what remains.")
  in
  let no_proofs =
    Arg.(
      value & flag
      & info [ "no-proofs" ]
          ~doc:
            "Report every diagnostic but the prover's, so the pinned solver is not needed. Only \
             the packages' own files are checked: a dependency is checked only for the proofs that \
             the program relies on.")
  in
  command "check" ~doc:"Report every diagnostic in the packages."
    Term.(
      const (fun directory fix no_proofs json ->
          Outcome.Exit (Check_command.run ~directory ~fix ~proofs:(not no_proofs) ~json))
      $ directory $ fix $ no_proofs $ json)

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
            "After the report, list every test with how long it took, slowest first. A cached test \
             shows the time of the run that kept its result.")
  in
  let rerun =
    Arg.(
      value & flag
      & info [ "rerun" ] ~doc:"Run every selected test, using no kept results, and keep new ones.")
  in
  command "test" ~doc:"Check the packages, then run the tests whose results are not kept."
    Term.(
      const (fun directory paths match_ timings rerun json sanitize ->
          Outcome.Exit (Test_command.run ~directory ~paths ~match_ ~timings ~rerun ~json ~sanitize))
      $ directory $ paths "tests" $ match_ $ timings $ rerun $ json $ sanitize)

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
      const (fun directory release sanitize arguments ->
          Program_command.run ~directory ~release ~sanitize ~arguments)
      $ directory
      $ release_flag "Build as $(b,truss build) does, refusing an $(b,echo) as it does."
      $ sanitize $ arguments)

let build =
  let output =
    Arg.(
      value
      & opt (some string) None
      & info [ "o"; "output" ] ~docv:"PATH"
          ~doc:"Write the program to $(docv), and not to a file named after the package here.")
  in
  command "build"
    ~doc:
      "Check the package and build its program for release, refusing any $(b,todo) or $(b,echo) \
       its $(b,main) can reach."
    Term.(
      const (fun directory output json -> Program_command.build ~directory ~output ~json)
      $ directory $ output $ json)

let holes =
  command "holes"
    ~doc:"List every $(b,todo), with its type, the names in scope, and what it blocks."
    Term.(
      const (fun directory paths json -> Outcome.Exit (Holes_command.run ~directory ~paths ~json))
      $ directory $ paths "holes" $ json)

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
      const (fun directory paths body json ->
          Outcome.Exit (Show_command.run ~directory ~paths ~body ~json))
      $ directory $ paths $ body $ json)

let impact =
  let base =
    Arg.(
      value
      & opt (some string) None
      & info [ "base" ] ~docv:"REVISION"
          ~doc:
            "Compare with the commit $(docv) names, and not with where this branch left the \
             default branch.")
  in
  command "impact"
    ~doc:
      "List the definitions the worktree's changes from a base commit modify, and their dependents."
    Term.(
      const (fun directory base json -> Outcome.Exit (Impact_command.run ~directory ~base ~json))
      $ directory $ base $ json)

let name_argument =
  Arg.(
    required
    & pos 0 (some string) None
    & info [] ~docv:"NAME"
        ~doc:
          "A definition: its full path, or the end of one, such as $(b,parse) or \
           $(b,Forecast.summary).")

let references =
  command "references" ~doc:"List what reads a definition, part by part."
    Term.(
      const (fun directory name json ->
          Outcome.Exit (Graph_command.run ~directory ~direction:References ~name ~json))
      $ directory $ name_argument $ json)

let dependencies =
  command "dependencies" ~doc:"List what a definition reads, part by part."
    Term.(
      const (fun directory name json ->
          Outcome.Exit (Graph_command.run ~directory ~direction:Dependencies ~name ~json))
      $ directory $ name_argument $ json)

let explain =
  let position =
    Arg.(
      required
      & pos 0 (some string) None
      & info [] ~docv:"FILE:LINE:COLUMN" ~doc:"A position, as diagnostics give them.")
  in
  command "explain"
    ~doc:"Say what is at a position: what a name means, its type, and the signature it refers to."
    Term.(
      const (fun directory position json ->
          Outcome.Exit (Explain_command.run ~directory ~position ~json))
      $ directory $ position $ json)

let overlap =
  let with_ =
    Arg.(
      value
      & opt (some string) None
      & info [ "with" ] ~docv:"BRANCH"
          ~doc:"Compare with $(docv), and not with the other open worktrees.")
  in
  let merge =
    Arg.(
      value & flag
      & info [ "merge" ] ~doc:"Also list the errors a merge of the two would have that neither has.")
  in
  command "overlap"
    ~doc:"List where this worktree's changes meet those of other worktrees, or of a branch."
    Term.(
      const (fun directory with_ merge json ->
          Outcome.Exit (Overlap_command.run ~directory ~with_ ~merge ~json))
      $ directory $ with_ $ merge $ json)

let rename =
  let from_ = Arg.(required & pos 0 (some string) None & info [] ~docv:"FROM") in
  let to_ = Arg.(required & pos 1 (some string) None & info [] ~docv:"TO") in
  command "rename"
    ~doc:
      "Rename a definition, method, or module, and every reference to it in the project's packages."
    Term.(
      const (fun directory from_ to_ json ->
          Outcome.Exit (Rename_command.run ~directory ~from_ ~to_ ~json))
      $ directory $ from_ $ to_ $ json)

let packages_argument ~doc = Arg.(value & pos_all string [] & info [] ~docv:"PACKAGE" ~doc)

let add =
  command "add"
    ~doc:
      "Make registry packages dependencies of the package, each granted nothing, at the version \
       written after $(b,@), or at its newest."
    Term.(
      const (fun directory names json -> Outcome.Exit (Add_command.run ~directory ~names ~json))
      $ directory
      $ packages_argument
          ~doc:"A package, such as $(b,acme::geometry) or $(b,acme::geometry@1.4.2)."
      $ json)

let upgrade =
  command "upgrade"
    ~doc:
      "Move the project's registry packages to their newest versions, or the packages named to \
       theirs or to the version written after $(b,@), and say what that changes."
    Term.(
      const (fun directory names json -> Outcome.Exit (Upgrade_command.run ~directory ~names ~json))
      $ directory
      $ packages_argument
          ~doc:"A package, such as $(b,acme::geometry) or $(b,acme::geometry@1.4.2)."
      $ json)

let publish =
  command "publish"
    ~doc:
      "Add the package to the registry as its next version, once it is finished and breaks nothing \
       its last version offers."
    Term.(
      const (fun directory json -> Outcome.Exit (Publish_command.run ~directory ~json))
      $ directory $ json)

let new_ =
  let name = Arg.(required & pos 0 (some string) None & info [] ~docv:"NAME") in
  command "new" ~doc:"Make a new package in a directory named $(i,NAME)."
    Term.(
      const (fun directory name -> Outcome.Exit (New_command.run ~directory ~name))
      $ directory $ name)

let sync =
  command "sync"
    ~doc:"Bring the project's session up to date with its files, and do nothing else."
    Term.(
      const (fun directory ->
          ignore (Project.load directory);
          Outcome.Exit 0)
      $ directory)

let status =
  command "status" ~doc:"List the background process's sessions."
    Term.(
      const (fun () ->
          List.iter
            (fun (name, nodes) -> Output.printf "%s: %d results\n" name nodes)
            (Database.sessions ());
          Outcome.Exit 0)
      $ const ())

let stop =
  command "stop" ~doc:"Stop the background process."
    Term.(
      const (fun () ->
          Database.stop ();
          Outcome.Exit 0)
      $ const ())

let clean =
  command "clean" ~doc:"Stop the background process and delete the store, which costs only time."
    Term.(const (fun () -> Outcome.Exit 0) $ const ())

(* The client runs the language server itself, since it reads standard
   input for as long as the editor is open; this is its help. *)
let lsp =
  command "lsp"
    ~doc:
      "Run the language server on standard input and output, for an editor: each open file's \
       diagnostics, with its proofs', and the state of each of its obligations."
    Term.(const (fun () -> Outcome.Exit 2) $ const ())

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

(* Parses the arguments and runs the command, writing as [Output] says. A
   reason the command cannot run, or a compiler bug with its context,
   gives status 2. *)
let evaluate arguments =
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
    | exception Project.Cannot_run message ->
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
  (* The command's results are saved for other processes. *)
  List.iter Database.save_session !Project.opened;
  Project.opened := [];
  outcome

(* Runs a command line, once more from the files if another process
   collected a state it read. A failure of the machine, such as a file that
   cannot be read, gives status 2. *)
let run_command_line arguments =
  match Database.recovering (fun () -> evaluate arguments) with
  | outcome -> outcome
  | exception exception_ ->
      Output.eprintf "The compiler failed: %s\n" (Printexc.to_string exception_);
      Outcome.Exit 2

type request = {
  arguments : string list;
  directory : string;  (** The client's current directory *)
  registry : string option;  (** The registry the client's environment names *)
  terminal : bool;
  columns : int option;
}

type response = { output : string; outcome : Outcome.t }

(* The background process's answer to a request: the command run as the
   client would have run it, from its directory, with its errors sent as
   progress so they show while it works. *)
let handle ~progress request =
  let buffer = Buffer.create 1024 in
  let previous = Sys.getcwd () in
  let outcome =
    Fun.protect
      ~finally:(fun () -> try Sys.chdir previous with Sys_error _ -> ())
      (fun () ->
        Sys.chdir request.directory;
        Registry.Index.configure request.registry;
        Output.with_
          {
            out = Buffer.add_string buffer;
            err = progress;
            terminal = request.terminal;
            columns = request.columns;
          }
          (fun () -> run_command_line request.arguments))
  in
  { output = Buffer.contents buffer; outcome }

let serve key = Database.serve ~key ~handle

(* The command's first word, and whether it is one that runs no code of a
   worktree, which the client runs itself. *)
let command_of arguments = List.find_opt (fun a -> not (String.starts_with ~prefix:"-" a)) arguments

let finish (outcome : Outcome.t) =
  match outcome with
  | Exit status -> status
  | Run_program { program; arguments } ->
      (* The program runs on this terminal, so it can prompt and read. *)
      Fun.protect
        ~finally:(fun () -> try Sys.remove program with Sys_error _ -> ())
        (fun () -> Process.run_attached program arguments)

let request arguments =
  {
    arguments;
    directory = Sys.getcwd ();
    registry = Sys.getenv_opt Registry.Index.variable;
    terminal = Output.terminal ();
    columns = Output.columns ();
  }

(* Asks each running background process, without starting one. *)
let ask_running arguments : (response, string) result list =
  List.map
    (fun key -> Database.call ~start_server:false ~key ~progress:Output.eprint (request arguments))
    (Database.servers ())

(* [truss clean]: stops every background process, each of which holds the
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

(* The directory a command line is about: what [-C] names, from the current
   directory, or the current directory. Its project's background process is
   the one that answers. *)
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

(* [truss lsp]: the language server, in the client's process, which checks
   the open files where every other command runs. *)
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
