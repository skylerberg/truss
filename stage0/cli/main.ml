(* The [truss] command line: its commands and arguments, and where each
   command runs.

   A command that reads code runs where its worktree's session is: in the
   background process, which keeps sessions between commands and starts
   when a command first needs it, or, with [--no-server] or
   [TRUSS_NO_SERVER=1], in the command's own process. Either way the same
   code below parses the arguments and runs the command, so the answer is
   the same. *)

open Cmdliner

(* Runs a command, turning a reason it cannot run into status 2: one the
   command gives, or a bug in the compiler, reported with what the compiler
   was doing. *)
let guard f =
  try f () with
  | Project.Cannot_run message ->
      Output.eprint_line message;
      Outcome.Exit 2
  | Compiler_bug.Bug bug ->
      Output.eprint_line
        ("The compiler has a bug, and cannot go on. Please report it.\n  "
       ^ Compiler_bug.to_string bug);
      Outcome.Exit 2

let exit_with f = guard (fun () -> Outcome.Exit (f ()))

(* Options many commands share *)

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

(* The commands *)

let check =
  let fix =
    Arg.(
      value & flag
      & info [ "fix" ]
          ~doc:
            "Apply every fix that is the only fix its diagnostic offers, check again, and repeat \
             until none is left, then report what remains.")
  in
  command "check" ~doc:"Report every diagnostic in the packages."
    Term.(
      const (fun directory fix json ->
          exit_with (fun () -> Check_command.run ~directory ~fix ~json))
      $ directory $ fix $ json)

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
          exit_with (fun () ->
              Test_command.run ~directory ~paths ~match_ ~timings ~rerun ~json ~sanitize))
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
          guard (fun () -> Program_command.run ~directory ~release ~sanitize ~arguments))
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
      const (fun directory output json ->
          guard (fun () -> Program_command.build ~directory ~output ~json))
      $ directory $ output $ json)

let holes =
  command "holes"
    ~doc:"List every $(b,todo), with its type, the names in scope, and what it blocks."
    Term.(
      const (fun directory paths json ->
          exit_with (fun () -> Holes_command.run ~directory ~paths ~json))
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
          exit_with (fun () -> Show_command.run ~directory ~paths ~body ~json))
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
    ~doc:"List what the worktree's changes from a base commit change, and what they reach."
    Term.(
      const (fun directory base json ->
          exit_with (fun () -> Impact_command.run ~directory ~base ~json))
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
          exit_with (fun () -> Graph_command.run ~directory ~direction:References ~name ~json))
      $ directory $ name_argument $ json)

let dependencies =
  command "dependencies" ~doc:"List what a definition reads, part by part."
    Term.(
      const (fun directory name json ->
          exit_with (fun () -> Graph_command.run ~directory ~direction:Dependencies ~name ~json))
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
          exit_with (fun () -> Explain_command.run ~directory ~position ~json))
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
          exit_with (fun () -> Overlap_command.run ~directory ~with_ ~merge ~json))
      $ directory $ with_ $ merge $ json)

let rename =
  let from_ = Arg.(required & pos 0 (some string) None & info [] ~docv:"FROM") in
  let to_ = Arg.(required & pos 1 (some string) None & info [] ~docv:"TO") in
  command "rename"
    ~doc:
      "Rename a definition, method, or module, and every reference to it in the project's packages."
    Term.(
      const (fun directory from_ to_ json ->
          exit_with (fun () -> Rename_command.run ~directory ~from_ ~to_ ~json))
      $ directory $ from_ $ to_ $ json)

let packages_argument ~doc = Arg.(value & pos_all string [] & info [] ~docv:"PACKAGE" ~doc)

let add =
  command "add"
    ~doc:
      "Make registry packages dependencies of the package, each granted nothing, at the version \
       written after $(b,@), or at its newest."
    Term.(
      const (fun directory names json ->
          exit_with (fun () -> Add_command.run ~directory ~names ~json))
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
      const (fun directory names json ->
          exit_with (fun () -> Upgrade_command.run ~directory ~names ~json))
      $ directory
      $ packages_argument
          ~doc:"A package, such as $(b,acme::geometry) or $(b,acme::geometry@1.4.2)."
      $ json)

let new_ =
  let name = Arg.(required & pos 0 (some string) None & info [] ~docv:"NAME") in
  command "new" ~doc:"Make a new package in a directory named $(i,NAME)."
    Term.(
      const (fun directory name -> exit_with (fun () -> New_command.run ~directory ~name))
      $ directory $ name)

let sync =
  command "sync"
    ~doc:"Bring the project's session up to date with its files, and do nothing else."
    Term.(
      const (fun directory ->
          exit_with (fun () ->
              ignore (Project.load directory);
              0))
      $ directory)

let status =
  command "status" ~doc:"List the background process's sessions."
    Term.(
      const (fun () ->
          exit_with (fun () ->
              List.iter
                (fun (name, nodes) -> Output.printf "%s: %d results\n" name nodes)
                (Database.sessions ());
              0))
      $ const ())

let stop =
  command "stop" ~doc:"Stop the background process."
    Term.(
      const (fun () ->
          exit_with (fun () ->
              Database.stop ();
              0))
      $ const ())

let clean =
  command "clean" ~doc:"Stop the background process and delete the store, which costs only time."
    Term.(const (fun () -> Outcome.Exit 0) $ const ())

let version =
  Printf.sprintf "stage0 (Truss %s, code generation %d, Unicode %s)"
    Type_checker.Manifest.truss_version Lir.version Unicode.version

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
      new_;
      sync;
      status;
      stop;
      clean;
    ]

(* Evaluating a command line *)

(* Parses the arguments and runs the command, writing as [Output] says. *)
let evaluate arguments =
  let buffer_out = Buffer.create 256 and buffer_err = Buffer.create 256 in
  let help = Format.formatter_of_buffer buffer_out
  and err = Format.formatter_of_buffer buffer_err in
  let outcome =
    match Cmd.eval_value ~help ~err ~argv:(Array.of_list ("truss" :: arguments)) truss with
    | Ok (`Ok outcome) -> outcome
    | Ok (`Version | `Help) -> Outcome.Exit 0
    | Error (`Parse | `Term | `Exn) -> Outcome.Exit 2
  in
  Format.pp_print_flush help ();
  Format.pp_print_flush err ();
  Output.print (Buffer.contents buffer_out);
  Output.eprint (Buffer.contents buffer_err);
  (* What the command computed is saved, so another process finds it. *)
  List.iter Database.save_session !Project.opened;
  Project.opened := [];
  outcome

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
          (fun () ->
            try evaluate request.arguments
            with exception_ ->
              Output.eprintf "The compiler failed: %s\n" (Printexc.to_string exception_);
              Outcome.Exit 2))
  in
  { output = Buffer.contents buffer; outcome }

let serve () = Database.serve ~handle

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
        (fun () -> Toolchain.run_attached program arguments)

let rec remove path =
  match (Unix.lstat path).st_kind with
  | S_DIR ->
      Array.iter (fun entry -> remove (Filename.concat path entry)) (Sys.readdir path);
      Unix.rmdir path
  | _ -> Sys.remove path
  | exception Unix.Unix_error (ENOENT, _, _) -> ()

let request arguments =
  {
    arguments;
    directory = Sys.getcwd ();
    registry = Sys.getenv_opt Registry.Index.variable;
    terminal = Output.terminal ();
    columns = Output.columns ();
  }

(* Asks a running background process, without starting one. *)
let ask_running arguments =
  Database.call ~start_server:false ~progress:Output.eprint (request arguments)

(* [truss clean]: stops the background process, which holds the store
   open, and deletes the store. *)
let clean_store () =
  ignore (ask_running [ "stop" ] : (response, string) result);
  Database.reset ();
  let directory = Database.store_directory () in
  match remove directory with
  | () -> 0
  | exception Unix.Unix_error (error, _, _) ->
      Output.eprintf "Cannot delete %s: %s\n" directory (Unix.error_message error);
      2

(* Runs a command line as the client: the command in its own process, or
   in the background process. *)
let client argv =
  let arguments = List.tl (Arguments.prepare argv) in
  let no_server = List.mem "--no-server" arguments || Sys.getenv_opt "TRUSS_NO_SERVER" = Some "1" in
  let arguments = List.filter (( <> ) "--no-server") arguments in
  let local () = finish (evaluate arguments) in
  match command_of arguments with
  | Some "clean" -> clean_store ()
  | None | Some "new" -> local ()
  | _ when no_server -> local ()
  | Some ("status" | "stop") -> (
      match (ask_running arguments : (response, string) result) with
      | Ok response ->
          Output.print response.output;
          finish response.outcome
      | Error message ->
          Output.eprint_line message;
          0)
  | Some _ -> (
      match
        (Database.call ~progress:Output.eprint (request arguments) : (response, string) result)
      with
      | Ok response ->
          Output.print response.output;
          finish response.outcome
      | Error message ->
          Output.eprint_line message;
          2)
