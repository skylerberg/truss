(* The [truss] command: parsing arguments, and running the commands in the
   [Cli] library. See CLI.md. *)

open Cmdliner
open Cli

(* Runs a command, turning a reason it cannot run into status 2. *)
let guard f =
  try f ()
  with Project.Cannot_run message ->
    prerr_endline message;
    2

(* Options many commands share *)

let directory =
  Arg.(
    value & opt dir "."
    & info [ "C" ] ~docv:"DIRECTORY"
        ~doc:"Run as if from $(docv): find the package from there, and read paths from there.")

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
  command "check" ~doc:"Report every diagnostic in the package."
    Term.(
      const (fun directory fix json -> guard (fun () -> Check_command.run ~directory ~fix ~json))
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
  command "test" ~doc:"Check the package, then run the tests whose results are not kept."
    Term.(
      const (fun directory paths match_ timings rerun json sanitize ->
          guard (fun () ->
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
          guard (fun () -> Holes_command.run ~directory ~paths ~json))
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
          guard (fun () -> Show_command.run ~directory ~paths ~body ~json))
      $ directory $ paths $ body $ json)

let impact =
  let since =
    Arg.(
      value & opt string "HEAD"
      & info [ "since" ] ~docv:"REVISION"
          ~doc:"Compare with the package at the git revision $(docv).")
  in
  let paths =
    Arg.(
      value & pos_all string []
      & info [] ~docv:"PATH"
          ~doc:"List what depends on each of these definitions now, in place of comparing.")
  in
  command "impact"
    ~doc:"List what changed since a revision, and what it reaches, or what depends on a definition."
    Term.(
      const (fun directory since paths json ->
          guard (fun () -> Impact_command.run ~directory ~since ~paths ~json))
      $ directory $ since $ paths $ json)

let rename =
  let from_ = Arg.(required & pos 0 (some string) None & info [] ~docv:"FROM") in
  let to_ = Arg.(required & pos 1 (some string) None & info [] ~docv:"TO") in
  command "rename"
    ~doc:"Rename a definition, method, or module, and every reference to it in the package."
    Term.(
      const (fun directory from_ to_ json ->
          guard (fun () -> Rename_command.run ~directory ~from_ ~to_ ~json))
      $ directory $ from_ $ to_ $ json)

let new_ =
  let name = Arg.(required & pos 0 (some string) None & info [] ~docv:"NAME") in
  command "new" ~doc:"Make a new package in a directory named $(i,NAME)."
    Term.(
      const (fun directory name -> guard (fun () -> New_command.run ~directory ~name))
      $ directory $ name)

let clean =
  command "clean" ~doc:"Delete the cache, which costs only time."
    Term.(const (fun () -> guard Cache.clean) $ const ())

let debug =
  let file = Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE") in
  Cmd.group
    (Cmd.info "debug" ~docs:Manpage.s_none ~doc:"Tools for working on the compiler.")
    [
      command "tokens" ~doc:"Print a file's tokens, one per line, and its diagnostics."
        Term.(
          const (fun file json -> guard (fun () -> Debug_command.tokens ~file ~json)) $ file $ json);
      command "tree" ~doc:"Print each definition's syntax tree, and the file's diagnostics."
        Term.(
          const (fun file json -> guard (fun () -> Debug_command.tree ~file ~json)) $ file $ json);
    ]

let version =
  Printf.sprintf "stage0 (hash format %d, code generation %d, Unicode %s)" Hash.format_version
    Lir.version Unicode.version

let truss =
  Cmd.group
    (Cmd.info "truss" ~version ~exits ~doc:"Check, test, build, and change Truss code.")
    [ check; test; run; build; holes; show; impact; rename; new_; clean; debug ]

let () =
  let argv = Array.of_list (Arguments.prepare (Array.to_list Sys.argv)) in
  exit
    (match Cmd.eval_value ~argv truss with
    | Ok (`Ok status) -> status
    | Ok (`Version | `Help) -> 0
    | Error (`Parse | `Term | `Exn) -> 2)
