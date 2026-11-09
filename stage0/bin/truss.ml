(* The [truss] command. Each command is a request to the code database,
   which the background process for this compiler answers, starting it if
   it is not running; with [--no-server], this process answers it. See
   DATABASE.md, "Requests". *)

let usage () =
  prerr_endline
    "usage: truss check [DIRECTORY]\n\
    \       truss test [--sanitize] [DIRECTORY]\n\
    \       truss build [--sanitize] DIRECTORY OUTPUT\n\
    \       truss run [--sanitize] DIRECTORY [ARGUMENTS...]\n\
    \       truss impact [--base COMMIT] [DIRECTORY]\n\
    \       truss holes [DIRECTORY]\n\
    \       truss references NAME [DIRECTORY]\n\
    \       truss dependencies NAME [DIRECTORY]\n\
    \       truss overlap [--with BRANCH] [--merge] [DIRECTORY]\n\
    \       truss explain FILE:LINE:COLUMN [DIRECTORY]\n\
    \       truss sync [DIRECTORY]\n\
    \       truss status | truss stop\n\
     Every command takes --no-server, to answer it in this process, and --json, for tools.";
  exit 2

let absolute directory =
  if Filename.is_relative directory then Filename.concat (Sys.getcwd ()) directory else directory

let () =
  match Array.to_list Sys.argv with
  | [ _; "__serve" ] -> Database.serve ()
  | _ :: command :: rest ->
      let flag name = List.mem name rest in
      let rest =
        List.filter
          (fun a -> not (List.mem a [ "--no-server"; "--json"; "--sanitize"; "--merge" ]))
          rest
      in
      let rec option name = function
        | key :: value :: _ when key = name -> Some value
        | _ :: more -> option name more
        | [] -> None
      in
      let rec without name = function
        | key :: _ :: more when key = name -> without name more
        | other :: more -> other :: without name more
        | [] -> []
      in
      let positional = without "--with" (without "--base" rest) in
      let directory_at i = absolute (Option.value (List.nth_opt positional i) ~default:".") in
      let sanitize = flag "--sanitize" || Sys.getenv_opt "TRUSS_SANITIZE" = Some "1" in
      let arguments = ref [] in
      let request command directory : Database.request =
        { directory; command; json = flag "--json" }
      in
      let request =
        match command with
        | "check" -> request Check (directory_at 0)
        | "test" -> request (Test { sanitize }) (directory_at 0)
        | "build" -> (
            match positional with
            | [ directory; output ] ->
                request (Build { output = absolute output; sanitize }) (absolute directory)
            | _ -> usage ())
        | "run" -> (
            match positional with
            | directory :: program_arguments ->
                arguments := program_arguments;
                request (Run { sanitize }) (absolute directory)
            | [] -> usage ())
        | "impact" -> request (Impact { base = option "--base" rest }) (directory_at 0)
        | "holes" -> request Holes (directory_at 0)
        | "references" -> (
            match positional with
            | name :: _ -> request (References { name }) (directory_at 1)
            | [] -> usage ())
        | "dependencies" -> (
            match positional with
            | name :: _ -> request (Dependencies { name }) (directory_at 1)
            | [] -> usage ())
        | "overlap" ->
            request
              (Overlap { other = option "--with" rest; merge = flag "--merge" })
              (directory_at 0)
        | "explain" -> (
            match positional with
            | place :: _ -> (
                match String.split_on_char ':' place with
                | [ file; line; column ] -> (
                    match (int_of_string_opt line, int_of_string_opt column) with
                    | Some line, Some column ->
                        request (Explain { file = absolute file; line; column }) (directory_at 1)
                    | _ -> usage ())
                | _ -> usage ())
            | [] -> usage ())
        | "sync" -> request Sync (directory_at 0)
        | "status" -> request Status (absolute ".")
        | "stop" -> request Stop (absolute ".")
        | _ -> usage ()
      in
      let response =
        if flag "--no-server" then Database.handle request else Database.call request
      in
      print_string response.output;
      prerr_string response.errors;
      (match (request.command, response.program) with
      | Run _, Some program ->
          (* The program runs on this terminal, so it can prompt and read. *)
          let status = Toolchain.run_attached program !arguments in
          (try Sys.remove program with Sys_error _ -> ());
          exit status
      | _ -> ());
      exit response.status
  | _ -> usage ()
