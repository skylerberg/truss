type t = { command : string; identity : string; added_flags : string list; objects : string }

let command_variable = "TRUSS_CC"
let flags_variable = "TRUSS_CFLAGS"
let kept_source_variable = "TRUSS_KEEP_C"
let variables = [ command_variable; flags_variable; kept_source_variable ]

let find_variable name =
  match Sys.getenv_opt name with Some "" | None -> None | Some value -> Some value

let identify command =
  match Process.run command [ "--version" ] with
  | 0, version, _ -> Ok (String.trim version ^ "\n" ^ command)
  | _ -> Error (command ^ " --version failed")
  | exception Unix.Unix_error _ -> Error ("cannot run " ^ command)

let find ~objects =
  let added_flags =
    match find_variable flags_variable with
    | Some flags -> List.filter (( <> ) "") (String.split_on_char ' ' flags)
    | None -> []
  in
  let rec identify_first errors = function
    | [] -> Error ("no C compiler found: " ^ String.concat "; " (List.rev errors))
    | command :: rest -> (
        match identify command with
        | Ok identity -> Ok { command; identity; added_flags; objects }
        | Error error -> identify_first (error :: errors) rest)
  in
  identify_first []
    (match find_variable command_variable with
    | Some command -> [ command ]
    | None -> [ "clang"; "cc" ])

let is_clang compiler = String.includes ~affix:"clang" compiler.identity

let required_flags =
  [
    "-std=c11";
    "-fwrapv";
    "-fno-strict-aliasing";
    "-fno-finite-loops";
    "-ffp-contract=off";
    "-fno-fast-math";
    "-fno-math-errno";
    "-fno-common";
    "-fvisibility=hidden";
    "-fno-exceptions";
    "-fno-asynchronous-unwind-tables";
  ]

let list_link_flags compiler : Profile.t -> string list = function
  | Development -> compiler.added_flags
  | Release ->
      "-O3" :: (if is_clang compiler then "-flto=thin" else "-flto") :: compiler.added_flags

let list_profile_flags : Profile.t -> string list = function
  | Development -> [ "-O1" ]
  | Release ->
      [ "-g1"; "-gno-column-info"; "-fno-omit-frame-pointer"; "-mno-omit-leaf-frame-pointer" ]

let list_compile_flags compiler profile =
  list_profile_flags profile @ required_flags @ list_link_flags compiler profile

let list_compilation_directory_flags : Profile.t -> string list = function
  | Development -> []
  | Release -> [ "-fdebug-prefix-map=" ^ Sys.getcwd () ^ "=." ]

let derive_fingerprint = Blake3.derive_key ~context:"truss 2026-11-17 C compiler fingerprint"

let make_fingerprint compiler profile =
  derive_fingerprint
    (Cbor.encode
       (Cbor.Array
          [
            Text compiler.identity;
            Cbor.Array (List.map (fun flag -> Cbor.Text flag) (list_compile_flags compiler profile));
          ]))

let derive_object_key = Blake3.derive_key ~context:"truss 2026-11-17 object key"

let make_object_key ~fingerprint text =
  Blake3.to_hex (derive_object_key (Cbor.encode (Cbor.Array [ Bytes fingerprint; Bytes text ])))

let make_object_path compiler key = Filename.concat compiler.objects (key ^ ".o")

let compile compiler flags ~text ~output =
  match
    Process.run ~input:text compiler.command (flags @ [ "-x"; "c"; "-c"; "-"; "-o"; output ])
  with
  | 0, _, _ -> Ok ()
  | _, out, err -> Error (out ^ err)

let compile_unit compiler flags ~on_compiled (name, text, key) =
  let output = make_object_path compiler key in
  if Sys.file_exists output then begin
    (try Unix.utimes output 0. 0. with Unix.Unix_error _ -> ());
    Ok output
  end
  else
    let base = Filename.concat compiler.objects (Printf.sprintf "%s.%d" key (Unix.getpid ())) in
    let partial = base ^ ".o" in
    let result =
      match compile compiler flags ~text ~output:partial with
      | Ok () ->
          Sys.rename partial output;
          if Option.is_some (find_variable kept_source_variable) then
            File_system.write (Filename.concat compiler.objects (key ^ ".c")) text;
          Ok output
      | Error message ->
          let source = base ^ ".c" in
          File_system.write source text;
          Error (Printf.sprintf "%s does not compile (kept as %s):\n%s" name source message)
    in
    on_compiled ();
    result

let run_parallel jobs run_job =
  let jobs = Array.of_list jobs in
  let results = Array.make (Array.length jobs) None in
  let workers = max 1 (min (Array.length jobs) (Domain.recommended_domain_count () - 1)) in
  let run_worker start =
    let next = ref start in
    while !next < Array.length jobs do
      results.(!next) <- Some (run_job jobs.(!next));
      next := !next + workers
    done
  in
  let domains =
    List.init (workers - 1) (fun worker -> Domain.spawn (fun () -> run_worker (worker + 1)))
  in
  run_worker 0;
  List.iter Domain.join domains;
  Array.to_list (Array.map Option.get results)

let compile_objects ?report_progress compiler profile units =
  File_system.make_directory compiler.objects;
  let fingerprint = make_fingerprint compiler profile in
  let keyed =
    List.map (fun (name, text) -> (name, text, make_object_key ~fingerprint text)) units
  in
  let missing =
    List.length
      (List.filter (fun (_, _, key) -> not (Sys.file_exists (make_object_path compiler key))) keyed)
  in
  let compiled = Atomic.make 0 in
  let lock = Mutex.create () in
  let report () =
    Option.iter
      (fun report_progress ->
        Mutex.protect lock (fun () -> report_progress (Atomic.get compiled) missing))
      report_progress
  in
  if missing > 0 then report ();
  let results =
    run_parallel keyed
      (compile_unit compiler
         (list_compile_flags compiler profile @ list_compilation_directory_flags profile)
         ~on_compiled:(fun () ->
           Atomic.incr compiled;
           report ()))
  in
  List.fold_right
    (fun result acc ->
      match (result, acc) with
      | Ok path, Ok paths -> Ok (path :: paths)
      | Error message, _ | _, Error message -> Error message)
    results (Ok [])

let quote_response_word path =
  let buffer = Buffer.create (String.length path + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (fun character ->
      if character = '"' || character = '\\' then Buffer.add_char buffer '\\';
      Buffer.add_char buffer character)
    path;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let link compiler flags ~objects ~output =
  let response = output ^ ".objects" in
  Out_channel.with_open_bin response (fun channel ->
      List.iter (fun path -> output_string channel (quote_response_word path ^ "\n")) objects);
  let result =
    Process.run compiler.command (flags @ [ "@" ^ response; "-o"; output; "-lm"; "-pthread" ])
  in
  (try Sys.remove response with Sys_error _ -> ());
  match result with 0, _, _ -> Ok () | _, out, err -> Error (out ^ err)

let lto_objects_built = Atomic.make 0

let link_with_dsym_bundle compiler flags ~objects ~output ~bundle =
  let lto_objects =
    Filename.concat compiler.objects
      (Printf.sprintf "lto.%d.%d" (Unix.getpid ()) (Atomic.fetch_and_add lto_objects_built 1))
  in
  let result =
    match link compiler (("-Wl,-object_path_lto," ^ lto_objects) :: flags) ~objects ~output with
    | Error _ as error -> error
    | Ok () -> (
        match Process.run "dsymutil" [ output; "-o"; bundle ] with
        | 0, _, _ -> Ok ()
        | _, out, err -> Error (out ^ err)
        | exception Unix.Unix_error _ -> Error "cannot run dsymutil")
  in
  File_system.remove lto_objects;
  result

let build_executable ?report_progress ?dsym_bundle compiler profile ~units ~output =
  match compile_objects ?report_progress compiler profile units with
  | Error message -> Error message
  | Ok objects -> (
      let flags = list_link_flags compiler profile in
      match dsym_bundle with
      | None -> link compiler flags ~objects ~output
      | Some bundle -> link_with_dsym_bundle compiler flags ~objects ~output ~bundle)

module For_testing = struct
  let reject_warnings compiler =
    {
      compiler with
      added_flags =
        [
          "-Wall";
          "-Wextra";
          "-Wtype-limits";
          "-Werror";
          "-Wno-unused-parameter";
          "-Wno-unused-but-set-variable";
          "-Wno-array-parameter";
          (if is_clang compiler then "-Wno-sometimes-uninitialized" else "-Wno-maybe-uninitialized");
        ]
        @ compiler.added_flags;
    }

  let has_sanitizer compiler =
    List.exists (String.starts_with ~prefix:"-fsanitize=") compiler.added_flags

  let compile compiler profile ~text ~output =
    compile compiler
      (list_compile_flags compiler profile @ list_compilation_directory_flags profile)
      ~text ~output

  let compile_objects compiler profile units = compile_objects compiler profile units
end
