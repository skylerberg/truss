type t = { command : string; identity : string; added_flags : string list; objects : string }
type optimization = O1 | O2_lto

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

let list_link_flags compiler = function
  | O1 -> compiler.added_flags
  | O2_lto -> (if is_clang compiler then "-flto=thin" else "-flto") :: compiler.added_flags

let list_compile_flags compiler optimization =
  ((match optimization with O1 -> "-O1" | O2_lto -> "-O2") :: required_flags)
  @ list_link_flags compiler optimization

let derive_fingerprint = Blake3.derive_key ~context:"truss 2026-11-17 C compiler fingerprint"

let make_fingerprint compiler optimization =
  derive_fingerprint
    (Cbor.encode
       (Cbor.Array
          [
            Text compiler.identity;
            Cbor.Array
              (List.map (fun flag -> Cbor.Text flag) (list_compile_flags compiler optimization));
          ]))

let derive_object_key = Blake3.derive_key ~context:"truss 2026-11-17 object key"

let make_object_key ~fingerprint text =
  Blake3.to_hex (derive_object_key (Cbor.encode (Cbor.Array [ Bytes fingerprint; Bytes text ])))

let make_object_path compiler key = Filename.concat compiler.objects (key ^ ".o")

let compile compiler flags ~source ~output =
  match Process.run compiler.command (flags @ [ "-c"; source; "-o"; output ]) with
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
    let source = base ^ ".c" in
    File_system.write source text;
    let partial = base ^ ".o" in
    let result =
      match compile compiler flags ~source ~output:partial with
      | Ok () ->
          Sys.rename partial output;
          (match find_variable kept_source_variable with
          | None -> Sys.remove source
          | Some _ -> Sys.rename source (Filename.concat compiler.objects (key ^ ".c")));
          Ok output
      | Error message ->
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

let compile_objects ?report_progress compiler optimization units =
  File_system.make_directory compiler.objects;
  let fingerprint = make_fingerprint compiler optimization in
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
      (compile_unit compiler (list_compile_flags compiler optimization) ~on_compiled:(fun () ->
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

let build_executable ?report_progress compiler optimization ~units ~output =
  match compile_objects ?report_progress compiler optimization units with
  | Error message -> Error message
  | Ok objects -> link compiler (list_link_flags compiler optimization) ~objects ~output

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

  let compile compiler optimization ~source ~output =
    compile compiler (list_compile_flags compiler optimization) ~source ~output

  let compile_objects compiler optimization units = compile_objects compiler optimization units
end
