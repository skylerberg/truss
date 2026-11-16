type cache = { directory : string }

let make_cache directory =
  File_system.make_directory directory;
  { directory }

type settings = { build : Emit_c.build; optimization : Toolchain.optimization; extra : string list }

let list_flags settings =
  (Toolchain.show_optimization_flag settings.optimization :: Toolchain.required_flags)
  @ settings.extra

let derive_object_key = Blake3.derive_key ~context:"truss 2026-11-12 object key"

let make_object_key (toolchain : Toolchain.t) settings text =
  Blake3.to_hex
    (derive_object_key
       (Cbor.encode
          (Cbor.Array
             [
               Bytes text;
               Text toolchain.identity;
               Cbor.Array (List.map (fun flag -> Cbor.Text flag) (list_flags settings));
             ])))

let make_object_path cache key = Filename.concat cache.directory (key ^ ".o")

let compile_one toolchain cache settings (name, text) =
  let key = make_object_key toolchain settings text in
  let output = make_object_path cache key in
  if Sys.file_exists output then begin
    (try Unix.utimes output 0. 0. with Unix.Unix_error _ -> ());
    Ok output
  end
  else
    let base = Filename.concat cache.directory (Printf.sprintf "%s.%d" key (Unix.getpid ())) in
    let source = base ^ ".c" in
    File_system.write source text;
    let partial = base ^ ".o" in
    match
      Toolchain.compile toolchain ~optimization:settings.optimization ~extra:settings.extra ~source
        ~output:partial
    with
    | Ok () ->
        Sys.rename partial output;
        if Option.value (Sys.getenv_opt "TRUSS_KEEP_C") ~default:"" = "" then Sys.remove source
        else Sys.rename source (Filename.concat cache.directory (key ^ ".c"));
        Ok output
    | Error message ->
        Error (Printf.sprintf "%s does not compile (kept as %s):\n%s" name source message)

let run_parallel jobs run_job =
  let jobs = Array.of_list jobs in
  let results = Array.make (Array.length jobs) None in
  let workers = max 1 (min (Array.length jobs) (Domain.recommended_domain_count () - 1)) in
  let work start =
    let next = ref start in
    while !next < Array.length jobs do
      results.(!next) <- Some (run_job jobs.(!next));
      next := !next + workers
    done
  in
  let domains =
    List.init (workers - 1) (fun worker -> Domain.spawn (fun () -> work (worker + 1)))
  in
  work 0;
  List.iter Domain.join domains;
  Array.to_list (Array.map Option.get results)

let compile_objects ?progress toolchain cache settings sources =
  let missing =
    List.length
      (List.filter
         (fun (_, text) ->
           not (Sys.file_exists (make_object_path cache (make_object_key toolchain settings text))))
         sources)
  in
  let compiled = Atomic.make 0 in
  let lock = Mutex.create () in
  let report () =
    match progress with
    | Some progress -> Mutex.protect lock (fun () -> progress (Atomic.get compiled) missing)
    | None -> ()
  in
  if missing > 0 then report ();
  let compile source =
    let cached =
      Sys.file_exists (make_object_path cache (make_object_key toolchain settings (snd source)))
    in
    let result = compile_one toolchain cache settings source in
    if not cached then begin
      Atomic.incr compiled;
      report ()
    end;
    result
  in
  let results = run_parallel sources compile in
  List.fold_right
    (fun result acc ->
      match (result, acc) with
      | Ok path, Ok paths -> Ok (path :: paths)
      | Error message, _ | _, Error message -> Error message)
    results (Ok [])

let build_program ?progress ?(tests = false) ?(copied = fun _ -> []) toolchain cache env settings
    ~files ~sources ~output =
  let emitted =
    List.mapi
      (fun part_index fragments ->
        let copies =
          List.fold_left
            (fun copies copy ->
              if
                List.exists
                  (fun other -> Instance.equal (Emit_c.key other) (Emit_c.key copy))
                  (fragments @ copies)
              then copies
              else copies @ [ copy ])
            []
            (List.concat_map copied fragments)
        in
        ( Printf.sprintf "file %d" part_index,
          Emit_c.render_file env settings.build
            (List.map (fun fragment -> (fragment, Emit_c.External)) fragments
            @ List.map (fun fragment -> (fragment, Emit_c.Internal)) copies) ))
      files
  in

  let runtime = ("the runtime", Startup.render_runtime ~tests) in
  match compile_objects ?progress toolchain cache settings ((runtime :: emitted) @ sources) with
  | Error message -> Error message
  | Ok objects -> Toolchain.link toolchain ~extra:settings.extra ~objects ~output

module For_testing = struct
  let objects = compile_objects
end
