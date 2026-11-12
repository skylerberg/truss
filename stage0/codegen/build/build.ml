type cache = { directory : string }

let cache directory =
  File_system.make_directory directory;
  { directory }

type settings = { build : Emit_c.build; optimization : Toolchain.optimization; extra : string list }

let flags settings =
  (Toolchain.optimization_flag settings.optimization :: Toolchain.required_flags) @ settings.extra

let derive_object_key = Blake3.derive_key ~context:"truss 2026-11-12 object key"

let object_key (toolchain : Toolchain.t) settings text =
  Blake3.to_hex
    (derive_object_key
       (Cbor.encode
          (Cbor.Array
             [
               Bytes text;
               Text toolchain.identity;
               Cbor.Array (List.map (fun flag -> Cbor.Text flag) (flags settings));
             ])))

let object_path cache key = Filename.concat cache.directory (key ^ ".o")

(* Writes the object under a temporary name and renames it into place, so a
   build that stops partway never leaves a broken object in the cache. An
   object that is found is given the present time, so its age is how long
   ago a build last used it. *)
let compile_one toolchain cache settings (name, text) =
  let key = object_key toolchain settings text in
  let output = object_path cache key in
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
        ~output:partial ()
    with
    | Ok () ->
        Sys.rename partial output;
        (* [TRUSS_KEEP_C] keeps each C file beside its object, for reading
           what was emitted. *)
        if Sys.getenv_opt "TRUSS_KEEP_C" = None then Sys.remove source
        else Sys.rename source (Filename.concat cache.directory (key ^ ".c"));
        Ok output
    | Error message ->
        Error (Printf.sprintf "%s does not compile (kept as %s):\n%s" name source message)

(* Runs the jobs on several domains, each taking every [n]th job, and
   returns the results in the jobs' order. *)
let parallel jobs run_job =
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

let objects ?progress toolchain cache settings sources =
  (* Only the files whose object is not cached count toward progress, since
     only they cost anything. *)
  let missing =
    List.length
      (List.filter
         (fun (_, text) ->
           not (Sys.file_exists (object_path cache (object_key toolchain settings text))))
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
    let cached = Sys.file_exists (object_path cache (object_key toolchain settings (snd source))) in
    let result = compile_one toolchain cache settings source in
    if not cached then begin
      Atomic.incr compiled;
      report ()
    end;
    result
  in
  let results = parallel sources compile in
  List.fold_right
    (fun result acc ->
      match (result, acc) with
      | Ok path, Ok paths -> Ok (path :: paths)
      | Error message, _ | _, Error message -> Error message)
    results (Ok [])

let program ?progress ?(tests = false) ?(in_order = tests) ?(copied = fun _ -> []) toolchain cache
    env settings ~files ~sources ~output =
  let target = Memory_layout.target env in
  let emitted =
    List.mapi
      (fun part_index units ->
        let own =
          List.filter_map (function Lir.Code instance -> Some instance | _ -> None) units
        in
        (* Each copy once, and none of an instance the file defines itself. *)
        let copies =
          List.fold_left
            (fun copies (copy : Lir.t) ->
              if
                List.exists (fun (other : Lir.t) -> Instance.equal other.key copy.key) (own @ copies)
              then copies
              else copies @ [ copy ])
            [] (List.concat_map copied own)
        in
        let code =
          List.map (fun instance -> (instance, Emit_c.External)) own
          @ List.map (fun instance -> (instance, Emit_c.Internal)) copies
        in
        let data = List.filter_map (function Lir.Data data -> Some data | _ -> None) units in
        let tables =
          List.filter_map (function Lir.Table instance -> Some instance | _ -> None) units
        in
        (Printf.sprintf "file %d" part_index, Emit_c.file env settings.build ~data ~tables code))
      files
  in

  let runtime = ("the runtime", Startup.runtime target ~tests ~in_order) in
  match objects ?progress toolchain cache settings ((runtime :: emitted) @ sources) with
  | Error message -> Error message
  | Ok objects -> Toolchain.link toolchain ~extra:settings.extra ~objects ~output ()
