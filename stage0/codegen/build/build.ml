type cache = { directory : string }

let cache directory =
  File_system.make_directory directory;
  { directory }

type settings = { build : Emit_c.build; optimization : Toolchain.optimization; extra : string list }

let frame_budget = 65536
let library_margin = 65536

let is_link_time_optimized settings =
  List.exists (String.starts_with ~prefix:"-flto") settings.extra

let compiled_flags settings =
  settings.extra
  @
  if is_link_time_optimized settings then
    [ Printf.sprintf "-Wframe-larger-than=%d" frame_budget; "-Wno-error=frame-larger-than" ]
  else [ "-fstack-usage" ]

let flags settings =
  (Toolchain.optimization_flag settings.optimization :: Toolchain.required_flags)
  @ compiled_flags settings

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
let stack_usage_path object_ = Filename.remove_extension object_ ^ ".su"

let is_compiled settings output =
  Sys.file_exists output
  && (is_link_time_optimized settings || Sys.file_exists (stack_usage_path output))

let compile_one toolchain cache settings (name, text) =
  let key = object_key toolchain settings text in
  let output = object_path cache key in
  if is_compiled settings output then begin
    List.iter
      (fun path -> try Unix.utimes path 0. 0. with Unix.Unix_error _ -> ())
      [ output; stack_usage_path output ];
    Ok output
  end
  else
    let base = Filename.concat cache.directory (Printf.sprintf "%s.%d" key (Unix.getpid ())) in
    let source = base ^ ".c" in
    File_system.write source text;
    let partial = base ^ ".o" in
    match
      Toolchain.compile toolchain ~optimization:settings.optimization
        ~extra:(compiled_flags settings) ~source ~output:partial ()
    with
    | Ok () ->
        if Sys.file_exists (stack_usage_path partial) then
          Sys.rename (stack_usage_path partial) (stack_usage_path output)
        else if not (is_link_time_optimized settings) then
          File_system.write (stack_usage_path output) "";
        Sys.rename partial output;
        if Option.value (Sys.getenv_opt "TRUSS_KEEP_C") ~default:"" = "" then Sys.remove source
        else Sys.rename source (Filename.concat cache.directory (key ^ ".c"));
        Ok output
    | Error message ->
        Error (Printf.sprintf "%s does not compile (kept as %s):\n%s" name source message)

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
  let missing =
    List.length
      (List.filter
         (fun (_, text) ->
           not (is_compiled settings (object_path cache (object_key toolchain settings text))))
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
      is_compiled settings (object_path cache (object_key toolchain settings (snd source)))
    in
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

let digits_from text start =
  let rec stop position =
    if position < String.length text && text.[position] >= '0' && text.[position] <= '9' then
      stop (position + 1)
    else position
  in
  int_of_string_opt (String.sub text start (stop start - start))

let reported_frame diagnostics =
  List.fold_left
    (fun largest line ->
      List.fold_left
        (fun largest marker ->
          match Substring.find line marker with
          | None -> largest
          | Some position -> (
              match digits_from line (position + String.length marker) with
              | Some size -> max largest size
              | None -> largest))
        largest
        [ "stack frame size ("; "the frame size of " ])
    0
    (String.split_on_char '\n' diagnostics)

let largest_frame objects =
  List.fold_left
    (fun largest object_ ->
      match largest with
      | Error _ -> largest
      | Ok largest -> (
          match In_channel.with_open_text (stack_usage_path object_) In_channel.input_all with
          | exception Sys_error message -> Error message
          | usage ->
              Ok
                (List.fold_left
                   (fun largest line ->
                     match String.split_on_char '\t' line with
                     | _ :: size :: _ -> (
                         match int_of_string_opt size with
                         | Some size -> max largest size
                         | None -> largest)
                     | _ -> largest)
                   largest (String.split_on_char '\n' usage))))
    (Ok 0) objects

let program ?progress ?(tests = false) ?(copied = fun _ -> []) toolchain cache env settings ~files
    ~sources ~output =
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
          Emit_c.file env settings.build
            (List.map (fun fragment -> (fragment, Emit_c.External)) fragments
            @ List.map (fun fragment -> (fragment, Emit_c.Internal)) copies) ))
      files
  in

  let runtime = ("the runtime", Startup.runtime ~tests) in
  match objects ?progress toolchain cache settings ((runtime :: emitted) @ sources) with
  | Error message -> Error message
  | Ok objects -> (
      let link largest_frame =
        let red_zone = ((2 * largest_frame) + library_margin + 4095) / 4096 * 4096 in
        match
          compile_one toolchain cache settings
            ( "the red zone",
              Printf.sprintf
                "typedef __UINT64_TYPE__ uint64_t;\nconst uint64_t t_runtime_red_zone = %dULL;\n"
                red_zone )
        with
        | Error message -> Error message
        | Ok red_zone_object ->
            Toolchain.link toolchain ~extra:settings.extra ~objects:(objects @ [ red_zone_object ])
              ~output ()
      in
      if is_link_time_optimized settings then
        match link frame_budget with
        | Error message -> Error message
        | Ok diagnostics ->
            let reported = reported_frame diagnostics in
            if reported > frame_budget then Result.map ignore (link reported) else Ok ()
      else
        match largest_frame objects with
        | Error message -> Error message
        | Ok largest_frame -> Result.map ignore (link largest_frame))

module For_testing = struct
  let objects = objects
end
