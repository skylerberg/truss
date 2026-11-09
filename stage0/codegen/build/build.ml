type cache = { directory : string }

let rec make_directory path =
  if not (Sys.file_exists path) then begin
    make_directory (Filename.dirname path);
    try Sys.mkdir path 0o755 with Sys_error _ when Sys.file_exists path -> ()
  end

let cache directory =
  make_directory directory;
  { directory }

type settings = { build : Emit_c.build; optimization : Toolchain.optimization; extra : string list }

let flags settings =
  (Toolchain.optimization_flag settings.optimization :: Toolchain.required_flags) @ settings.extra

let object_key (toolchain : Toolchain.t) settings text =
  Blake3.to_hex
    (Blake3.hash
       (Cbor.encode
          (Cbor.Array
             [
               Text "truss object";
               Bytes text;
               Text toolchain.identity;
               Cbor.Array (List.map (fun flag -> Cbor.Text flag) (flags settings));
             ])))

let write path text = Out_channel.with_open_bin path (fun channel -> output_string channel text)

(* Writes the object under a temporary name and renames it into place, so a
   build that stops partway never leaves a broken object in the cache. *)
let compile_one toolchain cache settings (name, text) =
  let key = object_key toolchain settings text in
  let output = Filename.concat cache.directory (key ^ ".o") in
  if Sys.file_exists output then Ok output
  else
    let base = Filename.concat cache.directory (Printf.sprintf "%s.%d" key (Unix.getpid ())) in
    let source = base ^ ".c" in
    write source text;
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
let parallel jobs f =
  let jobs = Array.of_list jobs in
  let results = Array.make (Array.length jobs) None in
  let workers = max 1 (min (Array.length jobs) (Domain.recommended_domain_count () - 1)) in
  let work start =
    let i = ref start in
    while !i < Array.length jobs do
      results.(!i) <- Some (f jobs.(!i));
      i := !i + workers
    done
  in
  let domains = List.init (workers - 1) (fun w -> Domain.spawn (fun () -> work (w + 1))) in
  work 0;
  List.iter Domain.join domains;
  Array.to_list (Array.map Option.get results)

let objects toolchain cache settings sources =
  let results = parallel sources (compile_one toolchain cache settings) in
  List.fold_right
    (fun result acc ->
      match (result, acc) with
      | Ok path, Ok paths -> Ok (path :: paths)
      | Error message, _ | _, Error message -> Error message)
    results (Ok [])

let program toolchain cache env settings ~files ~sources ~output =
  let target = Memory_layout.target env in
  let emitted =
    List.mapi
      (fun i units ->
        let code =
          List.filter_map (function Lir.Code t -> Some (t, Emit_c.External) | _ -> None) units
        in
        let data = List.filter_map (function Lir.Data d -> Some d | _ -> None) units in
        let tables = List.filter_map (function Lir.Table t -> Some t | _ -> None) units in
        let evidence = List.filter_map (function Lir.Evidence e -> Some e | _ -> None) units in
        (Printf.sprintf "file %d" i, Emit_c.file env settings.build ~data ~tables ~evidence code))
      files
  in

  let runtime = ("the runtime", Startup.runtime target) in
  match objects toolchain cache settings ((runtime :: emitted) @ sources) with
  | Error message -> Error message
  | Ok objects -> Toolchain.link toolchain ~objects ~output
