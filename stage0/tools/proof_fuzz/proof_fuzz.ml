let example : Path.module_ = { package = { owner = None; name = "example" }; modules = [] }
let example_file : Path.file = { module_ = example; name = "main" }
let standard_package_database = lazy (Workspace.For_testing.load_standard_package_database ())

let build_example_database text =
  Database.create
    ~loaded:[ Lazy.force standard_package_database ]
    [ { name = example.package; dependencies = []; files = [ (example_file, text) ] } ]

let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

let compiler =
  lazy
    (match Toolchain.find () with Ok toolchain -> toolchain | Error message -> failwith message)

let cache = lazy (Build.cache (Filename.concat (Filename.get_temp_dir_name ()) "truss-proof-fuzz"))
let settings : Build.settings = { build = Development; optimization = O1; extra = [] }

let load text =
  let database = build_example_database text in
  Database.check database [ example_file.module_.package ];
  if Database.file_diagnostics database example_file <> [] then None
  else
    Some
      ( database,
        lazy
          (Compile.create ~evaluation_time_limit_ms:2000
             (Database.lowering_requests database [ example.package ])
             (Lazy.force compiler) (Lazy.force cache) settings) )

let integer (ty : Types.ty) =
  if Types.is_builtin Bool ty then Some (1, false) else Types.integer_bits ty

let extremes (bits, signed) =
  if signed then
    let half = Z.shift_left Z.one (bits - 1) in
    [ Z.neg half; Z.minus_one; Z.zero; Z.one; Z.pred half ]
  else [ Z.zero; Z.one; Z.pred (Z.shift_left Z.one bits) ]

let random (bits, signed) =
  let value = Z.extract (Z.of_int64 (Random.bits64 ())) 0 bits in
  if signed && Z.testbit value (bits - 1) then Z.sub value (Z.shift_left Z.one bits) else value

type candidate = {
  path : Path.t;
  key : Resolve.Names.key;
  signature : Types.signature;
  admits : string list;
  ranges : (int * bool) list;
}

let runnable database =
  let mir = Database.For_testing.mir database example.package in
  let interface = Database.interface_lookups database [ example.package ] in
  let lookups = Database.make_proof_lookups database in
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match
        ( Interface.Definition.signature interface declaration.path,
          Prover.Contracts.home_source lookups key,
          Mir.contract_of_path mir declaration.path )
      with
      | ( Some ({ generics = []; receiver = None; uses; output = Returns output; _ } as signature),
          source,
          Some { requires; _ } )
        when uses = Types.no_capabilities
             && integer output <> None
             && List.for_all
                  (fun (requirement : Mir.requirement) -> requirement.is_executable)
                  requires -> (
          let ranges =
            List.map
              (fun (parameter : Types.parameter_info) -> integer parameter.type_)
              signature.parameters
          in
          let admits =
            List.map
              (fun (requirement : Mir.requirement) ->
                "(" ^ Prover.Facts.text_of source requirement.clause.origin ^ ")")
              requires
          in
          match List.filter_map Fun.id ranges with
          | ranges_written
            when List.length ranges_written = List.length ranges
                 && not (List.exists (fun admit -> Substring.contains admit "==>") admits) ->
              Some { path = declaration.path; key; signature; admits; ranges = ranges_written }
          | _ -> None)
      | _ -> None)
    (lookups.interface.names.declarations example)

let proven (names : Resolve.Names.lookups) key states =
  match (names.place key, names.text key) with
  | Some { base; _ }, Some text ->
      List.for_all
        (fun (state : Source.span Prover.state) ->
          state.span.stop <= base
          || state.span.start >= base + String.length text
          || state.failure = None)
        states
  | _ -> false

let admitting index candidate =
  Printf.sprintf "\nfn fuzz_requires_%d(%s) -> Bool {\n  %s\n}\n" index
    (String.concat ", "
       (List.map
          (fun (parameter : Types.parameter_info) ->
            parameter.name ^ ": " ^ Types.show parameter.type_)
          candidate.signature.parameters))
    (String.concat " && " candidate.admits)

let failures = ref 0
let checked = ref 0
let functions = ref 0
let runs = ref 0

let run_mutant ~samples text =
  match load text with
  | None -> ()
  | Some (database, _) -> (
      incr checked;
      let states =
        Prover.list_states
          (Prover.decide ~runs:[]
             (Database.make_proof_lookups database)
             (Lazy.force solver)
             (Database.list_proofs (Database.prove database [ example_file ])))
          example_file
      in
      let candidates =
        List.filter
          (fun candidate ->
            proven (Database.names database [ example.package ]) candidate.key states)
          (runnable database)
      in
      let with_admitting =
        text
        ^ String.concat ""
            (List.mapi
               (fun index candidate ->
                 if candidate.admits = [] then "" else admitting index candidate)
               candidates)
      in
      match load with_admitting with
      | None -> ()
      | Some (running, compile) ->
          List.iteri
            (fun index candidate ->
              incr functions;
              let call function_ arguments =
                Database.For_testing.root running (Call_evaluation { function_; arguments });
                Compile.For_testing.evaluate_call (Lazy.force compile) ~function_ ~arguments
              in
              let admitted arguments =
                candidate.admits = []
                ||
                match
                  call
                    (Top { module_ = example; name = Printf.sprintf "fuzz_requires_%d" index })
                    arguments
                with
                | Ok (Ran (Static_scalar (Bool true))) -> true
                | _ -> false
              in
              let tried = Hashtbl.create 16 in
              List.iter
                (fun arguments ->
                  if (not (Hashtbl.mem tried arguments)) && admitted arguments then begin
                    Hashtbl.replace tried arguments ();
                    incr runs;
                    match call candidate.path arguments with
                    | Ok (Stopped report) ->
                        incr failures;
                        Printf.printf "PROVEN BUT FAILS: %s (%s)\n%s\n%s\n\n"
                          (Path.show candidate.path)
                          (String.concat ", " (List.map Z.to_string arguments))
                          report text
                    | _ -> ()
                  end)
                (List.init samples (fun sample ->
                     List.map
                       (fun range ->
                         let edges = extremes range in
                         if sample < List.length edges then List.nth edges sample else random range)
                       candidate.ranges)))
            candidates)

let mutants text =
  let tokens, _ = Lexer.lex (Source.create ~path:"seed.truss" text) in
  let replace (span : Source.span) by =
    String.sub text 0 span.start ^ by ^ String.sub text span.stop (String.length text - span.stop)
  in
  Array.to_list tokens
  |> List.concat_map (fun (token : Token.t) ->
      match token.kind with
      | Integer value ->
          List.map
            (fun changed -> replace token.span (Z.to_string changed))
            (Z.succ value :: (if Z.sign value > 0 then [ Z.pred value ] else []))
      | Punctuation punctuation -> (
          let swapped : Token.punctuation option =
            match punctuation with
            | Less -> Some Less_equal
            | Less_equal -> Some Less
            | Greater -> Some Greater_equal
            | Greater_equal -> Some Greater
            | Plus -> Some Minus
            | Minus -> Some Plus
            | _ -> None
          in
          match swapped with
          | Some other -> [ replace token.span (Token.punctuation_spelling other) ]
          | None -> [])
      | _ -> [])

let () =
  let seed = ref 0 and count = ref 200 and samples = ref 8 and verbose = ref false in
  let files = ref [] in
  Arg.parse
    [
      ("--seed", Arg.Set_int seed, "N  the random seed");
      ("--count", Arg.Set_int count, "N  at most this many mutants");
      ("--samples", Arg.Set_int samples, "N  argument lists for each function");
      ("--verbose", Arg.Set verbose, "  print why each seed that is not used was not");
    ]
    (fun file -> files := file :: !files)
    "proof_fuzz [--seed N] [--count N] [--samples N] [--verbose] FILE...";
  Random.init !seed;
  let seeds =
    List.concat_map
      (fun file ->
        List.filter
          (fun text ->
            let shown diagnostics =
              if !verbose then
                List.iter
                  (fun (diagnostic : Diagnostic.t) ->
                    Printf.printf "seed diagnostic at %d: %s\n" diagnostic.span.start
                      diagnostic.message)
                  diagnostics
            in
            match load text with
            | Some (database, _) ->
                let unproven =
                  Prover.list_diagnostics
                    (Prover.decide ~runs:[]
                       (Database.make_proof_lookups database)
                       (Lazy.force solver)
                       (Database.list_proofs (Database.prove database [ example_file ])))
                    example_file
                in
                shown unproven;
                unproven = []
            | None ->
                let database = build_example_database text in
                Database.check database [ example_file.module_.package ];
                shown (Database.file_diagnostics database example_file);
                false)
          (if Filename.check_suffix file ".md" then Documents.truss_blocks (File_system.read file)
           else [ File_system.read file ]))
      (List.rev !files)
  in
  let all = List.concat_map mutants seeds in
  let chosen =
    List.map snd (List.sort compare (List.map (fun mutant -> (Random.bits (), mutant)) all))
    |> List.filteri (fun index _ -> index < !count)
  in
  Printf.printf "%d seeds, %d mutants, trying %d\n%!" (List.length seeds) (List.length all)
    (List.length chosen);
  List.iter (run_mutant ~samples:!samples) chosen;
  Printf.printf "%d mutants checked, %d functions that prove, run %d times\n" !checked !functions
    !runs;
  Printf.printf "%d proofs that should not have been made\n" !failures;
  exit (if !failures > 0 then 1 else 0)
