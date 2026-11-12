(* Fuzzing the prover. This is a tool, not a test: run it by hand to look
   for a program the prover proves that fails a run-time check when it
   runs, and turn each one it finds into a focused test.

     dune exec stage0/tools/proof_fuzz/proof_fuzz.exe -- [--seed N] [--count N] [--samples N] [--verbose] FILE...

   Each file is a seed, or, for a Markdown document, each of its ```truss
   blocks is: those that check and prove on their own, with the standard
   library, are used. [seeds.truss] beside this file is a seed of integer
   functions, as few of the documents' examples are. Each
   mutant changes one token of a seed: an integer moved by one, [<] for
   [<=] and the like, or [+] for [-]. For each mutant that checks, every
   function whose obligations all prove, with integer or [Bool] parameters
   and result, no capabilities, no generics, and [requires] that can run,
   is run, built with its checks, on its parameters' extremes and on random
   values that its [requires] admit, which a function the fuzzer adds
   decides. A run that stops at a check is a proof the prover should not
   have made.

   It prints each such mutant, function, and arguments, and exits with
   status 1 if there was one. *)

(* The oracles' responses, recorded in the engine, as the database does for
   a session. *)
let record database responses =
  let engine = Engine.of_context database in
  List.iter (fun (key, response) -> Engine.set engine Prover.oracle_response key response) responses

let example : Path.module_ = { package = { owner = None; name = "example" }; modules = [ "main" ] }
let standard = lazy (Database.Testing.standard_base ())

let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

let compiler =
  lazy
    (match Toolchain.find () with Ok toolchain -> toolchain | Error message -> failwith message)

let cache = lazy (Build.cache (Filename.concat (Filename.get_temp_dir_name ()) "truss-proof-fuzz"))
let settings : Build.settings = { build = Development; optimization = O1; extra = [] }

let target =
  match Libc.host with
  | Some system -> Memory_layout.target_64 system
  | None -> failwith "the fuzzer runs programs, so it runs only on Linux and macOS"

let load text =
  let engine = Engine.create ~bases:[ Lazy.force standard ] () in
  Database.load_package engine
    ~name:{ owner = None; name = "example" }
    ~dependencies:[]
    [ (example, text) ];
  let database = Engine.context engine in
  if Type_checker.diagnostics database example <> [] then None
  else
    Some
      ( database,
        lazy
          (Compile.create
             ~want:(fun lowering wanted ->
               Engine.set engine Compile.roots lowering
                 (Compile.add_roots (Engine.context engine) lowering wanted))
             database target (Lazy.force compiler) (Lazy.force cache) settings) )

(* The bits and signedness of a built-in integer type, or of [Bool] as one
   bit. *)
let integer (ty : Types.ty) =
  match ty with
  | Named { path; arguments = [] } -> (
      match Intrinsic.builtin_of_path path with
      | Some Int8 -> Some (8, true)
      | Some Int16 -> Some (16, true)
      | Some Int32 -> Some (32, true)
      | Some (Int64 | ISize) -> Some (64, true)
      | Some UInt8 -> Some (8, false)
      | Some UInt16 -> Some (16, false)
      | Some UInt32 -> Some (32, false)
      | Some (UInt64 | USize) -> Some (64, false)
      | Some Bool -> Some (1, false)
      | _ -> None)
  | _ -> None

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
  admits : string list;  (** Each [requires], as written. *)
  ranges : (int * bool) list;
}

(* The functions the fuzzer can run. *)
let runnable database =
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match
        ( Query.demand database Interface.Environment.signature declaration.path,
          Prover.Translate.source_at_key database key )
      with
      | ( Some
            ({ generics = []; receiver = None; uses = []; output = Returns output; _ } as signature),
          Some
            ({ core = { definition = Function { contract = { requires; _ }; _ }; _ }; _ } as source)
        )
        when integer output <> None
             && List.for_all (fun (condition : Core.condition) -> condition.executable) requires
        -> (
          let ranges =
            List.map (fun (p : Types.parameter_info) -> integer p.type_) signature.parameters
          in
          let admits =
            List.map
              (fun (condition : Core.condition) ->
                "(" ^ Prover.Translate.quote source condition.value.origin ^ ")")
              requires
          in
          (* [admitting] writes each clause as code, where [==>] is not
             allowed. *)
          match List.filter_map Fun.id ranges with
          | found
            when List.length found = List.length ranges
                 && not (List.exists (fun admit -> Substring.contains admit "==>") admits) ->
              Some { path = declaration.path; key; signature; admits; ranges = found }
          | _ -> None)
      | _ -> None)
    (Query.demand database Resolve.Names.declarations example)

(* Whether every obligation of a definition proves. *)
let proven database key states =
  match
    (Query.demand database Resolve.Names.base key, Query.demand database Resolve.Names.text key)
  with
  | Some (_, base), Some text ->
      List.for_all
        (fun (state : Diagnostic.span Prover.state) ->
          state.span.stop <= base
          || state.span.start >= base + String.length text
          || state.failure = None)
        states
  | _ -> false

(* A function that says whether arguments meet another's [requires]. *)
let admitting index candidate =
  Printf.sprintf "\nfn fuzz_requires_%d(%s) -> Bool {\n  %s\n}\n" index
    (String.concat ", "
       (List.map
          (fun (p : Types.parameter_info) -> p.name ^ ": " ^ Types.show p.type_)
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
      let states = Prover.states ~record:(record database) database (Lazy.force solver) example in
      let candidates =
        List.filter (fun candidate -> proven database candidate.key states) (runnable database)
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
      | Some (_, compile) ->
          List.iteri
            (fun index candidate ->
              incr functions;
              let call function_ arguments =
                Compile.evaluate_call (Lazy.force compile) ~time_limit:2000 ~function_ ~arguments
              in
              let admitted arguments =
                candidate.admits = []
                ||
                match
                  call
                    (Top { module_ = example; name = Printf.sprintf "fuzz_requires_%d" index })
                    arguments
                with
                | Ok (Returned (Static_scalar (Bool true))) -> true
                | _ -> false
              in
              let tried = Hashtbl.create 16 in
              List.iter
                (fun arguments ->
                  if (not (Hashtbl.mem tried arguments)) && admitted arguments then begin
                    Hashtbl.replace tried arguments ();
                    incr runs;
                    match call candidate.path arguments with
                    | Error message when Substring.contains message "ended with status" ->
                        incr failures;
                        Printf.printf "PROVEN BUT FAILS: %s (%s)\n%s\n%s\n\n"
                          (Path.show candidate.path)
                          (String.concat ", " (List.map Z.to_string arguments))
                          message text
                    | _ -> ()
                  end)
                (List.init samples (fun sample ->
                     List.map
                       (fun range ->
                         let edges = extremes range in
                         if sample < List.length edges then List.nth edges sample else random range)
                       candidate.ranges)))
            candidates)

(* Each one-token change of a seed that the fuzzer makes. *)
let mutants text =
  let tokens, _ = Lexer.lex (Source.create ~path:"seed.truss" text) in
  let replace (span : Token.span) by =
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
                  (fun (d : Diagnostic.t) ->
                    Printf.printf "seed diagnostic at %d: %s\n" d.span.start d.message)
                  diagnostics
            in
            match load text with
            | Some (database, _) ->
                let unproven =
                  Prover.diagnostics ~record:(record database) database (Lazy.force solver) example
                in
                shown unproven;
                unproven = []
            | None ->
                let engine = Engine.create ~bases:[ Lazy.force standard ] () in
                Database.load_package engine
                  ~name:{ owner = None; name = "example" }
                  ~dependencies:[]
                  [ (example, text) ];
                shown (Type_checker.diagnostics (Engine.context engine) example);
                false)
          (if Filename.check_suffix file ".md" then Documents.truss_blocks (Documents.read file)
           else [ Documents.read file ]))
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
