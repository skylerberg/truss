let solver () =
  let find, add = Database.results ~kind:Cache.Solver_answer in
  match Solver.find ~cache:{ find; add } () with
  | Ok solver -> solver
  | Error message -> Outcome.cannot_run "%s" message

type t = { proofs : Pipeline.proofs; verdicts : Prover.verdicts Lazy.t }

let run_template_checks compiler checks =
  List.map
    (fun ({ from_template; literals; clauses } as check : Prover.State.template_check) ->
      (check, Compile.run_template_check compiler ~from_template ~literals ~clauses))
    checks

let runs pipeline snapshot packages proofs =
  match Pipeline.template_checks proofs with
  | [] -> []
  | checks -> run_template_checks (Compiler.create pipeline snapshot packages Development) checks

let check pipeline snapshot packages files =
  let proofs = Pipeline.prove pipeline files in
  {
    proofs;
    verdicts =
      lazy
        (let solver = solver () in
         Prover.decide
           ~runs:(runs pipeline snapshot packages proofs)
           (Pipeline.make_proof_lookups pipeline)
           solver (Pipeline.list_proofs proofs));
  }

let diagnostics checked file = Prover.list_diagnostics (Lazy.force checked.verdicts) file
let states checked file = Prover.list_states (Lazy.force checked.verdicts) file

let holes snapshot packages checked definition =
  List.map
    (fun (file, offset) ->
      let source = Command_packages.source snapshot packages file in
      let line, column = Source.position source offset in
      (Shown_path.shown (Source.path source), line, column))
    (Pipeline.holes checked.proofs definition)
