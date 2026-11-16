let solver () =
  let cache = Workspace.open_cache () in
  match
    Solver.find
      ~cache:
        {
          find = (fun key -> Cache.find_result cache ~kind:Solver_answer ~key);
          add = (fun key value -> Cache.add_result cache ~kind:Solver_answer ~key value);
        }
      ()
  with
  | Ok solver -> solver
  | Error message -> Outcome.cannot_run "%s" message

type t = { proofs : Database.proofs; verdicts : Prover.verdicts Lazy.t }

let run_template_checks compiler checks =
  List.map
    (fun ({ from_template; literals; clauses } as check : Prover.State.template_check) ->
      (check, Compile.run_template_check compiler ~from_template ~literals ~clauses))
    checks

let runs database snapshot packages proofs =
  match Database.list_template_checks proofs with
  | [] -> []
  | checks -> run_template_checks (Compiler.create database snapshot packages Development) checks

let check database snapshot packages files =
  let proofs = Database.prove database files in
  {
    proofs;
    verdicts =
      lazy
        (let solver = solver () in
         Prover.decide
           ~runs:(runs database snapshot packages proofs)
           (Database.make_proof_lookups database)
           solver (Database.list_proofs proofs));
  }

let list_diagnostics checked file = Prover.list_diagnostics (Lazy.force checked.verdicts) file
let list_states checked file = Prover.list_states (Lazy.force checked.verdicts) file

let list_holes snapshot packages checked definition =
  List.map
    (fun (file, offset) ->
      let source = Command_packages.source snapshot packages file in
      let line, column = Source.position source offset in
      (Shown_path.shown (Source.path source), line, column))
    (Database.list_holes checked.proofs definition)
