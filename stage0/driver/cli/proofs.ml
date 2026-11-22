let make_solver () =
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
  | Error message -> Outcome.raise_cannot_run "%s" message

type t = {
  proofs : Database.proofs;
  warnings : Prover.warnings Lazy.t;
  verdicts : Prover.verdicts Lazy.t;
}

let list_runs database snapshot packages proofs =
  match Database.list_evaluations proofs with
  | [] -> []
  | evaluations ->
      Evaluations.run
        (Workspace_backend.create snapshot
           (Workspace_backend.require_lowered_lookups database packages)
           Development)
        evaluations

let check database snapshot packages files =
  let proofs = Database.prove database files in
  let lookups = Database.make_proof_lookups database in
  {
    proofs;
    warnings = lazy (Prover.collect_warnings lookups (Database.list_proofs proofs));
    verdicts =
      lazy
        (let solver = make_solver () in
         Prover.decide
           ~runs:(list_runs database snapshot packages proofs)
           lookups solver (Database.list_proofs proofs));
  }

let list_diagnostics checked file = Prover.list_diagnostics (Lazy.force checked.verdicts) file
let list_warnings checked file = Prover.list_warnings (Lazy.force checked.warnings) file
let list_states checked file = Prover.list_states (Lazy.force checked.verdicts) file

let list_holes snapshot checked ~reached =
  List.map
    (fun (file, line, column, way) -> (Workspace.locate_file snapshot file, line, column, way))
    (Database.list_holes checked.proofs ~reached)
