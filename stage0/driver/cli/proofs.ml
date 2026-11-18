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

type t = { proofs : Database.proofs; verdicts : Prover.verdicts Lazy.t }

let run_template_checks backend checks =
  List.map
    (fun ({ from_template; literals; clauses } as check : Prover.State.template_check) ->
      (check, Backend.run_template_check backend ~from_template ~literals ~clauses))
    checks

let list_runs database snapshot packages proofs =
  match Database.list_template_checks proofs with
  | [] -> []
  | checks ->
      run_template_checks (Workspace_backend.create database snapshot packages Development) checks

let check database snapshot packages files =
  let proofs = Database.prove database files in
  {
    proofs;
    verdicts =
      lazy
        (let solver = make_solver () in
         Prover.decide
           ~runs:(list_runs database snapshot packages proofs)
           (Database.make_proof_lookups database)
           solver (Database.list_proofs proofs));
  }

let list_diagnostics checked file = Prover.list_diagnostics (Lazy.force checked.verdicts) file
let list_states checked file = Prover.list_states (Lazy.force checked.verdicts) file

let list_holes snapshot packages checked definition =
  List.map
    (fun (file, offset) ->
      let source = Command_packages.read_source snapshot packages file in
      let line, column = Source.compute_position source offset in
      (Shown_path.show_path (Source.path source), line, column))
    (Database.list_holes checked.proofs definition)
