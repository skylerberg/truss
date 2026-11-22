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

type t = { database : Database.t; proofs : Database.proofs; decided : unit Lazy.t }

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
  {
    database;
    proofs;
    decided =
      lazy
        (Database.decide proofs
           ~runs:(list_runs database snapshot packages proofs)
           (lazy (make_solver ())));
  }

let list_diagnostics checked file =
  Lazy.force checked.decided;
  Database.list_proof_diagnostics checked.database file

let list_warnings checked file = Database.list_proof_warnings checked.database file

let list_states checked file =
  Lazy.force checked.decided;
  Database.list_proof_states checked.database file

let list_holes snapshot checked ~reached =
  List.map
    (fun (file, line, column, way) -> (Workspace.locate_file snapshot file, line, column, way))
    (Database.list_holes checked.proofs ~reached)
