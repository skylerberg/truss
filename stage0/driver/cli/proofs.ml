let make_solver () =
  match Solver.find () with
  | Ok solver -> solver
  | Error message -> Outcome.raise_cannot_run "%s" message

type t = { database : Database.t; proofs : Database.proofs; decided : unit Lazy.t }

let evaluate database snapshot packages proofs =
  match Database.list_evaluations proofs with
  | [] -> ()
  | evaluated ->
      ignore
        (Backend.evaluate
           (Workspace_backend.create snapshot
              (Workspace_backend.require_lowered_lookups database packages)
              Development)
           evaluated)

let check database snapshot packages scope =
  let proofs = Database.prove database scope in
  {
    database;
    proofs;
    decided =
      lazy
        (evaluate database snapshot packages proofs;
         let solver = lazy (make_solver ()) in
         Fun.protect
           ~finally:(fun () -> if Lazy.is_val solver then Solver.stop (Lazy.force solver))
           (fun () -> Database.decide proofs solver));
  }

let list_diagnostics checked file =
  Lazy.force checked.decided;
  Database.list_proof_diagnostics checked.database file

let list_states checked file =
  Lazy.force checked.decided;
  Database.list_proof_states checked.database file

let list_holes snapshot checked ~reached =
  List.map
    (fun (file, line, column, way) -> (Workspace.locate_file snapshot file, line, column, way))
    (Database.list_holes checked.proofs ~reached)
