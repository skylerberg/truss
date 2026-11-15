let solver () =
  let find, add = Database.results ~kind:Store.Solver_answer in
  match Solver.find ~cache:{ find; add } () with
  | Ok solver -> solver
  | Error message -> Outcome.cannot_run "%s" message

type t = { proofs : Pipeline.proofs; verdicts : Pipeline.verdicts Lazy.t }

let check pipeline snapshot packages files =
  let proofs = Pipeline.prove pipeline files in
  {
    proofs;
    verdicts =
      lazy
        (Pipeline.decide
           ~evaluator:
             (Evaluator.of_compiler (lazy (Compiler.create pipeline snapshot packages Development)))
           (solver ()) proofs);
  }

let diagnostics checked file = Pipeline.diagnostics (Lazy.force checked.verdicts) file
let states checked file = Pipeline.states (Lazy.force checked.verdicts) file

let holes snapshot packages checked definition =
  List.map
    (fun (file, offset) ->
      let source = Command_packages.source snapshot packages file in
      let line, column = Source.position source offset in
      (Shown_path.shown (Source.path source), line, column))
    (Pipeline.holes checked.proofs definition)
