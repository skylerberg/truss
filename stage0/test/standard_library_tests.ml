(* The tests of the standard library's source: each module checks through
   every stage with no diagnostic, and proves. *)

open Harness

(* Solver answers are kept by the text of the query, the solver's version
   and its limit, so with a directory to keep them in, a run solves only
   the queries that the last run did not. *)
let solver =
  match Solver.find ?cache:(Sys.getenv_opt "TRUSS_SOLVER_CACHE") () with
  | Ok solver -> solver
  | Error message ->
      prerr_endline message;
      exit 1

let () =
  let engine = Engine.create () in
  (* One engine holds every module's results, so an audit after each
     module's test would compute the whole library again for each of them.
     It is audited once, when every module is checked and before any is
     proven: the prover's own tests audit its queries, and auditing them
     here would translate every proof of the library a second time. *)
  Engine.skip_audit engine;
  let database = Engine.context engine in
  Database.load_standard engine;
  let checked =
    List.map
      (fun ((module_ : Path.module_), _) -> (module_, Type_checker.diagnostics database module_))
      Standard_library.modules
  in
  test "the code database kept every result of checking the standard library current" (fun () ->
      List.iter (fun problem -> fail "%s" problem) (Engine.audit engine));
  List.iter
    (fun ((module_ : Path.module_), errors) ->
      test
        (Printf.sprintf "%s checks cleanly and proves" (Path.show_module module_))
        (fun () ->
          let source = (Query.demand database Workspace.file module_).source in
          let report =
            List.iter (fun diagnostic -> fail "%s" (Diagnostic.render source diagnostic))
          in
          match errors with
          | [] -> report (Prover.diagnostics database solver module_)
          | errors -> report errors))
    checked

let () = finish ()
