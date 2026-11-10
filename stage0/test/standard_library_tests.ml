(* The tests of the standard library's source: each module checks through
   every stage with no diagnostic, and proves. *)

open Harness

let solver =
  match Solver.find () with
  | Ok solver -> solver
  | Error message ->
      prerr_endline message;
      exit 1

let () =
  let database = Engine.context (Engine.create ()) in
  Database.load_standard (Engine.of_context database);
  List.iter
    (fun ((module_ : Path.module_), _) ->
      test
        (Printf.sprintf "%s checks cleanly and proves" (Path.show_module module_))
        (fun () ->
          let source = (Query.demand database Workspace.file module_).source in
          let report =
            List.iter (fun diagnostic -> fail "%s" (Diagnostic.render source diagnostic))
          in
          match Type_checker.diagnostics database module_ with
          | [] -> report (Prover.diagnostics database solver module_)
          | errors -> report errors))
    Standard_library.modules

let () = finish ()
