(* The tests of the standard library's source: each module checks through
   every stage with no diagnostic. *)

open Harness

let () =
  let database = Engine.context (Engine.create ()) in
  Database.load_standard (Engine.of_context database);
  List.iter
    (fun ((module_ : Path.module_), _) ->
      test
        (Printf.sprintf "%s checks cleanly" (Path.show_module module_))
        (fun () ->
          let source = (Query.demand database Workspace.file module_).source in
          List.iter
            (fun diagnostic -> fail "%s" (Diagnostic.render source diagnostic))
            (Type_checker.diagnostics database module_)))
    Standard_library.modules

let () = finish ()
