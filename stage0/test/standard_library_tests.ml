(* The tests of the standard library's source: each module parses, resolves,
   and checks with no diagnostic. See TYPECHECKER.md, "The prelude". *)

open Harness

let database () =
  let database = Query.create () in
  List.iter
    (fun (module_, text) -> Query.set database Workspace.file_text module_ text)
    Standard_library.modules;
  Query.set database Workspace.packages Standard_library.package
    {
      name = Standard_library.package;
      dependencies = [];
      modules = List.map fst Standard_library.modules;
    };
  database

let show (diagnostic : Diagnostic.t) source = Diagnostic.render source diagnostic

let () =
  let database = database () in
  List.iter
    (fun ((module_ : Path.module_), _) ->
      test
        (Printf.sprintf "%s checks cleanly" (Path.show_module module_))
        (fun () ->
          let file = Query.demand database Workspace.file module_ in
          let diagnostics =
            file.diagnostics
            @ Resolve.diagnostics database module_
            @ Interface.diagnostics database module_
            @ Infer.diagnostics database module_
            @ Patterns.file_diagnostics database module_
            @ Usage.file_diagnostics database module_
            @ Ownership.file_diagnostics database module_
          in
          List.iter (fun diagnostic -> fail "%s" (show diagnostic file.source)) diagnostics))
    Standard_library.modules

let () = finish ()
