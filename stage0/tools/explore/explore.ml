let database =
  let database = Query.create () in
  List.iter (fun (module_, text) -> Query.set database Workspace.file_text module_ text) Standard_library.modules;
  Query.set database Workspace.packages Standard_library.package
    { name = Standard_library.package; dependencies = []; modules = List.map fst Standard_library.modules };
  database

let numbers : Path.module_ = { package = "standard"; modules = [ "numbers" ] }

let () =
  let path : Path.t = Impl { module_ = numbers; name = "Equal for Int64" } in
  match Query.demand database Interface.Summary.key path with
  | None -> print_endline "no key"
  | Some key -> (
      (match Query.demand database Resolve.Names.definition key with
      | Some d -> print_endline (Syntax_print.definition d)
      | None -> ());
      match Query.demand database Infer.checked key with
      | Some r ->
          Array.iteri
            (fun i c ->
              match c with
              | Some (c : Checked.call) -> (
                  match c.callee with
                  | Intrinsic { type_arguments; _ } ->
                      Printf.printf "call %d intrinsic [%s]\n" i (String.concat ", " (List.map Types.show_argument type_arguments))
                  | _ -> Printf.printf "call %d\n" i)
              | None -> ())
            r.checked.calls;
          Array.iteri (fun i t -> match t with Some t -> Printf.printf "  type %d: %s\n" i (Types.show t) | None -> ()) r.checked.types
      | None -> ())
