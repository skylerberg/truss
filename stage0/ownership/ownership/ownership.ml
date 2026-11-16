module Lookups = Lookups

type result = {
  diagnostics : Diagnostic.in_definition list;
  must_be_disjoint : (Core.origin * Core.origin) list;
}

let implements_capability (lookups : Lookups.t) key =
  match lookups.interface.names.find_container key with
  | Some (container : Resolve.Names.key) -> (
      match Interface.Definition.find_impl_interface lookups.interface container.path with
      | Some impl ->
          (Interface.Definition.read_trait_interface lookups.interface impl.implements.trait)
            .is_capability
      | None -> false)
  | None -> false

let check (lookups : Lookups.t) (key : Resolve.Names.key) : result =
  let elaborated = lookups.interface.read_elaborated_interface key in
  let context : Context.context =
    {
      lookups;
      list_bounds =
        (fun parameter ->
          Option.value ~default:[] (List.assoc_opt parameter elaborated.scope.bounds));
      spans = lazy (lookups.interface.names.read_spans key);
      mode_keywords = Hashtbl.create 8;
      names = Context.Local_table.create 32;
      binding_modes = Context.Local_table.create 32;
      types = Context.Local_table.create 32;
      parameters = [];
      implements_capability = implements_capability lookups key;
      mutable_locals = [];
      diagnostics = [];
      must_be_disjoint = [];
    }
  in
  let mir =
    if Interface.Definition.is_specification elaborated.interface then None
    else lookups.find_graph key
  in
  Option.iter
    (fun (mir : Mir.Graph.t) ->
      Context.collect context mir;
      let returns_to_caller =
        match elaborated.interface with Function_interface _ -> true | _ -> false
      in
      let move_analyses =
        List.map
          (fun body -> (body, Move_rules.analyse context body))
          (mir.body :: Array.to_list mir.lambdas)
      in
      let read_moves body = List.assq body move_analyses in
      Move_rules.check context mir ~read_moves ~returns_to_caller;
      Borrows.check context ~read_moves ~returns_to_caller mir;
      Task_loops.check context mir)
    mir;
  {
    diagnostics =
      List.sort
        (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
          compare (left.span, left.message) (right.span, right.message))
        context.diagnostics;
    must_be_disjoint = List.sort_uniq compare context.must_be_disjoint;
  }
