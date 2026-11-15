module Lookups = Lookups

type result = {
  diagnostics : Syntax.diagnostic list;
  must_be_disjoint : (Core.origin * Core.origin) list;
}

let implements_capability (lookups : Lookups.t) key =
  match lookups.interface.names.container key with
  | Some (container : Resolve.Names.key) -> (
      match Interface.Impls.impl_interface lookups.interface container.path with
      | Some impl -> (
          match Interface.Definition.trait_interface lookups.interface impl.implements.trait with
          | Some trait -> trait.is_capability
          | None -> false)
      | None -> false)
  | None -> false

let check (lookups : Lookups.t) (key : Resolve.Names.key) : result option =
  match (lookups.interface.names.spans key, lookups.interface.lowered_interface key) with
  | Some spans, Some lowered ->
      let context : Context.context =
        {
          lookups;
          bounds =
            (fun parameter ->
              Option.value ~default:[] (List.assoc_opt parameter lowered.scope.bounds));
          spans;
          mode_keywords = Hashtbl.create 8;
          names = Hashtbl.create 32;
          binding_modes = Hashtbl.create 32;
          types = Hashtbl.create 32;
          parameters = [];
          implements_capability = implements_capability lookups key;
          mutable_locals = [];
          diagnostics = [];
          must_be_disjoint = [];
        }
      in
      let mir =
        if Interface.Environment.is_specification lowered.interface then None else lookups.graph key
      in
      Option.iter
        (fun (mir : Mir.Graph.t) ->
          Context.collect context mir;
          let returns_to_caller =
            match lowered.interface with Function_interface _ -> true | _ -> false
          in
          let move_analyses =
            List.map
              (fun body -> (body, Move_rules.analyse context body))
              (mir.body :: Array.to_list mir.lambdas)
          in
          let moves body = List.assq body move_analyses in
          Move_rules.check context mir ~moves ~returns_to_caller;
          Borrows.check context ~moves ~returns_to_caller mir;
          Task_loops.check context mir)
        mir;
      Some
        {
          diagnostics =
            List.sort
              (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
                compare (left.span, left.message) (right.span, right.message))
              context.diagnostics;
          must_be_disjoint = List.sort_uniq compare context.must_be_disjoint;
        }
  | _ -> None
