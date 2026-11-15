type result = {
  diagnostics : Syntax.diagnostic list;
  must_be_disjoint : (Core.origin * Core.origin) list;
}

let inputs database (key : Resolve.Names.key) =
  match
    ( Query.demand database Resolve.Names.spans key,
      Query.demand database Interface.Environment.lowered_interface key )
  with
  | Some spans, Some lowered ->
      let context : Context.context =
        {
          database;
          bounds =
            (fun parameter -> Option.value ~default:[] (List.assoc_opt parameter lowered.bounds));
          spans;
          mode_keywords = Hashtbl.create 8;
          names = Hashtbl.create 32;
          kinds = Hashtbl.create 32;
          types = Hashtbl.create 32;
          parameters = [];
          implements_capability =
            (match Query.demand database Resolve.Names.container key with
            | Some container -> (
                match Interface.Impls.impl_interface database container.path with
                | Some (impl : Types.impl_interface) -> (
                    match
                      Query.demand database Interface.Environment.trait_interface
                        impl.implements.trait
                    with
                    | Some trait -> trait.is_capability
                    | None -> false)
                | None -> false)
            | None -> false);
          mutable_locals = [];
          diagnostics = [];
          must_be_disjoint = [];
        }
      in
      let mir =
        if Interface.Environment.is_specification lowered.interface then None
        else Query.demand database Mir.graph key
      in
      Option.iter (Context.collect context) mir;
      Some (context, lowered, mir)
  | _ -> None

let check database (key : Resolve.Names.key) : result option =
  Option.map
    (fun ((context : Context.context), (lowered : Interface.Environment.lowered_interface), mir) ->
      Option.iter
        (fun (mir : Mir.Graph.t) ->
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
      {
        diagnostics =
          List.sort_uniq
            (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
              compare (left.span, left.message) (right.span, right.message))
            context.diagnostics;
        must_be_disjoint = List.sort_uniq compare context.must_be_disjoint;
      })
    (inputs database key)

let ownership =
  Query.query ~name:"ownership" ~phase:Phases.bodies ~show:Resolve.Names.show_key ~saved:true
    ~about:(fun (key : Resolve.Names.key) ->
      Some { Query.path = key.path; part = Some "ownership" })
    check

let diagnostics database file =
  Resolve.Names.per_definition database file (fun key ->
      match Query.demand database ownership key with
      | Some result -> result.diagnostics
      | None -> [])
