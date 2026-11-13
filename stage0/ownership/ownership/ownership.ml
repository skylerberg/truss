(* The ownership check: moves, loans, and views, checked within each
   function. It prevents use after move, dangling views, mutation of a
   borrowed place, and data races. *)

type pulling = Yield_rules.pulling = Pullable | Yields_mut | Recursive | Yields_places

let pullable = Yield_rules.pullable

type result = { diagnostics : Syntax.diagnostic list; disjoint : (Core.origin * Core.origin) list }

(* The inputs of the check of one definition: a new context, the lowered
   interface, and the MIR of the definition's code. A specification-only
   function never runs, so it has no MIR, and no moves or borrows to check.
   [None] if the definition has no interface. *)
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
          marks = Hashtbl.create 8;
          names = Hashtbl.create 32;
          kinds = Hashtbl.create 32;
          types = Hashtbl.create 32;
          parameters = [];
          yields =
            (match lowered.interface with
            | Function_interface { output = Yields _; _ } -> true
            | _ -> false);
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
      let mir = Query.demand database Mir.mir key in
      Option.iter (Context.collect context) mir;
      Some (context, lowered, mir)
  | _ -> None

(* The result of the dataflow analyses of one definition. *)
type analysis = {
  reported : Syntax.diagnostic list;
  must_be_disjoint : (Core.origin * Core.origin) list;
  task_hazard : Views.task_hazard option;
}

(* The dataflow analyses of a definition: moves, loans, and views. They
   read no other definition's analysis. The rules on [yield] read a
   callee's [task_hazard], so they demand this query, and two methods that
   loop over each other cannot form a query cycle. *)
let analysis =
  Query.query ~name:"ownership_analysis" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      Option.map
        (fun ((context : Context.context), (lowered : Interface.Environment.lowered_interface), mir)
           ->
          let task_hazard =
            Option.bind mir (fun mir ->
                let graph =
                  Graph.of_mir ~plain:(Context.plain context) ~is_view:(Context.is_view context)
                    ~holds_function:(Context.holds_function context)
                    ~stores_function:(Context.stores_function context)
                    ~returns:
                      (match lowered.interface with
                      | Function_interface _ | Theorem_interface _ -> true
                      | _ -> false)
                    ~is_var:(fun local -> List.mem local context.mutable_locals)
                    mir
                in
                Moves.check context graph;
                Views.check context graph)
          in
          {
            reported = context.diagnostics;
            must_be_disjoint = context.must_be_disjoint;
            task_hazard;
          })
        (inputs database key))

(* A definition's result: the diagnostics of its analysis and its checks,
   and the pairs its analysis needs disjoint. Two rules can report the same
   pair, in either order, so the pairs are normalized and deduplicated. *)
let result (context : Context.context) analyzed =
  {
    diagnostics =
      List.sort_uniq
        (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
          compare (left.span, left.message) (right.span, right.message))
        (analyzed.reported @ context.diagnostics);
    disjoint =
      List.sort_uniq compare
        (List.map
           (fun (first, second) -> (min first second, max first second))
           analyzed.must_be_disjoint);
  }

(* [None] if the definition has no interface. *)
let check database (key : Resolve.Names.key) : result option =
  match (inputs database key, Query.demand database analysis key) with
  | Some (context, lowered, Some mir), Some analyzed ->
      Yield_rules.check_cursors context mir;
      Yield_rules.check_concurrent_loops context mir ~task_hazard:(fun path ->
          Option.map
            (fun (callee : analysis) -> callee.task_hazard)
            (Option.bind
               (Query.demand database Interface.Summary.key path)
               (Query.demand database analysis)));
      (* A lending method yields exactly once on every path. The report is at
         the method's name. *)
      (match (lowered.interface, Query.demand database Resolve.Names.definition key) with
      | ( Function_interface { output = Lends _; _ },
          Some
            {
              kind =
                Function { signature = { name = Plain_name name | Member_name (_, name); _ }; _ };
              _;
            } ) ->
          Yield_rules.check_yields_once context mir.body ~name:name.span
      | _ -> ());
      Some (result context analyzed)
  | Some (context, _, None), Some analyzed -> Some (result context analyzed)
  | _ -> None

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
