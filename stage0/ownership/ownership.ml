(* The ownership check: moves, loans, and views, checked within each
   function. It prevents use after move, dangling views, mutation of a
   borrowed place, and data races.

   The check reads a definition's core form. [Graph] builds the control-flow
   graph of the body. [Moves] and [Views] run dataflow analyses on it, and
   [Yield_rules] checks the rules on [yield]. *)

type pulling = Yield_rules.pulling = Pullable | Yields_mut | Recursive | Yields_places

let pullable = Yield_rules.pullable

type result = {
  diagnostics : Syntax.diagnostic list;
  moves : Core.id list;
  disjoint : (Core.origin * Core.origin) list;
}

(* The inputs of the check of one definition: a new context, the core form,
   the lowered interface, and whether the definition is executable. A
   specification-only function is never executed, so it has no moves or
   borrows to check. [None] if the definition has no core form. *)
let inputs database (key : Resolve.Names.key) =
  match
    ( Query.demand database Infer.core key,
      Query.demand database Resolve.Names.spans key,
      Query.demand database Resolve.Names.marks key,
      Query.demand database Interface.Environment.lowered_interface key )
  with
  | Some form, Some spans, Some marks, Some lowered ->
      let context : Context.context =
        {
          database;
          bounds =
            (fun parameter -> Option.value ~default:[] (List.assoc_opt parameter lowered.bounds));
          spans;
          marks;
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
          moves = [];
          must_be_disjoint = [];
        }
      in
      Context.collect context form.definition;
      let executable =
        match lowered.interface with
        | Function_interface signature | Theorem_interface signature ->
            not signature.specification_only
        | _ -> true
      in
      Some (context, form, lowered, executable)
  | _ -> None

(* The result of the dataflow analyses of one definition. *)
type analysis = {
  reported : Syntax.diagnostic list;
  moved : Core.id list;
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
        (fun ((context : Context.context), (form : Core.t), _, executable) ->
          let task_hazard =
            if executable then
              match
                Graph.of_definition ~plain:(Context.plain context)
                  ~is_view:(Context.is_view context)
                  ~holds_function:(Context.holds_function context)
                  ~stores_function:(Context.stores_function context) form.definition
              with
              | Some graph ->
                  Moves.check context graph;
                  Views.check context graph
              | None -> None
            else None
          in
          {
            reported = context.diagnostics;
            moved = context.moves;
            must_be_disjoint = context.must_be_disjoint;
            task_hazard;
          })
        (inputs database key))

(* [None] if the definition has no core form. *)
let check database (key : Resolve.Names.key) : result option =
  match (inputs database key, Query.demand database analysis key) with
  | Some (context, form, lowered, executable), Some analyzed ->
      if executable then begin
        Yield_rules.check_cursors context form.definition;
        Yield_rules.check_concurrent_loops context form.definition ~task_hazard:(fun path ->
            Option.map
              (fun (callee : analysis) -> callee.task_hazard)
              (Option.bind
                 (Query.demand database Interface.Summary.key path)
                 (Query.demand database analysis)));
        (* A lending method yields exactly once on every path. The report
           is at the method's name. *)
        match
          (form.definition, lowered.interface, Query.demand database Resolve.Names.definition key)
        with
        | ( Function { body = Some body; _ },
            Function_interface { output = Lends _; _ },
            Some
              {
                kind =
                  Function { signature = { name = Plain_name name | Member_name (_, name); _ }; _ };
                _;
              } ) ->
            Yield_rules.check_yields_once context body ~name:name.span
        | _ -> ()
      end;
      Some
        {
          diagnostics =
            List.sort_uniq
              (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
                compare (left.span, left.message) (right.span, right.message))
              (analyzed.reported @ context.diagnostics);
          moves = List.sort_uniq compare analyzed.moved;
          (* Two rules can report the same pair, in either order, so the
             pairs are normalized and deduplicated. *)
          disjoint =
            List.sort_uniq compare
              (List.map
                 (fun (first, second) -> (min first second, max first second))
                 analyzed.must_be_disjoint);
        }
  | _ -> None

let ownership =
  Query.query ~name:"ownership" ~phase:Phases.bodies ~show:Resolve.Names.show_key ~saved:true
    ~about:(fun (key : Resolve.Names.key) ->
      Some { Query.path = key.path; part = Some "ownership" })
    check

let diagnostics database module_ =
  Resolve.Names.per_definition database module_ (fun key ->
      match Query.demand database ownership key with
      | Some result -> result.diagnostics
      | None -> [])
