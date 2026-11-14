(* The ownership check: moves, loans, and views, checked within each
   function. It prevents use after move, dangling views, mutation of a
   borrowed place, and data races. *)

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
      let mir = Query.demand database Mir.mir key in
      Option.iter (Context.collect context) mir;
      Some (context, lowered, mir)
  | _ -> None

(* The check of one definition: moves, loans, views, and the rules on
   loops whose iterations run at the same time. It reads the definition's
   MIR and the signatures the MIR names, and no other definition's body.
   Two rules can report the same pair of parts that must be disjoint, in
   either order, so the pairs are normalized and deduplicated. [None] if
   the definition has no interface. *)
let check database (key : Resolve.Names.key) : result option =
  Option.map
    (fun ((context : Context.context), (lowered : Interface.Environment.lowered_interface), mir) ->
      Option.iter
        (fun (mir : Mir.t) ->
          let returns =
            match lowered.interface with
            | Function_interface _ | Theorem_interface _ -> true
            | _ -> false
          in
          (* One move analysis of each body, which both checks read. *)
          let analysed =
            List.map
              (fun body -> (body, Move_rules.analyse context body))
              (mir.body :: Array.to_list mir.lambdas)
          in
          let moves body = List.assq body analysed in
          Move_rules.check context mir ~moves ~returns;
          Borrows.check context ~moves ~returns mir;
          Task_loops.check context mir)
        mir;
      {
        diagnostics =
          List.sort_uniq
            (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
              compare (left.span, left.message) (right.span, right.message))
            context.diagnostics;
        disjoint =
          List.sort_uniq compare
            (List.map
               (fun (first, second) -> (min first second, max first second))
               context.must_be_disjoint);
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
