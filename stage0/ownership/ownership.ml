(* Moves, loans, and views, within each function.

   The check reads a definition's core form. [Graph] builds the control-flow
   graph of the body. [Moves] and [Views] run their analyses on it, and
   [Yield_rules] checks the rules on [yield]. *)

type pulling = Yield_rules.pulling = Pullable | Yields_mut | Recursive | Yields_places

let pullable = Yield_rules.pullable

type result = {
  diagnostics : Diagnostic.t list;
  moves : Core.id list;
  obligations : Checked.obligation list;
}

(* [None] if the definition has no core form. *)
let check database (key : Resolve.Names.key) : result option =
  match
    ( Query.demand database Infer.core key,
      Query.demand database Resolve.Names.spans key,
      Query.demand database Resolve.Names.text key,
      Query.demand database Interface.Environment.lowered key )
  with
  | Some form, Some spans, Some text, Some lowered ->
      let context : Context.context =
        {
          database;
          bounds =
            (fun parameter -> Option.value ~default:[] (List.assoc_opt parameter lowered.bounds));
          spans;
          text;
          names = Hashtbl.create 32;
          kinds = Hashtbl.create 32;
          types = Hashtbl.create 32;
          parameters = [];
          mut_parameters = [];
          variables = [];
          diagnostics = [];
          moves = [];
          disjoint = [];
        }
      in
      Context.collect context form.definition;
      (* A function for specifications only never runs, so it moves and
         borrows nothing. *)
      let runs =
        match lowered.interface with
        | Function_interface signature | Theorem_interface signature ->
            not signature.specification_only
        | _ -> true
      in
      (if runs then
         match
           Graph.of_definition ~plain:(Context.plain context) ~is_view:(Context.is_view context)
             form.definition
         with
         | Some graph ->
             Moves.check context graph;
             Views.check context graph
         | None -> ());
      if runs then begin
        Yield_rules.check_pulls context form.definition;
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
            Yield_rules.check_lends context body ~name:name.span
        | _ -> ()
      end;
      Some
        {
          diagnostics =
            List.sort_uniq
              (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
                compare (left.span, left.message) (right.span, right.message))
              context.diagnostics;
          moves = List.sort_uniq compare context.moves;
          obligations =
            List.rev_map
              (fun (first, second) -> Checked.Disjoint { first; second })
              context.disjoint;
        }
  | _ -> None

let ownership =
  Query.query ~name:"ownership" ~phase:Bodies ~show:Resolve.Names.show_key ~saved:true
    ~about:(fun (key : Resolve.Names.key) ->
      Some { Query.path = key.path; part = Some "ownership" })
    check

let diagnostics database module_ =
  Resolve.Names.per_definition database module_ (fun key ->
      match Query.demand database ownership key with
      | Some result -> result.diagnostics
      | None -> [])
