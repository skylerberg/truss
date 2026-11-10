(* The ownership check on the core form: moves, loans, and views of one
   definition. *)

type result = {
  diagnostics : Diagnostic.t list;
  moves : Core.id list;  (** The [Use] nodes that move a place. *)
  disjoint : (Core.origin * Core.origin) list;
      (** Pairs of index calls or slices of one collection, by origin, that must select different
          elements. The prover shows that they do. *)
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
      let context : Moves.context =
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
          diagnostics = [];
          moves = [];
          disjoint = [];
        }
      in
      Moves.collect context form.definition;
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
           Graph.of_definition ~plain:(Moves.plain context) ~is_view:(Moves.is_view context)
             form.definition
         with
         | Some graph ->
             Moves.check context graph;
             Views.check context graph
         | None -> ());
      Some
        {
          diagnostics =
            List.sort_uniq
              (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
                compare (left.span, left.message) (right.span, right.message))
              context.diagnostics;
          moves = List.sort_uniq compare context.moves;
          disjoint = List.rev context.disjoint;
        }
  | _ -> None
