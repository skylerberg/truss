module Lookups = Lookups

type result = {
  diagnostics : Catalog.description list;
  must_be_disjoint : (Core.id list * Core.id list) list;
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

let collect_bare_names (definition : Syntax.definition) =
  let names = Hashtbl.create 16 in
  let rec visit_expression (value : Syntax.expression) =
    (match value.kind with
    | Name name -> Hashtbl.replace names value.id name.text
    | Self_value -> Hashtbl.replace names value.id "self"
    | _ -> ());
    Syntax_walk.visit_expression_parts ~on_expression:visit_expression ~on_statement:visit_statement
      value
  and visit_statement statement =
    Syntax_walk.visit_statement_parts ~on_expression:visit_expression ~on_statement:visit_statement
      statement
  in
  Syntax_walk.visit_definition ~on_statement:visit_statement visit_expression definition;
  names

let check_definition (lookups : Lookups.t) (key : Resolve.Names.key) : result =
  let elaborated = lookups.interface.read_elaborated_interface key in
  let scope = Interface.Impls.read_scope lookups.interface key in
  let context : Context.context =
    {
      lookups;
      list_bounds = Interface.Properties.Bounds.of_known scope.bounds;
      mode_keywords = Hashtbl.create 8;
      bare_names = lazy (collect_bare_names (lookups.interface.names.read_definition key));
      places_without_keyword = Hashtbl.create 8;
      names = Context.Local_table.create 32;
      origins = Context.Local_table.create 32;
      binding_modes = Context.Local_table.create 32;
      literal_views = Context.Local_table.create 4;
      owned_scrutinees = Context.Local_table.create 4;
      types = Context.Local_table.create 32;
      decided_types = Context.Type_table.create 16;
      parameters = [];
      implements_capability = implements_capability lookups key;
      is_constant = (match elaborated.interface with Constant_interface _ -> true | _ -> false);
      mutable_locals = [];
      diagnostics = [];
      must_be_disjoint = [];
    }
  in
  let check_graph (mir : Mir.Graph.t) ~returns_to_caller =
    Context.collect context mir ~mode_keywords:(lookups.list_mode_keywords key);
    let move_analyses =
      List.map
        (fun body -> (body, Move_rules.analyse context body))
        (mir.body :: Array.to_list mir.lambdas)
    in
    let read_moves body = List.assq body move_analyses in
    Move_rules.check context mir ~read_moves ~returns_to_caller;
    Borrows.check context ~read_moves ~returns_to_caller mir;
    Task_loops.check context mir;
    Lent_variants.check context mir
  in
  Option.iter
    (fun (code : Mir.code) ->
      List.iter
        (fun (origin, needs) -> Hashtbl.replace context.places_without_keyword origin needs)
        (lookups.list_places_without_keyword key);
      if not (Interface.Definition.is_specification elaborated.interface) then
        check_graph code.graph
          ~returns_to_caller:
            (match elaborated.interface with
            | Function_interface _ | Constant_interface _ -> true
            | _ -> false);
      List.iter
        (fun (_, asserted) -> check_graph (Mir.expand asserted) ~returns_to_caller:false)
        (Mir.list_evaluated_asserts code.tree))
    (lookups.find_code key);
  {
    diagnostics = List.rev context.diagnostics;
    must_be_disjoint = List.sort_uniq compare context.must_be_disjoint;
  }

let check (lookups : Lookups.t) key =
  try check_definition lookups key
  with Interface.Properties.Recursion_limit diagnostic ->
    { diagnostics = [ Catalog.Typing.describe diagnostic ]; must_be_disjoint = [] }
