type written_entry = {
  capability : Syntax.capability_reference;
  entry : Core.origin Catalog.range;
  siblings : Core.origin Catalog.siblings;
}

let cover_use (use : Syntax.capability_use) : Core.origin Catalog.range =
  {
    covering =
      Core.Written use.capability.id
      :: List.map
           (fun (bound : Syntax.bound_condition) -> Core.Written bound.id)
           (Option.value use.unless ~default:[])
      @ List.map (fun (value : Syntax.expression) -> Core.Written value.id) use.unless_values;
  }

let list_signature_entries (signature : Syntax.signature) =
  List.concat_map
    (fun (clause : Syntax.clause) ->
      match clause.kind with
      | Uses uses ->
          let entries = List.map cover_use uses in
          List.mapi
            (fun index (use : Syntax.capability_use) ->
              {
                capability = use.capability;
                entry = List.nth entries index;
                siblings =
                  (match uses with
                  | [ _ ] ->
                      Alone
                        {
                          clause = Written clause.id;
                          is_only_clause = signature.clauses = [ clause ];
                        }
                  | _ -> Catalog.read_entry_siblings entries index);
              })
            uses
      | Requires _ | Ensures _ | Decreases _ | Modifies _ | Cost _ | Clause_error -> [])
    signature.clauses

let list_test_entries (name : Syntax.string_literal)
    (capabilities : Syntax.capability_reference list) =
  let entries =
    List.map
      (fun (capability : Syntax.capability_reference) : Core.origin Catalog.range ->
        { covering = [ Written capability.id ] })
      capabilities
  in
  List.mapi
    (fun index capability ->
      {
        capability;
        entry = List.nth entries index;
        siblings =
          (match capabilities with
          | [ _ ] -> Previous { covering = [ Written name.id ] }
          | _ -> Catalog.read_entry_siblings entries index);
      })
    capabilities

let contains_todo (definition : Syntax.definition) =
  let has_todo = ref false in
  let rec visit_expression (value : Syntax.expression) =
    (match value.kind with Todo -> has_todo := true | _ -> ());
    Syntax_walk.visit_expression_parts ~on_expression:visit_expression ~on_statement:visit_statement
      value
  and visit_statement written =
    Syntax_walk.visit_statement_parts ~on_expression:visit_expression ~on_statement:visit_statement
      written
  in
  Syntax_walk.visit_definition ~on_statement:visit_statement visit_expression definition;
  !has_todo

let is_checked (lookups : Lookups.t) (key : Resolve.Names.key) =
  Option.is_none (lookups.interface.names.find_container key)
  &&
  match (lookups.interface.names.read_declaration key).kind with
  | Function | Method | Test -> true
  | Type | Trait | Capability | Constant | Member_constant | Theorem | Impl | Law_proof -> false

let list_bases capabilities = List.map Types.find_base (Types.list_capabilities capabilities)

let declares_only_named_capabilities (lookups : Lookups.t) path =
  match Interface.Impls.read_signature lookups.interface path with
  | Some signature ->
      List.for_all
        (function Types.Built_in _ | Capability _ -> true | _ -> false)
        (list_bases signature.uses)
  | None -> false

let list_used_bases (lookups : Lookups.t) (key : Resolve.Names.key) uses =
  match lookups.list_recursion_group key.path with
  | [] -> List.concat_map (fun (use : Infer.capability_use) -> list_bases use.capabilities) uses
  | group ->
      let members =
        (key.path, uses)
        :: List.filter_map
             (fun path ->
               if Path.equal path key.path then None
               else
                 match lookups.interface.names.find_key path with
                 | Some member when is_checked lookups member ->
                     Option.map (fun uses -> (path, uses)) (lookups.find_capability_uses member)
                 | Some _ | None -> None)
             group
      in
      let is_refined callee =
        List.mem_assoc callee members && declares_only_named_capabilities lookups callee
      in
      let used = Hashtbl.create 8 in
      List.iter
        (fun (path, uses) ->
          Hashtbl.replace used path
            (Types.Built_in Run_forever
            :: List.concat_map
                 (fun (use : Infer.capability_use) ->
                   match use.callee with
                   | Some callee when is_refined callee -> []
                   | Some _ | None -> list_bases use.capabilities)
                 uses))
        members;
      let rec settle () =
        let is_changed = ref false in
        List.iter
          (fun (path, uses) ->
            List.iter
              (fun (use : Infer.capability_use) ->
                match use.callee with
                | Some callee when is_refined callee ->
                    let callee_used = Hashtbl.find used callee in
                    List.iter
                      (fun base ->
                        let caller_used = Hashtbl.find used path in
                        if List.mem base callee_used && not (List.mem base caller_used) then begin
                          Hashtbl.replace used path (base :: caller_used);
                          is_changed := true
                        end)
                      (list_bases use.capabilities)
                | Some _ | None -> ())
              uses)
          members;
        if !is_changed then settle ()
      in
      settle ();
      Hashtbl.find used key.path

let find (lookups : Lookups.t) (key : Resolve.Names.key) (definition : Syntax.definition) resolved =
  let entries =
    match definition.kind with
    | Function { signature; _ } -> list_signature_entries signature
    | Test { name; uses; _ } -> list_test_entries name uses
    | _ -> []
  in
  match (entries, lookups.find_capability_uses key) with
  | _ :: _, Some uses when is_checked lookups key && not (contains_todo definition) ->
      let used = list_used_bases lookups key uses in
      let context =
        Interface.Elaborator.create lookups.interface resolved
          (Interface.Impls.read_scope lookups.interface key)
      in
      let list_declared_bases (entry : written_entry) =
        list_bases
          (Interface.Impls.normalize_capabilities lookups.interface
             ~list_bounds:(Interface.Elaborator.list_known_bounds context)
             (Types.make_capability_set
                (Interface.Elaborator.elaborate_capability context entry.capability)))
      in
      List.filter_map
        (fun (entry : written_entry) ->
          let declared = list_declared_bases entry in
          let is_broken =
            List.exists (function Types.Capability_error _ -> true | _ -> false) declared
          in
          if is_broken || List.exists (fun base -> List.mem base used) declared then None
          else
            Some
              (Catalog.Usage
                 (Unused_capability
                    { definition = key.path; entry = entry.entry; siblings = entry.siblings })))
        entries
  | _ -> []
