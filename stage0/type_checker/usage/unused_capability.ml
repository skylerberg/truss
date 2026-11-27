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

let is_checked (lookups : Lookups.t) (key : Resolve.Names.key) =
  key.ordinal = 0
  && Option.is_none (lookups.interface.names.find_container key)
  &&
  match (lookups.interface.names.read_declaration key).kind with
  | Function | Method | Test -> true
  | Type | Trait | Capability | Constant | Member_constant | Theorem | Impl | Law_proof -> false

let list_bases capabilities = List.map Types.find_base (Types.list_capabilities capabilities)

let find (lookups : Lookups.t) (key : Resolve.Names.key) (definition : Syntax.definition) resolved =
  let entries =
    match definition.kind with
    | Function { signature; _ } -> list_signature_entries signature
    | Test { name; uses; _ } -> list_test_entries name uses
    | _ -> []
  in
  match entries with
  | _ :: _ when is_checked lookups key ->
      let used = list_bases (lookups.read_capability_uses key) in
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
