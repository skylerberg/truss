let run_forever_name = Language.Builtin_capability.show Run_forever

let names_run_forever (use : Syntax.capability_use) =
  match use.capability.kind with
  | Capability_path { path = { modules = []; last }; arguments = []; _ } ->
      last.text = run_forever_name
  | Capability_path _ | Self_capabilities _ | Associated_capabilities _ | Generic_capability _ ->
      false

let contains_run_forever (uses : Types.capability_set) =
  List.exists
    (fun capability -> Types.find_base capability = Built_in Run_forever)
    (Types.list_capabilities uses)

let cover_use (use : Syntax.capability_use) : Core.origin Catalog.range =
  {
    covering =
      Core.Written use.capability.id
      :: List.map
           (fun (bound : Syntax.bound_condition) -> Core.Written bound.id)
           (Option.value use.unless ~default:[])
      @ List.map (fun (value : Syntax.expression) -> Core.Written value.id) use.unless_values;
  }

let find_siblings (signature : Syntax.signature) (clause : Syntax.clause) uses index :
    Core.origin Catalog.siblings =
  match uses with
  | [ _ ] -> Alone { clause = Written clause.id; is_only_clause = signature.clauses = [ clause ] }
  | _ when index = 0 -> Next (cover_use (List.nth uses 1))
  | _ -> Previous (cover_use (List.nth uses (index - 1)))

let list_run_forever_entries (signature : Syntax.signature) =
  List.concat_map
    (fun (clause : Syntax.clause) ->
      match clause.kind with
      | Uses uses ->
          List.concat
            (List.mapi
               (fun index use -> if names_run_forever use then [ (clause, uses, index) ] else [])
               uses)
      | Requires _ | Ensures _ | Decreases _ | Cost _ | Clause_error -> [])
    signature.clauses

let find (lookups : Lookups.t) (key : Resolve.Names.key) (definition : Syntax.definition) =
  let names = lookups.interface.names in
  let declares_run_forever () =
    match Interface.Impls.read_signature lookups.interface key.path with
    | Some (signature : Types.signature) -> contains_run_forever signature.uses
    | None ->
        Compiler_bug.raise_bug ~stage:"Usage" "%s has a body and no signature" (Path.show key.path)
  in
  match ((names.read_declaration key).kind, definition.kind) with
  | (Function | Method), Function { signature; _ }
    when declares_run_forever ()
         && not (lookups.uses_run_forever key || lookups.is_recursive key.path) -> (
      match list_run_forever_entries signature with
      | [ (clause, uses, index) ] ->
          Some
            (Catalog.Usage.describe
               (Unused_run_forever
                  {
                    function_ = key.path;
                    entry = cover_use (List.nth uses index);
                    siblings = find_siblings signature clause uses index;
                  }))
      | [] | _ :: _ :: _ -> None)
  | _ -> None
