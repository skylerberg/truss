module Names = Resolve.Names

let public (lookups : Lookups.t) (module_ : Path.module_) name =
  match lookups.interface.names.find module_ name with
  | Some entry -> Names.is_public entry.visibility
  | None -> true

let visible_to_other_packages (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Top { module_; name } -> module_ = Intrinsic.module_ || public lookups module_ name
  | Method { owner = Top { module_; name }; _ }
  | Member_constant { owner = Top { module_; name }; _ } -> (
      public lookups module_ name
      &&
      match Resolve.Names.definition_of_path lookups.interface.names path with
      | Some (_, definition) -> Names.is_public definition.visibility
      | None -> true)
  | Method _ | Member_constant _ | Impl _ | Derived _ | Test _ | Law_proof _ -> true
  | Unresolved _ -> false

let called_from_other_packages (state : State.state) =
  match state.lookups.interface.names.container state.key with
  | None -> Names.is_public state.definition.visibility
  | Some container -> (
      match Interface.Definition.read_interface state.lookups.interface container.path with
      | Some (Trait_interface _) -> visible_to_other_packages state.lookups container.path
      | Some (Impl_interface impl) -> (
          visible_to_other_packages state.lookups impl.implements.trait
          &&
          match impl.for_type with
          | Types.Named { path; _ } -> visible_to_other_packages state.lookups path
          | _ -> true)
      | _ -> false)

let check (state : State.state) =
  let clauses, name =
    match state.definition.kind with
    | Function { signature; _ } | Method_declaration signature ->
        (signature.clauses, Names.signature_name signature)
    | Theorem { name; clauses; _ } -> (clauses, name)
    | _ -> ([], { text = ""; id = state.definition.id })
  in
  let requires_and_costs =
    List.filter_map
      (fun (clause : Syntax.clause) ->
        match clause.kind with
        | Requires _ | Cost _ -> Some (State.read_span state clause.id)
        | Ensures _ | Uses _ | Decreases _ | Clause_error -> None)
      clauses
  in
  if called_from_other_packages state && requires_and_costs <> [] then begin
    let named id (path : Path.t) =
      let span = State.read_span state id in
      if
        List.exists
          (fun (clause : Source.Definition_span.t) ->
            clause.start <= span.start && span.stop <= clause.stop)
          requires_and_costs
        && not (visible_to_other_packages state.lookups path)
      then
        let hidden = Path.show path in
        State.report state Private_in_public span
          (Printf.sprintf
             "Other packages can call `%s`, so the proofs of its callers there read this clause, \
              and those packages cannot see `%s`. Make `%s` public, or state the clause with \
              functions and constants that are public."
             name.text hidden hidden)
    in
    Array.iteri
      (fun id (call : Tables.call option) ->
        match call with Some { callee = Function { path; _ }; _ } -> named id path | _ -> ())
      state.tables.calls;
    Array.iteri
      (fun id (resolution : Tables.resolution option) ->
        match resolution with Some (Global { path; _ }) -> named id path | _ -> ())
      state.tables.resolutions
  end
