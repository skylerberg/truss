let is_public (lookups : Lookups.t) (module_ : Path.module_) name =
  match lookups.interface.names.find module_ name with
  | Some entry -> Resolve.Names.is_public entry.visibility
  | None -> true

let is_visible_to_other_packages (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Top { module_; name } -> module_ = Intrinsic.module_ || is_public lookups module_ name
  | Method { owner = Top { module_; name }; _ }
  | Member_constant { owner = Top { module_; name }; _ } -> (
      is_public lookups module_ name
      &&
      match Resolve.Names.find_definition lookups.interface.names path with
      | Some (_, definition) -> Resolve.Names.is_public definition.visibility
      | None -> true)
  | Method _ | Member_constant _ | Impl _ | Derived _ | Test _ | Law_proof _ -> true
  | Unresolved _ -> false

let is_called_from_other_packages (state : State.state) =
  match state.lookups.interface.names.find_container state.key with
  | None -> Resolve.Names.is_public state.definition.visibility
  | Some container -> (
      match Interface.Definition.read_interface state.lookups.interface container.path with
      | Some (Trait_interface _) -> is_visible_to_other_packages state.lookups container.path
      | Some (Impl_interface impl) -> (
          is_visible_to_other_packages state.lookups impl.implements.trait
          &&
          match impl.for_type with
          | Types.Named { path; _ } -> is_visible_to_other_packages state.lookups path
          | _ -> true)
      | _ -> false)

let check_clauses (state : State.state) (name : Syntax.name) clauses =
  let requires_and_costs =
    List.filter_map
      (fun (clause : Syntax.clause) ->
        match clause.kind with
        | Requires _ | Cost _ -> Some (State.read_span state clause.id)
        | Ensures _ | Uses _ | Decreases _ | Clause_error -> None)
      clauses
  in
  if is_called_from_other_packages state && requires_and_costs <> [] then begin
    let named id (path : Path.t) =
      let span = State.read_span state id in
      if
        List.exists
          (fun (clause : Source.Definition_span.t) ->
            clause.start <= span.start && span.stop <= clause.stop)
          requires_and_costs
        && not (is_visible_to_other_packages state.lookups path)
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

let check (state : State.state) =
  match state.definition.kind with
  | Syntax.Function { signature; _ } | Method_declaration signature ->
      check_clauses state (Resolve.Names.extract_signature_name signature) signature.clauses
  | Theorem { name; clauses; _ } -> check_clauses state name clauses
  | _ -> ()
