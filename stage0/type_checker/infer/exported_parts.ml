let is_public (lookups : Lookups.t) (module_ : Path.module_) name =
  match lookups.interface.names.find module_ name with
  | Some entry -> Resolve.Names.is_public entry.visibility
  | None -> true

let is_declared_public (lookups : Lookups.t) path =
  match lookups.interface.names.find_key path with
  | Some key -> Resolve.Names.is_public (lookups.interface.names.read_declaration key).visibility
  | None -> true

let rec is_visible_to_other_packages (lookups : Lookups.t) (path : Path.t) =
  match path with
  | Top { module_; name } -> module_ = Well_known.intrinsic_module || is_public lookups module_ name
  | Method { owner; _ } | Member_constant { owner; _ } ->
      is_visible_to_other_packages lookups owner && is_declared_public lookups path
  | Default { owner; _ } -> is_visible_to_other_packages lookups owner
  | Impl _ -> is_declared_public lookups path
  | Derived _ | Test _ | Law_proof _ -> true
  | Unresolved _ -> false

let is_called_from_other_packages (state : State.state) =
  Resolve.Names.is_public (state.lookups.interface.names.read_declaration state.key).visibility

let check_clauses (state : State.state) (name : Syntax.name) clauses =
  let requires_and_costs =
    List.filter_map
      (fun (clause : Syntax.clause) ->
        match clause.kind with
        | Requires _ | Cost _ -> Some clause.id
        | Ensures _ | Uses _ | Decreases _ | Modifies _ | Clause_error -> None)
      clauses
  in
  if is_called_from_other_packages state && requires_and_costs <> [] then begin
    let record_name id (path : Path.t) =
      if
        List.exists (fun clause -> State.contains state ~outer:clause ~inner:id) requires_and_costs
        && not (is_visible_to_other_packages state.lookups path)
      then
        State.report state
          (Hidden_in_public_clause { at = Written id; name = name.text; hidden = path })
    in
    Array.iteri
      (fun id (elaboration : Tables.elaboration option) ->
        match elaboration with
        | Some (Call { callee = Function { path; _ }; _ }) -> record_name id path
        | _ -> ())
      state.tables.elaborations;
    Array.iteri
      (fun id (resolution : Tables.resolution option) ->
        match resolution with Some (Global { path; _ }) -> record_name id path | _ -> ())
      state.tables.resolutions
  end

let check (state : State.state) =
  match state.definition.kind with
  | Syntax.Function { signature; _ } | Method_declaration signature ->
      check_clauses state (Resolve.Names.extract_signature_name signature) signature.clauses
  | Theorem { name; clauses; _ } -> check_clauses state name clauses
  | _ -> ()
