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
        | Requires _ | Cost _ -> Some (State.read_span state clause.id)
        | Ensures _ | Uses _ | Decreases _ | Clause_error -> None)
      clauses
  in
  if is_called_from_other_packages state && requires_and_costs <> [] then begin
    let record_name id (path : Path.t) =
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

let check_invariants (state : State.state) (form : Core.t) =
  match form.definition with
  | Type { invariants; _ }
    when (state.lookups.interface.names.read_declaration state.key).visibility = Public_opaque ->
      let owner = Path.show state.key.path in
      let report_hidden origin path =
        if not (is_visible_to_other_packages state.lookups path) then
          let hidden = Path.show path in
          State.report state Private_in_public
            (State.read_span state (Core_walk.locate_origin origin))
            (Printf.sprintf
               "This invariant reads no field of `%s`, so proofs in other packages assume it, and \
                those packages cannot see `%s`. Make `%s` public, or state the invariant with \
                functions and constants that are public."
               owner hidden hidden)
      in
      List.iter
        (fun (invariant : Core.condition) ->
          if not (Core_walk.reads_fields ~owner:state.key.path invariant.value) then
            Core_walk.walk_expression
              {
                Core_walk.ignore_all with
                expression =
                  (fun (node : Core.expression) ->
                    match node.kind with
                    | Call { callee = { target = Function { path; _ }; _ }; _ } ->
                        report_hidden node.origin path
                    | Call { callee = { target = Trait_method { trait; _ }; _ }; _ } ->
                        report_hidden node.origin trait.trait
                    | _ -> ());
                place =
                  (function Constant { path; origin; _ } -> report_hidden origin path | _ -> ());
              }
              invariant.value)
        invariants
  | _ -> ()

let check (state : State.state) =
  match state.definition.kind with
  | Syntax.Function { signature; _ } | Method_declaration signature ->
      check_clauses state (Resolve.Names.extract_signature_name signature) signature.clauses
  | Theorem { name; clauses; _ } -> check_clauses state name clauses
  | _ -> ()
