let rec has_valid_value (context : State.context) ?(entered = []) (ty : Types.ty) =
  match (Types.find_builtin ty, ty) with
  | ( Some
        ( Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64 | Float32 | Float64 | Bool
        | Character | Unit | Integer ),
      _ )
  | None, Integer ->
      true
  | Some (Never | Array | Storage | View | Handle | Shared), _ -> false
  | None, Named { path; arguments } when not (List.exists (Path.equal path) entered) -> (
      let have_values fields =
        List.for_all
          (fun (field : Types.field) ->
            has_valid_value context ~entered:(path :: entered) field.field_type)
          fields
      in
      Option.is_none (Validity.find_invariants context ty)
      &&
      match Interface.Definition.find_interface context.lookups.interface path with
      | Some (Type_interface ({ shape = Record _; _ } as declared)) ->
          Option.fold ~none:false ~some:have_values (Types.instantiate_fields declared arguments)
      | Some (Type_interface ({ shape = Sum _; _ } as declared)) ->
          List.exists
            (fun (variant : Types.variant) -> have_values (Option.value ~default:[] variant.fields))
            (Option.value ~default:[] (Types.instantiate_variants declared arguments))
      | Some _ | None -> false)
  | None, (Named _ | Parameter _ | Projection _ | Function _ | Never | Variable _ | Hole | Error _)
    ->
      false

let teaches_through_a_bound (context : State.context) frame ~self_type
    (trait : Types.trait_reference) (declared : Types.trait_method) =
  let name = declared.method_name and receiver = declared.method_receiver in
  let declaration = Path.Method { owner = trait.trait; name; receiver } in
  let has_ensures (clauses : State.clauses) = clauses.ensures <> [] in
  match Contracts.read_signature context declaration with
  | None -> true
  | Some signature ->
      (not (Costs.states_no_allocation signature.costs))
      &&
      let through_the_bound =
        Callee.resolve context frame
          (Trait_method
             {
               trait;
               name;
               receiver;
               self_type;
               instantiation =
                 {
                   type_arguments =
                     List.map
                       (fun (generic : Types.generic) ->
                         Types.Type (Types.Parameter generic.generic))
                       signature.generics;
                   capability_arguments = [];
                 };
               evidence = Bound;
             })
          ~lends:None ~uses:signature.uses
      in
      let has_default_that_returns =
        declared.provided && not (context.lookups.may_abort declaration)
      in
      let restates_ensures, states_ensures =
        match through_the_bound.target with
        | Definition { contract = Some contract; _ } ->
            ( List.exists has_ensures contract.restated_clauses,
              has_ensures contract.callee_clauses
              || Option.fold ~none:false ~some:has_ensures contract.trait_clauses )
        | Definition { contract = None; _ } | Function_value | Intrinsic _ -> (false, false)
      in
      restates_ensures
      || (not has_default_that_returns)
         && (states_ensures
            ||
            match signature.output with
            | Lends _ -> true
            | Returns output -> not (has_valid_value context output))

let deepest_supplied_bound = 8

let rec bound_may_abort (context : State.context) frame ?(depth = 0)
    ((type_ : Types.ty), (bound : Types.trait_reference)) =
  let interface = context.lookups.interface in
  let may_abort_below = bound_may_abort context frame ~depth:(depth + 1) in
  depth > deepest_supplied_bound
  || List.exists
       (fun (required : Types.trait_reference) ->
         let teaches = teaches_through_a_bound context frame ~self_type:type_ required in
         let declared = Interface.Definition.read_trait_interface interface required.trait in
         let substitution =
           Types.make_trait_substitution declared.trait_generics ~self:type_ required
         in
         List.exists
           (fun (associated : Types.associated_type) ->
             let chosen =
               Interface.Impls.normalize interface ~list_bounds:context.bounds
                 (Projection { base = type_; trait = required; name = associated.associated_name })
             in
             List.exists
               (fun bound ->
                 may_abort_below (chosen, Types.substitute_trait_erased substitution bound))
               associated.associated_bounds)
           declared.associated_types
         ||
         match
           Interface.Impls.find_evidence interface ~list_bounds:context.bounds type_ required
         with
         | Some
             (Evidence
                (Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution })) ->
             let supplied = Types.Impl { impl; substitution } in
             List.exists
               (fun (method_ : Types.trait_method) ->
                 teaches method_
                 && context.lookups.may_abort
                      (Option.value
                         (Mir.Call_edges.find_method_of_evidence interface ~trait:required.trait
                            supplied method_)
                         ~default:
                           (Path.Method
                              {
                                owner = required.trait;
                                name = method_.method_name;
                                receiver = method_.method_receiver;
                              })))
               declared.methods
             || List.exists may_abort_below
                  (Interface.Impls.list_required_bounds
                     (Interface.Definition.read_impl_interface interface impl).impl_generics
                     substitution)
         | Some Built_in -> false
         | Some (Evidence Bound | Accepted _) | None -> List.exists teaches declared.methods)
       (Interface.Properties.list_bound_closure interface ~self:type_ bound)

let generics_may_abort context frame path substitution =
  match Contracts.read_signature context path with
  | Some signature ->
      List.exists (bound_may_abort context frame)
        (Interface.Impls.list_required_bounds signature.generics substitution)
  | None -> false

let make_own_substitution substitution_of (contract : State.contract) =
  substitution_of
    { contract.callee_clauses with inherited = false; bindings = Types.no_substitution }

let function_value_may_abort context frame (callee : Callee.t) (passed : State.passed) =
  match
    Option.value (Callee.find_parameter_type context callee passed.position) ~default:passed.type_
  with
  | Function function_type when not (Costs.states_no_allocation function_type.costs) -> (
      (not (has_valid_value context function_type.output))
      ||
      match (passed.term, Callbacks.find_known context passed.term) with
      | (Symbol (Lambda _) | Apply (Lambda _, _)), _ -> false
      | _, Some (Named { path; contract; substitution_of; _ }) ->
          context.lookups.may_abort path
          || generics_may_abort context frame path (make_own_substitution substitution_of contract)
      | _, (Some (Own _) | None) -> (
          match callee.target with
          | Definition { declaration; _ } -> (
              match Contracts.find_callee_clauses context declaration with
              | Some clauses -> (
                  match List.assoc_opt passed.position clauses.callbacks with
                  | Some callback -> callback.ensures <> []
                  | None -> false)
              | None -> false)
          | Function_value | Intrinsic _ -> false))
  | _ -> false

let may_abort context frame (callee : Callee.t) (definition : Callee.definition)
    (contract : State.contract) (values : State.passed list) =
  let runs =
    match Contracts.read_signature context definition.path with
    | Some signature -> not signature.specification_only
    | None -> true
  in
  runs
  && (generics_may_abort context frame definition.path
        (make_own_substitution definition.substitution_of contract)
     || List.exists (function_value_may_abort context frame callee) values)
