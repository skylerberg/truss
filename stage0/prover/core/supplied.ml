let has_valid_value (context : State.context) =
  Mir.Call_edges.has_valid_value
    { interface = context.lookups.interface; mir = context.lookups.mir }

type supplied_method = { teaches : bool; states_no_allocation : bool }

let make_declaration (trait : Types.trait_reference) (declared : Types.trait_method) =
  Path.Method
    { owner = trait.trait; name = declared.method_name; receiver = declared.method_receiver }

let deepest_supplied_bound = 8

let rec bound_may_abort (context : State.context) ?(depth = 0) ?(entered = []) ~bound_methods_run
    ((type_ : Types.ty), (bound : Types.trait_reference)) =
  let interface = context.lookups.interface in
  let closure = Interface.Properties.list_bound_closure interface ~self:type_ bound in
  let is_restated (declared : Types.trait_method) =
    List.exists
      (fun (required : Types.trait_reference) ->
        List.exists
          (fun (restated : Types.restated_method) ->
            restated.restated_name = declared.method_name
            && restated.restated_receiver = declared.method_receiver)
          (Interface.Definition.read_trait_interface interface required.trait).restated)
      closure
  in
  let may_abort_below ~entered ~bound_methods_run =
    bound_may_abort context ~depth:(depth + 1) ~entered ~bound_methods_run
  in
  let judge required (method_ : Types.trait_method) =
    let declaration = make_declaration required method_ in
    match Contracts.read_signature context declaration with
    | None -> { teaches = true; states_no_allocation = false }
    | Some signature ->
        let states_ensures =
          match Contracts.find_callee_clauses context declaration with
          | Some clauses -> clauses.ensures <> []
          | None -> false
        in
        let has_default_that_returns () =
          method_.provided
          && (not (context.lookups.may_abort declaration))
          && (not (List.exists (Path.equal declaration) entered))
          && not
               (may_abort_below ~entered:(declaration :: entered)
                  ~bound_methods_run:(context.lookups.list_bound_methods_run declaration)
                  (type_, required))
        in
        {
          teaches =
            is_restated method_
            || (states_ensures
               ||
               match signature.output with
               | Lends _ -> true
               | Returns output -> not (has_valid_value context output))
               && not (has_default_that_returns ());
          states_no_allocation = Types.states_no_allocation signature.costs;
        }
  in
  depth > deepest_supplied_bound
  || List.exists
       (fun (required : Types.trait_reference) ->
         let declared = Interface.Definition.read_trait_interface interface required.trait in
         let run =
           List.filter
             (fun method_ ->
               List.exists (Path.equal (make_declaration required method_)) bound_methods_run)
             declared.methods
         in
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
                 may_abort_below ~entered ~bound_methods_run
                   (chosen, Types.substitute_trait_erased substitution bound))
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
               (fun method_ ->
                 let code =
                   Option.value
                     (Mir.Call_edges.find_method_of_evidence interface ~trait:required.trait
                        supplied method_)
                     ~default:(make_declaration required method_)
                 in
                 ((judge required method_).teaches && context.lookups.may_abort code)
                 || (not (List.exists (Path.equal code) entered))
                    &&
                    let below =
                      may_abort_below ~entered:(code :: entered)
                        ~bound_methods_run:(context.lookups.list_bound_methods_run code)
                    in
                    below (type_, required)
                    || List.exists below
                         (Interface.Impls.list_required_bounds
                            (Interface.Definition.read_impl_interface interface impl).impl_generics
                            substitution))
               run
         | Some Built_in -> false
         | Some (Evidence Bound | Accepted _) | None ->
             List.exists
               (fun method_ ->
                 let judged = judge required method_ in
                 judged.teaches && not judged.states_no_allocation)
               run)
       closure

let generics_may_abort (context : State.context) path substitution =
  match (context.lookups.list_bound_methods_run path, Contracts.read_signature context path) with
  | (_ :: _ as bound_methods_run), Some signature ->
      List.exists
        (bound_may_abort context ~bound_methods_run)
        (Interface.Impls.list_required_bounds signature.generics substitution)
  | [], _ | _, None -> false

let make_own_substitution substitution_of (contract : State.contract) =
  substitution_of
    { contract.callee_clauses with inherited = false; bindings = Types.no_substitution }

let function_value_may_abort context (callee : Callee.t) (passed : State.passed) =
  match
    Option.value (Callee.find_parameter_type context callee passed.position) ~default:passed.type_
  with
  | Function function_type -> (
      let states_an_ensures () =
        match callee.target with
        | Definition { declaration; _ } -> (
            match Contracts.find_callee_clauses context declaration with
            | Some clauses -> (
                match List.assoc_opt passed.position clauses.callbacks with
                | Some callback -> callback.ensures <> []
                | None -> false)
            | None -> false)
        | Function_value | Intrinsic _ -> false
      in
      match (passed.term, Callbacks.find_known context passed.term) with
      | _, Some (Named { path; contract; substitution_of; _ }) ->
          context.lookups.may_abort path
          || generics_may_abort context path (make_own_substitution substitution_of contract)
      | term, known ->
          (not (Types.states_no_allocation function_type.costs))
          && ((not (has_valid_value context function_type.output))
             ||
             match (term, known) with
             | (Symbol (Lambda _) | Apply (Lambda _, _)), _ -> false
             | _, (Some (Own _ | Named _) | None) -> states_an_ensures ()))
  | _ -> false

let may_abort context (callee : Callee.t) (definition : Callee.definition)
    (contract : State.contract) (values : State.passed list) =
  let runs =
    match Contracts.read_signature context definition.path with
    | Some signature -> not signature.specification_only
    | None -> true
  in
  runs
  && (generics_may_abort context definition.path
        (make_own_substitution definition.substitution_of contract)
     || List.exists (function_value_may_abort context callee) values)
