let tasks : Types.capability = Capability (Well_known.make_path Tasks)

type checking = {
  state : State.state;
  mutable provides : (Types.capability_set * Core.implementation list * Core.block) list;
}

let report checking ?(fixes = []) ?(notes = []) code (origin : Core.origin) message =
  let read_span = State.read_span checking.state in
  checking.state.diagnostics <-
    Diagnostic.make ~fixes
      ~notes:(List.map (fun (cited, note) -> (read_span cited, note)) notes)
      ~code:(Capabilities code) (read_span origin) message
    :: checking.state.diagnostics

type function_body = { path : Path.t; implementation : Interface.Impls.implementation option }

type scope_kind =
  | Function_body of function_body
  | Lambda_body of Core.origin
  | Restricted of { description : string; enclosing : scope option }
  | Parallel of { description : string; enclosing : scope }

and scope = { available : Types.capability_set; kind : scope_kind }

let find_implemented_capability scope : Types.capability option =
  match scope.kind with
  | Function_body { implementation = Some { trait = { is_capability = true; _ }; impl; _ }; _ } ->
      Some (Capability impl.implements.trait)
  | Function_body _ | Lambda_body _ | Restricted _ | Parallel _ -> None

let make_parallel_scope ~enclosing description =
  {
    available = Types.make_capability_set [ Types.panic; Types.run_forever ];
    kind = Parallel { description; enclosing };
  }

let make_no_capabilities_scope description =
  { available = Types.no_capabilities; kind = Restricted { description; enclosing = None } }

let make_quantifier_scope ~enclosing =
  {
    available = Types.make_capability_set [ Types.run_forever ];
    kind = Restricted { description = "a quantifier's body"; enclosing = Some enclosing };
  }

let find_enclosing_restriction scope =
  match scope.kind with
  | Parallel { enclosing; _ } ->
      Some (enclosing, Types.make_capability_set [ Types.panic; Types.run_forever ])
  | Restricted { enclosing = Some enclosing; _ } ->
      Some (enclosing, Types.make_capability_set [ Types.run_forever ])
  | Function_body _ | Lambda_body _ | Restricted { enclosing = None; _ } -> None

let check_grant checking (origin : Core.origin) ~subject package (uses : Types.capability_set) =
  List.iter
    (fun capability ->
      report checking Not_granted origin
        (Interface.Grants.describe_missing ~subject ~of_:package capability))
    (Interface.Grants.list_missing checking.state.lookups.interface ~package:checking.state.package
       ~of_:package uses)

let check_callee_grants checking (origin : Core.origin) (callee : Core.operand Core.target) =
  let state = checking.state in
  match callee with
  | Function { path; _ } ->
      Option.iter
        (fun (signature : Types.signature) ->
          check_grant checking origin
            ~subject:(Printf.sprintf "`%s`" (Path.show path))
            (Path.locate_package path) signature.uses)
        (Interface.Impls.read_signature state.lookups.interface path)
  | Trait_method { trait; name; receiver; evidence; _ } -> (
      (match
         Interface.Definition.find_trait_method state.lookups.interface trait.trait ~name ~receiver
       with
      | Some method_ ->
          check_grant checking origin
            ~subject:(Printf.sprintf "`%s.%s`" (Path.show trait.trait) name)
            (Path.locate_package trait.trait)
            (Interface.Definition.read_method_signature state.lookups.interface ~owner:trait.trait
               method_)
              .uses
      | None -> ());
      match evidence with
      | Impl { impl; _ } -> (
          match Interface.Definition.find_impl_interface state.lookups.interface impl with
          | Some interface when List.mem (name, receiver) interface.impl_methods ->
              Option.iter
                (fun (signature : Types.signature) ->
                  check_grant checking origin
                    ~subject:
                      (Printf.sprintf "The `impl` of `%s` for `%s`"
                         (Types.show_trait interface.implements)
                         (Types.show interface.for_type))
                    (Path.locate_package impl) signature.uses)
                (Interface.Impls.read_signature state.lookups.interface
                   (Method { owner = impl; name; receiver }))
          | Some _ | None -> ())
      | Bound | Dynamic -> ())
  | Capability_method _ | Intrinsic _ | Indirect _ -> ()

let add_alternative ~sentence_start alternative =
  match alternative with
  | Some alternative when sentence_start -> " " ^ String.capitalize_ascii alternative ^ "."
  | Some alternative -> ", or " ^ alternative
  | None -> ""

let rec require_available checking scope (origin : Core.origin) ?(subject = "This call")
    ?alternative ?(indirect_call = false) ?restriction (required : Types.capability_set) =
  let state = checking.state in
  let superset =
    if indirect_call then
      Types.union_capabilities scope.available
        (Types.make_capability_set (Option.to_list (find_implemented_capability scope)))
    else scope.available
  in
  let report_missing (missing : Types.capability_set) =
    List.iter
      (fun capability ->
        let shown = Types.show_capability capability in
        match scope.kind with
        | Lambda_body lambda ->
            report checking Lambda_uses lambda
              ~notes:
                (if Option.is_some alternative then
                   [ (origin, Printf.sprintf "%s uses `%s`." subject shown) ]
                 else [])
              (Printf.sprintf
                 "This lambda uses `%s`, which the function type it is passed as does not allow."
                 shown)
        | Restricted { description; _ } when Types.is_run_forever capability ->
            report checking Not_available origin
              (Printf.sprintf "%s uses `RunForever`, but %s must terminate.%s" subject description
                 (add_alternative ~sentence_start:true alternative))
        | Restricted { description; _ } ->
            report checking Not_available origin
              (Printf.sprintf
                 "%s uses `%s`, but %s may use no capabilities, not even `Panic`: its meaning must \
                  be a value. A function that fails on some inputs says so with `requires` \
                  instead."
                 subject shown description)
        | Parallel { description; _ } ->
            report checking Not_available origin
              (Printf.sprintf
                 "%s uses `%s`, but %s may use no capability except `Panic` and `RunForever`, even \
                  one that is available outside it. Parallel calls of one implementation could \
                  race."
                 subject shown description)
        | Function_body { path; _ } ->
            let can_provide =
              match capability with
              | Types.Capability path -> not (Well_known.is_built_in_capability path)
              | Capability_parameter _ | Capability_projection _ | Capability_variable _ -> false
              | Capability_error _ -> State.raise_bug "a capability with an error is missing"
            in
            report checking Not_available origin
              (match
                 Interface.Impls.find_capability_declaration state.lookups.interface path capability
               with
              | Some (Declared_by clause) ->
                  Printf.sprintf
                    "%s uses `%s`, which is not available here. Declare it with %s%s%s." subject
                    shown
                    (Interface.Impls.show_declaring_clause clause shown)
                    (if can_provide then ", or `provide` an implementation" else "")
                    (add_alternative ~sentence_start:false alternative)
              | Some (Fixed_by_trait { trait; method_name }) ->
                  Printf.sprintf
                    "%s uses `%s`, but `%s` can use only the capabilities `%s` declares for it.%s%s"
                    subject shown method_name (Types.show_trait trait)
                    (if can_provide then " Provide an implementation with `provide`." else "")
                    (add_alternative ~sentence_start:true alternative)
              | None ->
                  Printf.sprintf "%s uses `%s`, which is not available here.%s" subject shown
                    (add_alternative ~sentence_start:true alternative)))
      (missing :> Types.capability list)
  in
  if required <> Types.no_capabilities then begin
    state.capability_constraints <-
      { subset = required; restriction; superset; report_missing } :: state.capability_constraints;
    match find_enclosing_restriction scope with
    | Some (enclosing, passed) ->
        require_available checking enclosing origin ~subject ?alternative ~indirect_call
          ~restriction:
            (match restriction with
            | Some restriction -> Types.intersect_capabilities [ restriction; passed ]
            | None -> passed)
          required
    | None -> ()
  end

let compute_required_uses scope (callee : Core.callee) =
  match (callee.target, find_implemented_capability scope) with
  | Intrinsic _, Some _ -> Types.no_capabilities
  | (Function _ | Trait_method _ | Capability_method _ | Intrinsic _ | Indirect _), _ -> callee.uses

let require_callee_uses checking scope (origin : Core.origin) (callee : Core.callee) =
  check_callee_grants checking origin callee.target;
  require_available checking scope origin
    ~indirect_call:(match callee.target with Indirect _ -> true | _ -> false)
    (compute_required_uses scope callee)

let require_run_forever_of_unmeasured_loop checking scope (origin : Core.origin) ~alternative =
  require_available checking scope origin ~subject:"This loop has no measure, so it" ~alternative
    (Types.make_capability_set [ Types.run_forever ])

let compute_node_origin = function
  | `Expression (inner : Core.expression) -> inner.origin
  | `Statement (inner : Core.statement) -> inner.origin
  | `Pattern (inner : Core.pattern) -> inner.origin

let rec check_expression checking scope (node : Core.expression) =
  match node.kind with
  | Lambda { body; _ } ->
      let available =
        match node.type_ with Types.Function { uses; _ } -> uses | _ -> Types.no_capabilities
      in
      check_block checking { available; kind = Lambda_body node.origin } body
  | Provide { implementations; body } -> check_provide checking scope implementations body
  | Quantified _ ->
      check_children checking (make_quantifier_scope ~enclosing:scope) (`Expression node)
  | Function_value { path; _ } ->
      check_callee_grants checking node.origin
        (Function { path; instantiation = Types.no_instantiation })
  | _ -> check_children checking scope (`Expression node)

and make_visitor checking scope node : Core_walk.visit =
  {
    expression = check_expression checking scope;
    statement = check_statement checking scope;
    pattern = (fun inner -> check_children checking scope (`Pattern inner));
    callee = require_callee_uses checking scope (compute_node_origin node);
    place = ignore;
  }

and check_children checking scope node =
  let visit = make_visitor checking scope node in
  match node with
  | `Expression inner -> Core_walk.walk_expression_children visit inner
  | `Statement inner -> Core_walk.walk_statement_children visit inner
  | `Pattern inner -> Core_walk.walk_pattern_children visit inner

and check_block checking scope (body : Core.block) =
  List.iter (check_statement checking scope) body.statements;
  Option.iter (check_expression checking scope) body.value

and check_statement checking scope (statement : Core.statement) =
  match statement.kind with
  | Parallel branches ->
      List.iter
        (check_statement checking (make_parallel_scope ~enclosing:scope "a `parallel` branch"))
        branches
  | Concurrent branches ->
      require_available checking scope statement.origin (Types.make_capability_set [ tasks ]);
      List.iter (check_statement checking scope) branches
  | For { mode; pattern; iteration; clauses; body } ->
      Core_walk.walk_iteration (make_visitor checking scope (`Statement statement)) iteration;
      (match iteration with
      | Cursor { cursor; _ } when not (Core_walk.states_measure clauses) ->
          require_run_forever_of_unmeasured_loop checking scope statement.origin
            ~alternative:
              (Printf.sprintf
                 "give the loop a `decreases` clause, or `%s` a `remaining(self) -> UInt64` method"
                 (Types.show
                    (State.finalize_type checking.state (Core_walk.compute_place_type cursor))))
      | Integer_range _ | Elements _ | Cursor _ -> ());
      check_children checking scope (`Pattern pattern);
      check_loop_clauses checking clauses;
      check_block checking
        (match mode with
        | Parallel_loop -> make_parallel_scope ~enclosing:scope "a `parallel for`"
        | Sequential -> scope
        | Concurrent_loop ->
            require_available checking scope statement.origin (Types.make_capability_set [ tasks ]);
            scope)
        body
  | While { condition; clauses; body; _ } ->
      if not (Core_walk.states_measure clauses || Core_walk.has_implicit_measure condition) then
        require_run_forever_of_unmeasured_loop checking scope statement.origin
          ~alternative:"give the loop a `decreases` clause";
      check_expression checking scope condition;
      check_loop_clauses checking clauses;
      check_block checking scope body
  | Proof body -> check_block checking (make_no_capabilities_scope "a proof") body
  | Let _ | Evaluate _ | Assign _ | Compound_assign _ | Assert _ | Yield _ ->
      check_children checking scope (`Statement statement)

and check_loop_clauses checking (clauses : Core.loop_clause list) =
  List.iter
    (Core_walk.walk_loop_clause
       {
         Core_walk.ignore_all with
         expression = check_expression checking (make_no_capabilities_scope "a specification");
       })
    clauses

and check_provide checking scope implementations body =
  let state = checking.state in
  let provided = ref Types.no_capabilities in
  List.iter
    (fun (implementation : Core.implementation) ->
      Core_walk.walk_operand
        { Core_walk.ignore_all with expression = check_expression checking scope }
        implementation.value;
      let impls = Form.list_capability_impls state implementation.type_ in
      if impls = [] then
        report checking Not_an_implementation implementation.origin
          (Printf.sprintf "`%s` implements no capability, so it provides nothing."
             (Types.show implementation.type_));
      let mutates =
        List.exists
          (fun (_, (interface : Types.impl_interface)) ->
            List.exists (fun (_, receiver) -> receiver = Path.Mut) interface.impl_methods)
          impls
      in
      let provided_mut = implementation.mode = Mut in
      let is_place = match implementation.value with Place _ -> true | Value _ -> false in
      let start = (State.read_span checking.state implementation.origin).start in
      if is_place && mutates && not provided_mut then
        report checking Provide_mode implementation.origin
          ~fixes:
            [
              Diagnostic.fix "Provide it `mut`."
                [ Diagnostic.insert (Source.Definition_span.make_zero_width start) "mut " ];
            ]
          "This implementation mutates its own state, so the place is provided `mut`."
      else if provided_mut && not mutates then
        report checking Provide_mode implementation.origin
          ~fixes:
            [
              Diagnostic.fix "Remove the `mut`."
                [ Diagnostic.delete (Source.Definition_span.make start (start + 4)) ];
            ]
          "This implementation never mutates its own state, so the place is provided without `mut`.";
      List.iter
        (fun ((provided : Core.provided), (interface : Types.impl_interface)) ->
          check_grant checking implementation.origin
            ~subject:
              (Printf.sprintf "The `impl` of `%s` for `%s`" (Path.show provided.capability)
                 (Types.show interface.for_type))
            (Path.locate_package provided.impl)
            interface.impl_uses;
          require_available checking scope implementation.origin ~subject:"This implementation"
            interface.impl_uses)
        impls;
      provided :=
        Types.union_capabilities !provided
          (Types.make_capability_set
             (List.map
                (fun ((provided : Core.provided), _) -> Types.Capability provided.capability)
                impls)))
    implementations;
  checking.provides <- (scope.available, implementations, body) :: checking.provides;
  check_block checking
    { scope with available = Types.union_capabilities scope.available !provided }
    body

let solve (state : State.state) =
  state.capability_constraints <-
    List.map
      (fun (constraint_ : State.subset_constraint) ->
        {
          constraint_ with
          subset = State.finalize_capabilities state constraint_.subset;
          restriction = Option.map (State.finalize_capabilities state) constraint_.restriction;
          superset = State.finalize_capabilities state constraint_.superset;
        })
      state.capability_constraints;
  let solution = Hashtbl.create 8 in
  let read_value variable =
    Option.value ~default:Types.no_capabilities (Hashtbl.find_opt solution variable)
  in
  let substitute =
    Types.flat_map_capabilities (function
      | Types.Capability_variable variable -> (read_value variable :> Types.capability list)
      | capability -> [ capability ])
  in
  let compute_missing (constraint_ : State.subset_constraint) =
    let missing =
      Types.compute_missing_capabilities ~required:(substitute constraint_.subset)
        ~available:(substitute constraint_.superset)
    in
    match constraint_.restriction with
    | Some restriction -> Types.intersect_capabilities [ missing; substitute restriction ]
    | None -> missing
  in
  let add_to_variables (constraint_ : State.subset_constraint) missing =
    let variables =
      List.filter_map
        (function Types.Capability_variable variable -> Some variable | _ -> None)
        (constraint_.superset :> Types.capability list)
    in
    if variables = [] || missing = Types.no_capabilities then false
    else begin
      List.iter
        (fun variable ->
          Hashtbl.replace solution variable (Types.union_capabilities missing (read_value variable)))
        variables;
      true
    end
  in
  let rec grow () =
    let changed =
      List.fold_left
        (fun changed (constraint_ : State.subset_constraint) ->
          add_to_variables constraint_ (compute_missing constraint_) || changed)
        false state.capability_constraints
    in
    if changed then grow ()
  in
  grow ();
  state.capability_solution <- Some solution;
  List.iter
    (fun (constraint_ : State.subset_constraint) ->
      let missing = compute_missing constraint_ in
      if missing <> Types.no_capabilities then constraint_.report_missing missing)
    (List.rev state.capability_constraints)

let rec can_call_capability_code (state : State.state) ~list_bounds ?(seen = []) (type_ : Types.ty)
    =
  let can_call_inside = can_call_capability_code state ~list_bounds ~seen in
  let trait_uses (trait : Types.trait_reference) =
    let can_hold_a_capability : Types.capability -> bool = function
      | Capability_projection _ -> ( match type_ with Types.Any _ -> false | _ -> true)
      | Capability _ as capability -> not (Types.is_run_forever capability)
      | Capability_parameter _ | Capability_variable _ -> true
      | Capability_error _ -> State.raise_bug "a trait's method uses a capability with an error"
    in
    List.exists
      (fun (bound : Types.trait_reference) ->
        match Interface.Definition.find_trait_interface state.lookups.interface bound.trait with
        | Some interface ->
            List.exists
              (fun (method_ : Types.trait_method) ->
                List.exists can_hold_a_capability
                  ((Interface.Definition.read_method_signature state.lookups.interface
                      ~owner:bound.trait method_)
                     .uses
                    :> Types.capability list))
              interface.methods
        | None -> false)
      (trait :: Interface.Properties.list_bound_closure state.lookups.interface ~self:type_ trait)
  in
  let can_call_arguments =
    List.exists (function
      | Types.Type argument -> can_call_inside argument
      | Types.Value _ -> false)
  in
  match type_ with
  | Types.Function { uses; inputs; output; _ } ->
      List.exists
        (fun capability -> not (Types.is_run_forever capability))
        (uses :> Types.capability list)
      || List.exists (fun (_, input) -> can_call_inside input) inputs
      || can_call_inside output
  | Types.Any trait -> trait_uses trait
  | Types.Parameter parameter -> List.exists trait_uses (list_bounds parameter)
  | Types.Named { path; arguments = type_arguments } -> (
      can_call_arguments type_arguments
      || (not (List.exists (Path.equal path) seen))
         &&
         let can_call_inside = can_call_capability_code state ~list_bounds ~seen:(path :: seen) in
         let can_call_fields =
           List.exists (fun (field : Types.field) -> can_call_inside field.field_type)
         in
         (match Members.find_fields state.lookups path type_arguments with
           | Some named_fields -> can_call_fields named_fields
           | None -> false)
         ||
         match Members.find_variants state.lookups path type_arguments with
         | Some variants ->
             List.exists
               (fun (variant : Types.variant) ->
                 can_call_fields (Option.value ~default:[] variant.fields))
               variants
         | None -> false)
  | Types.Projection _ | Types.Never | Types.Integer | Types.Literal _ | Types.Variable _
  | Types.Hole | Types.Error _ ->
      false

let check_monitor_lock checking ~(read_solved : int -> Types.capability_set) available
    implementations =
  let state = checking.state in
  let provides_tasks (implementation : Core.implementation) =
    List.exists
      (fun ((provided : Core.provided), (_ : Types.impl_interface)) ->
        Path.equal provided.capability (Well_known.make_path Tasks))
      (Form.list_capability_impls state implementation.type_)
  in
  let available =
    Types.flat_map_capabilities
      (function
        | Types.Capability_variable variable -> (read_solved variable :> Types.capability list)
        | capability -> [ capability ])
      available
  in
  if
    not
      (List.mem tasks (available :> Types.capability list)
      || List.exists provides_tasks implementations)
  then
    List.iter
      (fun (implementation : Core.implementation) ->
        if implementation.mode = Mut && not (provides_tasks implementation) then
          report checking Monitor_needs_tasks implementation.origin
            (Printf.sprintf
               "`%s` is provided `mut`, and the body of this `provide` uses `Tasks`, so two tasks \
                could call its methods at the same time. Its methods are locked through `Tasks`, \
                but `Tasks` is provided only inside the body: it is not available at this \
                `provide`, and no implementation in it provides `Tasks`. Without the lock, the two \
                calls are a data race. Provide the implementation of `Tasks` in this `provide` or \
                in an enclosing one."
               (Types.show implementation.type_)))
      implementations

let check_monitor_callbacks checking implementations =
  let state = checking.state in
  List.iter
    (fun (implementation : Core.implementation) ->
      if implementation.mode = Mut then
        List.iter
          (fun ((provided : Core.provided), (_ : Types.impl_interface)) ->
            match
              Interface.Definition.find_trait_interface state.lookups.interface provided.capability
            with
            | Some capability ->
                List.iter
                  (fun (method_ : Types.trait_method) ->
                    let signature =
                      Interface.Definition.read_method_signature state.lookups.interface
                        ~owner:provided.capability method_
                    in
                    let list_bounds = Types.list_bounds signature.generics in
                    match
                      List.find_opt
                        (fun (parameter : Types.parameter_info) ->
                          can_call_capability_code state ~list_bounds parameter.type_)
                        signature.parameters
                    with
                    | Some parameter ->
                        report checking Callback_may_deadlock implementation.origin
                          (Printf.sprintf
                             "The body of this `provide` can use `Tasks`, so this implementation \
                              is a monitor: each call of its methods runs to completion before the \
                              next call starts. `%s.%s` takes `%s`, which can call code that uses \
                              a capability. Called while the monitor is held, that code could \
                              enter the monitor of a nested `provide`, and two tasks could \
                              deadlock. Pass the method the values that it needs instead of a \
                              callback."
                             (Types.show_capability (Types.Capability provided.capability))
                             method_.method_name parameter.name)
                    | None -> ())
                  capability.methods
            | None -> ())
          (Form.list_capability_impls state implementation.type_))
    implementations

let check (state : State.state) (elaborated : Interface.Environment.elaborated_interface)
    (form : Core.t) =
  let checking = { state; provides = [] } in
  let make_function_body_scope available =
    let path = state.key.path in
    {
      available;
      kind =
        Function_body
          {
            path;
            implementation =
              (match path with
              | Method { owner = (Impl _ | Derived _) as owner; _ } ->
                  Interface.Impls.find_implementation state.lookups.interface owner
              | _ -> None);
          };
    }
  in
  let check_specification =
    check_expression checking (make_no_capabilities_scope "a specification")
  in
  (match form.definition with
  | Function { parameters; contract; _ } ->
      List.iter
        (fun (parameter : Core.parameter) ->
          Option.iter
            (fun (contract : Core.callback_contract) ->
              List.iter check_specification contract.requires)
            parameter.callback_contract)
        parameters;
      List.iter
        (fun (condition : Core.condition) -> check_specification condition.value)
        contract.requires;
      List.iter check_specification contract.ensures;
      List.iter check_specification contract.decreases;
      List.iter
        (fun (cost : Core.cost) ->
          match cost.bound with
          | Order_of value | At_most value | Exactly value -> check_specification value)
        contract.costs
  | Type { invariants; potential; _ } ->
      List.iter (fun (invariant : Core.condition) -> check_specification invariant.value) invariants;
      Option.iter check_specification potential
  | Trait laws ->
      List.iter
        (fun (law : Core.law) ->
          List.iter check_specification law.requires;
          check_block checking (make_no_capabilities_scope "a law") law.body)
        laws
  | Constant _ | Test _ | Law_proof _ | Empty -> ());
  (match (form.definition, state.definition.kind, elaborated.interface) with
  | Function { body = Some body; _ }, (Function _ | Method_declaration _), Function_interface _
  | Test (Some body), _, Test_interface _ ->
      let signature =
        match Interface.Impls.read_signature state.lookups.interface state.key.path with
        | Some signature -> signature
        | None -> State.raise_bug "a checked function or test has no signature"
      in
      check_block checking
        (make_function_body_scope
           (Interface.Impls.normalize_capabilities state.lookups.interface
              ~list_bounds:(State.lookup_bounds state) signature.uses))
        body
  | Function { body = Some body; _ }, Theorem _, _ | Law_proof { body = Some body; _ }, _, _ ->
      check_block checking (make_no_capabilities_scope "a proof") body
  | _ -> ());
  solve state;
  let read_solved variable =
    match state.capability_solution with
    | Some solution ->
        Option.value ~default:Types.no_capabilities (Hashtbl.find_opt solution variable)
    | None -> Types.no_capabilities
  in
  List.iter
    (fun (available, implementations, body) ->
      match Core_walk.compute_tasks_use ~read_solved body with
      | No_tasks -> ()
      | Through_parameter -> check_monitor_callbacks checking implementations
      | Uses_tasks ->
          check_monitor_callbacks checking implementations;
          check_monitor_lock checking ~read_solved available implementations)
    (List.rev checking.provides)
