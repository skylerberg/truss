let panic : Types.capability = Capability (Well_known.make_path Panic)
let tasks : Types.capability = Capability (Well_known.make_path Tasks)

type checking = {
  state : State.state;
  mutable provides : (Types.capability_set * Core.implementation list * Core.block) list;
}

let report checking ?(fixes = []) code (origin : Core.origin) message =
  let span = State.read_span checking.state origin in
  checking.state.diagnostics <-
    Diagnostic.make ~fixes ~code:(Capabilities code) span message :: checking.state.diagnostics

type function_body = { path : Path.t; implementation : Interface.Impls.implementation option }

type scope_kind =
  | Function_body of function_body
  | Lambda_body of Core.origin
  | Restricted of string

type scope = { available : Types.capability_set; kind : scope_kind; termination_demand : string }

let allows_panic scope = List.mem panic (scope.available :> Types.capability list)

let find_implemented_capability scope : Types.capability option =
  match scope.kind with
  | Function_body { implementation = Some { trait = { is_capability = true; _ }; impl; _ }; _ } ->
      Some (Capability impl.implements.trait)
  | Function_body _ | Lambda_body _ | Restricted _ -> None

let make_panic_only_scope ~enclosing description =
  {
    available =
      Types.union_capabilities
        (Types.make_capability_set [ panic ])
        (Types.list_divergence enclosing.available);
    kind = Restricted description;
    termination_demand = enclosing.termination_demand;
  }

let make_no_capabilities_scope description =
  {
    available = Types.no_capabilities;
    kind = Restricted description;
    termination_demand = Printf.sprintf "%s calls only functions that terminate" description;
  }

let make_quantifier_scope ~enclosing =
  {
    available = Types.list_divergence enclosing.available;
    kind = Restricted "a quantifier's body";
    termination_demand = enclosing.termination_demand;
  }

let check_grant checking (origin : Core.origin) ~subject package (uses : Types.capability_set) =
  List.iter
    (fun capability ->
      report checking Not_granted origin
        (Interface.Grants.describe_missing ~subject ~of_:package capability))
    (Interface.Grants.list_missing checking.state.lookups.interface ~package:checking.state.package
       ~of_:package uses)

let check_callee_grants checking (origin : Core.origin) (callee : Core.callee) =
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

let require_available checking scope (origin : Core.origin) ?(for_implementation = false)
    ?(indirect_call = false) ?(explain_divergence = fun () -> ("This call may not terminate", None))
    (required : Types.capability_set) =
  let state = checking.state in
  let superset =
    if indirect_call then
      Types.union_capabilities scope.available
        (Types.make_capability_set (Option.to_list (find_implemented_capability scope)))
    else scope.available
  in
  let report_missing (missing : Types.capability_set) =
    if Types.list_divergence missing <> Types.no_capabilities then begin
      let reason, advice = explain_divergence () in
      report checking May_not_terminate origin
        (Printf.sprintf "%s, and %s.%s" reason scope.termination_demand
           (match advice with Some advice -> " " ^ advice | None -> ""))
    end;
    List.iter
      (fun capability ->
        let shown = Types.show_capability capability in
        match scope.kind with
        | Lambda_body lambda ->
            report checking Lambda_uses lambda
              (Printf.sprintf
                 "This lambda uses `%s`, which the function type it is passed as does not allow."
                 shown)
        | Restricted description when not (allows_panic scope) ->
            report checking Not_available origin
              (Printf.sprintf
                 "This call uses `%s`, but %s may use no capabilities, not even `Panic`: its \
                  meaning must be a value. A function that fails on some inputs says so with \
                  `requires` instead."
                 shown description)
        | Restricted description ->
            report checking Not_available origin
              (Printf.sprintf
                 "This call uses `%s`, but %s may use only `Panic`, whatever the function declares."
                 shown description)
        | Function_body { path; _ } ->
            let subject = if for_implementation then "This implementation" else "This call" in
            let can_provide =
              match capability with
              | Types.Capability path -> not (Well_known.is Panic path)
              | Capability_parameter _ | Capability_projection _ | Capability_variable _ -> false
              | Capability_error _ -> State.raise_bug "a capability with an error is missing"
              | Divergence _ -> State.raise_bug "divergence is reported as a capability"
            in
            report checking Not_available origin
              (match
                 Interface.Impls.find_capability_declaration state.lookups.interface path capability
               with
              | Some (Declared_by clause) ->
                  Printf.sprintf "%s uses `%s`, which is not available here. Declare it with %s%s."
                    subject shown
                    (Interface.Impls.show_declaring_clause clause shown)
                    (if can_provide then ", or `provide` an implementation" else "")
              | Some (Fixed_by_trait { trait; method_name }) ->
                  Printf.sprintf
                    "%s uses `%s`, but `%s` can use only the capabilities `%s` declares for it.%s"
                    subject shown method_name (Types.show_trait trait)
                    (if can_provide then " Provide an implementation with `provide`." else "")
              | None -> Printf.sprintf "%s uses `%s`, which is not available here." subject shown))
      (Types.remove_divergence missing :> Types.capability list)
  in
  if required <> Types.no_capabilities then
    state.capability_constraints <-
      { subset = required; superset; report_missing } :: state.capability_constraints

let require_intrinsic_uses checking scope (origin : Core.origin) operation =
  if Option.is_none (find_implemented_capability scope) then
    require_available checking scope origin
      (Types.make_capability_set
         (List.map (fun capability -> Types.Capability capability) (Intrinsic.list_uses operation)))

let compute_operand_type : Core.operand -> Types.ty = function
  | Place core_place -> Core_walk.compute_place_type core_place
  | Value value -> value.type_

let diverges_whatever_it_is_passed (state : State.state) (callee : Core.callee) =
  let empty = List.map (fun _ -> Types.no_capabilities) in
  match callee with
  | Function function_ ->
      not
        (Types.terminates
           (State.compute_callee_uses state
              (Function
                 { function_ with capability_arguments = empty function_.capability_arguments })))
  | Trait_method method_ ->
      not
        (Types.terminates
           (State.compute_callee_uses state
              (Trait_method
                 { method_ with capability_arguments = empty method_.capability_arguments })))
  | Capability_method _ -> not (Types.terminates (State.compute_callee_uses state callee))
  | Intrinsic _ | Indirect _ -> false

let find_callee_name (callee : Core.callee) =
  match callee with
  | Function { path; _ } -> Some (Path.show path)
  | Trait_method { trait; name; _ } ->
      Some (Printf.sprintf "%s.%s" (Types.show_trait { trait with trait_arguments = [] }) name)
  | Capability_method { capability; name } ->
      Some (Printf.sprintf "%s.%s" (Types.show_capability (Types.Capability capability)) name)
  | Intrinsic _ | Indirect _ -> None

let list_parameter_names (state : State.state) (callee : Core.callee) =
  let list_names (signature : Types.signature) =
    (match signature.receiver with Some ((Read | Mut | Own), _) -> [ "self" ] | _ -> [])
    @ List.map (fun (parameter : Types.parameter_info) -> parameter.name) signature.parameters
  in
  match callee with
  | Function { path; _ } ->
      Option.fold ~none:[] ~some:list_names
        (Interface.Impls.read_signature state.lookups.interface path)
  | Trait_method { trait; name; receiver; _ } ->
      Option.fold ~none:[]
        ~some:(fun method_ ->
          list_names
            (Interface.Definition.read_method_signature state.lookups.interface ~owner:trait.trait
               method_))
        (Interface.Definition.find_trait_method state.lookups.interface trait.trait ~name ~receiver)
  | Capability_method _ | Intrinsic _ | Indirect _ -> []

let explain_call_divergence checking scope (call : Core.call) () =
  let state = checking.state in
  let may_not_terminate type_ =
    match type_ with
    | Types.Function { uses; _ } ->
        Types.list_divergence (State.finalize_capabilities state uses) <> Types.no_capabilities
    | _ -> false
  in
  let names = list_parameter_names state call.callee in
  let diverging_argument =
    List.find_map
      (fun (index, (argument : Core.argument)) ->
        match argument with
        | Passed { value; _ } when may_not_terminate (compute_operand_type value) ->
            Some
              (Printf.sprintf "the %s passed %s may not"
                 (match value with Value { kind = Lambda _; _ } -> "lambda" | _ -> "function")
                 (match List.nth_opt names index with
                 | Some name -> Printf.sprintf "for `%s`" name
                 | None -> "to it"))
        | Passed _ | Default -> None)
      (List.mapi (fun index argument -> (index, argument)) call.arguments)
  in
  match (call.callee, find_callee_name call.callee, diverging_argument) with
  | callee, Some shown, _ when diverges_whatever_it_is_passed state callee ->
      (Printf.sprintf "This call may not terminate, since `%s` has no `time` clause" shown, None)
  | _, _, Some argument -> (Printf.sprintf "This call may not terminate, since %s" argument, None)
  | Indirect function_value, _, None -> (
      let name =
        match function_value with
        | Place (Local { local; _ }) -> Core_walk.find_local_name local
        | Place (Constant _ | Field _ | Lent _ | Temporary _) | Value _ -> None
      in
      let is_unconditional =
        match compute_operand_type function_value with
        | Types.Function { uses; _ } -> not (Types.terminates uses)
        | _ -> true
      in
      match (name, is_unconditional) with
      | Some name, true ->
          ( Printf.sprintf
              "This call may not terminate, since the type of `%s` has no `time` clause" name,
            None )
      | Some name, false ->
          ( Printf.sprintf "This call may not terminate, since the function passed for `%s` may not"
              name,
            match scope.kind with
            | Function_body _ ->
                Some
                  (Printf.sprintf "A `time` clause follows `%s` where its bound names `time(%s)`."
                     name name)
            | Lambda_body _ | Restricted _ -> None )
      | None, _ ->
          ( "This call may not terminate, since the type of the function it calls has no `time` \
             clause",
            None ))
  | _ -> ("This call may not terminate", None)

let require_callee_uses checking scope (origin : Core.origin) (callee : Core.callee) =
  check_callee_grants checking origin callee;
  require_available checking scope origin
    ~explain_divergence:(fun () ->
      ( (match find_callee_name callee with
        | Some shown ->
            Printf.sprintf "This call of `%s` may not terminate, since it has no `time` clause"
              shown
        | None -> "This call may not terminate"),
        None ))
    (State.compute_callee_uses checking.state callee);
  match callee with
  | Intrinsic { operation; _ } -> require_intrinsic_uses checking scope origin operation
  | Function _ | Trait_method _ | Capability_method _ | Indirect _ -> ()

let require_divergence_of_unmeasured_loop checking scope (origin : Core.origin)
    ~explain_missing_measure =
  require_available checking scope origin
    ~explain_divergence:(fun () ->
      ( Printf.sprintf "This loop may not terminate, since %s" (explain_missing_measure ()),
        Some "Give the loop a `decreases` clause." ))
    (Types.make_capability_set [ Types.unconditional_divergence ])

let rec check_expression checking scope (node : Core.expression) =
  match node.kind with
  | Lambda { body; _ } ->
      check_block checking
        {
          available =
            (match node.type_ with
            | Types.Function { uses; _ } -> uses
            | _ -> Types.no_capabilities);
          kind = Lambda_body node.origin;
          termination_demand =
            "the function type that this lambda is passed as promises that the lambda terminates";
        }
        body
  | Provide { implementations; body } -> check_provide checking scope implementations body
  | Quantified _ ->
      check_children checking (make_quantifier_scope ~enclosing:scope) (`Expression node)
  | Function_value { path; _ } ->
      check_callee_grants checking node.origin
        (Function { path; type_arguments = []; capability_arguments = [] })
  | Call call -> (
      check_children checking scope (`Expression node);
      check_callee_grants checking node.origin call.callee;
      require_available checking scope node.origin
        ~indirect_call:(match call.callee with Indirect _ -> true | _ -> false)
        ~explain_divergence:(explain_call_divergence checking scope call)
        call.uses;
      match call.callee with
      | Intrinsic { operation; _ } -> require_intrinsic_uses checking scope node.origin operation
      | Function _ | Trait_method _ | Capability_method _ | Indirect _ -> ())
  | _ -> check_children checking scope (`Expression node)

and check_children checking scope node =
  let origin =
    match node with
    | `Expression (inner : Core.expression) -> inner.origin
    | `Statement (inner : Core.statement) -> inner.origin
    | `Pattern (inner : Core.pattern) -> inner.origin
  in
  let visit : Core_walk.visit =
    {
      expression = check_expression checking scope;
      statement = check_statement checking scope;
      pattern = (fun inner -> check_children checking scope (`Pattern inner));
      callee = require_callee_uses checking scope origin;
      place = ignore;
    }
  in
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
        (check_statement checking (make_panic_only_scope ~enclosing:scope "a `parallel` branch"))
        branches
  | Concurrent branches ->
      require_available checking scope statement.origin (Types.make_capability_set [ tasks ]);
      List.iter (check_statement checking scope) branches
  | For { mode; pattern; iteration; clauses; body } ->
      (match iteration with
      | Integer_range { start; stop; _ } ->
          check_expression checking scope start;
          check_expression checking scope stop
      | Elements { count; element; _ } ->
          check_expression checking scope count;
          Core_walk.walk_place
            { Core_walk.ignore_all with expression = check_expression checking scope }
            element
      | Cursor { cursor; next } ->
          Core_walk.walk_place
            { Core_walk.ignore_all with expression = check_expression checking scope }
            cursor;
          require_callee_uses checking scope statement.origin next;
          if not (Core_walk.states_measure clauses) then
            require_divergence_of_unmeasured_loop checking scope statement.origin
              ~explain_missing_measure:(fun () ->
                Printf.sprintf
                  "`%s` has no `remaining(self) -> UInt64` method to give the loop a measure"
                  (Types.show
                     (State.finalize_type checking.state (Core_walk.compute_place_type cursor)))));
      check_children checking scope (`Pattern pattern);
      check_loop_clauses checking clauses;
      check_block checking
        (match mode with
        | Parallel_loop -> make_panic_only_scope ~enclosing:scope "a `parallel for`"
        | Sequential -> scope
        | Concurrent_loop ->
            require_available checking scope statement.origin (Types.make_capability_set [ tasks ]);
            scope)
        body
  | While { condition; clauses; body; _ } ->
      if not (Core_walk.states_measure clauses || Core_walk.has_implicit_measure condition) then
        require_divergence_of_unmeasured_loop checking scope statement.origin
          ~explain_missing_measure:(fun () -> "it has no measure");
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
          require_available checking scope implementation.origin ~for_implementation:true
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
          superset = State.finalize_capabilities state constraint_.superset;
        })
      state.capability_constraints;
  let solution = Hashtbl.create 8 in
  let read_value variable =
    Option.value ~default:Types.no_capabilities (Hashtbl.find_opt solution variable)
  in
  let substitute =
    Types.flat_map_capabilities (function
      | Types.Capability_variable variable ->
          (Types.remove_divergence (read_value variable) :> Types.capability list)
      | Types.Divergence (Of_variable variable) ->
          (Types.list_divergence (read_value variable) :> Types.capability list)
      | capability -> [ capability ])
  in
  let compute_missing (constraint_ : State.subset_constraint) =
    Types.compute_missing_capabilities ~required:(substitute constraint_.subset)
      ~available:(substitute constraint_.superset)
  in
  let add_to_variables (constraint_ : State.subset_constraint) find_variable missing =
    let variables = List.filter_map find_variable (constraint_.superset :> Types.capability list) in
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
          let missing = compute_missing constraint_ in
          let added_capabilities =
            add_to_variables constraint_
              (function Types.Capability_variable variable -> Some variable | _ -> None)
              (Types.remove_divergence missing)
          in
          let added_divergence =
            add_to_variables constraint_
              (function Types.Divergence (Of_variable variable) -> Some variable | _ -> None)
              (Types.list_divergence missing)
          in
          changed || added_capabilities || added_divergence)
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
      | Capability _ | Capability_parameter _ | Capability_variable _ -> true
      | Divergence _ -> false
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
      Types.remove_divergence uses <> Types.no_capabilities
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
      termination_demand = "this function has a `time` clause";
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
          | Finite -> ()
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
  | Function { body; _ }, (Function _ | Method_declaration _), Function_interface _ ->
      let signature =
        match Interface.Impls.read_signature state.lookups.interface state.key.path with
        | Some signature -> signature
        | None -> State.raise_bug "a checked function has no signature"
      in
      Option.iter
        (check_block checking
           (make_function_body_scope
              (Interface.Impls.normalize_capabilities state.lookups.interface
                 ~list_bounds:(State.lookup_bounds state) signature.uses)))
        body
  | Test (Some body), _, Test_interface uses ->
      check_block checking
        (make_function_body_scope
           (Types.union_capabilities uses
              (Types.make_capability_set [ panic; Types.unconditional_divergence ])))
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
