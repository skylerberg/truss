open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
open State

let panic : Types.capability = Capability (Well_known.path Panic)
let tasks : Types.capability = Capability (Well_known.path Tasks)

type checking = {
  state : state;
  spans : Source.Definition_span.t array;
  mutable provides : (Types.capability_set * Core.implementation list * Core.block) list;
}

let report checking ?(fixes = []) code (origin : Core.origin) message =
  let span = checking.spans.(origin) in
  checking.state.diagnostics <-
    Diagnostic.make ~fixes ~code:(Capabilities code) span message :: checking.state.diagnostics

type scope_kind = Function_body | Lambda_body of Core.origin | Restricted of string

type scope = {
  available : Types.capability_set;
  kind : scope_kind;
  implemented_capability : Types.capability option;
}

let panic_only description =
  {
    available = Types.capability_set [ panic ];
    kind = Restricted description;
    implemented_capability = None;
  }

let no_capabilities description =
  {
    available = Types.no_capabilities;
    kind = Restricted description;
    implemented_capability = None;
  }

let check_grant checking (origin : Core.origin) ~subject package (uses : Types.capability_set) =
  List.iter
    (fun capability ->
      report checking Not_granted origin (Interface.Grants.message ~subject ~of_:package capability))
    (Interface.Grants.missing checking.state.lookups.interface ~package:checking.state.package
       ~of_:package uses)

let check_callee_grants checking (origin : Core.origin) (callee : Core.callee) =
  let state = checking.state in
  match callee with
  | Function { path; _ } ->
      Option.iter
        (fun (signature : Types.signature) ->
          check_grant checking origin
            ~subject:(Printf.sprintf "`%s`" (Path.show path))
            (Path.package path) signature.uses)
        (Interface.Impls.signature state.lookups.interface path)
  | Trait_method { trait; name; receiver; evidence; _ } -> (
      (match Members.trait_method state.lookups trait.trait name receiver with
      | Some method_ ->
          check_grant checking origin
            ~subject:(Printf.sprintf "`%s.%s`" (Path.show trait.trait) name)
            (Path.package trait.trait)
            (Interface.Definition.method_signature state.lookups.interface ~owner:trait.trait
               method_)
              .uses
      | None -> ());
      match evidence with
      | Impl { impl; _ } -> (
          match Interface.Impls.impl_interface state.lookups.interface impl with
          | Some interface when List.mem (name, receiver) interface.impl_methods ->
              Option.iter
                (fun (signature : Types.signature) ->
                  check_grant checking origin
                    ~subject:
                      (Printf.sprintf "The `impl` of `%s` for `%s`"
                         (Types.show_trait interface.implements)
                         (Types.show interface.for_type))
                    (Path.package impl) signature.uses)
                (Interface.Impls.signature state.lookups.interface
                   (Method { owner = impl; name; receiver }))
          | Some _ | None -> ())
      | Bound | Dynamic -> ())
  | Capability_method _ | Intrinsic _ | Indirect _ -> ()

let require_available checking scope (origin : Core.origin) ?(for_implementation = false)
    ?(indirect_call = false) (required : Types.capability_set) =
  let state = checking.state in
  let superset =
    if indirect_call then
      Types.capability_union scope.available
        (Types.capability_set (Option.to_list scope.implemented_capability))
    else scope.available
  in
  let report_missing (missing : Types.capability_set) =
    List.iter
      (fun capability ->
        let shown = Types.show_capability capability in
        match scope.kind with
        | Lambda_body lambda ->
            report checking Lambda_uses lambda
              (Printf.sprintf
                 "This lambda uses `%s`, which the function type it is passed as does not allow."
                 shown)
        | Restricted description when scope.available = Types.no_capabilities ->
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
        | Function_body when for_implementation ->
            report checking Not_available origin
              (Printf.sprintf "This implementation uses `%s`, which is not available here." shown)
        | Function_body -> (
            match capability with
            | Types.Capability _ ->
                report checking Not_available origin
                  (Printf.sprintf
                     "This call uses `%s`, which is not available here. Declare it with `uses %s`, \
                      or `provide` an implementation."
                     shown shown)
            | Capability_parameter _ | Capability_projection _ | Capability_variable _ ->
                report checking Not_available origin
                  (Printf.sprintf
                     "This call uses `%s`, which is not available here. Declare it with `uses %s`."
                     shown shown)))
      (missing :> Types.capability list)
  in
  if required <> Types.no_capabilities then
    state.capability_constraints <-
      { subset = required; superset; report_missing } :: state.capability_constraints

let require_intrinsic_uses checking scope (origin : Core.origin) operation =
  if Option.is_none scope.implemented_capability then
    require_available checking scope origin
      (Types.capability_set
         (List.map (fun capability -> Types.Capability capability) (Intrinsic.uses operation)))

let require_callee_uses checking scope (origin : Core.origin) (callee : Core.callee) =
  let state = checking.state in
  check_callee_grants checking origin callee;
  match callee with
  | Function { path; _ } ->
      require_available checking scope origin
        (match Interface.Impls.signature state.lookups.interface path with
        | Some signature -> signature.uses
        | None -> Types.no_capabilities)
  | Trait_method { trait; name; receiver; self_type; type_arguments; _ } ->
      require_available checking scope origin
        (match
           ( Members.trait_method state.lookups trait.trait name receiver,
             Interface.Definition.trait_interface state.lookups.interface trait.trait )
         with
        | Some method_, Some interface ->
            let signature =
              Interface.Definition.method_signature state.lookups.interface ~owner:trait.trait
                method_
            in
            Interface.Impls.normalize_capabilities state.lookups.interface ~bounds:(bounds state)
              (Types.substitute_capabilities
                 (Interface.Properties.trait_substitution interface ~self:self_type trait
                 @ Option.value ~default:[]
                     (Types.substitution_of signature.generics type_arguments))
                 signature.uses)
        | _ -> Types.no_capabilities)
  | Capability_method { capability; _ } ->
      require_available checking scope origin (Types.capability_set [ Types.Capability capability ])
  | Intrinsic { operation; _ } -> require_intrinsic_uses checking scope origin operation
  | Indirect _ -> ()

let rec check_expression checking scope (node : Core.expression) =
  match node.kind with
  | Lambda { body; _ } ->
      let uses =
        match node.type_ with Types.Function { uses; _ } -> uses | _ -> Types.no_capabilities
      in
      check_block checking
        { available = uses; kind = Lambda_body node.origin; implemented_capability = None }
        body
  | Provide { implementations; body } -> check_provide checking scope implementations body
  | Quantified _ ->
      check_children checking (no_capabilities "a quantifier's body") (`Expression node)
  | Function_value { path; _ } ->
      check_callee_grants checking node.origin (Function { path; type_arguments = [] })
  | Call call -> (
      check_children checking scope (`Expression node);
      check_callee_grants checking node.origin call.callee;
      require_available checking scope node.origin
        ~indirect_call:(match call.callee with Indirect _ -> true | _ -> false)
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
  | `Expression inner -> Core_walk.expression_children visit inner
  | `Statement inner -> Core_walk.statement_children visit inner
  | `Pattern inner -> Core_walk.pattern_children visit inner

and check_block checking scope (body : Core.block) =
  List.iter (check_statement checking scope) body.statements;
  Option.iter (check_expression checking scope) body.value

and check_statement checking scope (statement : Core.statement) =
  match statement.kind with
  | Parallel branches ->
      List.iter (check_statement checking (panic_only "a `parallel` branch")) branches
  | Concurrent branches ->
      require_available checking scope statement.origin (Types.capability_set [ tasks ]);
      List.iter (check_statement checking scope) branches
  | For { mode; pattern; iteration; clauses; body } ->
      (match iteration with
      | Integer_range { start; stop; _ } ->
          check_expression checking scope start;
          check_expression checking scope stop
      | Elements { count; element; _ } ->
          check_expression checking scope count;
          Core_walk.place
            { Core_walk.ignore_all with expression = check_expression checking scope }
            element
      | Cursor { cursor; next } ->
          Core_walk.place
            { Core_walk.ignore_all with expression = check_expression checking scope }
            cursor;
          require_callee_uses checking scope statement.origin next);
      check_children checking scope (`Pattern pattern);
      check_loop_clauses checking clauses;
      check_block checking
        (match mode with
        | Parallel_loop -> panic_only "a `parallel for`"
        | Sequential -> scope
        | Concurrent_loop ->
            require_available checking scope statement.origin (Types.capability_set [ tasks ]);
            scope)
        body
  | While { condition; clauses; body; _ } ->
      check_expression checking scope condition;
      check_loop_clauses checking clauses;
      check_block checking scope body
  | Proof body -> check_block checking (no_capabilities "a proof") body
  | _ -> check_children checking scope (`Statement statement)

and check_loop_clauses checking (clauses : Core.loop_clause list) =
  List.iter
    (Core_walk.loop_clause
       {
         Core_walk.ignore_all with
         expression = check_expression checking (no_capabilities "a specification");
       })
    clauses

and check_provide checking scope implementations body =
  let state = checking.state in
  let provided = ref Types.no_capabilities in
  List.iter
    (fun (implementation : Core.implementation) ->
      Core_walk.operand
        { Core_walk.ignore_all with expression = check_expression checking scope }
        implementation.value;
      let impls = Form.capability_impls state implementation.type_ in
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
      let start = checking.spans.(implementation.origin).start in
      if is_place && mutates && not provided_mut then
        report checking Provide_mode implementation.origin
          ~fixes:
            [
              Diagnostic.fix "Provide it `mut`."
                [ Diagnostic.insert (Source.Definition_span.zero_width start) "mut " ];
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
            (Path.package provided.impl) interface.impl_uses;
          require_available checking scope implementation.origin ~for_implementation:true
            interface.impl_uses)
        impls;
      provided :=
        Types.capability_union !provided
          (Types.capability_set
             (List.map
                (fun ((provided : Core.provided), _) -> Types.Capability provided.capability)
                impls)))
    implementations;
  checking.provides <- (scope.available, implementations, body) :: checking.provides;
  check_block checking
    { scope with available = Types.capability_union scope.available !provided }
    body

let solve (state : state) =
  state.capability_constraints <-
    List.map
      (fun (constraint_ : subset_constraint) ->
        {
          constraint_ with
          subset = final_capabilities state constraint_.subset;
          superset = final_capabilities state constraint_.superset;
        })
      state.capability_constraints;
  let solution = Hashtbl.create 8 in
  let value_of variable =
    Option.value ~default:Types.no_capabilities (Hashtbl.find_opt solution variable)
  in
  let substitute =
    Types.flat_map_capabilities (function
      | Types.Capability_variable variable -> (value_of variable :> Types.capability list)
      | capability -> [ capability ])
  in
  let missing (constraint_ : subset_constraint) =
    Types.capability_difference (substitute constraint_.subset) (substitute constraint_.superset)
  in
  let rec grow () =
    let changed =
      List.fold_left
        (fun changed (constraint_ : subset_constraint) ->
          let variables =
            List.filter_map
              (function Types.Capability_variable variable -> Some variable | _ -> None)
              (constraint_.superset :> Types.capability list)
          in
          let missing = missing constraint_ in
          if variables = [] || missing = Types.no_capabilities then changed
          else begin
            List.iter
              (fun variable ->
                Hashtbl.replace solution variable
                  (Types.capability_union missing (value_of variable)))
              variables;
            true
          end)
        false state.capability_constraints
    in
    if changed then grow ()
  in
  grow ();
  state.capability_solution <- Some solution;
  List.iter
    (fun (constraint_ : subset_constraint) ->
      let missing = missing constraint_ in
      if missing <> Types.no_capabilities then constraint_.report_missing missing)
    (List.rev state.capability_constraints)

let rec can_call_capability_code (state : state) ~bounds ?(seen = []) (type_ : Types.ty) =
  let inside = can_call_capability_code state ~bounds ~seen in
  let trait_uses (trait : Types.trait_reference) =
    let can_hold_a_capability : Types.capability -> bool = function
      | Capability_projection _ -> ( match type_ with Types.Any _ -> false | _ -> true)
      | Capability _ | Capability_parameter _ | Capability_variable _ -> true
    in
    List.exists
      (fun (bound : Types.trait_reference) ->
        match Interface.Definition.trait_interface state.lookups.interface bound.trait with
        | Some interface ->
            List.exists
              (fun (method_ : Types.trait_method) ->
                List.exists can_hold_a_capability
                  ((Interface.Definition.method_signature state.lookups.interface ~owner:bound.trait
                      method_)
                     .uses
                    :> Types.capability list))
              interface.methods
        | None -> false)
      (trait :: Interface.Properties.bound_closure state.lookups.interface ~self:type_ trait)
  in
  let arguments =
    List.exists (function
      | Types.Type argument -> inside argument
      | Types.Value _ | Types.Capabilities _ -> false)
  in
  match type_ with
  | Types.Function { uses; inputs; output; _ } ->
      uses <> Types.no_capabilities
      || List.exists (fun (_, input) -> inside input) inputs
      || inside (Types.result_type output)
  | Types.Any trait -> trait_uses trait
  | Types.Parameter parameter -> List.exists trait_uses (bounds parameter)
  | Types.Named { path; arguments = type_arguments } -> (
      arguments type_arguments
      || (not (List.exists (Path.equal path) seen))
         &&
         let inside = can_call_capability_code state ~bounds ~seen:(path :: seen) in
         let fields = List.exists (fun (field : Types.field) -> inside field.field_type) in
         (match Members.fields state.lookups path type_arguments with
           | Some named_fields -> fields named_fields
           | None -> false)
         ||
         match Members.variants state.lookups path type_arguments with
         | Some variants ->
             List.exists
               (fun (variant : Types.variant) -> fields (Option.value ~default:[] variant.fields))
               variants
         | None -> false)
  | Types.Projection _ | Types.Never | Types.Integer | Types.Literal _ | Types.Variable _
  | Types.Hole | Types.Error _ ->
      false

let check_monitor_lock checking ~(solved : int -> Types.capability_set) available implementations =
  let state = checking.state in
  let provides_tasks (implementation : Core.implementation) =
    List.exists
      (fun ((provided : Core.provided), (_ : Types.impl_interface)) ->
        Path.equal provided.capability (Well_known.path Tasks))
      (Form.capability_impls state implementation.type_)
  in
  let available =
    Types.flat_map_capabilities
      (function
        | Types.Capability_variable variable -> (solved variable :> Types.capability list)
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
              Interface.Definition.trait_interface state.lookups.interface provided.capability
            with
            | Some capability ->
                List.iter
                  (fun (method_ : Types.trait_method) ->
                    let signature =
                      Interface.Definition.method_signature state.lookups.interface
                        ~owner:provided.capability method_
                    in
                    let bounds = Types.bounds_of signature.generics in
                    match
                      List.find_opt
                        (fun (parameter : Types.parameter_info) ->
                          can_call_capability_code state ~bounds parameter.type_)
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
          (Form.capability_impls state implementation.type_))
    implementations

let check (state : state) (lowered : Environment.lowered_interface) (form : Core.t) =
  let checking = { state; spans = Syntax_walk.spans state.definition; provides = [] } in
  let function_body ?implemented_capability available =
    { available; kind = Function_body; implemented_capability }
  in
  let check_specification = check_expression checking (no_capabilities "a specification") in
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
          check_block checking (no_capabilities "a law") law.body)
        laws
  | Constant _ | Test _ | Law_proof _ | Empty -> ());
  (match (form.definition, state.definition.kind, lowered.interface) with
  | Function { body; _ }, (Function _ | Method_declaration _), Function_interface signature ->
      let implemented_capability =
        Option.bind (state.lookups.interface.names.container state.key) (fun container ->
            match state.lookups.interface.lowered_interface container with
            | Some { interface = Impl_interface impl; _ }
              when Resolve.Names.kind_of state.lookups.interface.names impl.implements.trait
                   = Some Capability ->
                Some (Types.Capability impl.implements.trait)
            | _ -> None)
      in
      Option.iter
        (check_block checking
           (function_body ?implemented_capability
              (Interface.Impls.normalize_capabilities state.lookups.interface ~bounds:(bounds state)
                 signature.uses)))
        body
  | Test (Some body), _, Test_interface uses ->
      check_block checking
        (function_body (Types.capability_union uses (Types.capability_set [ panic ])))
        body
  | Function { body = Some body; _ }, Theorem _, _ | Law_proof { body = Some body; _ }, _, _ ->
      check_block checking (no_capabilities "a proof") body
  | _ -> ());
  solve state;
  let solved variable =
    match state.capability_solution with
    | Some solution ->
        Option.value ~default:Types.no_capabilities (Hashtbl.find_opt solution variable)
    | None -> Types.no_capabilities
  in
  List.iter
    (fun (available, implementations, body) ->
      match Core_walk.tasks_use ~solved body with
      | No_tasks -> ()
      | Through_parameter -> check_monitor_callbacks checking implementations
      | Uses_tasks ->
          check_monitor_callbacks checking implementations;
          check_monitor_lock checking ~solved available implementations)
    (List.rev checking.provides)
