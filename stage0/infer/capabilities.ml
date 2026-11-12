(* The capability check: a call can use only the capabilities that are
   available at the call.

   The check runs on a definition's core form, because the core form has a
   node for every call, including the calls that desugaring introduces (the
   [each] of a [for] loop, the [display] of an interpolated value).

   The capabilities that are available at a point of the code are its scope:
   - in a function body: the function's [uses], and the capabilities of
     every enclosing [provide];
   - in a lambda body: the [uses] of the lambda's function type;
   - in a specification, a proof, or a [parallel] branch: fewer than the
     function declares (see [scope_kind]).

   The check cannot decide each call independently, because a capability set
   can contain capability variables. A capability variable is the set that a
   capability parameter is instantiated with at one call, and it is solved
   from constraints. So the check only collects constraints of the form "the
   capabilities that this call requires are a subset of the capabilities
   available here". [solve] then solves all constraints of the definition,
   including those that type inference collected when it converted function
   values to function types. *)

open Syntax
module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
open State

let panic : T.capability = Capability (Well_known.path Panic)

(* The capability that [concurrent] code uses, because its behavior can
   depend on task scheduling. *)
let tasks : T.capability = Capability Core_walk.tasks_capability

(* [spans] maps a syntax node id to its span. A core node is reported at the
   span of its origin. *)
type checking = {
  state : state;
  spans : span array;
  mutable provides : (T.capability list * Core.implementation list * Core.block) list;
      (** Every [provide] of the definition: the capabilities available at it, its implementations,
          and its body. *)
}

let report checking ?(fixes = []) code (origin : Core.origin) message =
  let span = checking.spans.(origin) in
  checking.state.diagnostics <-
    Diagnostic.make ~fixes ~code:(Capabilities code) (Source.span span.start span.stop) message
    :: checking.state.diagnostics

let union left right = List.sort_uniq compare (left @ right)

type scope_kind =
  | Function_body  (** The body of a function or a test. *)
  | Lambda_body of Core.origin
      (** The body of the lambda with this origin. The available capabilities are the [uses] of the
          lambda's type. If that type has a capability variable, solving adds the capabilities that
          the body requires to the variable. *)
  | Restricted of string
      (** Code that may use less than the enclosing function declares: a [parallel] branch (only
          [Panic]), or a specification or proof (nothing). The string names the kind of code, for
          error messages. *)

type scope = {
  available : T.capability list;
  kind : scope_kind;
  implemented_capability : T.capability option;
      (** Set in a method of an [impl] of a capability, and not in a lambda, a [parallel] branch, or
          a specification inside it. An indirect call (a call through a function value) in such a
          method may use that capability, because the method can pass its own implementation on to
          the callee. A call of an intrinsic in such a method needs no capability (see
          [require_intrinsic_uses]). *)
}

(* The scope of a [parallel] branch: only [Panic] is available. *)
let panic_only description =
  { available = [ panic ]; kind = Restricted description; implemented_capability = None }

(* The scope of a specification or a proof: no capability is available, not
   even [Panic], because a specification must denote a value. *)
let no_capabilities description =
  { available = []; kind = Restricted description; implemented_capability = None }

(* A dependency may only use the capabilities that the package's manifest
   grants it. [uses] are the capabilities that [what], a definition of
   [package], uses. Capability parameters are not checked: they are
   instantiated by the caller. *)
let check_grant checking (origin : Core.origin) ~what package (uses : T.capability list) =
  List.iter
    (fun capability ->
      report checking Not_granted origin (Interface.Grants.message ~what ~of_:package capability))
    (Interface.Grants.missing checking.state.database ~package:checking.state.package ~of_:package
       uses)

(* Checks the grants for a callee: for a function, its [uses]; for a trait
   method, the [uses] the trait declares and the [uses] of the [impl] that
   runs. *)
let check_callee_grants checking (origin : Core.origin) (callee : Core.callee) =
  let state = checking.state in
  match callee with
  | Function { path; _ } ->
      Option.iter
        (fun (signature : T.signature) ->
          check_grant checking origin
            ~what:(Printf.sprintf "`%s`" (Path.show path))
            (Path.package path) signature.uses)
        (Query.demand state.database Environment.signature path)
  | Trait_method { trait; name; receiver; evidence; _ } -> (
      (match Members.trait_method state.database trait.trait name receiver with
      | Some method_ ->
          check_grant checking origin
            ~what:(Printf.sprintf "`%s.%s`" (Path.show trait.trait) name)
            (Path.package trait.trait) method_.method_signature.uses
      | None -> ());
      match evidence with
      | Impl { impl; _ } -> (
          match Interface.Impls.impl_interface state.database impl with
          | Some interface ->
              List.iter
                (fun (method_name, method_receiver, (method_signature : T.signature)) ->
                  if method_name = name && method_receiver = receiver then
                    check_grant checking origin
                      ~what:
                        (Printf.sprintf "The `impl` of `%s` for `%s`"
                           (T.show_trait interface.implements)
                           (T.show interface.for_type))
                      (Path.package impl) method_signature.uses)
                interface.impl_methods
          | None -> ())
      | Bound | Dynamic -> ())
  | Capability_method _ | Intrinsic _ | Indirect _ -> ()

(* Adds the constraint that [required] is a subset of the capabilities
   available in [scope]. [origin] is where a violation is reported. *)
let require_available checking scope (origin : Core.origin) ?(for_implementation = false)
    ?(indirect_call = false) (required : T.capability list) =
  let state = checking.state in
  let superset =
    if indirect_call then union scope.available (Option.to_list scope.implemented_capability)
    else scope.available
  in
  let report_missing =
    List.iter (fun capability ->
        let shown = T.show_capability capability in
        match scope.kind with
        | Lambda_body lambda ->
            report checking Lambda_uses lambda
              (Printf.sprintf
                 "This lambda uses `%s`, which the function type it is passed as does not allow."
                 shown)
        | Restricted description when scope.available = [] ->
            report checking Not_available origin
              (Printf.sprintf
                 "This call uses `%s`, but %s may use no capabilities, not even `Panic`: what it \
                  means must be a value. A function that fails on some inputs says so with \
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
            | T.Capability _ ->
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
  in
  if required <> [] then
    state.capability_constraints <-
      { subset = required; superset; report_missing } :: state.capability_constraints

(* An intrinsic has no signature with a [uses] clause: [Intrinsic.uses] lists
   the capabilities that a call of it requires.

   A method of an [impl] of a capability is exempt. Its callers reach it
   only through a capability call, which is an effect that their signatures
   declare, so no code without capabilities can observe what the intrinsic
   does. A capability is not a trait, so the method cannot be called on the
   value, through a bound, or through [any]. A lambda, a [parallel] branch,
   and a specification inside the method are not exempt, and neither is a
   helper function that the method calls. *)
let require_intrinsic_uses checking scope (origin : Core.origin) operation =
  if Option.is_none scope.implemented_capability then
    require_available checking scope origin
      (List.map (fun capability -> T.Capability capability) (Intrinsic.uses operation))

(* Handles a callee that is stored in a node other than a [Call] (see
   [Core_walk.visit]). It requires the [uses] of the callee's signature. A
   trait's method requires the [uses] that the trait declares, for the type
   that the method is called on: [next] declares [Self.Uses]. *)
let require_callee_uses checking scope (origin : Core.origin) (callee : Core.callee) =
  let state = checking.state in
  check_callee_grants checking origin callee;
  match callee with
  | Function { path; _ } ->
      require_available checking scope origin
        (match Interface.Impls.signature state.database path with
        | Some signature -> signature.uses
        | None -> [])
  | Trait_method { trait; name; receiver; self_type; type_arguments; _ } ->
      require_available checking scope origin
        (match
           ( Members.trait_method state.database trait.trait name receiver,
             Query.demand state.database Environment.trait_interface trait.trait )
         with
        | Some method_, Some interface ->
            let signature = method_.method_signature in
            Impls.normalize_capabilities state.database ~bounds:(bounds state)
              (T.substitute_capabilities
                 (Interface.Properties.trait_substitution interface ~self:self_type trait
                 @ Option.value ~default:[] (T.substitution_of signature.generics type_arguments))
                 signature.uses)
        | _ -> [])
  | Capability_method { capability; _ } ->
      require_available checking scope origin [ T.Capability capability ]
  | Intrinsic { operation; _ } -> require_intrinsic_uses checking scope origin operation
  | Indirect _ -> ()

let rec check_expression checking scope (node : Core.expression) =
  match node.kind with
  | Lambda { body; _ } ->
      let uses = match node.type_ with T.Function { uses; _ } -> uses | _ -> [] in
      check_block checking
        { available = uses; kind = Lambda_body node.origin; implemented_capability = None }
        body
  | Provide { implementations; body } -> check_provide checking scope implementations body
  | Quantified _ ->
      (* The body of a quantifier is a specification even when the
         quantifier is in executable code. *)
      check_children checking (no_capabilities "a quantifier's body") (`Expression node)
  | Function_value { path; _ } ->
      (* Taking a function as a value lets the holder call it, so the grants
         are checked here as they are for a call. *)
      check_callee_grants checking node.origin (Function { path; type_arguments = [] })
  | Cursor_next cursor ->
      check_children checking scope (`Expression node);
      require_available checking scope node.origin
        (Impls.cursor_uses checking.state.database (Core_walk.place_type cursor))
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
      (* A branch may only use [Panic], so the result of a [parallel] block
         does not depend on the order its branches run in. *)
      List.iter (check_statement checking (panic_only "a `parallel` branch")) branches
  | Concurrent branches ->
      (* A branch may use the capabilities that are available at the block. *)
      require_available checking scope statement.origin [ tasks ];
      List.iter (check_statement checking scope) branches
  | For { mode; pattern; iteration; clauses; body } ->
      (match iteration with
      | Integer_range { start; stop; _ } ->
          check_expression checking scope start;
          check_expression checking scope stop
      | Yielding_call call -> check_expression checking scope call
      | Cursor { cursor; next } -> (
          Core_walk.place
            { Core_walk.ignore_all with expression = check_expression checking scope }
            cursor;
          match next with
          | Some next -> require_callee_uses checking scope statement.origin next
          | None ->
              require_available checking scope statement.origin
                (Impls.cursor_uses checking.state.database (Core_walk.place_type cursor))));
      check_children checking scope (`Pattern pattern);
      check_loop_clauses checking clauses;
      check_block checking
        (match mode with
        | Parallel_loop -> panic_only "a `parallel for`"
        | Sequential -> scope
        | Concurrent_loop ->
            require_available checking scope statement.origin [ tasks ];
            scope)
        body
  | While { condition; clauses; body } ->
      check_expression checking scope condition;
      check_loop_clauses checking clauses;
      check_block checking scope body
  | Proof body -> check_block checking (no_capabilities "a proof") body
  | _ -> check_children checking scope (`Statement statement)

(* Loop clauses ([invariant], [decreases], [cost]) are specifications. *)
and check_loop_clauses checking (clauses : Core.loop_clause list) =
  List.iter
    (Core_walk.loop_clause
       {
         Core_walk.ignore_all with
         expression = check_expression checking (no_capabilities "a specification");
       })
    clauses

(* A [provide] block. The type of each implementation implements one or
   more capabilities. Those capabilities are available in the body. Each
   [impl] has its own [uses], which must be available where the [provide]
   is. A place must be provided [mut] exactly when one of the [impl]s has a
   [mut self] method. *)
and check_provide checking scope implementations body =
  let state = checking.state in
  let provided = ref [] in
  List.iter
    (fun (implementation : Core.implementation) ->
      Core_walk.operand
        { Core_walk.ignore_all with expression = check_expression checking scope }
        implementation.value;
      let impls = Form.capability_impls state implementation.type_ in
      if impls = [] then
        report checking Not_an_implementation implementation.origin
          (Printf.sprintf "`%s` implements no capability, so it provides nothing."
             (T.show implementation.type_));
      let mutates =
        List.exists
          (fun (_, (interface : T.impl_interface)) ->
            List.exists (fun (_, receiver, _) -> receiver = Path.Mut) interface.impl_methods)
          impls
      in
      let marked_mut = implementation.mode = Mut in
      let is_place = match implementation.value with Place _ -> true | Value _ -> false in
      let start = checking.spans.(implementation.origin).start in
      if is_place && mutates && not marked_mut then
        report checking Provide_mark implementation.origin
          ~fixes:[ Diagnostic.fix "Mark it `mut`." [ Diagnostic.insert start "mut " ] ]
          "This implementation changes its own state, so the place is provided `mut`."
      else if marked_mut && not mutates then
        report checking Provide_mark implementation.origin
          ~fixes:
            [
              Diagnostic.fix "Remove the mark."
                [ Diagnostic.delete (Source.span start (start + 4)) ];
            ]
          "This implementation never changes its own state, so the place is provided without `mut`.";
      List.iter
        (fun ((found : Core.provided), (interface : T.impl_interface)) ->
          check_grant checking implementation.origin
            ~what:
              (Printf.sprintf "The `impl` of `%s` for `%s`" (Path.show found.capability)
                 (T.show interface.for_type))
            (Path.package found.impl) interface.impl_uses;
          require_available checking scope implementation.origin ~for_implementation:true
            interface.impl_uses)
        impls;
      provided :=
        union !provided
          (List.map (fun ((found : Core.provided), _) -> T.Capability found.capability) impls))
    implementations;
  checking.provides <- (scope.available, implementations, body) :: checking.provides;
  check_block checking { scope with available = union scope.available !provided } body

(* Solves the definition's capability constraints.

   Each capability variable starts as the empty set. For every constraint
   whose superset has a variable, the capabilities that the subset has and
   the superset lacks are added to that variable. This repeats until
   nothing changes, which gives the least solution. Then every constraint
   that still does not hold is reported. *)
let solve (state : state) =
  (* A constraint was collected while types were inferred, so its sets can
     name an associated capability set of a type that was not known then. *)
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
  let value_of variable = Option.value ~default:[] (Hashtbl.find_opt solution variable) in
  let substitute capabilities =
    List.concat_map
      (function
        | T.Capability_variable variable -> value_of variable | capability -> [ capability ])
      capabilities
  in
  let missing (constraint_ : subset_constraint) =
    let superset = substitute constraint_.superset in
    List.sort_uniq compare
      (List.filter
         (fun capability -> not (List.mem capability superset))
         (substitute constraint_.subset))
  in
  let rec grow () =
    let changed =
      List.fold_left
        (fun changed (constraint_ : subset_constraint) ->
          let variables =
            List.filter_map
              (function T.Capability_variable variable -> Some variable | _ -> None)
              constraint_.superset
          in
          match (variables, missing constraint_) with
          | [], _ | _, [] -> changed
          | variables, missing ->
              List.iter
                (fun variable ->
                  Hashtbl.replace solution variable (union missing (value_of variable)))
                variables;
              true)
        false state.capability_constraints
    in
    if changed then grow ()
  in
  grow ();
  state.capability_solution <- Some solution;
  List.iter
    (fun (constraint_ : subset_constraint) ->
      match missing constraint_ with [] -> () | missing -> constraint_.report_missing missing)
    (List.rev state.capability_constraints)

(* Whether a value of a type can call code that uses a capability: the type
   is a function type with a [uses] clause, an [any] type or a bounded type
   parameter whose trait has a method with one, or a type that contains one
   of these at any depth. An associated capability set is empty for an [any]
   type, and can hold any capability for a type parameter. *)
let rec can_call_capability_code (state : state) ~bounds ?(seen = []) (type_ : T.ty) =
  let inside = can_call_capability_code state ~bounds ~seen in
  let trait_uses (trait : T.trait_reference) =
    let can_hold_a_capability : T.capability -> bool = function
      | Capability_projection _ -> ( match type_ with T.Any _ -> false | _ -> true)
      | Capability _ | Capability_parameter _ | Capability_variable _ -> true
    in
    List.exists
      (fun (bound : T.trait_reference) ->
        match Query.demand state.database Environment.trait_interface bound.trait with
        | Some interface ->
            List.exists
              (fun (method_ : T.trait_method) ->
                List.exists can_hold_a_capability method_.method_signature.uses)
              interface.methods
        | None -> false)
      (trait :: Interface.Properties.bound_closure state.database ~self:type_ trait)
  in
  let arguments =
    List.exists (function
      | T.Type argument -> inside argument
      | T.Value _ | T.Capabilities _ -> false)
  in
  match type_ with
  | T.Function { uses; inputs; output; _ } ->
      uses <> []
      || List.exists (fun (_, input) -> inside input) inputs
      || inside (match output with Returns given | Yields (_, given) | Lends (_, given) -> given)
  | T.Any trait -> trait_uses trait
  | T.Parameter parameter -> List.exists trait_uses (bounds parameter)
  | T.Cursor { arguments = given; _ } -> arguments given
  | T.Named { path; arguments = given } -> (
      arguments given
      || (not (List.exists (Path.equal path) seen))
         &&
         let inside = can_call_capability_code state ~bounds ~seen:(path :: seen) in
         let fields = List.exists (fun (field : T.field) -> inside field.field_type) in
         (match Members.fields state.database path given with
           | Some found -> fields found
           | None -> false)
         ||
         match Members.variants state.database path given with
         | Some variants ->
             List.exists
               (fun (variant : T.variant) -> fields (Option.value ~default:[] variant.fields))
               variants
         | None -> false)
  | T.Projection _ | T.Never | T.Integer | T.Literal _ | T.Variable _ | T.Hole | T.Error _ -> false

(* Data race prevention. A monitor locks its methods through [Tasks]: code
   generation wraps each method with [Tasks.lock] and [Tasks.unlock], using
   the implementation of [Tasks] in the same [provide], or else the one that
   is available at the [provide]. If the body uses [Tasks] and neither
   exists, the only implementation of [Tasks] is provided in a nested
   [provide]. The methods then have no lock, and two tasks could run a [mut
   self] method at the same time.

   A body that can use [Tasks] only through a capability parameter is not
   checked here. Each instance of the function receives evidence for the
   capabilities that the parameter is instantiated with, so evidence for
   [Tasks] exists at the [provide] exactly in the instances that can start
   tasks, and code generation adds the lock in those.

   An implementation of [Tasks] itself is not a monitor. *)
let check_monitor_lock checking ~solved available implementations =
  let state = checking.state in
  let provides_tasks (implementation : Core.implementation) =
    List.exists
      (fun ((found : Core.provided), (_ : T.impl_interface)) ->
        Path.equal found.capability Core_walk.tasks_capability)
      (Form.capability_impls state implementation.type_)
  in
  let available =
    List.concat_map
      (function T.Capability_variable variable -> solved variable | capability -> [ capability ])
      available
  in
  if not (List.mem tasks available || List.exists provides_tasks implementations) then
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
               (T.show implementation.type_)))
      implementations

(* Deadlock prevention. Where the body of a [provide] can use [Tasks], an
   implementation that is provided [mut] is a monitor: each call of its
   methods runs to completion before the next call starts.

   An implementation calls only capabilities that are provided outside its
   own [provide], so tasks acquire monitors from the innermost outward,
   which cannot deadlock. A callback parameter breaks that order: a callback
   that uses a capability could enter the monitor of a nested [provide]
   while the outer monitor is held. So a capability that a monitor
   implements has no method with a parameter that can call code with a
   [uses] clause. *)
let check_monitor_callbacks checking implementations =
  let state = checking.state in
  List.iter
    (fun (implementation : Core.implementation) ->
      if implementation.mode = Mut then
        List.iter
          (fun ((found : Core.provided), (_ : T.impl_interface)) ->
            match Query.demand state.database Environment.trait_interface found.capability with
            | Some capability ->
                List.iter
                  (fun (method_ : T.trait_method) ->
                    let signature = method_.method_signature in
                    let bounds (parameter : T.parameter) =
                      List.concat_map
                        (fun (generic : T.generic) ->
                          match generic.kind with
                          | Type_generic bounds when generic.generic = parameter -> bounds
                          | _ -> [])
                        signature.generics
                    in
                    match
                      List.find_opt
                        (fun (parameter : T.parameter_info) ->
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
                             (T.show_capability (T.Capability found.capability))
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
      List.iter check_specification invariants;
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
      (* If this function is a method of an [impl] of a capability, that
         capability is the scope's [implemented_capability]. *)
      let implemented_capability =
        Option.bind (Query.demand state.database Names.container state.key) (fun container ->
            match Query.demand state.database Environment.lowered_interface container with
            | Some { interface = Impl_interface impl; _ }
              when Interface.Summary.kind_of state.database impl.implements.trait = Some Capability
              ->
                Some (T.Capability impl.implements.trait)
            | _ -> None)
      in
      Option.iter
        (check_block checking
           (function_body ?implemented_capability
              (Impls.normalize_capabilities state.database ~bounds:(bounds state) signature.uses)))
        body
  | Test body, _, Test_interface uses ->
      check_block checking (function_body (union uses [ panic ])) body
  | Function { body = Some body; _ }, Theorem _, _ | Law_proof { body; _ }, _, _ ->
      check_block checking (no_capabilities "a proof") body
  | _ -> ());
  solve state;
  (* Whether a [provide]'s body can use [Tasks] is known once the
     capability variables are solved. *)
  let solved variable =
    match state.capability_solution with
    | Some solution -> Option.value ~default:[] (Hashtbl.find_opt solution variable)
    | None -> []
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
