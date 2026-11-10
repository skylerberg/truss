(* What code may call: capabilities at each point, what lambdas use,
   capability parameters, [provide], and what a dependency is granted.

   This runs on a definition's core form, where every call the code makes is
   a node, whether it was written as a call or as a loop, an operator, or an
   interpolation. It sets on each call what each capability parameter of
   what is called stands for there, and on each [provide] what its
   implementations provide. Each walk returns the capabilities its code
   uses, which is what a lambda's [uses] are inferred from. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
open State

let panic : T.capability =
  Capability
    (Top { module_ = { package = "standard"; modules = [ "capabilities" ] }; name = "Panic" })

(* The definition being checked, and where each node of its syntax is, by
   which a node of the form is reported. *)
type checking = { state : state; spans : span array }

let report checking ?(fixes = []) code (origin : Core.origin) message =
  let span = checking.spans.(origin) in
  checking.state.diagnostics <-
    Diagnostic.make ~fixes ~code:(Capabilities code) (Source.span span.start span.stop) message
    :: checking.state.diagnostics

let show_capability = function
  | T.Capability (Top { name; _ }) -> name
  | T.Capability path -> Path.show path
  | T.Capability_parameter { name; _ } -> name

let union left right = List.sort_uniq compare (left @ right)
let minus left right = List.filter (fun capability -> not (List.mem capability right)) left

(* Where code is: what it may use, and whether it reports what it may not
   (inside a lambda, what it uses is collected instead, for its [uses]).
   [restricted] names code that may use less than the function declares: a
   [parallel] branch, which may use only [Panic], or a specification or a
   proof, which may use nothing. *)
type scope = {
  available : T.capability list;
  collecting : bool;
  restricted : string option;
  handed_on : T.capability option;
      (** In an implementation of a capability, that capability, which only calls through function
          values may use. *)
  own : T.parameter list;
      (** The capability parameters of the function being checked, each of which stands for itself.
      *)
  passed : (T.parameter * T.capability list ref) list;
      (** In the arguments of a call, each capability parameter of what it calls, with what has been
          passed for it so far, nearest call first. *)
}

(* Code that may use only [Panic], whatever the function declares. *)
let only_panic scope reason =
  { scope with available = [ panic ]; collecting = false; restricted = Some reason }

(* Code that may use no capability at all, not even [Panic]: a
   specification or a proof, whose meaning must be a value. *)
let pure_only scope reason =
  { scope with available = []; collecting = false; restricted = Some reason }

(* The capabilities a type implements, each with the [impl] that provides
   it, its generic arguments, and its interface. An [impl] lives with its
   type or its capability, so it is in the type's package, this one, or the
   standard library, where the capabilities a dependency could not see are
   not. *)
let capability_impls (state : state) (type_ : T.ty) =
  match type_ with
  | T.Named { path; _ } ->
      List.filter_map
        (fun (trait, _) ->
          if Interface.Summary.kind_of state.database trait = Some Capability then
            match implements state type_ (trait_reference trait) with
            | Some (Interface.Impls.From_impl { impl; substitution }) ->
                Option.map
                  (fun interface ->
                    ({ Core.capability = trait; impl; arguments = substitution }, interface))
                  (Interface.Impls.impl_interface state.database impl)
            | _ -> None
          else None)
        (List.concat_map
           (fun package -> Interface.Impls.impls_for state.database path package)
           (List.sort_uniq compare [ Path.package path; state.package; "standard" ]))
  | _ -> []

(* A dependency may use only what its manifest entry grants: [what] of the
   [package] uses [uses], except what reaches it through a capability
   parameter, which is the caller's own. *)
let check_grant checking (origin : Core.origin) ~what package (uses : T.capability list) =
  List.iter
    (fun capability ->
      report checking Not_granted origin (Interface.Grants.message ~what ~of_:package capability))
    (Interface.Grants.missing checking.state.database ~package:checking.state.package ~of_:package
       uses)

(* A function value that uses more than the function type it meets lists.
   What the type does not list is passed for the type's capability
   parameters, each of which the nearest call around of the function it
   belongs to solves. With no such call, nothing allows it. *)
let pass checking scope (origin : Core.origin) ~what ~uses ~unlisted =
  if unlisted <> [] then
    match
      List.filter_map
        (function
          | T.Capability_parameter parameter -> List.assoc_opt parameter scope.passed
          | T.Capability _ -> None)
        uses
    with
    | [] ->
        List.iter
          (fun capability ->
            report checking Lambda_uses origin
              (Printf.sprintf
                 "%s uses `%s`, which the function type it is passed as does not allow." what
                 (show_capability capability)))
          unlisted
    | solving -> List.iter (fun passed -> passed := union !passed unlisted) solving

(* The signature of what a call calls, whose capability parameters the call
   solves: a function's, or a trait's method's as the trait declares it. *)
let called state (callee : Core.callee) : T.signature option =
  match callee with
  | Function { path; _ } -> Query.demand state.database Environment.signature path
  | Trait_method { trait; name; receiver; _ } ->
      Option.map
        (fun (method_ : T.trait_method) -> method_.method_signature)
        (Members.trait_method state.database trait.trait name receiver)
  | Capability_method _ | Intrinsic _ | Value _ -> None

(* What a dependency's code that is called uses must be granted to it: a
   function's, and for a trait's method what the trait declares for it and
   what the [impl] that runs uses. *)
let check_grants checking (origin : Core.origin) (callee : Core.callee) =
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
  | Capability_method _ | Intrinsic _ | Value _ -> ()

(* What is needed must be available where the code is, unless the code is
   a lambda's, whose needs are collected. *)
let check_available checking scope (origin : Core.origin) ~through_value needed =
  if not scope.collecting then
    List.iter
      (fun capability ->
        if
          not
            (List.mem capability scope.available
            || (through_value && scope.handed_on = Some capability))
        then
          report checking Not_available origin
            (match scope.restricted with
            | Some reason when scope.available = [] ->
                Printf.sprintf
                  "This call uses `%s`, but %s may use no capabilities, not even `Panic`: what it \
                   means must be a value. A function that fails on some inputs says so with \
                   `requires` instead."
                  (show_capability capability) reason
            | Some reason ->
                Printf.sprintf
                  "This call uses `%s`, but %s may use only `Panic`, whatever the function \
                   declares."
                  (show_capability capability) reason
            | None ->
                Printf.sprintf
                  "This call uses `%s`, which is not available here. Declare it with `uses %s`, or \
                   `provide` an implementation."
                  (show_capability capability) (show_capability capability)))
      needed

(* What the tables hold of a call that was written as one is kept the same
   as the form's, for the stages that still read them. *)
let record_in_tables state (origin : Core.origin) (call : Core.call) =
  match state.tables.calls.(origin) with
  | Some recorded
    when match (recorded.callee, call.callee) with
         | Function { path; _ }, Function { path = called; _ } -> Path.equal path called
         | Trait_method { trait; name; _ }, Trait_method { trait = called; name = called_name; _ }
           ->
             Path.equal trait.trait called.trait && name = called_name
         | Capability_method { capability; name }, Capability_method called ->
             Path.equal capability called.capability && name = called.name
         | Intrinsic { operation; _ }, Intrinsic called -> operation = called.operation
         | Function_value, Value _ -> true
         | _ -> false ->
      state.tables.calls.(origin) <-
        Some { recorded with capability_arguments = call.capability_arguments; uses = call.uses }
  | _ -> ()

let rec expression checking scope (node : Core.expression) : T.capability list =
  let state = checking.state in
  (match node.kind with
  | Convert { conversion = Widen; _ } -> (
      match Hashtbl.find_opt state.widened node.origin with
      | Some (uses, unlisted) ->
          pass checking scope node.origin ~what:"This function" ~uses ~unlisted
      | None -> ())
  | _ -> ());
  match node.kind with
  | Lambda { body; _ } -> lambda checking scope node body
  | Provide { implementations; body } -> provide checking scope node implementations body
  | Quantified _ ->
      (* A quantifier's body may use no capability, in code as in a
         specification, since what it means must be a value the prover can
         read. *)
      ignore (inside checking (pure_only scope "a quantifier's body") (`Expression node));
      []
  | Function_value { path; _ } ->
      (* A function taken as a value is named as surely as one that is
         called, and whoever is handed the value may call it. *)
      check_grants checking node.origin (Function { path; type_arguments = [] });
      []
  | Call call ->
      (* What the arguments pass for each capability parameter of what is
         called, which a call of a function by itself leaves as it is. *)
      let callee = called state call.callee in
      let passed =
        match callee with
        | Some signature ->
            List.filter_map
              (fun parameter ->
                if List.mem parameter scope.own then None else Some (parameter, ref []))
              (T.capability_parameters signature.generics)
        | None -> []
      in
      let inner =
        inside checking { scope with passed = passed @ scope.passed } (`Expression node)
      in
      union inner (call_needs checking scope node call passed)
  | _ -> inside checking scope (`Expression node)

(* What the nodes directly inside a node use. *)
and inside checking scope node : T.capability list =
  let used = ref [] in
  let visit : Core_walk.visit =
    {
      expression = (fun inner -> used := union !used (expression checking scope inner));
      statement = (fun inner -> used := union !used (statement checking scope inner));
      pattern = (fun inner -> used := union !used (inside checking scope (`Pattern inner)));
      callee = (fun called -> used := union !used (callee_needs checking scope node called));
    }
  in
  (match node with
  | `Expression inner -> Core_walk.expression_parts visit inner
  | `Statement inner -> Core_walk.statement_parts visit inner
  | `Pattern inner -> Core_walk.pattern_parts visit inner);
  !used

and block checking scope (body : Core.block) : T.capability list =
  let used =
    List.fold_left
      (fun used written -> union used (statement checking scope written))
      [] body.statements
  in
  match body.value with Some value -> union used (expression checking scope value) | None -> used

and statement checking scope (written : Core.statement) : T.capability list =
  match written.kind with
  | Parallel branches ->
      (* Branches have only [Panic], so their results do not depend on the
         order they run in. *)
      List.iter
        (fun branch -> ignore (statement checking (only_panic scope "a `parallel` branch") branch))
        branches;
      []
  | For { parallel; pattern; drive; clauses; body } ->
      let used =
        match drive with
        | Count { start; stop; _ } ->
            union (expression checking scope start) (expression checking scope stop)
        | Each each -> expression checking scope each
        | Pull { cursor; next } ->
            union
              (expression checking scope cursor)
              (match next with
              | Some next -> callee_needs checking scope (`Statement written) next
              | None -> [])
      in
      let used = union used (inside checking scope (`Pattern pattern)) in
      specifications checking scope clauses;
      if parallel then begin
        ignore (block checking (only_panic scope "a `parallel for`") body);
        used
      end
      else union used (block checking scope body)
  | While { condition; clauses; body } ->
      let used = expression checking scope condition in
      specifications checking scope clauses;
      union used (block checking scope body)
  | Proof body ->
      ignore (block checking (pure_only scope "a proof") body);
      []
  | _ -> inside checking scope (`Statement written)

(* A loop's clauses are specifications, which may use nothing, whatever
   the function around them declares. *)
and specifications checking scope (clauses : Core.loop_clause list) =
  List.iter
    (Core_walk.loop_clause
       {
         Core_walk.nothing with
         expression =
           (fun value -> ignore (expression checking (pure_only scope "a specification") value));
       })
    clauses

(* What is called without being a call of its own: what a piece is
   displayed by, the method that gives a view, what builds a collection.
   It needs what its signature says it uses. *)
and callee_needs checking scope node (callee : Core.callee) : T.capability list =
  let state = checking.state in
  let origin =
    match node with
    | `Expression (inner : Core.expression) -> inner.origin
    | `Statement (inner : Core.statement) -> inner.origin
    | `Pattern (inner : Core.pattern) -> inner.origin
  in
  let needed =
    match callee with
    | Function { path; _ } -> (
        match Interface.Impls.signature state.database path with
        | Some signature -> signature.uses
        | None -> [])
    | Trait_method { trait; name; receiver; _ } -> (
        match Members.trait_method state.database trait.trait name receiver with
        | Some method_ -> method_.method_signature.uses
        | None -> [])
    | Capability_method { capability; _ } -> [ T.Capability capability ]
    | Intrinsic _ | Value _ -> []
  in
  check_grants checking origin callee;
  check_available checking scope origin ~through_value:false needed;
  needed

(* What a call needs, with each capability parameter of what it calls
   solved as what was passed for it. *)
and call_needs checking scope (node : Core.expression) (call : Core.call) passed : T.capability list
    =
  let solved = List.map (fun (parameter, passed) -> (parameter, !passed)) passed in
  let needed =
    List.sort_uniq compare
      (List.concat_map
         (function
           | T.Capability_parameter parameter as capability -> (
               match List.assoc_opt parameter solved with Some set -> set | None -> [ capability ])
           | capability -> [ capability ])
         call.uses)
  in
  call.capability_arguments <- solved;
  call.uses <- needed;
  record_in_tables checking.state node.origin call;
  (* A dependency may use only what its manifest grants, except what reaches
     it through a capability parameter, which is the caller's own. *)
  check_grants checking node.origin call.callee;
  check_available checking scope node.origin
    ~through_value:(match call.callee with Value _ -> true | _ -> false)
    needed;
  needed

(* A lambda's [uses] are inferred from its body, and must be within the
   [uses] of the function type it is checked against, but for what a call
   around it solves a capability parameter of that type as. *)
and lambda checking scope (node : Core.expression) body =
  let used = block checking { scope with available = []; collecting = true } body in
  (match node.type_ with
  | T.Function { uses; _ } ->
      pass checking scope node.origin ~what:"This lambda" ~uses ~unlisted:(minus used uses)
  | _ -> ());
  []

(* [provide]: each implementation's type provides every capability it
   implements, each of whose [impl]s needs its own [uses] here. A place is
   marked [mut] exactly when one of those [impl]s changes it. *)
and provide checking scope (node : Core.expression) implementations body =
  let state = checking.state in
  let used = ref [] in
  let provided = ref [] in
  List.iter
    (fun (implementation : Core.implementation) ->
      let visit : Core_walk.visit =
        {
          Core_walk.nothing with
          expression = (fun inner -> used := union !used (expression checking scope inner));
        }
      in
      Core_walk.operand visit implementation.value;
      let type_ = implementation.type_ in
      let impls = capability_impls state type_ in
      if impls = [] then
        report checking Not_an_implementation implementation.origin
          (Printf.sprintf "`%s` implements no capability, so it provides nothing." (T.show type_));
      let changes =
        List.exists
          (fun (_, (interface : T.impl_interface)) ->
            List.exists (fun (_, receiver, _) -> receiver = Path.Mut) interface.impl_methods)
          impls
      in
      let marked = implementation.mode = Mut in
      let is_place = match implementation.value with Place _ -> true | Value _ -> false in
      let start = checking.spans.(implementation.origin).start in
      if is_place && changes && not marked then
        report checking Provide_mark implementation.origin
          ~fixes:[ Diagnostic.fix "Mark it `mut`." [ Diagnostic.insert start "mut " ] ]
          "This implementation changes its own state, so the place is provided `mut`."
      else if marked && not changes then
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
          used := union !used interface.impl_uses;
          if not scope.collecting then
            List.iter
              (fun capability ->
                if not (List.mem capability scope.available) then
                  report checking Not_available implementation.origin
                    (Printf.sprintf "This implementation uses `%s`, which is not available here."
                       (show_capability capability)))
              interface.impl_uses)
        impls;
      provided :=
        union !provided
          (List.map (fun ((found : Core.provided), _) -> T.Capability found.capability) impls);
      implementation.provides <- List.map fst impls)
    implementations;
  state.tables.provides.(node.origin) <-
    Some
      {
        implementations =
          List.map
            (fun (implementation : Core.implementation) ->
              ( implementation.origin,
                List.map
                  (fun ({ capability; impl; arguments } : Core.provided) : C.provided ->
                    { capability; impl; arguments })
                  implementation.provides ))
            implementations;
      };
  let body_used = block checking { scope with available = union scope.available !provided } body in
  union !used (minus body_used !provided)

let check (state : state) (lowered : Environment.lowered) (form : Core.t) =
  let checking = { state; spans = Syntax_walk.spans state.definition } in
  let scope ?(own = []) available =
    { available; collecting = false; restricted = None; handed_on = None; own; passed = [] }
  in
  (* What states and does not run may use nothing: a contract, what a
     function-typed parameter requires, an invariant, a potential, and a
     law. *)
  let specification value =
    ignore (expression checking (pure_only (scope []) "a specification") value)
  in
  (match form.parts with
  | Function { parameters; contract; _ } ->
      List.iter
        (fun (parameter : Core.parameter) ->
          Option.iter
            (fun (accepted : Core.accepts) -> List.iter specification accepted.requires)
            parameter.accepts)
        parameters;
      List.iter (fun (clause : Core.clause) -> specification clause.value) contract.requires;
      List.iter specification contract.ensures;
      List.iter specification contract.decreases;
      List.iter
        (fun (cost : Core.cost) ->
          match cost.bound with
          | Finite -> ()
          | Order_of value | At_most value | Exactly value -> specification value)
        contract.costs
  | Type { invariants; potential; _ } ->
      List.iter specification invariants;
      Option.iter specification potential
  | Trait laws ->
      List.iter
        (fun (law : Core.law) ->
          List.iter specification law.requires;
          ignore (block checking (pure_only (scope []) "a law") law.body))
        laws
  | Constant _ | Test _ | Law_proof _ | Nothing -> ());
  match (form.parts, state.definition.kind, lowered.interface) with
  | Function { body; _ }, (Function _ | Method_declaration _), Function_interface signature ->
      (* Inside an implementation of a capability, a function value it
         calls may use the capability, which there means this
         implementation, as [write_with] hands [FileWrite] to its
         callback. A direct call of the capability would call the
         implementation itself, so it still needs [uses]. *)
      let handed_on =
        Option.bind (Query.demand state.database Names.container state.key) (fun container ->
            match Query.demand state.database Environment.lowered container with
            | Some { interface = Impl_interface impl; _ }
              when Interface.Summary.kind_of state.database impl.implements.trait = Some Capability
              ->
                Some (T.Capability impl.implements.trait)
            | _ -> None)
      in
      Option.iter
        (fun body ->
          ignore
            (block checking
               {
                 (scope ~own:(T.capability_parameters signature.generics) signature.uses) with
                 handed_on;
               }
               body))
        body
  | Test body, _, Test_interface uses -> ignore (block checking (scope (union uses [ panic ])) body)
  | Function { body = Some body; _ }, Theorem _, _ | Law_proof body, _, _ ->
      ignore (block checking (pure_only (scope []) "a proof") body)
  | _ -> ()
