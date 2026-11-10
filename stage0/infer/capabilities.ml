(* What code may call: capabilities at each point, what lambdas use,
   capability parameters, [provide], and what a dependency is granted.

   This runs on a definition's core form, where every call the code makes is
   a node, whether it was written as a call or as a loop, an operator, or an
   interpolation. What each call needs must be within what is available
   where it is: the function's [uses] and what an enclosing [provide]
   provides, or inside a lambda the [uses] of the lambda's type.

   A capability parameter of what a call calls stands there for an unknown
   set, which is in the type of everything that got it from the call. What
   a call needs and what a lambda's type lists may hold such unknowns, so
   nothing is decided as the form is walked: each need is noted, with those
   that checking the bodies noted where a function value met a function
   type, and then every unknown is solved as the least set that holds what
   must be within it. *)

open Syntax
module T = Types
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
  | T.Capability_variable _ -> "_"

let union left right = List.sort_uniq compare (left @ right)

(* Where code is, by what it may use. *)
type place =
  | Body  (** A function's or a test's own code. *)
  | Lambda of Core.origin
      (** A lambda's body, which may use what the lambda's type lists: where that holds an unknown,
          the unknown comes to hold what the body needs. *)
  | Restricted of string
      (** Code that may use less than the function declares: a [parallel] branch, which may use only
          [Panic], or a specification or a proof, which may use nothing. *)

type scope = {
  available : T.capability list;
  place : place;
  handed_on : T.capability option;
      (** In an implementation of a capability, that capability, which only calls through function
          values may use. *)
}

(* Code that may use only [Panic], whatever the function declares. *)
let only_panic reason = { available = [ panic ]; place = Restricted reason; handed_on = None }

(* Code that may use no capability at all, not even [Panic]: a
   specification or a proof, whose meaning must be a value. *)
let pure_only reason = { available = []; place = Restricted reason; handed_on = None }

(* A dependency may use only what its manifest entry grants: [what] of the
   [package] uses [uses], except what reaches it through a capability
   parameter, which is the caller's own. *)
let check_grant checking (origin : Core.origin) ~what package (uses : T.capability list) =
  List.iter
    (fun capability ->
      report checking Not_granted origin (Interface.Grants.message ~what ~of_:package capability))
    (Interface.Grants.missing checking.state.database ~package:checking.state.package ~of_:package
       uses)

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
  | Capability_method _ | Intrinsic _ | Through _ -> ()

(* What code needs must be within what is available where it is. *)
let need checking scope (origin : Core.origin) ?(implementation = false) ?(through_value = false)
    (needed : T.capability list) =
  let state = checking.state in
  let wanted =
    if through_value then union scope.available (Option.to_list scope.handed_on)
    else scope.available
  in
  let lacking =
    List.iter (fun capability ->
        let shown = show_capability capability in
        match scope.place with
        | Lambda lambda ->
            report checking Lambda_uses lambda
              (Printf.sprintf
                 "This lambda uses `%s`, which the function type it is passed as does not allow."
                 shown)
        | Restricted reason when scope.available = [] ->
            report checking Not_available origin
              (Printf.sprintf
                 "This call uses `%s`, but %s may use no capabilities, not even `Panic`: what it \
                  means must be a value. A function that fails on some inputs says so with \
                  `requires` instead."
                 shown reason)
        | Restricted reason ->
            report checking Not_available origin
              (Printf.sprintf
                 "This call uses `%s`, but %s may use only `Panic`, whatever the function declares."
                 shown reason)
        | Body when implementation ->
            report checking Not_available origin
              (Printf.sprintf "This implementation uses `%s`, which is not available here." shown)
        | Body ->
            report checking Not_available origin
              (Printf.sprintf
                 "This call uses `%s`, which is not available here. Declare it with `uses %s`, or \
                  `provide` an implementation."
                 shown shown))
  in
  if needed <> [] then state.within <- { given = needed; wanted; lacking } :: state.within

(* What is called without being a call of its own: what a piece is
   displayed by, the method that gives a view, what builds a collection.
   It needs what its signature says it uses. *)
let callee_needs checking scope (origin : Core.origin) (callee : Core.callee) =
  let state = checking.state in
  check_grants checking origin callee;
  need checking scope origin
    (match callee with
    | Function { path; _ } -> (
        match Interface.Impls.signature state.database path with
        | Some signature -> signature.uses
        | None -> [])
    | Trait_method { trait; name; receiver; _ } -> (
        match Members.trait_method state.database trait.trait name receiver with
        | Some method_ -> method_.method_signature.uses
        | None -> [])
    | Capability_method { capability; _ } -> [ T.Capability capability ]
    | Intrinsic _ | Through _ -> [])

let rec expression checking scope (node : Core.expression) =
  match node.kind with
  | Lambda { body; _ } ->
      (* A lambda's body may use what the lambda's type lists, which is the
         function type it was checked against. *)
      let uses = match node.type_ with T.Function { uses; _ } -> uses | _ -> [] in
      block checking { available = uses; place = Lambda node.origin; handed_on = None } body
  | Provide { implementations; body } -> provide checking scope implementations body
  | Quantified _ ->
      (* A quantifier's body may use no capability, in code as in a
         specification, since what it means must be a value the prover can
         read. *)
      inside checking (pure_only "a quantifier's body") (`Expression node)
  | Function_value { path; _ } ->
      (* A function taken as a value is named as surely as one that is
         called, and whoever is handed the value may call it. *)
      check_grants checking node.origin (Function { path; type_arguments = [] })
  | Call call ->
      inside checking scope (`Expression node);
      (* A dependency may use only what its manifest grants, except what
         reaches it through a capability parameter, which is the caller's
         own. *)
      check_grants checking node.origin call.callee;
      need checking scope node.origin
        ~through_value:(match call.callee with Through _ -> true | _ -> false)
        call.uses
  | _ -> inside checking scope (`Expression node)

(* The nodes directly inside a node. *)
and inside checking scope node =
  let origin =
    match node with
    | `Expression (inner : Core.expression) -> inner.origin
    | `Statement (inner : Core.statement) -> inner.origin
    | `Pattern (inner : Core.pattern) -> inner.origin
  in
  let visit : Core_walk.visit =
    {
      expression = expression checking scope;
      statement = statement checking scope;
      pattern = (fun inner -> inside checking scope (`Pattern inner));
      callee = callee_needs checking scope origin;
    }
  in
  match node with
  | `Expression inner -> Core_walk.expression_parts visit inner
  | `Statement inner -> Core_walk.statement_parts visit inner
  | `Pattern inner -> Core_walk.pattern_parts visit inner

and block checking scope (body : Core.block) =
  List.iter (statement checking scope) body.statements;
  Option.iter (expression checking scope) body.value

and statement checking scope (written : Core.statement) =
  match written.kind with
  | Parallel branches ->
      (* Branches have only [Panic], so their results do not depend on the
         order they run in. *)
      List.iter (statement checking (only_panic "a `parallel` branch")) branches
  | For { parallel; pattern; drive; clauses; body } ->
      (match drive with
      | Count { start; stop; _ } ->
          expression checking scope start;
          expression checking scope stop
      | Each each -> expression checking scope each
      | Pull { cursor; next } ->
          Core_walk.place { Core_walk.nothing with expression = expression checking scope } cursor;
          Option.iter (callee_needs checking scope written.origin) next);
      inside checking scope (`Pattern pattern);
      specifications checking clauses;
      block checking (if parallel then only_panic "a `parallel for`" else scope) body
  | While { condition; clauses; body } ->
      expression checking scope condition;
      specifications checking clauses;
      block checking scope body
  | Proof body -> block checking (pure_only "a proof") body
  | _ -> inside checking scope (`Statement written)

(* A loop's clauses are specifications, which may use nothing, whatever
   the function around them declares. *)
and specifications checking (clauses : Core.loop_clause list) =
  List.iter
    (Core_walk.loop_clause
       { Core_walk.nothing with expression = expression checking (pure_only "a specification") })
    clauses

(* [provide]: each implementation's type provides every capability it
   implements, each of whose [impl]s needs its own [uses] here. A place is
   marked [mut] exactly when one of those [impl]s changes it. *)
and provide checking scope implementations body =
  let state = checking.state in
  let provided = ref [] in
  List.iter
    (fun (implementation : Core.implementation) ->
      Core_walk.operand
        { Core_walk.nothing with expression = expression checking scope }
        implementation.value;
      let impls = Form.capability_impls state implementation.type_ in
      if impls = [] then
        report checking Not_an_implementation implementation.origin
          (Printf.sprintf "`%s` implements no capability, so it provides nothing."
             (T.show implementation.type_));
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
          need checking scope implementation.origin ~implementation:true interface.impl_uses)
        impls;
      provided :=
        union !provided
          (List.map (fun ((found : Core.provided), _) -> T.Capability found.capability) impls))
    implementations;
  block checking { scope with available = union scope.available !provided } body

(* Solves every unknown set as the least that holds what must be within
   it, and then reports what is still not within what it must be. *)
let solve (state : state) =
  let solution = Hashtbl.create 8 in
  let known capabilities =
    List.concat_map
      (function
        | T.Capability_variable unknown ->
            Option.value ~default:[] (Hashtbl.find_opt solution unknown)
        | capability -> [ capability ])
      capabilities
  in
  let lacking (constraint_ : within) =
    let have = known constraint_.wanted in
    List.sort_uniq compare
      (List.filter (fun capability -> not (List.mem capability have)) (known constraint_.given))
  in
  let rec grow () =
    let grew =
      List.fold_left
        (fun grew (constraint_ : within) ->
          match
            ( List.filter_map
                (function T.Capability_variable unknown -> Some unknown | _ -> None)
                constraint_.wanted,
              lacking constraint_ )
          with
          | [], _ | _, [] -> grew
          | unknowns, lacking ->
              List.iter
                (fun unknown ->
                  Hashtbl.replace solution unknown
                    (union lacking (Option.value ~default:[] (Hashtbl.find_opt solution unknown))))
                unknowns;
              true)
        false state.within
    in
    if grew then grow ()
  in
  grow ();
  state.capabilities <- Some solution;
  List.iter
    (fun (constraint_ : within) ->
      match lacking constraint_ with [] -> () | lacking -> constraint_.lacking lacking)
    (List.rev state.within)

let check (state : state) (lowered : Environment.lowered) (form : Core.t) =
  let checking = { state; spans = Syntax_walk.spans state.definition } in
  let body ?handed_on available = { available; place = Body; handed_on } in
  (* What states and does not run may use nothing: a contract, what a
     function-typed parameter requires, an invariant, a potential, and a
     law. *)
  let specification = expression checking (pure_only "a specification") in
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
          block checking (pure_only "a law") law.body)
        laws
  | Constant _ | Test _ | Law_proof _ | Nothing -> ());
  (match (form.parts, state.definition.kind, lowered.interface) with
  | Function { body = code; _ }, (Function _ | Method_declaration _), Function_interface signature
    ->
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
      Option.iter (block checking (body ?handed_on signature.uses)) code
  | Test code, _, Test_interface uses -> block checking (body (union uses [ panic ])) code
  | Function { body = Some code; _ }, Theorem _, _ | Law_proof code, _, _ ->
      block checking (pure_only "a proof") code
  | _ -> ());
  solve state
