(* What code may call: capabilities at each point, what lambdas use,
   capability parameters, [provide], and what a dependency is granted. See
   TYPECHECKER.md, "Capabilities".

   This runs once a definition's bodies are checked, over the checked form,
   and records in it what each capability parameter stands for at each call
   and what each [provide] builds. Each walk returns the capabilities its
   code uses, which is what a lambda's [uses] are inferred from and what a
   capability parameter is solved as. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
open Expressions

let panic : T.capability =
  Capability
    (Top { module_ = { package = "standard"; modules = [ "capabilities" ] }; name = "Panic" })

let report state ?(fixes = []) code (span : span) message =
  state.diagnostics <-
    Diagnostic.make ~fixes ~code:(Capabilities code) (Source.span span.start span.stop) message
    :: state.diagnostics

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
   proof, which may use nothing. [lambdas] holds, for the whole definition,
   what each lambda checked so far uses, by its id. *)
type scope = {
  available : T.capability list;
  collecting : bool;
  restricted : string option;
  lambdas : (id, T.capability list) Hashtbl.t;
  handed_on : T.capability option;
      (** In an implementation of a capability, that capability, which only calls through function
          values may use. *)
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
        (fun ((trait, head), _) ->
          if
            Path.equal head path && Interface.Summary.kind_of state.database trait = Some Capability
          then
            match implements state type_ (trait_reference trait) with
            | Some (Interface.Impls.From_impl { impl; substitution }) ->
                Option.map
                  (fun interface ->
                    ({ C.capability = trait; impl; arguments = substitution }, interface))
                  (Interface.Impls.impl_interface state.database impl)
            | _ -> None
          else None)
        (List.concat_map
           (fun package -> Query.demand state.database Interface.Impls.index package)
           (List.sort_uniq compare [ Path.package path; state.package; "standard" ]))
  | _ -> []

let dependency_grant (state : state) package =
  match Workspace.package state.database state.package with
  | Some manifest ->
      Option.map
        (fun (dependency : Workspace.dependency) -> dependency.capabilities)
        (List.find_opt
           (fun (dependency : Workspace.dependency) -> dependency.package = package)
           manifest.dependencies)
  | None -> None

(* A dependency may use only what its manifest entry grants: [what] of the
   [package] uses [uses], except what reaches it through a capability
   parameter, which is the caller's own. *)
let check_grant (state : state) (span : span) ~what package (uses : T.capability list) =
  if package <> state.package && package <> "standard" then
    match dependency_grant state package with
    | Some granted ->
        List.iter
          (function
            | T.Capability capability_path ->
                let name = show_capability (T.Capability capability_path) in
                if not (List.mem name granted) then
                  report state Not_granted span
                    (Printf.sprintf
                       "%s uses `%s`, which the manifest does not grant `%s`. Grant it in the \
                        manifest's entry for `%s`."
                       what name package package)
            | T.Capability_parameter _ -> ())
          uses
    | None -> ()

let rec expression state scope (value : expression) : T.capability list =
  let children () =
    let used = ref [] in
    let rec visit_statement (written : statement) =
      used := union !used (statement state scope written)
    and visit_expression (inner : expression) =
      used := union !used (expression state scope inner)
    in
    Syntax_walk.expression_parts ~expression:visit_expression ~statement:visit_statement value;
    !used
  in
  match value.kind with
  | Lambda { body; _ } -> lambda state scope value body
  | Provide { implementations; body } -> provide state scope value implementations body
  | Quantified _ -> quantifier state scope value
  | _ -> (
      let inner = children () in
      match state.tables.calls.(value.id) with
      | Some call -> union inner (call_needs state scope value call)
      | None -> inner)

and statement state scope (written : statement) : T.capability list =
  match written.kind with
  | Parallel body ->
      (* Branches have only [Panic], so their results do not depend on the
         order they run in. *)
      List.iter
        (fun (branch : statement) ->
          ignore (statement state (only_panic scope "a `parallel` branch") branch))
        body.statements;
      []
  | For { parallel = true; iterable; body; _ } ->
      let used = expression state scope iterable in
      List.iter
        (fun branch -> ignore (statement state (only_panic scope "a `parallel for`") branch))
        body.statements;
      used
  | Proof body ->
      List.iter
        (fun branch -> ignore (statement state (pure_only scope "a proof") branch))
        body.statements;
      []
  | _ ->
      let used = ref [] in
      let rec visit_statement (inner : statement) =
        used := union !used (statement state scope inner)
      and visit_expression (inner : expression) =
        used := union !used (expression state scope inner)
      in
      Syntax_walk.statement_parts ~expression:visit_expression ~statement:visit_statement written;
      !used

(* A quantifier's body may use no capability, in code as in a
   specification, since what it means must be a value the prover can read. *)
and quantifier state scope (value : expression) =
  let scope = pure_only scope "a quantifier's body" in
  let rec visit_statement written = ignore (statement state scope written)
  and visit_expression inner = ignore (expression state scope inner) in
  Syntax_walk.expression_parts ~expression:visit_expression ~statement:visit_statement value;
  []

(* What a call needs, with each of the callee's capability parameters
   solved as what the lambdas and function values passed for it use. *)
and call_needs state scope (value : expression) (call : C.call) : T.capability list =
  let callee_parameters, path =
    match call.callee with
    | Function { path; _ } -> (
        match Query.demand state.database Environment.signature path with
        | Some signature ->
            ( List.filter_map
                (fun (generic : T.generic) ->
                  match generic.kind with Capability_generic -> Some generic.generic | _ -> None)
                signature.generics,
              Some (path, signature) )
        | None -> ([], None))
    | _ -> ([], None)
  in
  let solved =
    List.map
      (fun parameter ->
        let from_arguments =
          match path with
          | Some (_, signature) ->
              List.concat_map
                (fun (argument : C.argument) ->
                  let parameter_type =
                    if argument.parameter = 0 && signature.receiver <> None then None
                    else
                      let index =
                        if signature.receiver <> None then argument.parameter - 1
                        else argument.parameter
                      in
                      Option.map
                        (fun (info : T.parameter_info) -> info.type_)
                        (List.nth_opt signature.parameters index)
                  in
                  match parameter_type with
                  | Some (T.Function { uses; _ })
                    when List.mem (T.Capability_parameter parameter) uses -> (
                      match state.tables.types.(argument.expression) with
                      | Some (T.Function given) -> given.uses
                      | _ -> [])
                  | _ -> [])
                call.arguments
          | None -> []
        in
        (parameter, List.sort_uniq compare from_arguments))
      callee_parameters
  in
  let lambda_uses =
    List.concat_map
      (fun (argument : C.argument) ->
        match Hashtbl.find_opt scope.lambdas argument.expression with
        | Some used -> [ (argument, used) ]
        | None -> [])
      call.arguments
  in
  let solved =
    List.map
      (fun (parameter, from_values) ->
        let from_lambdas =
          match path with
          | Some (_, signature) ->
              List.concat_map
                (fun ((argument : C.argument), used) ->
                  let index =
                    if signature.receiver <> None then argument.parameter - 1
                    else argument.parameter
                  in
                  match List.nth_opt signature.parameters index with
                  | Some { type_ = T.Function { uses; _ }; _ }
                    when List.mem (T.Capability_parameter parameter) uses ->
                      used
                  | _ -> [])
                lambda_uses
          | None -> []
        in
        (parameter, minus (union from_values from_lambdas) [ T.Capability_parameter parameter ]))
      solved
  in
  let needed =
    List.sort_uniq compare
      (List.concat_map
         (function
           | T.Capability_parameter parameter as capability -> (
               match List.assoc_opt parameter solved with Some set -> set | None -> [ capability ])
           | capability -> [ capability ])
         call.uses)
  in
  state.tables.calls.(value.id) <- Some { call with capability_arguments = solved; uses = needed };
  (* A dependency may use only what its manifest grants, except what reaches
     it through a capability parameter, which is the caller's own. *)
  (match (path, call.callee) with
  | Some (callee, signature), _ ->
      check_grant state value.span
        ~what:(Printf.sprintf "`%s`" (Path.show callee))
        (Path.package callee) signature.uses
  | None, Trait_method { trait; name; receiver; evidence; _ } -> (
      (* The trait's method as declared, and the [impl]'s that runs. *)
      (match Members.trait_methods state.database trait.trait name with
      | method_ :: _ ->
          check_grant state value.span
            ~what:(Printf.sprintf "`%s.%s`" (Path.show trait.trait) name)
            (Path.package trait.trait) method_.method_signature.uses
      | [] -> ());
      match evidence with
      | Impl { impl; _ } -> (
          match Interface.Impls.impl_interface state.database impl with
          | Some interface ->
              List.iter
                (fun (method_name, method_receiver, (method_signature : T.signature)) ->
                  if method_name = name && method_receiver = receiver then
                    check_grant state value.span
                      ~what:
                        (Printf.sprintf "The `impl` of `%s` for `%s`"
                           (T.show_trait interface.implements)
                           (T.show interface.for_type))
                      (Path.package impl) method_signature.uses)
                interface.impl_methods
          | None -> ())
      | _ -> ())
  | None, _ -> ());
  if not scope.collecting then
    List.iter
      (fun capability ->
        if
          not
            (List.mem capability scope.available
            || (call.callee = Function_value && scope.handed_on = Some capability))
        then
          report state Not_available value.span
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
      needed;
  needed

(* A lambda's [uses] are inferred from its body, and must be within the
   [uses] of the function type it is checked against, unless that is a
   capability parameter, which the call solves from them. *)
and lambda state scope (value : expression) body =
  let inner = { scope with available = []; collecting = true } in
  let used =
    List.fold_left
      (fun used written -> union used (statement state inner written))
      [] body.statements
  in
  Hashtbl.replace scope.lambdas value.id used;
  (match state.tables.types.(value.id) with
  | Some (T.Function { uses; _ }) ->
      let open_parameter =
        List.exists (function T.Capability_parameter _ -> true | _ -> false) uses
      in
      if not open_parameter then
        List.iter
          (fun capability ->
            if not (List.mem capability uses) then
              report state Lambda_uses value.span
                (Printf.sprintf
                   "This lambda uses `%s`, which the function type it is passed as does not allow."
                   (show_capability capability)))
          used
  | _ -> ());
  []

(* [provide]: each implementation's type provides every capability it
   implements, each of whose [impl]s needs its own [uses] here. A place is
   marked [mut] exactly when one of those [impl]s changes it. *)
and provide state scope (value : expression) implementations body =
  let used = ref [] in
  let provided = ref [] in
  let evidence =
    List.map
      (fun (implementation : expression) ->
        used := union !used (expression state scope implementation);
        let type_ = Option.value ~default:T.Error state.tables.types.(implementation.id) in
        let impls = capability_impls state type_ in
        if impls = [] && type_ <> T.Error then
          report state Not_an_implementation implementation.span
            (Printf.sprintf "`%s` implements no capability, so it provides nothing." (T.show type_));
        let changes =
          List.exists
            (fun (_, (interface : T.impl_interface)) ->
              List.exists (fun (_, receiver, _) -> receiver = Path.Mut) interface.impl_methods)
            impls
        in
        let marked = match implementation.kind with Mode (Mut, _) -> true | _ -> false in
        let is_place =
          match implementation.kind with Name _ | Member _ | Mode _ -> true | _ -> false
        in
        if is_place && changes && not marked then
          report state Provide_mark implementation.span
            ~fixes:
              [
                Diagnostic.fix "Mark it `mut`."
                  [ Diagnostic.insert implementation.span.start "mut " ];
              ]
            "This implementation changes its own state, so the place is provided `mut`."
        else if marked && not changes then
          report state Provide_mark implementation.span
            ~fixes:
              [
                Diagnostic.fix "Remove the mark."
                  [
                    Diagnostic.delete
                      (Source.span implementation.span.start (implementation.span.start + 4));
                  ];
              ]
            "This implementation never changes its own state, so the place is provided without \
             `mut`.";
        List.iter
          (fun ((provided : C.provided), (interface : T.impl_interface)) ->
            check_grant state implementation.span
              ~what:
                (Printf.sprintf "The `impl` of `%s` for `%s`" (Path.show provided.capability)
                   (T.show interface.for_type))
              (Path.package provided.impl) interface.impl_uses;
            used := union !used interface.impl_uses;
            if not scope.collecting then
              List.iter
                (fun capability ->
                  if not (List.mem capability scope.available) then
                    report state Not_available implementation.span
                      (Printf.sprintf "This implementation uses `%s`, which is not available here."
                         (show_capability capability)))
                interface.impl_uses)
          impls;
        provided :=
          union !provided
            (List.map (fun ((provided : C.provided), _) -> T.Capability provided.capability) impls);
        (implementation.id, List.map fst impls))
      implementations
  in
  state.tables.provides.(value.id) <- Some { implementations = evidence };
  let inner = { scope with available = union scope.available !provided } in
  let body_used =
    List.fold_left
      (fun used written -> union used (statement state inner written))
      [] body.statements
  in
  union !used (minus body_used !provided)

let check (state : state) (lowered : Environment.lowered) =
  let lambdas = Hashtbl.create 16 in
  let scope available =
    { available; collecting = false; restricted = None; lambdas; handed_on = None }
  in
  let definition = state.definition in
  let broken = Resolve.Parts.broken definition in
  let run_in scope (body : block) =
    List.iter (fun written -> ignore (statement state scope written)) body.statements
  in
  let run available body = run_in (scope available) body in
  if not (broken Header || broken Body) then
    match (definition.kind, lowered.interface) with
    | Function { body; signature = written }, Function_interface signature ->
        (* A function's clauses are specifications, with only [Panic]. *)
        List.iter
          (fun (clause : clause) ->
            let check value =
              ignore (expression state (pure_only (scope []) "a specification") value)
            in
            match clause.kind with
            | Requires value | Ensures value -> check value
            | Decreases measures -> List.iter check measures
            | Cost { bound = Big_o value | At_most value | Exactly value; _ } -> check value
            | Cost { bound = Finite; _ } | Uses _ | Clause_error -> ())
          written.clauses;
        run signature.uses body
    | Test { body; _ }, Test_interface uses -> run (union uses [ panic ]) body
    | Theorem { body; _ }, _ | Law_proof { body; _ }, _ ->
        run_in (pure_only (scope []) "a proof") body
    | Impl { members; _ }, Impl_interface impl ->
        let is_capability =
          Interface.Summary.kind_of state.database impl.implements.trait = Some Capability
        in
        List.iter
          (fun (line : impl_member line) ->
            match line.kind with
            | Impl_method { body; signature } ->
                let name =
                  match signature.name with Plain_name name | Member_name (_, name) -> name.text
                in
                let receiver = Names.receiver signature.parameters in
                let uses =
                  if is_capability then impl.impl_uses
                  else
                    match
                      List.find_opt
                        (fun (method_name, method_receiver, _) ->
                          method_name = name && method_receiver = receiver)
                        impl.impl_methods
                    with
                    | Some (_, _, method_signature) -> method_signature.uses
                    | None -> []
                in
                (* Inside an implementation of a capability, a function
                   value it calls may use the capability, which there means
                   this implementation, as [write_with] hands [FileWrite] to
                   its callback. A direct call of the capability would call
                   the implementation itself, so it still needs [uses]. *)
                let own =
                  if is_capability then Some (T.Capability impl.implements.trait) else None
                in
                run_in { (scope uses) with handed_on = own } body
            | _ -> ())
          members
    | Trait { members; _ }, Trait_interface trait ->
        List.iter
          (fun (line : trait_member line) ->
            match line.kind with
            | Trait_method { body = Some body; signature } -> (
                let name =
                  match signature.name with Plain_name name | Member_name (_, name) -> name.text
                in
                match
                  List.find_opt
                    (fun (method_ : T.trait_method) -> method_.method_name = name)
                    trait.methods
                with
                | Some method_ -> run method_.method_signature.uses body
                | None -> ())
            | _ -> ())
          members
    | _ -> ()
