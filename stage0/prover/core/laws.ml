(* The laws of a trait as facts, and a named function passed for a
   function-typed parameter. *)

open Core
open State
open Facts
open Contracts
open Validity
open Operations

(* A call through a function-typed parameter whose type has a [requires]
   must meet it. *)
let check_callback_requires context frame (site : Invocation.site) through (values : passed list) =
  match through with
  | Some (_, _, Invocation.Forwarded local) -> (
      match own_callback context local with
      | Some (name, { inputs; requires }) when List.length inputs = List.length values ->
          (* The [requires] is read with the callback's parameters bound to
             this call's arguments. *)
          let inside =
            callback_contract_frame frame inputs
              (List.map (fun (passed : passed) -> passed.term) values)
          in
          List.iter
            (fun (clause : Mir.formula) ->
              oblige context frame Requires
                (span_of frame.source site.origin)
                (Printf.sprintf "`%s` may not hold for this call through `%s`."
                   (quote frame.source clause.origin)
                   name)
                (snd (specification_value context inside clause)))
            requires
      | _ -> ())
  | _ -> ()

(* Whether a call is to a private method that takes [mut self], which is a
   step of an update: its receiver's invariant is neither shown at the call
   nor assumed after. *)
let updating_helper context (invocation : Invocation.t) =
  match invocation.callee with
  | Function { path; _ } -> is_updating_helper context.database path
  | _ -> false

let laws_key (trait : Types.trait_reference) ty = Types.show_trait trait ^ " for " ^ type_key ty

let laws_of context trait =
  match Query.demand context.database Interface.Summary.key trait with
  | Some key -> (
      match source_at_key context.database key with
      | Some source ->
          List.map
            (fun (law : Mir.law) -> (source, law))
            (Query.demand context.database Mir.laws key)
      | None -> [])
  | None -> []

let law_parameter_types ~substitution (law : Mir.law) =
  List.map (fun (_, type_) -> Types.substitute substitution type_) law.parameters

(* A law's frame: its parameters as the given terms, with [Self] and the
   trait's parameters as the substitution says. *)
let law_frame frame source ~substitution (law : Mir.law) terms =
  let types = law_parameter_types ~substitution law in
  let locals, types =
    List.fold_left2
      (fun (locals, types_) ((local, _), ty) term ->
        (Locals.add local term locals, Locals.add local ty types_))
      (Locals.empty, Locals.empty)
      (List.combine law.parameters types)
      terms
  in
  {
    frame with
    source;
    locals;
    types;
    old_locals = locals;
    self = None;
    old_self = None;
    result = None;
    checking = false;
    substitution;
    self_type = None;
  }

let law_fact context frame source ~substitution (law : Mir.law) =
  let types = law_parameter_types ~substitution law in
  if List.exists (fun ty -> Types.is_error ty) types then None
  else begin
    context.fresh <- context.fresh + 1;
    let symbols =
      List.mapi
        (fun index _ -> Symbol.Variable { label = "law"; numbers = [ context.fresh; index ] })
        types
    in
    (* A law is stated for every value, so its premise and its body are
       read on no path: a conditional in one would otherwise hold the
       condition of the code that first uses the law, and the law would be
       false where that condition fails. *)
    let inside =
      law_frame
        { frame with bound = symbols @ frame.bound; condition = Logic.Boolean true }
        source ~substitution law
        (List.map (fun symbol -> Logic.Symbol symbol) symbols)
    in
    try
      let premise =
        Logic.conjunction
          (List.map (fun clause -> snd (specification_value context inside clause)) law.requires)
      in
      let range =
        Logic.conjunction
          (List.map2 (fun symbol ty -> in_range ty (Logic.Symbol symbol)) symbols types)
      in
      let _, holds = specification_value context inside law.states in
      Some
        (Logic.forall
           ( List.map2 (fun symbol ty -> (symbol, sort_of context ty)) symbols types,
             Logic.( ==> ) (Logic.( &&& ) range premise) holds ))
    with Unsupported _ | Foreign_unsupported _ -> None
  end

(* A trait's laws, and those of the traits it requires, as facts about a
   type, each quantified over its parameters. A law is shown for each
   [impl] written by hand, by the [impl], so it is a fact wherever the
   trait's methods are used. *)
let assume_laws context frame ~at (trait : Types.trait_reference) (ty : Types.ty) =
  let key = laws_key trait ty in
  if not (List.mem key context.laws_assumed) then begin
    context.laws_assumed <- key :: context.laws_assumed;
    List.iter
      (fun path ->
        let required =
          if Path.equal path trait.trait then trait
          else { Types.trait = path; trait_arguments = []; associated = [] }
        in
        let substitution = trait_substitution context.database required ty in
        let impl = Option.map fst (concrete_impl context required ty) in
        List.iter
          (fun (source, (law : Mir.law)) ->
            match law_fact context frame source ~substitution law with
            | Some fact_ ->
                (match impl with
                | Some impl when law_unshown context.database impl required ty law.name ->
                    context.holes <- (context.home, at) :: context.holes
                | _ -> ());
                fact context frame fact_
            | None -> ())
          (laws_of context path))
      (Call_graph.traits_with_required context.database trait.trait)
  end

let template_trait : Path.t = Well_known.path From_template

let signature_terminates context path =
  match Interface.Impls.signature context.database path with
  | Some (signature : Types.signature) -> signature.terminates
  | None -> true

(* Whether a named function's cost clauses imply one a function type asks
   for, which can only be a constant: a constant [O(...)], or a number of
   at most, or exactly, the asked bound. *)
let keeps_cost context path (contract : contract) (asked : Types.cost) =
  let constant = literal in
  let same (cost : Mir.cost) =
    match (asked.resource, cost.resource) with
    | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
    | _ -> false
  in
  match asked with
  | { resource = Time; bound = Finite_cost; _ } -> signature_terminates context path
  | { resource = Calls _; _ } -> false
  | _ -> (
      match
        List.find_map
          (fun (part : part) ->
            List.find_map (fun cost -> if same cost then Some cost else None) part.costs)
          contract.parts
      with
      | Some cost -> (
          match (asked.bound, cost.bound) with
          | Order_of, (Order_of value | At_most value | Exactly value) -> constant value <> None
          | No_more_than (Some most), (At_most value | Exactly value) -> (
              match constant value with Some limit -> Z.leq limit most | None -> false)
          | Exactly_cost (Some exact), Exactly value -> constant value = Some exact
          | _ -> false)
      | None -> false)

(* A function named as a value and passed for a function-typed parameter
   must accept every argument the parameter's type promises it, and keep
   the cost clauses the type asks of the passed function. *)
let check_named_callback context frame (invocation : Invocation.t) (passed : passed) ~origin path
    (contract : contract) (values : passed list) =
  let span = span_of frame.source origin in
  let own = List.hd contract.parts in
  match parameter_type context frame invocation passed.position with
  | Some (Types.Function expected) ->
      let inputs = callback_arguments context frame expected.inputs in
      let known = List.map (fun (passed : passed) -> (passed.position, passed.term)) values in
      let promised =
        Logic.conjunction (callback_facts context frame invocation passed.position known inputs)
      in
      let at_call = restrict frame promised in
      (if List.length own.parameters = List.length inputs then
         let inside =
           part_frame frame own
             ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
             ~substitution:[]
         in
         List.iter
           (fun (requirement : Mir.formula) ->
             oblige context at_call Requires span
               (Printf.sprintf
                  "`%s` may not accept every argument this parameter's type promises it: its `%s` \
                   may not hold."
                  (Path.show path)
                  (quote own.callee requirement.origin))
               (snd (specification_value context inside requirement)))
           (clauses own.requires));
      List.iter
        (fun (cost : Types.cost) ->
          if not (keeps_cost context path contract cost) then
            oblige context frame Cost span
              (Printf.sprintf
                 "`%s` does not promise the contract this parameter's type, `%s`, asks of a \
                  function passed for it."
                 (Path.show path)
                 (Types.show (Types.Function expected)))
              (Logic.Boolean false))
        expected.costs
  | _ ->
      if own.requires <> [] || own.costs <> [] then
        unsupported span "a function passed for a parameter whose type the prover cannot read"
