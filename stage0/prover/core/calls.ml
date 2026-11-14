(* A call: through the callee's contract, or for an intrinsic, its meaning. *)

open Core
open State
open Facts
open Contracts
open Validity
open Operations
open Models
open Lambdas
open Intrinsics
open Laws
open Amounts

(* A call to a function whose contract the prover reads: its [requires]
   must hold, its [ensures] holds after, and a recursive call decreases. *)
let contract_call context frame (site : Invocation.site) (invocation : Invocation.t) path contract
    (values : passed list) ~lent_final ~havoc_mut ~substitution_of ~instance =
  (* A pure call's result is the function applied to its arguments, so a
     nested call's argument holds every call inside it, which its clauses
     and its definition then repeat at each use. Each argument that holds
     another call is named once, by its term, and the name stands for it.
     The same term gets the same name, so the same call is the same term
     wherever it is made. *)
  let values =
    if contract.pure then
      List.map
        (fun (passed : passed) ->
          if passed.mode = Types.Mut || Logic.mentions frame.bound passed.term then passed
          else { passed with term = named_term context passed.type_ passed.term })
        values
    else values
  in
  let caller = frame.source in
  let span = span_of frame.source site.origin in
  let argument_at index =
    List.find_map
      (fun (passed : passed) -> if passed.position = index then Some passed.term else None)
      values
  in
  (* Each part binds its own parameters to the call's arguments, or to its
     defaults. *)
  let bindings (part : part) =
    List.mapi
      (fun index (parameter : Mir.parameter) ->
        let term =
          match argument_at index with
          | Some term -> Some term
          | None ->
              if parameter.has_default then
                let empty =
                  {
                    frame with
                    source = part.callee;
                    locals = Locals.empty;
                    types = Locals.empty;
                    checking = false;
                    substitution = substitution_of part;
                  }
                in
                Some (default_value context empty part index)
              else None
        in
        (parameter, term))
      part.parameters
  in
  let bind bindings =
    List.fold_left
      (fun (locals, types, self) ((parameter : Mir.parameter), term) ->
        match (parameter.local, term) with
        | Self, Some term -> (locals, types, Some (term, parameter.type_))
        | local, Some term ->
            (Locals.add local term locals, Locals.add local parameter.type_ types, self)
        | _, None -> (locals, types, self))
      (Locals.empty, Locals.empty, None)
      bindings
  in
  let self_of self = Option.map fst self
  and self_type_of part self =
    Option.map (fun (_, ty) -> Types.substitute (substitution_of part) ty) self
  in
  let entry_frame (part : part) =
    let locals, types, self = bind (bindings part) in
    {
      frame with
      source = part.callee;
      locals;
      types;
      old_locals = locals;
      self = self_of self;
      old_self = self_of self;
      self_type = self_type_of part self;
      result = None;
      checking = false;
      substitution = substitution_of part;
    }
  in
  let own = List.hd contract.parts in
  (* A call in a cycle of the call graph must decrease: the callee's
     measure, at the call's arguments, is below the caller's on entry. *)
  if
    context.terminates && frame.checking
    && (match invocation.callee with
      | Trait_method _ -> Call_graph.dispatched invocation.callee
      | _ -> true)
    && Call_graph.reaches context.database ~package:(Path.package context.current) ~from:path
         ~target:context.current
  then
    begin match (context.measures, own.decreases) with
    | [], [] when Path.equal path context.current && structural_parameters context frame own <> []
      ->
        (* With no [decreases], a call on parts of the parameters ends:
           their ranks decrease, compared in the parameters' order. *)
        let pairs = structural_parameters context frame own in
        let before = List.map (fun (ty, entry, _) -> rank context ty entry) pairs in
        let after =
          List.map (fun (ty, _, index) -> rank context ty (argument_at_index values index)) pairs
        in
        oblige context frame Termination span
          "This recursive call may not be on a part of its parameters: give the function a \
           `decreases` clause."
          Logic.(
            conjunction
              (List.map (fun right_term -> Operation ("<=", [ int 0; right_term ])) before)
            &&& lexicographically_less before after)
    | [], _ | _, [] ->
        oblige context frame Termination span
          (Printf.sprintf
             "This call to `%s` may not end: it calls back here, and both need a `decreases` \
              clause for the prover to show that the recursion ends."
             (Path.show path))
          (Logic.Boolean false)
    | measures, callee_measures ->
        let current_frame =
          { frame with checking = false; locals = frame.old_locals; self = frame.old_self }
        in
        let callee_entry = entry_frame own in
        let rec prefix before after =
          match (before, after) with
          | right_term :: before, left_term :: after ->
              let rest_before, rest_after = prefix before after in
              (right_term :: rest_before, left_term :: rest_after)
          | _ -> ([], [])
        in
        let before =
          List.map (fun measure -> snd (specification_value context current_frame measure)) measures
        in
        let after =
          List.map
            (fun measure -> snd (specification_value context callee_entry measure))
            callee_measures
        in
        let before, after = prefix before after in
        oblige context frame Termination span
          (Printf.sprintf "This call may not decrease `%s`."
             (String.concat ", "
                (List.map (fun (measure : Mir.formula) -> quote caller measure.origin) measures)))
          (lexicographically_less before after)
    end;
  (* The callee's [requires]: its own when it states any, and otherwise
     its trait's. *)
  let requiring =
    match contract.parts with
    | own :: others -> if own.requires <> [] || others = [] then [ own ] else others
    | [] -> []
  in
  let required =
    List.concat_map
      (fun (part : part) ->
        let entry = entry_frame part in
        List.map
          (fun (requirement : Mir.requirement) ->
            let clause = requirement.clause in
            let _, term = specification_value context entry clause in
            oblige context frame Requires span
              ?cited:
                (Option.map (fun key -> (key, span_of part.callee clause.origin)) part.callee.key)
              ~fixes:(requires_fix context frame part requirement term values)
              (Printf.sprintf "`%s` may not hold for this call to `%s`."
                 (quote part.callee clause.origin) (Path.show path))
              term;
            term)
          part.requires)
      requiring
  in
  let required = Logic.conjunction required in
  (* Each part's [ensures] holds where its [requires] does: a trait's, of
     an [impl]'s method whose own precondition is weaker, only where the
     trait's holds too. *)
  let required_by (part : part) =
    if List.memq part requiring then required
    else
      Logic.conjunction
        (List.map
           (fun requirement -> snd (specification_value context (entry_frame part) requirement))
           (clauses part.requires))
  in
  let after = havoc_mut frame in
  (* A pure call's [ensures], where its [requires] holds, and its
     definition are facts of mathematics, true whether or not the body of a
     quantifier around the call runs. *)
  let in_quantifier = contract.pure && frame.binders <> [] in
  let state term = if in_quantifier then fact context after term else assume context after term in
  (* Each [mut] argument's value after the call: its place's value, which
     [havoc_mut] made fresh. *)
  let changed =
    List.filter_map
      (fun (passed : passed) ->
        match (passed.mode, passed.passed_place) with
        | Types.Mut, Some place -> (
            try Some (passed.position, place.read after)
            with Unsupported _ | Foreign_unsupported _ ->
              Some (passed.position, arrive context after "changed" passed.type_))
        | _ -> None)
      values
  in
  let own_bound = bindings own in
  let own_arguments = List.filter_map snd own_bound in
  let is_on_bound_values = List.exists (Logic.mentions after.bound) own_arguments in
  let result_type = substituted context frame site.type_ in
  let applied_as = ref None in
  let is_limited_call = ref false in
  let result =
    if contract.pure && List.length own_arguments = List.length own_bound then begin
      let function_symbol = Symbol.Function { callee = path; instance } in
      let sorts =
        List.mapi
          (fun index ((parameter : Mir.parameter), _) ->
            match List.find_opt (fun (passed : passed) -> passed.position = index) values with
            | Some passed -> sort_of context passed.type_
            | None ->
                sort_of context
                  (Interface.Impls.normalize context.database
                     ~bounds:(fun _ -> [])
                     (Types.substitute (substitution_of own) parameter.type_)))
          own_bound
      in
      let result_sort = sort_of context result_type in
      declare context (Logic.Function (function_symbol, sorts, result_sort));
      (match (path, own_bound) with
      | Method { name = "model"; receiver = Read; _ }, [ (self, _) ] when self.local = Self ->
          model_ranked context
            (Interface.Impls.normalize context.database
               ~bounds:(fun _ -> [])
               (Types.substitute (substitution_of own) self.type_))
            ~model:result_type function_symbol
      | _ -> ());
      (* Inside the axioms being stated of a function, a call to it is its
         limited copy, of which nothing is stated, so that the solver
         unfolds each use once rather than without end. *)
      let symbol =
        if List.mem function_symbol context.axiomatizing then begin
          is_limited_call := true;
          let limited = Symbol.Limited { callee = path; instance } in
          declare context (Logic.Function (limited, sorts, result_sort));
          once context (Limited_link function_symbol) (fun () ->
              let parameters =
                List.mapi
                  (fun index sort ->
                    (Symbol.Variable { label = "linked"; numbers = [ index ] }, sort))
                  sorts
              in
              let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
              let applied = Logic.Apply (function_symbol, inputs) in
              add_fact context
                (Logic.forall ~trigger:[ applied ]
                   (parameters, Logic.equal applied (Logic.Apply (limited, inputs)))));
          limited
        end
        else function_symbol
      in
      applied_as := Some (symbol, sorts);
      let term = Logic.Apply (symbol, own_arguments) in
      assume context after (in_range result_type term);
      if bounds result_type <> None && is_on_bound_values then
        once context (In_range symbol) (fun () ->
            let parameters =
              List.mapi
                (fun index sort ->
                  (Symbol.Variable { label = "ranged"; numbers = [ index ] }, sort))
                sorts
            in
            add_fact context
              (Logic.forall
                 ( parameters,
                   in_range result_type
                     (Logic.Apply (symbol, List.map (fun (name, _) -> Logic.Symbol name) parameters))
                 )));
      note_known_call context invocation path term own_arguments;
      term
    end
    else arrive context after "result" result_type
  in
  assume_valid context after result_type result;
  (* A part lent [mut] goes back into the value it is part of when the lend
     ends, as the caller's statement left it, so that value is valid only
     if the part is, which is checked below. *)
  let left_valid =
    match (contract.result_kind, invocation.lends, lent_final) with
    | `Lends, Some Types.Mut, Some leave ->
        Some (validity context after ~assuming:false ~deep:true result_type (leave result), leave)
    | _ -> None
  in
  let check_left () =
    match left_valid with
    | Some (_, leave) ->
        check_valid context after span result_type (leave result) ~deep:true
          ~when_:"when the lend of this part ends"
    | None -> ()
  in
  let is_updating_helper = updating_helper context invocation in
  List.iter
    (fun (passed : passed) ->
      if passed.mode = Types.Mut && not (is_updating_helper && passed.position = 0) then
        match List.assoc_opt passed.position changed with
        | Some term ->
            let valid = validity context after ~assuming:true passed.type_ term in
            assume context after
              (match left_valid with Some (left, _) -> Logic.( ==> ) left valid | None -> valid)
        | None -> ())
    values;
  if not (List.exists (Path.equal path) context.instantiating) then begin
    context.instantiating <- path :: context.instantiating;
    (* The definition, unfolded once, where the [requires] holds. A body
       the prover cannot read is simply not unfolded. *)
    (* A pure function that returns has its definition and its contract
       stated once, as axioms over its parameters triggered by the function
       applied, so that the solver unfolds them only for the calls its
       search meets, and a call states neither again. A function of the
       unit, such as a theorem, is applied in no term a trigger could
       match, so its calls state its contract themselves. *)
    let axiom_symbol =
      match !applied_as with
      | Some (symbol, sorts)
        when contract.result_kind = `Returns && (not !is_limited_call)
             && not (Types.equal result_type Types.unit) ->
          Some (symbol, sorts)
      | _ -> None
    in
    (* Each axiom's parameters are its own, since one axiom is stated while
       another is open, and a fact of one must not be taken for the
       other's. *)
    let parameters_of label sorts =
      context.fresh <- context.fresh + 1;
      let axiom = context.fresh in
      List.mapi
        (fun index sort -> (Symbol.Variable { label; numbers = [ axiom; index ] }, sort))
        sorts
    in
    let readable_clause mark clause inside =
      match snd (specification_value context inside clause) with
      | term when not (mentions_fresh_after context mark term) -> Some term
      | _ -> None
      | exception (Unsupported _ | Foreign_unsupported _) -> None
    in
    (* An axiom holds only of arguments of the parameters' types: in their
       range and valid. Over every integer, a contract such as [append]'s,
       which says the appended value is the last element, contradicts the
       range of the elements. *)
    let parameters_valid outside inputs =
      Logic.conjunction
        (List.map2
           (fun ((parameter : Mir.parameter), _) input ->
             let ty = Types.substitute (substitution_of own) parameter.type_ in
             Logic.( &&& ) (in_range ty input) (validity context outside ~assuming:true ty input))
           own_bound inputs)
    in
    let axiomatizing symbol parameters make =
      let mark = context.fresh in
      let facts = ref [] in
      let axiom = { parameters = List.map fst parameters; hypotheses = []; at_calls = [] } in
      let scopes = context.scopes and open_axioms = context.open_axioms in
      context.axiomatizing <- symbol :: context.axiomatizing;
      context.scopes <- List.map (fun (name, _) -> (name, facts)) parameters @ scopes;
      context.open_axioms <- axiom :: open_axioms;
      Fun.protect
        ~finally:(fun () ->
          context.axiomatizing <- List.tl context.axiomatizing;
          context.scopes <- scopes;
          context.open_axioms <- open_axioms)
        (fun () ->
          let stated = make () in
          let kept terms =
            List.filter (fun term -> not (mentions_fresh_after context mark term)) (List.rev terms)
          in
          axiom.hypotheses <- kept axiom.hypotheses;
          (stated, Logic.conjunction (kept !facts), axiom))
    in
    let record_axiom symbol axiom = Hashtbl.add context.axioms_of symbol axiom in
    let definition_axiom symbol sorts (part : part) body =
      match Hashtbl.find_opt context.defined_by_axiom symbol with
      | Some is_defined -> is_defined
      | None -> (
          Hashtbl.replace context.defined_by_axiom symbol false;
          let parameters = parameters_of "defined" sorts in
          let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
          let arguments = List.mapi (fun index input -> (index, input)) inputs in
          let outside = { after with bound = []; binders = []; condition = Logic.Boolean true } in
          let mark = context.fresh in
          let stated, facts, axiom =
            axiomatizing symbol parameters (fun () ->
                let inside =
                  part_frame
                    { outside with bound = List.map fst parameters; checking = false }
                    part ~arguments ~substitution:(substitution_of part)
                in
                let guard =
                  List.map
                    (fun requirement -> readable_clause mark requirement inside)
                    (clauses part.requires)
                in
                let valid = parameters_valid inside inputs in
                if List.mem None guard || mentions_fresh_after context mark valid then None
                else
                  Option.map
                    (fun defined ->
                      (Logic.conjunction (valid :: List.filter_map Fun.id guard), defined))
                    (body_over context outside parameters body (fun inside ->
                         part_frame inside part ~arguments ~substitution:(substitution_of part))))
          in
          match stated with
          | Some (guard, defined) ->
              let applied = Logic.Apply (symbol, inputs) in
              record_axiom symbol axiom;
              add_fact context
                (Logic.forall ~trigger:[ applied ]
                   ( parameters,
                     Logic.(
                       guard &&& conjunction axiom.hypotheses ==> (facts &&& equal applied defined))
                   ));
              Hashtbl.replace context.defined_by_axiom symbol true;
              true
          | None -> false)
    in
    let contract_axiom symbol sorts =
      once context (Contract_of symbol) (fun () ->
          let parameters = parameters_of "ensured" sorts in
          let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
          let arguments = List.mapi (fun index input -> (index, input)) inputs in
          let applied = Logic.Apply (symbol, inputs) in
          let outside =
            {
              after with
              bound = List.map fst parameters;
              binders = [];
              condition = Logic.Boolean true;
              checking = false;
            }
          in
          let mark = context.fresh in
          let stated, facts, axiom =
            axiomatizing symbol parameters (fun () ->
                let valid = parameters_valid outside inputs in
                let parts =
                  List.filter_map
                    (fun (part : part) ->
                      let inside =
                        {
                          (part_frame outside part ~arguments ~substitution:(substitution_of part)) with
                          result = Some applied;
                          checking = false;
                        }
                      in
                      let required =
                        List.map
                          (fun requirement -> readable_clause mark requirement inside)
                          (clauses part.requires)
                      in
                      if List.mem None required then None
                      else
                        match
                          List.filter_map
                            (fun (clause : Mir.formula) ->
                              Option.map
                                (fun term -> (clause, term))
                                (readable_clause mark clause inside))
                            part.ensures
                        with
                        | [] -> None
                        | ensures -> Some (part, List.filter_map Fun.id required, ensures))
                    contract.parts
                in
                if parts = [] || mentions_fresh_after context mark valid then None
                else Some (valid, parts))
          in
          match stated with
          | None -> ()
          | Some (valid, parts) ->
              List.iter
                (fun ((part : part), _, ensures) ->
                  List.iter
                    (fun ((clause : Mir.formula), _) ->
                      Hashtbl.replace context.axiom_clauses
                        (symbol, part.callee.name, clause.origin)
                        ())
                    ensures)
                parts;
              record_axiom symbol axiom;
              add_fact context
                (Logic.forall ~trigger:[ applied ]
                   ( parameters,
                     Logic.( ==> )
                       (Logic.conjunction (valid :: axiom.hypotheses))
                       (Logic.conjunction
                          (facts
                          :: List.map
                               (fun (_, required, ensures) ->
                                 Logic.( ==> ) (Logic.conjunction required)
                                   (Logic.conjunction (List.map snd ensures)))
                               parts)) )))
    in
    (* The definition at this call's arguments, where the [requires] holds. *)
    let unfold (part : part) body =
      let unfolding =
        if in_quantifier then
          { (entry_frame part) with condition = Logic.Boolean true; bound = []; binders = [] }
        else { (entry_frame part) with condition = after.condition }
      in
      try
        let _, defined = definition_value context unfolding body in
        state (Logic.( ==> ) required (Logic.equal result defined))
      with Unsupported _ | Foreign_unsupported _ -> ()
    in
    (match (!is_limited_call, axiom_symbol) with
    | true, _ -> ()
    | false, Some (symbol, sorts) ->
        let is_defined =
          match contract.definition with
          | Some (part, body) -> definition_axiom symbol sorts part body
          | None -> false
        in
        (match contract.definition with
        | Some (part, body) when (not is_defined) && not is_on_bound_values -> unfold part body
        | _ -> ());
        contract_axiom symbol sorts
    | false, None -> (
        match contract.definition with
        | Some (part, body) when not is_on_bound_values -> unfold part body
        | Some (part, body) when part.requires = [] -> (
            (* Called on a quantifier's bound values, the definition is stated
               once for every argument, so that it holds for each of them. *)
            match !applied_as with
            | Some (symbol, sorts) ->
                once context (Definition_of symbol) (fun () ->
                    let parameters =
                      List.mapi
                        (fun index sort ->
                          (Symbol.Variable { label = "defined"; numbers = [ index ] }, sort))
                        sorts
                    in
                    let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
                    let outside =
                      { after with bound = []; binders = []; condition = Logic.Boolean true }
                    in
                    match
                      body_over context outside parameters body (fun inside ->
                          part_frame inside part
                            ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
                            ~substitution:(substitution_of part))
                    with
                    | Some defined ->
                        add_fact context
                          (Logic.forall
                             (parameters, Logic.equal (Logic.Apply (symbol, inputs)) defined))
                    | None -> ())
            | None -> ())
        | (None | Some _) when is_on_bound_values -> (
            (* Called on a quantifier's bound values, a callee known by its
               contract alone, or with a [requires], has its [ensures] stated
               once, for every valid argument where its [requires] holds. *)
            match !applied_as with
            | Some (symbol, sorts) ->
                once context (Contract_of symbol) (fun () ->
                    let parameters =
                      List.mapi
                        (fun index sort ->
                          (Symbol.Variable { label = "ensured"; numbers = [ index ] }, sort))
                        sorts
                    in
                    let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
                    let outside =
                      {
                        after with
                        bound = List.map fst parameters;
                        binders = [];
                        condition = Logic.Boolean true;
                        checking = false;
                      }
                    in
                    let mark = context.fresh in
                    let valid =
                      Logic.conjunction
                        (List.map2
                           (fun ((parameter : Mir.parameter), _) input ->
                             validity context outside ~assuming:true
                               (Types.substitute (substitution_of own) parameter.type_)
                               input)
                           own_bound inputs)
                    in
                    let ensured =
                      List.filter_map
                        (fun (part : part) ->
                          let inside =
                            {
                              (part_frame outside part
                                 ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
                                 ~substitution:(substitution_of part))
                              with
                              result = Some (Logic.Apply (symbol, inputs));
                              checking = false;
                            }
                          in
                          let required =
                            List.map
                              (fun requirement -> readable_clause mark requirement inside)
                              (clauses part.requires)
                          in
                          match
                            List.filter_map
                              (fun clause -> readable_clause mark clause inside)
                              part.ensures
                          with
                          | [] -> None
                          | _ when List.mem None required -> None
                          | ensures ->
                              Some
                                Logic.(
                                  conjunction (List.filter_map Fun.id required)
                                  ==> conjunction ensures))
                        contract.parts
                    in
                    if ensured <> [] && not (mentions_fresh_after context mark valid) then
                      add_fact context
                        (Logic.forall (parameters, Logic.( ==> ) valid (Logic.conjunction ensured))))
            | None -> ())
        | _ -> ()));
    (* The [ensures], after, where the [requires] held: [mut] parameters
       have their new values, and [old] the ones they had. *)
    let in_axiom (part : part) (clause : Mir.formula) =
      match axiom_symbol with
      | Some (symbol, _) ->
          Hashtbl.mem context.axiom_clauses (symbol, part.callee.name, clause.origin)
      | None -> false
    in
    let assume_ensures keep =
      List.iter
        (fun (part : part) ->
          let entry = bindings part in
          let exit_bindings =
            List.mapi
              (fun index (parameter, term) ->
                ( parameter,
                  match List.assoc_opt index changed with Some term -> Some term | None -> term ))
              entry
          in
          let entry_locals, types, entry_self = bind entry in
          let exit_locals, _, exit_self = bind exit_bindings in
          (* Called inside a quantifier on no bound value, the call's
             [ensures] is a fact outside the quantifier, as its definition
             is: true whether or not the quantifier's body runs. *)
          let is_unbound_in_quantifier = in_quantifier && not is_on_bound_values in
          let ensures_frame =
            {
              frame with
              source = part.callee;
              condition = (if is_unbound_in_quantifier then Logic.Boolean true else after.condition);
              bound = (if is_unbound_in_quantifier then [] else frame.bound);
              binders = (if is_unbound_in_quantifier then [] else frame.binders);
              locals = exit_locals;
              types;
              old_locals = entry_locals;
              self = self_of exit_self;
              old_self = self_of entry_self;
              self_type = self_type_of part entry_self;
              result = Some result;
              checking = false;
              substitution = substitution_of part;
            }
          in
          let ensures_frame =
            match contract.result_kind with
            | `Lends when List.exists mentions_history part.ensures ->
                let left = match lent_final with Some leave -> leave result | None -> result in
                let none = empty_parts context after result_type in
                { ensures_frame with yielded = Some (appended context after result_type none left) }
            | `Lends | `Returns -> ensures_frame
          in
          List.iter
            (fun (clause : Mir.formula) ->
              if keep clause && not (!is_limited_call || in_axiom part clause) then
                let frame_for_clause =
                  if contract.result_kind = `Lends && mentions_result clause then
                    {
                      ensures_frame with
                      locals = entry_locals;
                      self = self_of entry_self;
                      yielded = None;
                    }
                  else ensures_frame
                in
                (* A clause that reads what this package cannot see, such
                   as an opaque type's fields, is a fact only in the
                   callee's own package, and leaving a fact out is sound. *)
                match specification_value context frame_for_clause clause with
                | _, term ->
                    (* A pure call's [ensures], where its [requires] holds, is a
                   fact of mathematics, true whether or not a quantifier's
                   body around it runs. *)
                    state (Logic.( ==> ) (required_by part) term)
                | exception Foreign_unsupported _ -> ())
            part.ensures)
        contract.parts
    in
    let about_part clause = contract.result_kind <> `Lends || mentions_result clause in
    assume_ensures about_part;
    check_left ();
    assume_ensures (fun clause -> not (about_part clause));
    context.instantiating <- List.tl context.instantiating
  end
  else check_left ();
  (* What the callee's axioms need of their parameters holds of the
     arguments, which are values of the parameters' types. *)
  (match !applied_as with
  | Some (symbol, _) when not !is_limited_call ->
      List.iter
        (fun (axiom : open_axiom) ->
          let substitute = Logic.substitute (List.combine axiom.parameters own_arguments) in
          List.iter
            (fun hypothesis -> assume_typed context after (substitute hypothesis))
            axiom.hypotheses;
          List.iter (fun at_call -> at_call after substitute) axiom.at_calls)
        (Hashtbl.find_all context.axioms_of symbol)
  | _ -> ());
  (* The call's cost is the callee's cost clauses with the arguments and
     [result] substituted. [change] is the call's change in potential: that
     of its result and its [mut] arguments after the call, less that of its
     [mut] and [own] arguments before it. *)
  let change () =
    List.fold_left
      (fun total (passed : passed) ->
        let ty = passed.type_ in
        match passed.mode with
        | Types.Mut -> (
            match List.assoc_opt passed.position changed with
            | Some later ->
                Costs.plus total
                  (Costs.minus
                     (potential context after ty later)
                     (potential context frame ty passed.term))
            | None -> total)
        | Types.Own -> Costs.minus total (potential context frame ty passed.term)
        | Types.Read -> total)
      (match contract.result_kind with
      | `Lends -> (
          (* A lent part stays in place, so the call hands over none of its
             potential, and the caller, not the method, pays for the
             caller's changes to it. *)
          match lent_final with
          | Some leave ->
              Costs.minus
                (potential context after result_type result)
                (potential context after result_type (leave result))
          | None -> Costs.zero)
      | `Returns -> potential context after result_type result)
      values
  in
  let after =
    spend context after (fun counter ->
        match (invocation.callee, counter.resource) with
        | Capability_method _, Calls _ ->
            (* A call of a capability's method is one of its calls. *)
            step_amount context after invocation values counter
        | _ ->
            (* A trait's method that promises only that it ends takes at most
               [time(Types.method)] for the type it is called on. *)
            let ends_in =
              match invocation.callee with
              | Trait_method _ when signature_terminates context path ->
                  Some (method_time context frame invocation.callee)
              | _ -> None
            in
            callee_amount ?ends_in context after ~path ~parts:contract.parts
              ~bound_frame:(fun part ->
                { (entry_frame part) with result = Some result; condition = after.condition })
              ~uses:(invocation.uses :> Types.capability list)
              ~values ~change:(Some change) counter)
  in
  (after, result)

let time_of context frame (ty : Types.ty) term =
  let sort = sort_of context ty in
  let symbol = Symbol.Time sort in
  declare context (Logic.Function (symbol, [ sort ], Logic.Int));
  let time = Logic.Apply (symbol, [ term ]) in
  fact context frame (Logic.Operation ("<=", [ Logic.int 1; time ]));
  (match ty with
  | Types.Function { costs; _ }
    when List.exists
           (fun (cost : Types.cost) -> cost.resource = Types.Time && cost.bound = Order_of)
           costs ->
      fact context frame (Logic.equal time (Logic.int 1))
  | _ -> ());
  (match List.assoc_opt term context.lambda_times with
  | Some (bound, showing) ->
      (* The bound is used, so the obligations that show it are made. *)
      context.lambda_times <- List.remove_assoc term context.lambda_times;
      context.obligations <- List.rev_append showing context.obligations;
      fact context frame (Logic.equal time (Costs.larger (Logic.int 1) bound))
  | None -> ());
  time

(* The cost of a call through a function value: its [time], which is one
   unit for a function type with an [O(...)] bound, and its type's clauses
   for other resources. *)
let function_value_amount context frame (function_type : Types.function_type) callee_term
    (counter : Costs.counter) =
  let clause resource =
    List.find_opt (fun (cost : Types.cost) -> cost.resource = resource) function_type.costs
  in
  let by_clause resource =
    match (clause resource, counter.counting) with
    | Some { bound = Order_of; _ }, Units -> Logic.int 1
    | Some { bound = No_more_than (Some limit) | Exactly_cost (Some limit); _ }, Units ->
        Logic.Integer limit
    | Some { bound = No_more_than (Some limit); _ }, (At_most | Exactly) ->
        bounded_amount context frame (Logic.Integer limit)
    | Some { bound = Exactly_cost (Some limit); _ }, (At_most | Exactly) -> Logic.Integer limit
    | _ -> unknown_amount context frame counter
  in
  match counter.resource with
  | Time -> time_of context frame (Types.Function function_type) callee_term
  | Allocations -> by_clause Types.Allocations
  | Allocated_bytes -> by_clause Types.Allocated_bytes
  | Calls (Through term) ->
      if lambda_captures_target context callee_term term then unknown_amount context frame counter
      else
        spent_where
          (may_be_target context frame callee_term (Types.Function function_type) term)
          (Logic.int 1)
  | Calls (Capability path | Capability_method (path, _)) ->
      if
        List.exists
          (function
            | Types.Capability used -> Path.equal used path
            | Types.Capability_parameter _ | Types.Capability_projection _
            | Types.Capability_variable _ ->
                true)
          (function_type.uses :> Types.capability list)
      then unknown_amount context frame counter
      else Costs.zero

(* A call, given its arguments' values and, for a call through a function
   value, the value and its type: the callee's contract, or for an
   intrinsic, its meaning. *)
let apply_call ?lent_final context frame (site : Invocation.site) (invocation : Invocation.t)
    ~through (values : passed list) =
  let span = span_of frame.source site.origin in
  List.iter
    (fun (passed : passed) ->
      match passed.shape with
      | Named_function { origin; path; _ } -> (
          match
            function_contract ?reading_package:(reading_package context) context.database path
          with
          | Some contract ->
              check_named_callback context frame invocation passed ~origin path contract values
          | None -> ())
      | Forwarded local ->
          check_forwarded_callback context frame site invocation passed local values
      | Other -> ())
    values;
  (* An index read, which the ownership check may have paired with
     another. *)
  (match (invocation.lends, values) with
  | Some _, _ :: index :: _ -> note_place context frame site.origin (One index.term)
  | _ -> ());
  let result_type = substituted context frame site.type_ in
  (match invocation.callee with
  | Intrinsic _ -> ()
  | _ ->
      let exempt = updating_helper context invocation in
      List.iter
        (fun (passed : passed) ->
          if not (exempt && passed.position = 0) then
            check_valid context frame span passed.type_ passed.term ~deep:true
              ~when_:"when it is passed to this call")
        values);
  (* Each [mut] argument takes a fresh value, stored into its place: a
     local, [self], a field, which rebuilds the value it is in, or an
     element, through its collection's [lends mut] index. *)
  let havoc_mut frame =
    List.fold_left
      (fun frame (passed : passed) ->
        match (passed.mode, passed.passed_place) with
        | Types.Mut, Some place -> place.write frame (arrive context frame "changed" passed.type_)
        | _ -> frame)
      frame values
  in
  let arguments_of (type_arguments : Types.argument list) =
    List.map
      (fun argument ->
        match Types.substitute_argument frame.substitution argument with
        | Types.Type ty -> Types.Type (substituted context frame ty)
        | other -> other)
      type_arguments
  in
  let generics_of path =
    match Interface.Impls.signature context.database path with
    | Some (signature : Types.signature) ->
        List.map (fun (generic : Types.generic) -> generic.generic) signature.generics
    | None -> []
  in
  (* Pairs generic parameters with arguments, leaving out those already
     given, such as an [impl]'s. *)
  let pair parameters arguments ~fixed =
    let parameters =
      List.filter (fun parameter -> not (List.mem_assoc parameter fixed)) parameters
    in
    let rec pair_remaining parameters arguments =
      match (parameters, arguments) with
      | parameter :: parameters, argument :: arguments ->
          (parameter, argument) :: pair_remaining parameters arguments
      | _ -> []
    in
    fixed @ pair_remaining parameters arguments
  in
  (* In a function with a [time] clause, every call must end, and an
     [impl] used where a bound needs one must not reach back here. *)
  if context.terminates && frame.checking then begin
    let ends =
      match invocation.callee with
      | Function { path; _ } -> signature_terminates context path
      | Trait_method { evidence = Impl { impl; _ }; name; receiver; _ } ->
          signature_terminates context (Path.Method { owner = impl; name; receiver })
      | Trait_method { trait; name; receiver; evidence = Bound; self_type; _ } -> (
          (* A bound on a type the frame's substitution makes known, as in
             code proven once for each integer type, reaches its [impl]. *)
          let trait =
            {
              trait with
              trait_arguments =
                List.map
                  (function
                    | Types.Type ty -> Types.Type (substituted context frame ty)
                    | argument -> argument)
                  trait.trait_arguments;
            }
          in
          match concrete_impl context trait (substituted context frame self_type) with
          | Some (impl, _)
            when Interface.Impls.signature context.database
                   (Path.Method { owner = impl; name; receiver })
                 <> None ->
              signature_terminates context (Path.Method { owner = impl; name; receiver })
          | _ -> signature_terminates context (Path.Method { owner = trait.trait; name; receiver }))
      | Trait_method { trait; name; receiver; _ } ->
          signature_terminates context (Path.Method { owner = trait.trait; name; receiver })
      | Capability_method { capability; name } ->
          signature_terminates context (Path.Method { owner = capability; name; receiver = Static })
      | Indirect () -> (
          match through with
          | Some (Types.Function function_type, _, _) -> Types.terminates function_type
          | _ -> false)
      | Intrinsic _ -> true
    in
    if not ends then
      oblige context frame Termination span
        "This call may not end, since its callee has no `time` clause, so neither may this \
         function."
        (Logic.Boolean false);
    let impls =
      Query.demand context.database Call_graph.package_impls (Path.package context.current)
    in
    List.iter
      (fun impl ->
        let reaches_here =
          List.exists
            (fun method_ ->
              Call_graph.reaches context.database ~package:(Path.package context.current)
                ~from:method_ ~target:context.current)
            (Call_graph.impl_methods context.database impl)
        in
        if reaches_here then
          oblige context frame Termination span
            (Printf.sprintf
               "This call uses `%s` where a bound needs it, and that `impl`'s methods reach back \
                here. Such a use passes no arguments the prover can compare, so the recursion \
                cannot be shown to end: write it as a direct call on a part."
               (Path.show impl))
            (Logic.Boolean false))
      (Call_graph.impls_used context.database impls invocation.callee)
  end;
  let with_contract ?(substitution_of = fun _ -> []) ?(instance = []) path = function
    | Some contract ->
        Some
          (contract_call ~lent_final context frame site invocation path contract values ~havoc_mut
             ~substitution_of ~instance)
    | None ->
        let frame = havoc_mut frame in
        let frame = spend context frame (step_amount context frame invocation values) in
        Some (frame, arrive context frame "result" result_type)
  in
  match invocation.callee with
  | Function { path; type_arguments } ->
      let arguments = arguments_of type_arguments in
      let substitution = pair (generics_of path) arguments ~fixed:[] in
      with_contract
        ~substitution_of:(fun _ -> substitution)
        ~instance:(List.map argument_key arguments) path
        (function_contract ?reading_package:(reading_package context) context.database path)
  | Trait_method { trait; name; receiver; evidence; self_type; type_arguments } -> (
      let arguments = arguments_of type_arguments in
      let self_type = substituted context frame self_type in
      let trait = { trait with trait_arguments = arguments_of trait.trait_arguments } in
      (* A bound on [Self], read where [Self] is a known type, as in a law
         proven for one [impl], reaches that type's [impl]. *)
      let evidence : evidence =
        match evidence with
        | Bound -> (
            match concrete_impl context trait self_type with
            | Some (impl, arguments) -> Impl { impl; arguments }
            | None -> evidence)
        | _ -> evidence
      in
      assume_laws context frame ~at:span trait self_type;
      let operands () = List.map (fun (passed : passed) -> passed.term) values in
      match (name, evidence, operands ()) with
      | ("minimum_value" | "maximum_value" | "bit_width"), _, []
        when Well_known.is Fixed_width_integer trait.trait && Types.integer_bits self_type <> None
        -> (
          (* A built-in integer type's bounds and bits are numbers, so that
             an obligation that names them stays linear. *)
          match (name, Types.integer_range self_type, Types.integer_bits self_type) with
          | "minimum_value", Some (low, _), _ -> Some (frame, Logic.Integer low)
          | "maximum_value", Some (_, high), _ -> Some (frame, Logic.Integer high)
          | _, _, Some (bits, _) -> Some (frame, Logic.int bits)
          | _ -> None)
      | "equal", _, [ left; right ]
        when Path.equal trait.trait equal_trait && structural context self_type ->
          (* [==] on a type with identity semantics is the solver's
             equality. *)
          Some (frame, Logic.equal left right)
      | "equal", Impl { impl = Derived _; _ }, [ left; right ]
        when Path.equal trait.trait equal_trait ->
          (* A derived [impl] is defined by the rule that derived it. *)
          Some (frame, equal_of context frame self_type left right)
      | _ ->
          (match evidence with
          | (Bound | Dynamic) when name = "from_template" && Path.equal trait.trait template_trait
            ->
              oblige context frame Requires span
                "A call of `from_template` through a bound or `any` cannot see the tag's \
                 `requires` on its template: build the value with a template, where the tag is \
                 known."
                (Logic.Boolean false)
          | _ -> ());
          let trait_path = Path.Method { owner = trait.trait; name; receiver } in
          (* The trait's clauses are about [Self] and the trait's parameters. *)
          let trait_substitution =
            pair (generics_of trait_path) arguments
              ~fixed:(trait_substitution context.database trait self_type)
          in
          let path, own_substitution =
            match evidence with
            | Impl { impl; arguments = impl_arguments } ->
                let impl_substitution =
                  List.map
                    (fun (parameter, argument) ->
                      (parameter, Types.substitute_argument frame.substitution argument))
                    impl_arguments
                in
                let path = Path.Method { owner = impl; name; receiver } in
                (path, pair (generics_of path) arguments ~fixed:impl_substitution)
            | _ -> (trait_path, trait_substitution)
          in
          let substitution_of (part : part) =
            if part.inherited then trait_substitution else own_substitution
          in
          with_contract ~substitution_of
            ~instance:(List.map argument_key (Types.Type self_type :: arguments))
            path
            (method_contract ?reading_package:(reading_package context) context.database trait name
               receiver evidence))
  | Indirect () ->
      check_callback_requires context frame site through values;
      let frame = havoc_mut frame in
      let frame =
        match through with
        | _ when context.counters = [] -> frame
        | Some (Types.Function function_type, callee_term, _) ->
            spend context frame (function_value_amount context frame function_type callee_term)
        | _ -> spend context frame (unknown_amount context frame)
      in
      let result =
        match through with
        | Some (Types.Function function_type, callee_term, _) when in_the_logic function_type ->
            let term =
              applied context function_type callee_term
                (List.map (fun (passed : passed) -> passed.term) values)
            in
            assume context frame (in_range result_type term);
            term
        | _ -> arrive context frame "result" result_type
      in
      (* A function value meets its type's invariants where it returns, as
         a function does, so its result and the final value of a [mut]
         argument are valid. *)
      assume_valid context frame result_type result;
      List.iter
        (fun (passed : passed) ->
          match (passed.mode, passed.passed_place) with
          | Types.Mut, Some place -> (
              try assume_valid context frame passed.type_ (place.read frame)
              with Unsupported _ | Foreign_unsupported _ -> ())
          | _ -> ())
        values;
      Some (frame, result)
  | Capability_method { capability; name } ->
      with_contract
        (Path.Method { owner = capability; name; receiver = Static })
        (capability_contract context.database capability name)
  | Intrinsic { operation; type_arguments } ->
      (* Lending a part of a storage mutates nothing until the lend ends,
         when the borrower's final value is written back. *)
      let frame =
        match operation with
        | Storage_at_mut | Array_at_mut | View_at_mut -> frame
        | _ -> havoc_mut frame
      in
      let operands = List.map (fun (passed : passed) -> passed.term) values in
      (* Each argument's value after the call: a [mut] one read again. *)
      let changed =
        List.map
          (fun (passed : passed) ->
            match (passed.mode, passed.passed_place) with
            | Types.Mut, Some place -> (
                try place.read frame with Unsupported _ | Foreign_unsupported _ -> passed.term)
            | _ -> passed.term)
          values
      in
      let types =
        List.filter_map
          (function Types.Type ty -> Some (substituted context frame ty) | _ -> None)
          type_arguments
      in
      let result =
        match (operation, values) with
        | Array_model, [ array ] -> array_model context frame array.type_ array.term
        | Array_take_view, [ array; part; start ] -> (
            match (array.type_, changed) with
            | Types.Named { arguments = Types.Type element :: _; _ }, after :: _ ->
                let before = array_model context frame array.type_ array.term in
                let run = buffer_model context View element part.term in
                oblige context frame Requires span
                  (Printf.sprintf "`%s` may not take back a view within the array."
                     (quote frame.source site.origin))
                  Logic.(
                    Operation
                      ( "<=",
                        [
                          Operation ("+", [ start.term; sequence_length context element run ]);
                          sequence_length context element before;
                        ] ));
                run_replaced context frame element ~before
                  ~after:(array_model context frame array.type_ after)
                  ~start:start.term
                  ~stop:(Logic.Operation ("+", [ start.term; sequence_length context element run ]))
                  ~run:(Some run);
                arrive context frame "result" result_type
            | _ -> arrive context frame "result" result_type)
        | Array_view, [ array ] -> (
            (* A view of the array's elements. *)
            match array.type_ with
            | Types.Named { arguments = Types.Type element :: _; _ } ->
                let view = arrive context frame "view" result_type in
                assume context frame
                  (Logic.equal
                     (buffer_model context View element view)
                     (array_model context frame array.type_ array.term));
                view
            | _ -> arrive context frame "view" result_type)
        | Array_at_mut, [ array; index ] -> (
            (* The element at [index], lent [mut] until the lend ends, when the
               borrower's final value is written back to the array. *)
            match array.type_ with
            | Types.Named { arguments = Types.Type element :: _; _ } -> (
                let model = array_model context frame array.type_ array.term in
                oblige context frame Requires span
                  (Printf.sprintf "`%s` may not be within the array."
                     (quote frame.source site.origin))
                  Logic.(
                    Operation ("<=", [ int 0; index.term ])
                    &&& Operation ("<", [ index.term; sequence_length context element model ]));
                match sequence_at context element model index.term with
                | Some part -> part
                | None -> arrive context frame "part" result_type)
            | _ -> arrive context frame "part" result_type)
        | Storage_from_array, [ array ] -> (
            (* The array's elements, moved into storage with room for exactly
               them. *)
            match array.type_ with
            | Types.Named { arguments = [ Types.Type element; Types.Value count ]; _ } ->
                let storage = arrive context frame "storage" result_type in
                let elements = buffer_model context Storage element storage in
                let count = value_term context frame count in
                assume context frame
                  Logic.(
                    equal elements (array_model context frame array.type_ array.term)
                    &&& equal (sequence_length context element elements) count
                    &&& equal (buffer_capacity context element storage) count);
                storage
            | _ -> arrive context frame "storage" result_type)
        | Holds_invariant, [ subject; clause ] -> (
            (* One clause of the value's type's invariant, read with
               [self] as the value. *)
            match (clause.term, invariants_of context subject.type_) with
            | Logic.Integer index, Some (source, written) -> (
                match List.nth_opt written (Z.to_int index) with
                | Some invariant ->
                    let inner =
                      type_frame context frame source subject.type_ ~self:(Some subject.term)
                    in
                    snd (specification_value context inner invariant)
                | None -> arrive context frame "holds" result_type)
            | _ -> arrive context frame "holds" result_type)
        | Array_from_storage, [ storage ] -> (
            (* The storage's elements, moved into an array, which must be
               exactly as many as the array's count. *)
            match result_type with
            | Types.Named { arguments = [ Types.Type element; Types.Value count ]; _ } ->
                let elements = buffer_model context Storage element storage.term in
                let count = value_term context frame count in
                oblige context frame Requires span
                  (Printf.sprintf "`%s` may not have as many elements as the array's count."
                     (quote frame.source site.origin))
                  (Logic.equal (sequence_length context element elements) count);
                let array = arrive context frame "array" result_type in
                assume context frame
                  (Logic.equal (array_model context frame result_type array) elements);
                array
            | _ -> arrive context frame "array" result_type)
        | _ ->
            let arguments = List.map (fun (passed : passed) -> passed.origin) values in
            intrinsic context frame ~site operation types operands ~arguments ~changed result_type
      in
      let frame = spend context frame (step_amount context frame invocation values) in
      Some (frame, result)
