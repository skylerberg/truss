let require_home (source : State.source) =
  match source.key with
  | Some key -> key
  | None -> Facts.raise_bug "%s has no definition key" source.name

let make_context (lookups : Lookups.t) ~home ~current ~terminates ~measures =
  let rec context =
    {
      State.run_body = (fun frame ~lambdas body -> Reader.read_body context frame ~lambdas body);
      read_formula =
        (fun frame formula ~arguments -> Reader.read_formula context frame formula ~arguments);
      home;
      laws_assumed = [];
      lookups;
      current;
      terminates;
      measures;
      declarations = [];
      declared = Tables.Symbol_table.create 64;
      datatypes = Tables.Type_table.create 16;
      stated = Tables.Stated_table.create 64;
      facts = [];
      scopes = [];
      quantifier_facts = Tables.Term_table.create 16;
      quantifier_symbols = [];
      obligations = [];
      fresh = 0;
      values = [];
      local_names = Tables.Local_table.create 16;
      returns = [];
      lent_back = [];
      instantiating = [];
      axiomatizing = [];
      open_axioms = [];
      axioms_of = Tables.Symbol_table.create 16;
      axiom_clauses = Tables.Axiom_clause_table.create 16;
      yielded_part = None;
      yield_ensures = None;
      callbacks = [];
      counters = [];
      own_bounds = [];
      fresh_order = Tables.Symbol_table.create 64;
      logs = [];
      powers = [];
      lambda_times = [];
      lambda_captures = [];
      lambda_definitions = Tables.Symbol_table.create 8;
      potentials = [];
      models = Tables.Model_table.create 16;
      holds_potential = Tables.Type_table.create 16;
      buffers = Tables.Type_table.create 16;
      equalities = [];
      decisions = [];
      entry = [];
      proving = false;
      holes = [];
      unfinished = [];
      call_targets = [];
      reading_callback = false;
      validating = [];
      ranking = terminates && measures = [] && lookups.list_recursion_group current <> [];
      disjoint = lookups.list_must_be_disjoint home;
      indexes = [];
    }
  in
  context

let make_outcome (context : State.context) =
  { State.obligations = List.rev context.obligations; holes = List.rev context.holes }

let make_empty_frame source =
  {
    State.source;
    locals = Locals.empty;
    types = Locals.empty;
    old_locals = Locals.empty;
    self = None;
    old_self = None;
    result = None;
    condition = Logic.Boolean true;
    makes_obligations = true;
    panic = Undeclarable;
    bound = [];
    binders = [];
    substitution = [];
    self_type = None;
    aliases = Locals.empty;
    slices = Locals.empty;
    lends = Locals.empty;
    yielded = None;
    yielded_so_far = None;
    spent = [];
  }

type promise = {
  counter : Costs.counter;
  clause : Mir.cost;
  written_in : State.source;
  inherited : bool;
}

let list_promises context (source : State.source) locals (costs : Mir.cost list) ~inherited =
  List.filter_map
    (fun (cost : Mir.cost) ->
      match cost with
      | { resource = Time; bound = Finite; _ } -> None
      | _ -> (
          match Contracts.find_resource cost ~locals with
          | None ->
              Facts.raise_unsupported
                (Facts.locate context source cost.origin)
                "this `calls` target"
          | Some resource ->
              let counter =
                {
                  Costs.resource;
                  counting = Lambdas.classify_counting cost;
                  amortized = cost.amortized;
                }
              in
              (match (cost.resource, resource) with
              | Calls (Function_parameter local), Calls (Through term) ->
                  context.call_targets <- (term, local) :: context.call_targets
              | _ -> ());
              if counter.counting = Units && not (List.mem counter context.own_bounds) then
                context.own_bounds <- counter :: context.own_bounds;
              Some { counter; clause = cost; written_in = source; inherited }))
    costs

let show_promiser_kind (lookups : Lookups.t) (source : State.source) =
  match source.key with
  | Some { path = Method { owner; _ }; _ }
    when Resolve.Names.find_kind lookups.interface.names owner = Some Resolve.Names.Capability ->
      "capability"
  | _ -> "trait"

let keep_promise context (frame : State.frame) (promise : promise) ~(at : State.frame) ~location
    ~compute_change =
  let spent =
    match List.assoc_opt promise.counter frame.spent with Some term -> term | None -> Costs.zero
  in
  let spent = if promise.clause.amortized then Costs.plus spent (compute_change ()) else spent in
  let amount =
    match promise.clause.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (Validity.read_specification context { at with makes_obligations = false } amount)
    | Finite -> Costs.zero
  in
  let goal =
    match promise.counter.counting with
    | Units -> Costs.at_most spent (Costs.bound amount)
    | Exactly -> Logic.equal spent amount
    | At_most -> Costs.at_most spent amount
  in
  Facts.oblige context frame Cost location
    [
      Text
        (if promise.inherited then
           Printf.sprintf "This method may spend more than its %s's `"
             (show_promiser_kind context.lookups promise.written_in)
         else "This may spend more than `");
      Facts.quote promise.written_in promise.clause.origin;
      Text "` allows.";
    ]
    goal

let translate_function ?(proof = false) ?(is_updating_helper = false) ?inherited
    ?(substitution = []) (lookups : Lookups.t) (source : State.source) ~path =
  let contract =
    match Mir.read_contract lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.raise_bug "`%s` has no MIR of its contract" source.name
  in
  let parameters = contract.parameters in
  let signature =
    Option.map
      (Types.map_signature (Types.substitute substitution))
      (Interface.Impls.read_signature lookups.interface path)
  in
  let terminates =
    proof
    ||
    match signature with
    | Some (signature : Types.signature) -> signature.terminates
    | None -> false
  in
  let home = require_home source in
  let context = make_context lookups ~home ~current:path ~terminates ~measures:contract.decreases in
  context.proving <- proof;
  context.callbacks <-
    List.filter_map
      (fun (position, callback) ->
        Option.map
          (fun (parameter : Mir.parameter) -> (parameter.local, parameter.name, callback))
          (List.nth_opt parameters position))
      contract.callbacks;
  let own_requires = Facts.list_clauses contract.requires and own_ensures = contract.ensures in
  let output = match signature with Some { output = Returns ty; _ } -> Some ty | _ -> None in
  let start =
    List.fold_left
      (fun frame (parameter : Mir.parameter) ->
        match parameter.local with
        | Self ->
            let self_type =
              match signature with
              | Some { receiver = Some (_, ty); _ } -> ty
              | _ -> Facts.raise_unsupported Whole_definition "`self` without a type"
            in
            let self = Facts.arrive context frame "self" self_type in
            (match self with
            | Logic.Symbol symbol -> context.entry <- symbol :: context.entry
            | _ -> ());
            if not is_updating_helper then Validity.assume_valid context frame self_type self;
            { frame with self = Some self; self_type = Some self_type }
        | local ->
            let ty = Facts.substitute_type context frame parameter.type_ in
            let term = Facts.arrive context frame ("parameter." ^ parameter.name) ty in
            (match term with
            | Logic.Symbol symbol ->
                context.values <- (symbol, parameter.name) :: context.values;
                context.entry <- symbol :: context.entry
            | _ -> ());
            Validity.assume_valid context frame ty term;
            Facts.bind frame (Core_local local) ty term)
      {
        (make_empty_frame source) with
        substitution;
        panic =
          (match signature with
          | Some { uses; _ } when not proof -> if Types.may_panic uses then Declared else Undeclared
          | Some _ | None -> Undeclarable);
      }
      parameters
  in
  let start = { start with old_locals = start.locals; old_self = start.self } in
  let start =
    match signature with
    | Some { output = Lends (_, part); _ } ->
        context.yielded_part <- Some part;
        context.yield_ensures <-
          Some
            ( List.filter Amounts.mentions_result own_ensures,
              List.filter (fun clause -> not (Amounts.mentions_result clause)) own_ensures );
        { start with yielded_so_far = Some (Amounts.make_empty_parts context start part) }
    | _ -> start
  in
  let list_values (at : State.frame) =
    List.filter_map
      (fun (parameter : Mir.parameter) ->
        match parameter.local with
        | Self -> at.self
        | local -> Locals.find_opt (Core_local local) at.locals)
      parameters
  in
  let pair_up terms =
    match (inherited, parameters, terms) with
    | Some ((part : State.part), _), { local = Self; _ } :: _, _ :: rest
      when not
             (List.exists
                (fun (parameter : Mir.parameter) -> parameter.local = Self)
                part.parameters) ->
        rest
    | _ -> terms
  in
  let list_paired_values (at : State.frame) = pair_up (list_values at) in
  let own_terms = list_paired_values start in
  let find_trait_frame (at : State.frame) ~result =
    match inherited with
    | Some ((part : State.part), substitution)
      when List.length part.parameters = List.length own_terms ->
        let locals, types, self, old_locals =
          List.fold_left2
            (fun (locals, types, self, old_locals) (parameter : Mir.parameter) (entry, exit_) ->
              match parameter.local with
              | Self -> (locals, types, Some (exit_, parameter.type_), old_locals)
              | local ->
                  ( Locals.add (Core_local local) exit_ locals,
                    Locals.add (Core_local local) parameter.type_ types,
                    self,
                    Locals.add (Core_local local) entry old_locals ))
            (Locals.empty, Locals.empty, None, Locals.empty)
            part.parameters
            (List.combine own_terms (list_paired_values at))
        in
        Some
          ( part,
            {
              at with
              source = part.callee;
              locals;
              types;
              old_locals;
              self = Option.map fst self;
              old_self = start.self;
              self_type = Option.map (fun (_, ty) -> Types.substitute substitution ty) self;
              result;
              makes_obligations = false;
              substitution;
            } )
    | _ -> None
  in
  let trait_requires =
    match find_trait_frame start ~result:None with
    | Some (part, inside) ->
        Logic.conjunction
          (List.map
             (fun requirement -> snd (Validity.read_specification context inside requirement))
             (Facts.list_clauses part.requires))
    | None -> Logic.Boolean true
  in
  let mir =
    match Mir.read_code lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.raise_bug "`%s` has a body and no MIR" source.name
  in
  let promised =
    list_promises context source start.locals contract.costs ~inherited:false
    @
    match find_trait_frame start ~result:None with
    | Some (part, inside) ->
        list_promises context part.callee inside.locals part.costs ~inherited:true
    | None -> []
  in
  context.counters <-
    Contracts.deduplicate_counters
      (List.map (fun promise -> promise.counter) promised
      @ Lambdas.list_loop_counters start.locals mir.body);
  let start =
    { start with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
  in
  let start =
    match find_trait_frame start ~result:None with
    | Some (part, _)
      when not
             (match part.callee.key with
             | Some { path = Method { owner; _ }; _ } -> Path.equal owner Laws.template_trait
             | _ -> false) ->
        if own_requires = [] then begin
          Facts.assume context start trait_requires;
          start
        end
        else begin
          ignore
            (List.fold_left
               (fun frame (requirement : Mir.formula) ->
                 let frame, term = Validity.read_specification context frame requirement in
                 Facts.oblige context frame Requires
                   (Facts.locate context frame.source requirement.origin)
                   [
                     Text "`";
                     Facts.quote source requirement.origin;
                     Text
                       "` may not follow from the trait's precondition, which callers through the \
                        trait show, and an `impl`'s precondition must.";
                   ]
                   term;
                 frame)
               (Facts.restrict start trait_requires)
               own_requires);
          List.fold_left
            (fun frame requirement ->
              let frame, term = Validity.read_specification context frame requirement in
              Facts.assume context frame term;
              frame)
            start own_requires
        end
    | _ ->
        List.fold_left
          (fun frame requirement ->
            let frame, term = Validity.read_specification context frame requirement in
            Facts.assume context frame term;
            frame)
          start own_requires
  in
  List.iter
    (fun (promise : promise) ->
      if not promise.inherited then
        match promise.clause.bound with
        | Order_of amount | At_most amount | Exactly amount ->
            let result = Option.map (Facts.arrive context start "result") output in
            ignore (Validity.read_specification context { start with result } amount)
        | Finite -> ())
    promised;
  Reader.read_body context start ~lambdas:mir.lambdas mir.body;
  let returns = List.rev context.returns in
  let mut_parameters =
    List.filter
      (fun (parameter : Mir.parameter) -> parameter.mode = Types.Mut && parameter.local <> Self)
      parameters
  in
  let mut_self =
    List.exists
      (fun (parameter : Mir.parameter) -> parameter.mode = Types.Mut && parameter.local = Self)
      parameters
  in
  List.iter
    (fun ((frame : State.frame), returned) ->
      let frame = { frame with result = returned } in
      (match (returned, output) with
      | Some term, Some output ->
          Lambdas.check_valid context frame Whole_definition output term ~deep:true
            ~when_:"for the value returned"
      | _ -> ());
      List.iter
        (fun (parameter : Mir.parameter) ->
          match
            ( Locals.find_opt (Core_local parameter.local) frame.locals,
              Facts.find_local_type context frame (Core_local parameter.local) )
          with
          | Some term, Some ty ->
              Lambdas.check_valid context frame Whole_definition ty term ~deep:true
                ~when_:(Printf.sprintf "for `%s` when the function returns" parameter.name)
          | _ -> ())
        mut_parameters;
      (match (mut_self, is_updating_helper, frame.self, frame.self_type) with
      | true, false, Some self, Some self_type ->
          Lambdas.check_valid context frame Whole_definition self_type self ~deep:true
            ~when_:"for `self` when the method returns"
      | _ -> ());
      (match (context.yield_ensures, frame.yielded_so_far) with
      | Some (_, at_end), Some yielded_so_far ->
          List.iter
            (fun (ensured : Mir.formula) ->
              let _, term =
                Validity.read_specification context
                  { frame with yielded = Some yielded_so_far }
                  ensured
              in
              Facts.oblige context frame Ensures
                (Facts.locate context frame.source ensured.origin)
                [
                  Text "`";
                  Facts.quote source ensured.origin;
                  Text "` may not hold when the method ends.";
                ]
                term)
            at_end
      | _ ->
          List.iter
            (fun (ensured : Mir.formula) ->
              let _, term = Validity.read_specification context frame ensured in
              Facts.oblige context frame Ensures
                (Facts.locate context frame.source ensured.origin)
                [
                  Text "`";
                  Facts.quote source ensured.origin;
                  Text "` may not hold when the function returns.";
                ]
                term)
            own_ensures);
      let compute_change () =
        let potential_change =
          List.fold_left
            (fun total (parameter : Mir.parameter) ->
              let entry, later, ty =
                match parameter.local with
                | Self -> (start.self, frame.self, frame.self_type)
                | local ->
                    ( Locals.find_opt (Core_local local) start.locals,
                      Locals.find_opt (Core_local local) frame.locals,
                      Facts.find_local_type context frame (Core_local local) )
              in
              match (parameter.mode, entry, ty) with
              | (Types.Mut | Types.Own), Some entry, Some ty ->
                  let potential_after =
                    match (parameter.mode, later) with
                    | Types.Mut, Some later -> Amounts.compute_potential context frame ty later
                    | _ -> Costs.zero
                  in
                  Costs.plus total
                    (Costs.minus potential_after (Amounts.compute_potential context frame ty entry))
              | _ -> total)
            Costs.zero parameters
        in
        let potential_change =
          List.fold_left
            (fun total (ty, handed, back) ->
              Costs.minus total
                (Costs.minus
                   (Amounts.compute_potential context frame ty back)
                   (Amounts.compute_potential context frame ty handed)))
            potential_change context.lent_back
        in
        match (returned, output) with
        | Some term, Some output ->
            Costs.plus potential_change (Amounts.compute_potential context frame output term)
        | _ -> potential_change
      in
      let under_trait = Facts.restrict frame trait_requires in
      List.iter
        (fun promise ->
          if promise.inherited then
            match find_trait_frame frame ~result:returned with
            | Some (_, inside) ->
                keep_promise context under_trait promise
                  ~at:{ inside with locals = inside.old_locals; self = inside.old_self }
                  ~location:Whole_definition ~compute_change
            | None -> ()
          else
            keep_promise context frame promise
              ~at:{ frame with locals = frame.old_locals; self = frame.old_self; result = returned }
              ~location:(Facts.locate context source promise.clause.origin)
              ~compute_change)
        promised;
      match find_trait_frame frame ~result:returned with
      | Some (part, inside) ->
          List.iter
            (fun (clause : Mir.formula) ->
              let _, term = Validity.read_specification context inside clause in
              Facts.oblige context under_trait Ensures Whole_definition
                [
                  Text (Printf.sprintf "The %s's `" (show_promiser_kind lookups part.callee));
                  Facts.quote part.callee clause.origin;
                  Text "` may not hold when this method returns.";
                ]
                term)
            part.ensures
      | _ -> ())
    returns;
  make_outcome context

let translate_laws (lookups : Lookups.t) (source : State.source) ~impl ~trait ~for_type ~proofs ~at
    =
  let home = require_home source in
  let context = make_context lookups ~home ~current:impl ~terminates:false ~measures:[] in
  let start = make_empty_frame source in
  let substitution = Contracts.make_trait_substitution lookups trait for_type in
  List.iter
    (fun (law_source, (law : Mir.law)) ->
      let types = Laws.list_law_parameter_types ~substitution law in
      if not (List.exists (fun ty -> Types.is_error ty) types) then begin
        context.laws_assumed <- (trait, for_type) :: context.laws_assumed;
        let terms =
          List.map
            (fun ty ->
              let term = Facts.arrive context start "law" ty in
              Validity.assume_valid context start ty term;
              term)
            types
        in
        let inside = Laws.bind_law_parameters start law_source ~substitution law terms in
        List.iter
          (fun clause ->
            Facts.assume context start (snd (Validity.read_specification context inside clause)))
          law.requires;
        let start =
          List.fold_left
            (fun (start : State.frame) ((proof_source : State.source), renaming) ->
              let proof =
                match
                  Option.bind proof_source.key (fun key ->
                      Mir.find_code (lookups.mir.read_body_part key))
                with
                | Some proof -> proof
                | None -> Facts.raise_bug "the proof `%s` has no MIR" proof_source.name
              in
              let parameters =
                List.map
                  (fun parameter ->
                    match proof.body.locals.(parameter) with
                    | { kind = Source { local; _ }; type_; _ } -> (local, type_)
                    | { kind = Temporary | Lent _; _ } ->
                        Facts.raise_bug "a parameter of the proof `%s` is a temporary"
                          proof_source.name)
                  proof.body.parameters
              in
              let locals, types =
                List.fold_left2
                  (fun (locals, types) (local, type_) term ->
                    ( Locals.add (Core_local local) term locals,
                      Locals.add (Core_local local) (Types.substitute renaming type_) types ))
                  (start.locals, start.types) parameters
                  (List.take (List.length parameters) terms)
              in
              Facts.restrict start
                (Logic.not_
                   (Values.run_ghost_code context
                      {
                        start with
                        source = proof_source;
                        makes_obligations = false;
                        locals;
                        types;
                        substitution = renaming;
                      }
                      proof)))
            start
            (List.filter_map
               (fun (name, proof) -> if name = law.name then Some proof else None)
               proofs)
        in
        let _, holds = Validity.read_specification context inside law.states in
        Facts.oblige context start Law at
          [
            Text
              (Printf.sprintf "The law `%s.%s` may not hold for `%s`." (Types.show_trait trait)
                 law.name (Types.show for_type));
          ]
          holds
      end)
    (Laws.list_laws context trait.trait);
  make_outcome context

let translate_type (lookups : Lookups.t) (source : State.source) ~path =
  let home = require_home source in
  let context = make_context lookups ~home ~current:path ~terminates:false ~measures:[] in
  (match Mir.read_type_clauses lookups.mir path with
  | Some { form = { invariants; potential }; _ } ->
      let ty =
        match Interface.Definition.read_interface lookups.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            Types.Named { path; arguments = Types.list_generic_arguments interface.type_generics }
        | _ -> Types.Named { path; arguments = [] }
      in
      let start = { (make_empty_frame source) with self_type = Some ty } in
      (match Mir.read_defaults lookups.mir path with
      | Some { form = Field_defaults defaults; _ } ->
          List.iter
            (fun (default : Mir.t Mir.field_default) ->
              ignore
                (Amounts.run_code context start default.value
                   ~type_:(Facts.substitute_type context start default.type_)))
            defaults
      | Some { form = Parameter_defaults _; _ } | None -> ());
      let value_ = Facts.arrive context start "value" ty in
      Facts.assume context start
        (Validity.make_validity context start ~assuming:true ~own:false ty value_);
      let at_value = { start with self = Some value_; old_self = Some value_ } in
      List.iter
        (fun (invariant : Mir.requirement) ->
          let after, holds = Validity.read_specification context at_value invariant.clause in
          Facts.assume context after holds)
        invariants;
      Option.iter
        (fun (written : Mir.formula) ->
          let _, own = Validity.read_specification context at_value written in
          Facts.oblige context at_value Cost
            (Facts.locate context at_value.source written.origin)
            [
              Text
                (Printf.sprintf
                   "The potential of `%s` may be below zero for a value that meets its invariants."
                   (Types.show ty));
            ]
            (Logic.Operation ("<=", [ Logic.int 0; own ])))
        potential
  | None -> ());
  make_outcome context

let test (lookups : Lookups.t) (source : State.source) ~path =
  let home = require_home source in
  let context = make_context lookups ~home ~current:path ~terminates:false ~measures:[] in
  (match Mir.find_code (lookups.mir.read_body_part home) with
  | Some (mir : Mir.t) ->
      Reader.read_body context (make_empty_frame source) ~lambdas:mir.lambdas mir.body
  | None -> Facts.raise_bug "the test `%s` has no MIR" source.name);
  make_outcome context

let translate_constant (lookups : Lookups.t) (source : State.source) ~path =
  let home = require_home source in
  let context = make_context lookups ~home ~current:path ~terminates:false ~measures:[] in
  (match Mir.read_initializer lookups.mir path with
  | Some { form = code; _ } ->
      ignore
        (Amounts.run_code context (make_empty_frame source) code
           ~type_:(Values.compute_constant_type context path))
  | None -> Facts.raise_bug "the constant `%s` has no MIR" (Path.show path));
  make_outcome context

let translate_theorem lookups source ~path = translate_function ~proof:true lookups source ~path
