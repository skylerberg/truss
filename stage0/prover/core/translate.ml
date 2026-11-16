module Names = Resolve.Names

let home (source : State.source) =
  match source.key with Some key -> key | None -> Facts.bug "%s has no definition key" source.name

let new_context (lookups : Lookups.t) ~home ~current ~terminates ~measures =
  let rec context =
    {
      State.run_body = (fun frame ~lambdas body -> Reader.read_body context frame ~lambdas body);
      formula_term =
        (fun frame formula ~arguments -> Reader.formula_term context frame formula ~arguments);
      home;
      laws_assumed = [];
      lookups;
      current;
      terminates;
      measures;
      declarations = [];
      declared = Hashtbl.create 64;
      datatypes = Hashtbl.create 16;
      stated = Hashtbl.create 64;
      facts = [];
      scopes = [];
      quantifier_facts = Hashtbl.create 16;
      quantifier_symbols = [];
      obligations = [];
      fresh = 0;
      values = [];
      local_names = Hashtbl.create 16;
      returns = [];
      lent_back = [];
      instantiating = [];
      axiomatizing = [];
      open_axioms = [];
      axioms_of = Hashtbl.create 16;
      axiom_clauses = Hashtbl.create 16;
      yielded_part = None;
      yield_ensures = None;
      callbacks = [];
      counters = [];
      own_bounds = [];
      fresh_order = Hashtbl.create 64;
      logs = [];
      powers = [];
      lambda_times = [];
      lambda_captures = [];
      lambda_definitions = Hashtbl.create 8;
      potentials = [];
      models = Hashtbl.create 16;
      holds_potential = Hashtbl.create 16;
      buffers = Hashtbl.create 16;
      equalities = [];
      decisions = [];
      entry = [];
      proving = false;
      holes = [];
      unfinished = [];
      call_targets = [];
      reading_callback = false;
      validating = [];
      ranking = terminates && measures = [] && lookups.recursion_group current <> [];
      disjoint = lookups.must_be_disjoint home;
      indexes = [];
    }
  in
  context

let outcome (context : State.context) =
  { State.obligations = List.rev context.obligations; holes = List.rev context.holes }

let empty_frame source =
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

let promises context (source : State.source) locals (costs : Mir.cost list) ~inherited =
  List.filter_map
    (fun (cost : Mir.cost) ->
      match cost with
      | { resource = Time; bound = Finite; _ } -> None
      | _ -> (
          match Contracts.resource_of cost ~locals with
          | None ->
              Facts.unsupported (Facts.locate context source cost.origin) "this `calls` target"
          | Some resource ->
              let counter =
                { Costs.resource; counting = Lambdas.counting_of cost; amortized = cost.amortized }
              in
              (match (cost.resource, resource) with
              | Calls (Function_parameter local), Calls (Through term) ->
                  context.call_targets <- (term, local) :: context.call_targets
              | _ -> ());
              if counter.counting = Units && not (List.mem counter context.own_bounds) then
                context.own_bounds <- counter :: context.own_bounds;
              Some { counter; clause = cost; written_in = source; inherited }))
    costs

let promised_by (lookups : Lookups.t) (source : State.source) =
  match source.key with
  | Some { path = Method { owner; _ }; _ }
    when Names.kind_of lookups.interface.names owner = Some Names.Capability ->
      "capability"
  | _ -> "trait"

let keep_promise context (frame : State.frame) (promise : promise) ~(at : State.frame) ~location
    ~change =
  let spent =
    match List.assoc_opt promise.counter frame.spent with Some term -> term | None -> Costs.zero
  in
  let spent = if promise.clause.amortized then Costs.plus spent (change ()) else spent in
  let amount =
    match promise.clause.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (Validity.specification_value context { at with makes_obligations = false } amount)
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
             (promised_by context.lookups promise.written_in)
         else "This may spend more than `");
      Facts.quote promise.written_in promise.clause.origin;
      Text "` allows.";
    ]
    goal

let function_ ?(proof = false) ?(is_updating_helper = false) ?inherited ?(substitution = [])
    (lookups : Lookups.t) (source : State.source) ~path =
  let contract =
    match Mir.contract_of_path lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.bug "`%s` has no MIR of its contract" source.name
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
  let home = home source in
  let context = new_context lookups ~home ~current:path ~terminates ~measures:contract.decreases in
  context.proving <- proof;
  context.callbacks <-
    List.filter_map
      (fun (position, callback) ->
        Option.map
          (fun (parameter : Mir.parameter) -> (parameter.local, parameter.name, callback))
          (List.nth_opt parameters position))
      contract.callbacks;
  let own_requires = Facts.clauses contract.requires and own_ensures = contract.ensures in
  let output = match signature with Some { output = Returns ty; _ } -> Some ty | _ -> None in
  let start =
    List.fold_left
      (fun frame (parameter : Mir.parameter) ->
        match parameter.local with
        | Self ->
            let self_type =
              match signature with
              | Some { receiver = Some (_, ty); _ } -> ty
              | _ -> Facts.unsupported Whole_definition "`self` without a type"
            in
            let self = Facts.arrive context frame "self" self_type in
            (match self with
            | Logic.Symbol symbol -> context.entry <- symbol :: context.entry
            | _ -> ());
            if not is_updating_helper then Validity.assume_valid context frame self_type self;
            { frame with self = Some self; self_type = Some self_type }
        | local ->
            let ty = Facts.substituted context frame parameter.type_ in
            let term = Facts.arrive context frame ("parameter." ^ parameter.name) ty in
            (match term with
            | Logic.Symbol symbol ->
                context.values <- (symbol, parameter.name) :: context.values;
                context.entry <- symbol :: context.entry
            | _ -> ());
            Validity.assume_valid context frame ty term;
            Facts.bind frame local ty term)
      { (empty_frame source) with substitution }
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
        { start with yielded_so_far = Some (Amounts.empty_parts context start part) }
    | _ -> start
  in
  let values_of (at : State.frame) =
    List.filter_map
      (fun (parameter : Mir.parameter) ->
        match parameter.local with Self -> at.self | local -> Locals.find_opt local at.locals)
      parameters
  in
  let paired terms =
    match (inherited, parameters, terms) with
    | Some ((part : State.part), _), { local = Self; _ } :: _, _ :: rest
      when not
             (List.exists
                (fun (parameter : Mir.parameter) -> parameter.local = Self)
                part.parameters) ->
        rest
    | _ -> terms
  in
  let values_of (at : State.frame) = paired (values_of at) in
  let own_terms = values_of start in
  let trait_frame (at : State.frame) ~result =
    match inherited with
    | Some ((part : State.part), substitution)
      when List.length part.parameters = List.length own_terms ->
        let locals, types, self, old_locals =
          List.fold_left2
            (fun (locals, types, self, old_locals) (parameter : Mir.parameter) (entry, exit_) ->
              match parameter.local with
              | Self -> (locals, types, Some (exit_, parameter.type_), old_locals)
              | local ->
                  ( Locals.add local exit_ locals,
                    Locals.add local parameter.type_ types,
                    self,
                    Locals.add local entry old_locals ))
            (Locals.empty, Locals.empty, None, Locals.empty)
            part.parameters
            (List.combine own_terms (values_of at))
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
    match trait_frame start ~result:None with
    | Some (part, inside) ->
        Logic.conjunction
          (List.map
             (fun requirement -> snd (Validity.specification_value context inside requirement))
             (Facts.clauses part.requires))
    | None -> Logic.Boolean true
  in
  let mir =
    match Mir.code_of_path lookups.mir path with
    | Some { form; _ } -> form
    | None -> Facts.bug "`%s` has a body and no MIR" source.name
  in
  let promised =
    promises context source start.locals contract.costs ~inherited:false
    @
    match trait_frame start ~result:None with
    | Some (part, inside) -> promises context part.callee inside.locals part.costs ~inherited:true
    | None -> []
  in
  context.counters <-
    Contracts.distinct_counters
      (List.map (fun promise -> promise.counter) promised
      @ Lambdas.loop_counters start.locals mir.body);
  let start =
    { start with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
  in
  let start =
    match trait_frame start ~result:None with
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
                 let frame, term = Validity.specification_value context frame requirement in
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
              let frame, term = Validity.specification_value context frame requirement in
              Facts.assume context frame term;
              frame)
            start own_requires
        end
    | _ ->
        List.fold_left
          (fun frame requirement ->
            let frame, term = Validity.specification_value context frame requirement in
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
            ignore (Validity.specification_value context { start with result } amount)
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
            ( Locals.find_opt parameter.local frame.locals,
              Facts.local_type context frame parameter.local )
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
                Validity.specification_value context
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
              let _, term = Validity.specification_value context frame ensured in
              Facts.oblige context frame Ensures
                (Facts.locate context frame.source ensured.origin)
                [
                  Text "`";
                  Facts.quote source ensured.origin;
                  Text "` may not hold when the function returns.";
                ]
                term)
            own_ensures);
      let change () =
        let potential_change =
          List.fold_left
            (fun total (parameter : Mir.parameter) ->
              let entry, later, ty =
                match parameter.local with
                | Self -> (start.self, frame.self, frame.self_type)
                | local ->
                    ( Locals.find_opt local start.locals,
                      Locals.find_opt local frame.locals,
                      Facts.local_type context frame local )
              in
              match (parameter.mode, entry, ty) with
              | (Types.Mut | Types.Own), Some entry, Some ty ->
                  let potential_after =
                    match (parameter.mode, later) with
                    | Types.Mut, Some later -> Amounts.potential context frame ty later
                    | _ -> Costs.zero
                  in
                  Costs.plus total
                    (Costs.minus potential_after (Amounts.potential context frame ty entry))
              | _ -> total)
            Costs.zero parameters
        in
        let potential_change =
          List.fold_left
            (fun total (ty, handed, back) ->
              Costs.minus total
                (Costs.minus
                   (Amounts.potential context frame ty back)
                   (Amounts.potential context frame ty handed)))
            potential_change context.lent_back
        in
        match (returned, output) with
        | Some term, Some output ->
            Costs.plus potential_change (Amounts.potential context frame output term)
        | _ -> potential_change
      in
      let under_trait = Facts.restrict frame trait_requires in
      List.iter
        (fun promise ->
          if promise.inherited then
            match trait_frame frame ~result:returned with
            | Some (_, inside) ->
                keep_promise context under_trait promise
                  ~at:{ inside with locals = inside.old_locals; self = inside.old_self }
                  ~location:Whole_definition ~change
            | None -> ()
          else
            keep_promise context frame promise
              ~at:{ frame with locals = frame.old_locals; self = frame.old_self; result = returned }
              ~location:(Facts.locate context source promise.clause.origin)
              ~change)
        promised;
      match trait_frame frame ~result:returned with
      | Some (part, inside) ->
          List.iter
            (fun (clause : Mir.formula) ->
              let _, term = Validity.specification_value context inside clause in
              Facts.oblige context under_trait Ensures Whole_definition
                [
                  Text (Printf.sprintf "The %s's `" (promised_by lookups part.callee));
                  Facts.quote part.callee clause.origin;
                  Text "` may not hold when this method returns.";
                ]
                term)
            part.ensures
      | _ -> ())
    returns;
  outcome context

let laws (lookups : Lookups.t) (source : State.source) ~impl ~trait ~for_type ~proofs ~at =
  let home = home source in
  let context = new_context lookups ~home ~current:impl ~terminates:false ~measures:[] in
  let start = empty_frame source in
  let substitution = Contracts.trait_substitution lookups trait for_type in
  List.iter
    (fun (law_source, (law : Mir.law)) ->
      let types = Laws.law_parameter_types ~substitution law in
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
        let inside = Laws.law_frame start law_source ~substitution law terms in
        List.iter
          (fun clause ->
            Facts.assume context start (snd (Validity.specification_value context inside clause)))
          law.requires;
        let start =
          List.fold_left
            (fun (start : State.frame) ((proof_source : State.source), renaming) ->
              let proof =
                match
                  Option.bind proof_source.key (fun key -> Mir.code (lookups.mir.body_part key))
                with
                | Some proof -> proof
                | None -> Facts.bug "the proof `%s` has no MIR" proof_source.name
              in
              let parameters =
                List.map
                  (fun parameter ->
                    match proof.body.locals.(parameter) with
                    | { kind = Source { local; _ }; type_; _ } -> (local, type_)
                    | { kind = Temporary | Lent _; _ } ->
                        Facts.bug "a parameter of the proof `%s` is a temporary" proof_source.name)
                  proof.body.parameters
              in
              let locals, types =
                List.fold_left2
                  (fun (locals, types) (local, type_) term ->
                    ( Locals.add local term locals,
                      Locals.add local (Types.substitute renaming type_) types ))
                  (start.locals, start.types) parameters
                  (List.filteri (fun index _ -> index < List.length parameters) terms)
              in
              Facts.restrict start
                (Logic.not_
                   (Values.ghost_code context
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
        let _, holds = Validity.specification_value context inside law.states in
        Facts.oblige context start Law at
          [
            Text
              (Printf.sprintf "The law `%s.%s` may not hold for `%s`." (Types.show_trait trait)
                 law.name (Types.show for_type));
          ]
          holds
      end)
    (Laws.laws_of context trait.trait);
  outcome context

let type_ (lookups : Lookups.t) (source : State.source) ~path =
  let home = home source in
  let context = new_context lookups ~home ~current:path ~terminates:false ~measures:[] in
  (match Mir.type_clauses_of_path lookups.mir path with
  | Some { form = { invariants; potential }; _ } ->
      let ty =
        match Interface.Definition.read_interface lookups.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            Types.Named { path; arguments = Types.list_generic_arguments interface.type_generics }
        | _ -> Types.Named { path; arguments = [] }
      in
      let start = { (empty_frame source) with self_type = Some ty } in
      (match Mir.defaults_of_path lookups.mir path with
      | Some { form = Field_defaults defaults; _ } ->
          List.iter
            (fun (default : Mir.t Mir.field_default) ->
              ignore
                (Amounts.code_value context start default.value
                   ~type_:(Facts.substituted context start default.type_)))
            defaults
      | Some { form = Parameter_defaults _; _ } | None -> ());
      let value_ = Facts.arrive context start "value" ty in
      Facts.assume context start
        (Validity.validity context start ~assuming:true ~own:false ty value_);
      let at_value = { start with self = Some value_; old_self = Some value_ } in
      List.iter
        (fun (invariant : Mir.requirement) ->
          let after, holds = Validity.specification_value context at_value invariant.clause in
          Facts.assume context after holds)
        invariants;
      Option.iter
        (fun (written : Mir.formula) ->
          let _, own = Validity.specification_value context at_value written in
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
  outcome context

let test (lookups : Lookups.t) (source : State.source) ~path =
  let home = home source in
  let context = new_context lookups ~home ~current:path ~terminates:false ~measures:[] in
  (match Mir.code (lookups.mir.body_part home) with
  | Some (mir : Mir.t) ->
      Reader.read_body context (empty_frame source) ~lambdas:mir.lambdas mir.body
  | None -> Facts.bug "the test `%s` has no MIR" source.name);
  outcome context

let constant (lookups : Lookups.t) (source : State.source) ~path =
  let home = home source in
  let context = new_context lookups ~home ~current:path ~terminates:false ~measures:[] in
  (match Mir.initializer_of_path lookups.mir path with
  | Some { form = code; _ } ->
      ignore
        (Amounts.code_value context (empty_frame source) code
           ~type_:(Values.constant_type context path))
  | None -> Facts.bug "the constant `%s` has no MIR" (Path.show path));
  outcome context

let theorem lookups source ~path = function_ ~proof:true lookups source ~path
