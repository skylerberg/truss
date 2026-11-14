(* A checked definition as obligations: a function's, a theorem's, a type's,
   a test's, a constant's, and the laws of an [impl]. Each starts a context
   and a frame, runs the definition's code by the reader of the MIR, and
   obliges what the definition states. *)

open Core
open State
open Facts
open Contracts
open Validity
open Lambdas
open Laws
open Amounts
open Values
open Reader

let new_context database ~home ~current ~terminates ~measures =
  let rec context =
    {
      run_body = (fun frame ~lambdas body -> mir_run context frame ~lambdas body);
      formula_term = (fun frame formula ~arguments -> formula_term context frame formula ~arguments);
      home;
      laws_assumed = [];
      database;
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
      defined_by_axiom = Hashtbl.create 16;
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
      known_calls = [];
      decisions = [];
      entry = [];
      proving = false;
      holes = [];
      unfinished = [];
      call_targets = [];
      reading_callback = false;
      validating = [];
      ranking =
        terminates && measures = []
        && Call_graph.recursive database ~package:(Path.package current) current;
      disjoint =
        (match Query.demand database Ownership.ownership home with
        | Some ownership -> ownership.disjoint
        | None -> []);
      indexes = [];
      evaluated_keys = [];
    }
  in
  context

let outcome context = { obligations = List.rev context.obligations; holes = List.rev context.holes }

(* A frame at the start of a definition, before its parameters are bound. *)
let empty_frame source =
  {
    source;
    locals = Locals.empty;
    types = Locals.empty;
    old_locals = Locals.empty;
    self = None;
    old_self = None;
    result = None;
    condition = Logic.Boolean true;
    checking = true;
    bound = [];
    binders = [];
    substitution = [];
    self_type = None;
    yielded = None;
    yielded_so_far = None;
    spent = [];
  }

(* The span of the whole definition, for an obligation about how it
   returns. *)
let definition_span (source : source) =
  let spans = Lazy.force source.spans in
  match Array.length spans with 0 -> Syntax.Span.make 0 0 | count -> spans.(count - 1)

(* A cost clause, as a promise about one counter, shown at each way its
   definition returns. A trait's clause, which an [impl]'s method keeps, is
   read in the trait's form. *)
type promise = { counter : Costs.counter; clause : Mir.cost; written_in : source; inherited : bool }

let promises context (source : source) locals (costs : Mir.cost list) ~inherited =
  List.filter_map
    (fun (cost : Mir.cost) ->
      match cost with
      | { resource = Time; bound = Finite; _ } -> None
      | _ -> (
          match resource_of cost ~locals with
          | None -> unsupported (span_of source cost.origin) "this `calls` target"
          | Some resource ->
              let counter =
                { Costs.resource; counting = counting_of cost; amortized = cost.amortized }
              in
              (match (cost.resource, resource) with
              | Calls (Function_parameter local), Calls (Through term) ->
                  context.call_targets <- (term, local) :: context.call_targets
              | _ -> ());
              if counter.counting = Units && not (List.mem counter context.own_bounds) then
                context.own_bounds <- counter :: context.own_bounds;
              Some { counter; clause = cost; written_in = source; inherited }))
    costs

(* The source of a method's inherited clauses, for messages: its trait,
   or its capability. *)
let promised_by database (source : source) =
  match source.key with
  | Some { path = Method { owner; _ }; _ }
    when Interface.Summary.kind_of database owner = Some Names.Capability ->
      "capability"
  | _ -> "trait"

(* A promise shown where its definition returns: the cost within
   its bound, read with the parameters as they were on entry. *)
let keep_promise context (frame : frame) (promise : promise) ~(at : frame) ~span ~change =
  let spent =
    match List.assoc_opt promise.counter frame.spent with Some term -> term | None -> Costs.zero
  in
  (* An amortized bound is on the cost plus the change in potential of the
     definition's result and mutated values. *)
  let spent = if promise.clause.amortized then Costs.plus spent (change ()) else spent in
  let amount =
    match promise.clause.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (specification_value context { at with checking = false } amount)
    | Finite -> Costs.zero
  in
  let goal =
    match promise.counter.counting with
    | Units -> Costs.at_most spent (Costs.bound amount)
    | Exactly -> Logic.equal spent amount
    | At_most -> Costs.at_most spent amount
  in
  oblige context frame Cost span
    (if promise.inherited then
       Printf.sprintf "This method may spend more than its %s's `%s` allows."
         (promised_by context.database promise.written_in)
         (quote promise.written_in promise.clause.origin)
     else
       Printf.sprintf "This may spend more than `%s` allows."
         (quote promise.written_in promise.clause.origin))
    goal

(* A function, method, or theorem: its parameters arrive, its
   preconditions are assumed, its body runs, and its postconditions and
   cost clauses are shown at each way it returns. [inherited] is, for an
   [impl]'s method, its trait's clauses, with the substitution they are
   read under and the body the trait provides, if any. *)
let function_ ?(proof = false) ?(updating_helper = false) ?inherited ?(substitution = []) database
    (source : source) ~path =
  let contract =
    match Query.demand database Mir.contract_of_path path with
    | Some contract -> contract
    | None -> bug "`%s` has no MIR of its contract" source.name
  in
  let parameters = contract.parameters in
  let signature =
    Option.map
      (Types.map_signature (Types.substitute substitution))
      (Interface.Impls.signature database path)
  in
  let terminates =
    proof
    ||
    match signature with
    | Some (signature : Types.signature) -> signature.terminates
    | None -> false
  in
  let home = home source in
  let context = new_context database ~home ~current:path ~terminates ~measures:contract.decreases in
  let returns_span = definition_span source in
  context.proving <- proof;
  context.callbacks <-
    List.filter_map
      (fun (position, callback) ->
        Option.map
          (fun (parameter : Mir.parameter) -> (parameter.local, parameter.name, callback))
          (List.nth_opt parameters position))
      contract.callbacks;
  let own_requires = clauses contract.requires and own_ensures = contract.ensures in
  let output = match signature with Some { output = Returns ty; _ } -> Some ty | _ -> None in
  let start =
    List.fold_left
      (fun frame (parameter : Mir.parameter) ->
        match parameter.local with
        | Self ->
            let self_type =
              match signature with
              | Some { receiver = Some (_, ty); _ } -> ty
              | _ -> unsupported returns_span "`self` without a type"
            in
            let self = arrive context frame "self" self_type in
            (match self with
            | Logic.Symbol symbol -> context.entry <- symbol :: context.entry
            | _ -> ());
            if not updating_helper then assume_valid context frame self_type self;
            { frame with self = Some self; self_type = Some self_type }
        | local ->
            let ty = substituted context frame parameter.type_ in
            let term = arrive context frame ("parameter." ^ parameter.name) ty in
            (match term with
            | Logic.Symbol symbol ->
                context.values <- (symbol, parameter.name) :: context.values;
                context.entry <- symbol :: context.entry
            | _ -> ());
            assume_valid context frame ty term;
            bind frame local ty term)
      { (empty_frame source) with substitution }
      parameters
  in
  let start = { start with old_locals = start.locals; old_self = start.self } in
  (* A lending method lends a part: its postconditions that mention
     [result] hold where it lends, and its others where the lend ends. *)
  let start =
    match signature with
    | Some { output = Lends (_, part); _ } ->
        context.yielded_part <- Some part;
        context.yield_ensures <-
          Some
            ( List.filter mentions_result own_ensures,
              List.filter (fun clause -> not (mentions_result clause)) own_ensures );
        { start with yielded_so_far = Some (empty_parts context start part) }
    | _ -> start
  in
  (* Each parameter's value, [self] first, as a call's arguments are
     numbered. *)
  let values_of (at : frame) =
    List.filter_map
      (fun (parameter : Mir.parameter) ->
        match parameter.local with Self -> at.self | local -> Locals.find_opt local at.locals)
      parameters
  in
  (* A capability's method takes no [self], but the method an [impl] of the
     capability writes does, so the [impl]'s [self] is left out when the
     two are paired. *)
  let paired terms =
    match (inherited, parameters, terms) with
    | Some ((part : part), _, _), { local = Self; _ } :: _, _ :: rest
      when not
             (List.exists
                (fun (parameter : Mir.parameter) -> parameter.local = Self)
                part.parameters) ->
        rest
    | _ -> terms
  in
  let values_of (at : frame) = paired (values_of at) in
  let own_terms = values_of start in
  (* An [impl]'s method also keeps its trait's or its capability's contract.
     Callers through a bound or the capability prove that precondition, so
     it is assumed and must imply the method's own. They assume that
     postcondition, so it is proven. *)
  let trait_frame (at : frame) ~result =
    match inherited with
    | Some ((part : part), substitution, _) when List.length part.parameters = List.length own_terms
      ->
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
              checking = false;
              substitution;
            } )
    | _ -> None
  in
  (* The trait's precondition, on entry, under which its postcondition and
     cost clauses are promised. *)
  let trait_requires =
    match trait_frame start ~result:None with
    | Some (part, inside) ->
        Logic.conjunction
          (List.map
             (fun requirement -> snd (specification_value context inside requirement))
             (clauses part.requires))
    | None -> Logic.Boolean true
  in
  let mir =
    match Query.demand database Mir.of_path path with
    | Some mir -> mir
    | None -> bug "`%s` has a body and no MIR" source.name
  in
  (* Its cost clauses, and its trait's, each count from zero. *)
  let promised =
    promises context source start.locals contract.costs ~inherited:false
    @
    match trait_frame start ~result:None with
    | Some (part, inside) -> promises context part.callee inside.locals part.costs ~inherited:true
    | None -> []
  in
  context.counters <-
    distinct_counters
      (List.map (fun promise -> promise.counter) promised @ mir_loop_counters start.locals mir.body);
  let start =
    { start with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
  in
  let start =
    match trait_frame start ~result:None with
    | Some (part, _)
    (* A tag's [from_template] may require more than its trait, since only
       a template calls it, where the tag is known; a call through a bound
       is an error, which keeps that sound. *)
      when not
             (match part.callee.key with
             | Some { path = Method { owner; _ }; _ } -> Path.equal owner template_trait
             | _ -> false) ->
        if own_requires = [] then begin
          assume context start trait_requires;
          start
        end
        else begin
          ignore
            (List.fold_left
               (fun frame (requirement : Mir.formula) ->
                 let frame, term = specification_value context frame requirement in
                 oblige context frame Requires
                   (span_of frame.source requirement.origin)
                   (Printf.sprintf
                      "`%s` may not follow from the trait's precondition, which callers through \
                       the trait show, and an `impl`'s precondition must."
                      (quote source requirement.origin))
                   term;
                 frame)
               (restrict start trait_requires) own_requires);
          List.fold_left
            (fun frame requirement ->
              let frame, term = specification_value context frame requirement in
              assume context frame term;
              frame)
            start own_requires
        end
    | _ ->
        List.fold_left
          (fun frame requirement ->
            let frame, term = specification_value context frame requirement in
            assume context frame term;
            frame)
          start own_requires
  in
  (* Each of its own cost bounds is well defined, read where it is
     checked: on entry, with any result. *)
  List.iter
    (fun (promise : promise) ->
      if not promise.inherited then
        match promise.clause.bound with
        | Order_of amount | At_most amount | Exactly amount ->
            let result = Option.map (arrive context start "result") output in
            ignore (specification_value context { start with result } amount)
        | Finite -> ())
    promised;
  mir_run context start ~lambdas:mir.lambdas mir.body;
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
    (fun ((frame : frame), returned) ->
      let frame = { frame with result = returned } in
      (match (returned, output) with
      | Some term, Some output ->
          check_valid context frame returns_span output term ~deep:true
            ~when_:"for the value returned"
      | _ -> ());
      List.iter
        (fun (parameter : Mir.parameter) ->
          match
            (Locals.find_opt parameter.local frame.locals, local_type context frame parameter.local)
          with
          | Some term, Some ty ->
              check_valid context frame returns_span ty term ~deep:true
                ~when_:(Printf.sprintf "for `%s` when the function returns" parameter.name)
          | _ -> ())
        mut_parameters;
      (match (mut_self, updating_helper, frame.self, frame.self_type) with
      | true, false, Some self, Some self_type ->
          check_valid context frame returns_span self_type self ~deep:true
            ~when_:"for `self` when the method returns"
      | _ -> ());
      (match (context.yield_ensures, frame.yielded_so_far) with
      | Some (_, at_end), Some yielded_so_far ->
          List.iter
            (fun (ensured : Mir.formula) ->
              let _, term =
                specification_value context { frame with yielded = Some yielded_so_far } ensured
              in
              oblige context frame Ensures
                (span_of frame.source ensured.origin)
                (Printf.sprintf "`%s` may not hold when the method ends."
                   (quote source ensured.origin))
                term)
            at_end
      | _ ->
          List.iter
            (fun (ensured : Mir.formula) ->
              let _, term = specification_value context frame ensured in
              oblige context frame Ensures
                (span_of frame.source ensured.origin)
                (Printf.sprintf "`%s` may not hold when the function returns."
                   (quote source ensured.origin))
                term)
            own_ensures);
      (* For an amortized bound: the potential of the result and the [mut]
         parameters on return, less that of the [mut] and [own] parameters
         on entry. *)
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
                      local_type context frame local )
              in
              match (parameter.mode, entry, ty) with
              | (Types.Mut | Types.Own), Some entry, Some ty ->
                  let potential_after =
                    match (parameter.mode, later) with
                    | Types.Mut, Some later -> potential context frame ty later
                    | _ -> Costs.zero
                  in
                  Costs.plus total (Costs.minus potential_after (potential context frame ty entry))
              | _ -> total)
            Costs.zero parameters
        in
        (* The caller pays for its changes to a part lent to it [mut], so the
           part's change in potential is not the method's. *)
        let potential_change =
          List.fold_left
            (fun total (ty, handed, back) ->
              Costs.minus total
                (Costs.minus (potential context frame ty back) (potential context frame ty handed)))
            potential_change context.lent_back
        in
        match (returned, output) with
        | Some term, Some output ->
            Costs.plus potential_change (potential context frame output term)
        | _ -> potential_change
      in
      let under_trait = restrict frame trait_requires in
      List.iter
        (fun promise ->
          if promise.inherited then
            match trait_frame frame ~result:returned with
            | Some (_, inside) ->
                keep_promise context under_trait promise
                  ~at:{ inside with locals = inside.old_locals; self = inside.old_self }
                  ~span:returns_span ~change
            | None -> ()
          else
            keep_promise context frame promise
              ~at:{ frame with locals = frame.old_locals; self = frame.old_self; result = returned }
              ~span:(span_of source promise.clause.origin)
              ~change)
        promised;
      match trait_frame frame ~result:returned with
      | Some (part, inside) ->
          List.iter
            (fun (clause : Mir.formula) ->
              let _, term = specification_value context inside clause in
              oblige context under_trait Ensures returns_span
                (Printf.sprintf "The %s's `%s` may not hold when this method returns."
                   (promised_by database part.callee)
                   (quote part.callee clause.origin))
                term)
            part.ensures;
          begin match (inherited, returned) with
          | Some (_, _, Some (Mir.Functional provided)), Some returned ->
              let _, defined = definition_value context inside provided in
              oblige context frame Ensures returns_span
                "This method overrides its trait's default body, so it must return the same value, \
                 and it may not."
                (Logic.equal returned defined)
          | Some (_, _, Some Not_functional), Some _ ->
              oblige context frame Ensures returns_span
                "This method overrides its trait's default body, which is not functional, so there \
                 is no definition to prove it equal to."
                (Logic.Boolean false)
          | _ -> ()
          end
      | _ -> ())
    returns;
  outcome context

(* The laws of a trait an [impl] writes by hand, each shown for fresh
   values of its parameters, after the bodies of the [proof]s written for
   it. *)
let laws database (source : source) ~impl ~trait ~for_type ~proofs ~at =
  let home = home source in
  let context = new_context database ~home ~current:impl ~terminates:false ~measures:[] in
  let start = empty_frame source in
  let substitution = trait_substitution database trait for_type in
  List.iter
    (fun (law_source, (law : Mir.law)) ->
      let types = law_parameter_types ~substitution law in
      if not (List.exists (fun ty -> Types.is_error ty) types) then begin
        (* The other laws are facts here, and this one is not. *)
        context.laws_assumed <- laws_key trait for_type :: context.laws_assumed;
        let terms =
          List.map
            (fun ty ->
              let term = arrive context start "law" ty in
              assume_valid context start ty term;
              term)
            types
        in
        let inside = law_frame start law_source ~substitution law terms in
        List.iter
          (fun clause -> assume context start (snd (specification_value context inside clause)))
          law.requires;
        (* A [proof]'s statements are hints: its calls' postconditions are
           facts where their preconditions hold, which is all a proof
           needs. Its parameters are bound by position to the law's
           arguments, its generic parameters stand for the type's
           arguments, and the law's [requires] are assumed. *)
        let start =
          List.fold_left
            (fun start ((proof_source : source), renaming) ->
              let proof =
                match Option.bind proof_source.key (Query.demand database Mir.mir) with
                | Some proof -> proof
                | None -> bug "the proof `%s` has no MIR" proof_source.name
              in
              let parameters =
                List.map
                  (fun parameter ->
                    match proof.body.locals.(parameter) with
                    | { kind = Source { local; _ }; type_; _ } -> (local, type_)
                    | { kind = Temporary | Lent _; _ } ->
                        bug "a parameter of the proof `%s` is a temporary" proof_source.name)
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
              restrict start
                (Logic.not_
                   (ghost_code context
                      {
                        start with
                        source = proof_source;
                        checking = false;
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
        let _, holds = specification_value context inside law.states in
        oblige context start Law at
          (Printf.sprintf "The law `%s.%s` may not hold for `%s`." (Types.show_trait trait) law.name
             (Types.show for_type))
          holds
      end)
    (laws_of context trait.trait);
  outcome context

(* A type's own clauses. Each invariant is well defined for a value whose
   fields meet their own types' invariants, given the invariants before
   it. The type's [cost potential] is well defined and never below zero
   for a value that meets its invariants, which makes each
   potential a fact about every valid value. *)
let type_ database (source : source) ~path =
  let home = home source in
  let context = new_context database ~home ~current:path ~terminates:false ~measures:[] in
  (match Query.demand database Mir.type_clauses_of_path path with
  | Some { invariants; potential } ->
      let ty =
        match Query.demand database Interface.Environment.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            Types.Named { path; arguments = Types.generic_arguments interface.type_generics }
        | _ -> Types.Named { path; arguments = [] }
      in
      let start = { (empty_frame source) with self_type = Some ty } in
      (* A field's default is well defined, as a constant is, and a value
         it builds meets its type's invariant. *)
      (match Query.demand database Mir.defaults_of_path path with
      | Some (Field_defaults defaults) ->
          List.iter
            (fun (default : Mir.field_default) ->
              ignore
                (code_value context start default.value
                   ~type_:(substituted context start default.type_)))
            defaults
      | Some (Parameter_defaults _) | None -> ());
      let value_ = arrive context start "value" ty in
      assume context start (validity context start ~assuming:true ~own:false ty value_);
      let at_value = { start with self = Some value_; old_self = Some value_ } in
      List.iter
        (fun (invariant : Mir.requirement) ->
          let after, holds = specification_value context at_value invariant.clause in
          assume context after holds)
        invariants;
      Option.iter
        (fun (written : Mir.formula) ->
          let _, own = specification_value context at_value written in
          oblige context at_value Cost
            (span_of at_value.source written.origin)
            (Printf.sprintf
               "The potential of `%s` may be below zero for a value that meets its invariants."
               (Types.show ty))
            (Logic.Operation ("<=", [ Logic.int 0; own ])))
        potential
  | None -> ());
  outcome context

let test database (source : source) ~path =
  let home = home source in
  let context = new_context database ~home ~current:path ~terminates:false ~measures:[] in
  (match Query.demand database Mir.mir home with
  | Some (mir : Mir.t) -> mir_run context (empty_frame source) ~lambdas:mir.lambdas mir.body
  | None -> bug "the test `%s` has no MIR" source.name);
  outcome context

(* A constant's value is well defined, as any expression is: its
   arithmetic stays in range, and its shifts and divisions are valid. *)
let constant database (source : source) ~path =
  let home = home source in
  let context = new_context database ~home ~current:path ~terminates:false ~measures:[] in
  (match Query.demand database Mir.of_constant path with
  | Some code ->
      ignore (code_value context (empty_frame source) code ~type_:(constant_type context path))
  | None -> bug "the constant `%s` has no MIR" (Path.show path));
  outcome context

let theorem database source ~path = function_ ~proof:true database source ~path
