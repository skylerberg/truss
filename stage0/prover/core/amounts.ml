(* Bodies read whole, and what a call costs: a callee's bounds, a value's
   potential, and a method's time. *)

open Core
open State
open Facts
open Contracts
open Validity
open Operations
open Models
open Lambdas
open Intrinsics

(* The value of a functional body, read from its formula in a frame that
   binds its parameters. *)
let definition_value context frame (definition : Mir.formula) =
  context.formula_term frame definition ~arguments:[]

(* A functional body's value over bound names, as a definition states it:
   [bind] binds them in the frame the body reads. Nothing is counted or
   obliged, and a body that the prover cannot read, or whose value needs a
   fresh symbol, gives none. *)
let body_over context frame bound (definition : Mir.formula) bind =
  let mark = context.fresh in
  let saved_counters = context.counters in
  context.counters <- [];
  Fun.protect
    ~finally:(fun () -> context.counters <- saved_counters)
    (fun () ->
      try
        let inside =
          bind
            { frame with bound = List.map fst bound @ frame.bound; checking = false; result = None }
        in
        let _, defined = definition_value context inside definition in
        if mentions_fresh_after context mark defined then None else Some defined
      with Unsupported _ | Foreign_unsupported _ -> None)

(* A frame's locals without the temporaries of the code it is in: a body or
   a formula read from the frame numbers its own from zero too. *)
let without_temporaries locals =
  Locals.filter
    (fun key _ -> match key with Core.Synthetic number -> number >= 0 | _ -> true)
    locals

(* Runs a body of the MIR that stands alone from [frame]: a [proof] block's
   or a law's proof's, a default's, or a constant's, which reads the frame's
   locals as its parameters. Gives the value it returns, of [type_], with
   the frame as it was but for the cost the body spent, or [None] where no
   path returns. *)
let body_run context frame ~(lambdas : Mir.body array) (body : Mir.body) ~type_ =
  let is_foreign = frame.source.key <> Some context.home in
  let saved_returns = context.returns in
  context.returns <- [];
  Fun.protect
    ~finally:(fun () -> context.returns <- saved_returns)
    (fun () ->
      (* The temporaries of the code around are not this body's: its own
         are numbered from zero too. *)
      let inside = { frame with locals = without_temporaries frame.locals } in
      (try context.run_body inside ~lambdas body
       with Unsupported (_, message) when is_foreign ->
         raise (Foreign_unsupported (Printf.sprintf "%s, in `%s`" message frame.source.name)));
      match join context ~value_type:type_ (List.rev context.returns) with
      | Some (returned, Some term) -> Some ({ frame with spent = returned.spent }, term)
      | Some (_, None) | None -> None)

(* The value, of [type_], that code which stands alone returns: a default's
   or a constant's. *)
let code_value context frame (code : Mir.t) ~type_ =
  match body_run context frame ~lambdas:code.lambdas code.body ~type_ with
  | Some returned -> returned
  | None -> raise (Foreign_unsupported "code that returns no value")

(* The default of the parameter at a position of a part's callee, read in a
   frame of the callee's form. *)
let default_value context frame (part : part) position =
  match
    Option.bind part.callee.key (fun (key : Names.key) ->
        Query.demand context.database Mir.defaults_of_path key.path)
  with
  | Some (Parameter_defaults defaults) -> (
      match (List.assoc_opt position defaults, List.nth_opt part.parameters position) with
      | Some default, Some parameter ->
          snd (code_value context frame default ~type_:(substituted context frame parameter.type_))
      | _ -> bug "a parameter's default has no MIR")
  | Some (Field_defaults _) | None -> bug "a callee with no MIR of its defaults"

(* A symbol for a term that holds a pure call, named by the term, and
   equal to it. *)
let named_term context ty term =
  let rec holds_call = function
    | Logic.Apply ((Symbol.Function _ | Symbol.Limited _), _) -> true
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> holds_call body
    | term -> List.exists holds_call (Logic.arguments term)
  in
  if not (holds_call term) then term
  else
    let symbol = Symbol.Argument term in
    let named = Logic.Symbol symbol in
    once context (Value_of symbol) (fun () ->
        declare context (Logic.Constant (symbol, sort_of context ty));
        add_fact context (Logic.equal named term));
    named

(* A sequence of parts with nothing in it. *)
let empty_parts context frame element =
  let parts = fresh context frame "parts" (sort_of context (sequence_type element)) in
  assume context frame (Logic.equal (sequence_length context element parts) (Logic.int 0));
  parts

(* Whether a formula holds a value of a specification that [is_one] picks,
   the bodies of its lambdas included. *)
let holds_specification (formula : Mir.formula) is_one =
  let holds = ref false in
  let visit (statement : Mir.statement) =
    match statement.kind with
    | Assign { value = Specification value; _ } when is_one value -> holds := true
    | _ -> ()
  in
  Mir.iter_formula ~statement:visit formula;
  !holds

(* Whether a clause mentions [result], so that it holds where a lending
   method lends its part, rather than where the lend ends. *)
let mentions_result (clause : Mir.formula) =
  holds_specification clause (function Result -> true | _ -> false)

(* Whether a clause reads [yielded]: in a lending method, its part as the
   caller left it. *)
let mentions_history (clause : Mir.formula) =
  holds_specification clause (function Yielded -> true | _ -> false)

(* A fact that holds of a value because it is of its type, such as the
   range of its field. Of an axiom's parameters, which range over every
   term of their sort, it holds only of the values of their types, so it
   is a hypothesis of the axiom: the logic's datatype has values whose
   fields are out of every range, of which a conclusion that the field is
   in range would be false. *)
let assume_typed context frame term =
  match innermost_axiom context frame term with
  | Some axiom -> axiom.hypotheses <- Logic.( ==> ) frame.condition term :: axiom.hypotheses
  | None -> assume context frame term

(* A fix for a callee's [requires] that is about the definition's
   parameters alone: the clause, with each of the callee's parameters
   written as its argument, as a [requires] of the definition, which then
   holds at every call of it instead. *)
let requires_fix context frame (part : part) (requirement : Mir.requirement) term
    (values : passed list) =
  let clause = requirement.clause in
  let fixed name =
    List.mem name context.entry
    || match name with Symbol.Constant _ | Symbol.Literal _ -> true | _ -> false
  in
  let simple text =
    String.for_all
      (fun character ->
        character = '_' || character = '.'
        || Char.code character >= 128
        || (character >= 'a' && character <= 'z')
        || (character >= 'A' && character <= 'Z')
        || (character >= '0' && character <= '9'))
      text
  in
  let written =
    List.filter_map
      (fun (index, (parameter : Mir.parameter)) ->
        match List.find_opt (fun (passed : passed) -> passed.position = index) values with
        | Some { origin; _ } -> (
            match origin with
            | Some origin ->
                let text = quote frame.source origin in
                Some (parameter.local, if simple text then text else "(" ^ text ^ ")")
            | None -> None)
        | _ -> None)
      (List.mapi (fun index parameter -> (index, parameter)) part.parameters)
  in
  if frame.source.key <> Some context.home || not (List.for_all fixed (Logic.free_symbols term))
  then []
  else
    let clause_span = span_of part.callee clause.origin in
    let clause_text = quote part.callee clause.origin in
    (* Each place where the clause names a parameter, with the argument's text. *)
    let references =
      List.filter_map
        (fun (local, origin) ->
          Option.map (fun text -> (span_of part.callee origin, text)) (List.assoc_opt local written))
        requirement.names
    in
    let buffer = Buffer.create (String.length clause_text) in
    let next =
      List.fold_left
        (fun next ((span : span), text) ->
          let start = span.start - clause_span.start and stop = span.stop - clause_span.start in
          if start < next || stop > String.length clause_text then next
          else begin
            Buffer.add_string buffer (String.sub clause_text next (start - next));
            Buffer.add_string buffer text;
            stop
          end)
        0
        (List.sort_uniq compare references)
    in
    Buffer.add_string buffer (String.sub clause_text next (String.length clause_text - next));
    if written <> [] || part.parameters = [] then
      add_requires context frame (Buffer.contents buffer)
    else []

(* A call that running code could give a value: a function that is
   compiled and not generic, reached directly, with every argument an
   integer or [Bool] literal and a result of one of those. *)
let note_known_call context (invocation : Invocation.t) path term arguments =
  let direct =
    match invocation.callee with
    | Function { type_arguments = []; _ } -> true
    | Trait_method { evidence = Impl { arguments = []; _ }; type_arguments = []; _ } -> true
    | _ -> false
  in
  let literal = function
    | Logic.Integer value -> Some value
    | Logic.Boolean value -> Some (if value then Z.one else Z.zero)
    | _ -> None
  in
  let values = List.filter_map literal arguments in
  match Interface.Impls.signature context.database path with
  | Some
      ({ specification_only = false; generics = []; output = Returns result; _ } : Types.signature)
    when direct
         (* Running a callee reads its body, so only a callee of the
            definition's own package is run. *)
         && Path.package path = Path.package context.current
         && List.length values = List.length arguments
         && (is_numeric result || is_bool result)
         && not (Types.equal result Types.Integer) ->
      if not (List.exists (fun (known : known_call) -> known.term = term) context.known_calls) then
        context.known_calls <-
          { function_ = path; arguments = values; term; result_is_bool = is_bool result }
          :: context.known_calls
  | _ -> ()

let is_datatype ty = match ty with Types.Named _ -> builtin ty = None | _ -> false

(* The parameters of the definition proven whose types are datatypes,
   with their values on entry and their arguments' positions. *)
let structural_parameters context frame (own : part) =
  List.concat
    (List.mapi
       (fun index (parameter : Mir.parameter) ->
         match parameter.local with
         | Self -> (
             match (frame.old_self, frame.self_type) with
             | Some entry, Some ty when is_datatype ty -> [ (ty, entry, index) ]
             | _ -> [])
         | local -> (
             match (Locals.find_opt local frame.old_locals, local_type context frame local) with
             | Some entry, Some ty when is_datatype ty -> [ (ty, entry, index) ]
             | _ -> []))
       own.parameters)

let argument_at_index (values : passed list) index =
  match
    List.find_map
      (fun (passed : passed) -> if passed.position = index then Some passed.term else None)
      values
  with
  | Some term -> term
  | None -> Logic.Boolean false

let rec lexicographically_less before after =
  match (before, after) with
  | [ right ], [ left ] ->
      Logic.(Operation ("<=", [ int 0; right ]) &&& Operation ("<", [ left; right ]))
  | right :: before, left :: after ->
      Logic.(
        Operation ("<=", [ int 0; right ])
        &&& (Operation ("<", [ left; right ])
            ||| (equal left right &&& lexicographically_less before after)))
  | _ -> Logic.Boolean true

(* Whether a cost clause is about a counter's resource. A [calls] clause's
   target is read with the locals of the clause's own form. *)
let same_resource (cost : Mir.cost) ~locals (counter : Costs.counter) =
  match (cost.resource, counter.resource) with
  | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
  | Calls _, Calls counted -> (
      match resource_of cost ~locals with
      | Some (Calls target) -> Costs.covers ~clause:target ~counter:counted
      | _ -> false)
  | _ -> false

(* An amount from zero to [bound], for a counter that counts exactly. *)
let bounded_amount context frame bound =
  let amount = fresh context frame "spent" Logic.Int in
  assume context frame
    Logic.(Operation ("<=", [ int 0; amount ]) &&& Operation ("<=", [ amount; bound ]));
  amount

let promised_amount context frame (counter : Costs.counter) (bound : Mir.bound) ~evaluate
    ~is_recursive_call ~exact_target ~change =
  match (bound, counter.counting) with
  | Order_of amount, Units ->
      let amount = evaluate amount in
      let amount =
        if is_recursive_call then
          let hypothesis = Costs.at_least_zero (Costs.bound amount) in
          if counter.resource = Time then Costs.plus hypothesis (Logic.int 1) else hypothesis
        else Costs.units amount
      in
      Costs.minus amount change
  | (At_most amount | Exactly amount), Units ->
      Costs.at_least_zero (Costs.minus (evaluate amount) change)
  | At_most amount, (At_most | Exactly) ->
      bounded_amount context frame (Costs.minus (evaluate amount) change)
  | Exactly amount, (At_most | Exactly) ->
      let amount = Costs.minus (evaluate amount) change in
      if exact_target then amount else bounded_amount context frame amount
  | (Order_of _ | Finite), _ -> unknown_amount context frame counter

(* How much a potential grew, or zero where it fell or cannot be read. *)
let growth change =
  try Costs.at_least_zero (change ()) with Unsupported _ | Foreign_unsupported _ -> Costs.zero

(* Whether a function value is a [calls] clause's target: the target
   itself, or a value of its sort that may equal it, as one chosen by [if]
   or read from a field may. *)
let may_be_target context frame term ty target =
  if term = target then Logic.Boolean true
  else
    match List.assoc_opt target context.call_targets with
    | Some local -> (
        match (ty, local_type context frame local) with
        | Types.Function _, Some target_type when sort_of context ty = sort_of context target_type
          ->
            Logic.equal term target
        | _ -> Logic.Boolean false)
    | None -> Logic.Boolean false

let lambda_captures_target context lambda target =
  match
    (List.assoc_opt lambda context.lambda_captures, List.assoc_opt target context.call_targets)
  with
  | Some captured, Some local -> List.mem local captured
  | _ -> false

(* Whether a call can reach a [calls] clause's target: a function value
   passed to it, or captured by a lambda passed to it, or a capability it
   uses. *)
let call_reaches context frame uses (values : passed list) (target : Costs.target) =
  match target with
  | Through term ->
      Logic.disjunction
        (List.map
           (fun (passed : passed) ->
             if lambda_captures_target context passed.term term then Logic.Boolean true
             else may_be_target context frame passed.term passed.type_ term)
           values)
  | Capability path | Capability_method (path, _) ->
      Logic.Boolean
        (List.exists
           (function
             | Types.Capability used -> Path.equal used path
             | Types.Capability_parameter _ | Types.Capability_projection _
             | Types.Capability_variable _ ->
                 true)
           uses)

(* An amount spent only where [condition] holds. *)
let spent_where condition amount =
  match condition with
  | Logic.Boolean true -> amount
  | Logic.Boolean false -> Costs.zero
  | condition -> Logic.ite condition amount Costs.zero

(* The cost on a counter of a call to a callee whose clauses are read: its
   clause about the counter's resource, from its first part that has one.
   A call back into the definition proven, through a cycle, assumes its
   [O(...)] bound. *)
let callee_amount ?ends_in context after ~path ~(parts : part list) ~(bound_frame : part -> frame)
    ~uses ~(values : passed list) ~change (counter : Costs.counter) =
  let is_recursive_call =
    counter.counting = Units
    && List.mem counter context.own_bounds
    && Call_graph.reaches context.database ~package:(Path.package context.current) ~from:path
         ~target:context.current
  in
  let clauses_of (part : part) =
    let frame = bound_frame part in
    List.filter_map
      (fun (cost : Mir.cost) ->
        if same_resource cost ~locals:frame.locals counter then Some (part, frame, cost) else None)
      part.costs
  in
  let amount (_, (frame : frame), (cost : Mir.cost)) =
    let exact_target =
      match (cost.resource, counter.resource) with
      | Calls (Capability _), Calls (Capability_method _) -> false
      | _ -> true
    in
    match (cost.amortized, change) with
    | true, None -> unknown_amount context after counter
    | _ ->
        promised_amount context after counter cost.bound
          ~evaluate:(fun amount -> snd (specification_value context frame amount))
          ~is_recursive_call ~exact_target
          ~change:
            (match (cost.amortized, change) with true, Some change -> change () | _ -> Costs.zero)
  in
  let first_clauses () =
    let amortized_first = Option.is_some change && counter.amortized in
    List.find_map
      (fun part ->
        match clauses_of part with
        | [] -> None
        | clauses ->
            let amortized, plain =
              List.partition (fun (_, _, (cost : Mir.cost)) -> cost.amortized) clauses
            in
            Some (if amortized_first then amortized @ plain else plain @ amortized))
      parts
  in
  match counter.resource with
  | Calls target when call_reaches context after uses values target = Logic.Boolean false ->
      Costs.zero
  | Calls (Through term) -> (
      let reaches = call_reaches context after uses values (Through term) in
      (* Each parameter the function value is passed for must have a
         clause about it. *)
      let receiving =
        List.filter_map
          (fun (passed : passed) -> if passed.term = term then Some passed.position else None)
          values
      in
      let captured =
        List.exists
          (fun (passed : passed) -> lambda_captures_target context passed.term term)
          values
      in
      match first_clauses () with
      | Some clauses
        when (not captured) && List.length clauses >= List.length receiving && receiving <> [] ->
          List.fold_left (fun total clause -> Costs.plus total (amount clause)) Costs.zero clauses
      | _ -> spent_where reaches (unknown_amount context after counter))
  | _ -> (
      (* [time(Types.method)] is the most one call takes plus the potential it
         makes, so a call that makes potential has paid for it. *)
      let within_time time =
        Costs.minus
          (Costs.plus time (Logic.int 1))
          (match change with Some change -> growth change | None -> Costs.zero)
      in
      match (first_clauses (), counter.resource, counter.counting, ends_in) with
      | Some ((_, _, { bound = Finite; _ }) :: _), Time, Units, Some time -> within_time time
      | Some (clause :: _), _, _, _ -> amount clause
      | _, Time, Units, Some time -> within_time time
      | _ -> unknown_amount context after counter)

(* The cost of a call whose contract is not read. *)
let step_amount context frame (invocation : Invocation.t) (values : passed list)
    (counter : Costs.counter) =
  match invocation.callee with
  | Intrinsic { operation; type_arguments } -> (
      let cost = Intrinsic_signatures.cost operation in
      match counter.resource with
      | Time -> (
          match (cost.time, counter.counting) with
          | Constant_time, _ -> Costs.zero
          | Linear_in position, Units -> (
              match List.find_opt (fun (passed : passed) -> passed.position = position) values with
              | Some passed -> (
                  match passed.type_ with
                  | Types.Named { path; arguments = [ Types.Type element ] } -> (
                      match Intrinsic.builtin_of_path path with
                      | Some ((Storage | View) as builtin) ->
                          sequence_length context element
                            (buffer_model context builtin element passed.term)
                      | _ -> unknown_amount context frame counter)
                  | _ -> unknown_amount context frame counter)
              | None -> unknown_amount context frame counter)
          | (Linear_in _ | Unbounded_time), _ -> unknown_amount context frame counter)
      | Allocations | Allocated_bytes -> (
          match (cost.allocations, counter.resource, counter.counting) with
          | No_allocations, _, _ -> Costs.zero
          | One_if_positive amount, resource, counting -> (
              let amount_term =
                match amount with
                | Argument position ->
                    Option.map
                      (fun (passed : passed) -> passed.term)
                      (List.find_opt (fun (passed : passed) -> passed.position = position) values)
                | Generic name -> generic_argument context frame operation type_arguments name
              in
              match amount_term with
              | Some amount_term when resource = Allocations || counting = Units ->
                  Logic.ite
                    (Logic.Operation (">", [ amount_term; Logic.int 0 ]))
                    (Logic.int 1) (Logic.int 0)
              | _ -> unknown_amount context frame counter)
          | Unknown_allocations, _, _ -> unknown_amount context frame counter)
      | Calls _ -> Costs.zero)
  | Capability_method { capability; name } -> (
      let direct =
        match counter.resource with
        | Calls (Capability path) when Path.equal path capability -> Logic.int 1
        | Calls (Capability_method (path, method_))
          when Path.equal path capability && method_ = name ->
            Logic.int 1
        | _ -> Costs.zero
      in
      match counter.resource with
      | Calls _ -> direct
      | _ -> (
          match capability_part context.database capability name with
          | Some part ->
              let inside =
                part_frame frame part
                  ~arguments:
                    (List.map (fun (passed : passed) -> (passed.position, passed.term)) values)
                  ~substitution:[]
              in
              callee_amount context frame
                ~path:(Path.Method { owner = capability; name; receiver = Static })
                ~parts:[ part ]
                ~bound_frame:(fun _ -> inside)
                ~uses:(invocation.uses :> Types.capability list)
                ~values ~change:None counter
          | None -> unknown_amount context frame counter))
  | Function _ | Trait_method _ | Indirect () -> (
      match counter.resource with
      | Calls target ->
          spent_where
            (call_reaches context frame (invocation.uses :> Types.capability list) values target)
            (unknown_amount context frame counter)
      | _ -> unknown_amount context frame counter)

let held_symbol context ty term =
  let symbol = Symbol.Potential (type_key ty) in
  declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let find_buffer_elements context (ty : Types.ty) =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element; Types.Value _ ] }
    when Intrinsic.builtin_of_path path = Some Array ->
      Option.map
        (fun model_of -> (element, model_of))
        (model_function context ty ~model:(sequence_type element))
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Intrinsic.builtin_of_path path = Some Storage ->
      Some (element, fun term -> buffer_model context Storage element term)
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Intrinsic.builtin_of_path path = Some View ->
      Some (element, fun term -> buffer_model context View element term)
  | Types.Named { path; arguments } when builtin ty = None -> (
      match Query.demand context.database Interface.Environment.interface path with
      | Some (Interface.Environment.Type_interface { shape = Record [ field ]; type_generics; _ })
        -> (
          let substitution =
            try
              List.combine
                (List.map (fun (generic : Types.generic) -> generic.generic) type_generics)
                arguments
            with Invalid_argument _ -> []
          in
          match Types.substitute substitution field.field_type with
          | Types.Named { path = field_path; arguments = [ Types.Type element ] }
            when Intrinsic.builtin_of_path field_path = Some Storage
                 || Intrinsic.builtin_of_path field_path = Some View ->
              Option.map
                (fun model_of -> (element, model_of))
                (model_function context ty ~model:(sequence_type element))
          | _ -> None)
      | _ -> None)
  | _ -> None

(* A growable buffer's elements and model: a storage, by its own model, or
   a type whose [Model] is the sequence of the storage it holds in its one
   field, as a [List] and a [String] are. *)
let buffer_elements context (ty : Types.ty) =
  let key = type_key ty in
  match Hashtbl.find_opt context.buffers key with
  | Some elements -> elements
  | None ->
      let elements = find_buffer_elements context ty in
      Hashtbl.replace context.buffers key elements;
      elements

(* A buffer's slack for growing, as a function of it. *)
let buffer_slack context (ty : Types.ty) term =
  let symbol = Symbol.Slack (type_key ty) in
  declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

(* A value's potential as a measure, for a sum over a collection of such
   values: applied, it is the potential. *)
let potential_measure context element =
  let symbol = Symbol.Potential_measure (type_key element) in
  let measure = measure_type element in
  declare context (Logic.Constant (symbol, sort_of context (Types.Function measure)));
  let term = Logic.Symbol symbol in
  if not (List.mem term context.potentials) then begin
    context.potentials <- term :: context.potentials;
    let each = Symbol.Variable { label = "potential.element"; numbers = [] } in
    add_fact context
      (Logic.forall
         ( [ (each, sort_of context element) ],
           Logic.equal
             (applied context measure term [ Logic.Symbol each ])
             (held_symbol context element (Logic.Symbol each)) ))
  end;
  term

(* Potentials. *)

(* A type's own [cost potential], from its form. *)
let rec potential_clause context (ty : Types.ty) =
  match type_clauses context ty with
  | Some (source, { potential = Some potential; _ }) -> Some (source, potential)
  | _ -> None

and has_potential context ?(seen = []) (ty : Types.ty) =
  if seen <> [] then holds_potential_type context ~seen ty
  else
    let key = type_key ty in
    match Hashtbl.find_opt context.holds_potential key with
    | Some holds -> holds
    | None ->
        let holds = holds_potential_type context ~seen ty in
        Hashtbl.replace context.holds_potential key holds;
        holds

and holds_potential_type context ~seen (ty : Types.ty) =
  if List.exists (Types.equal ty) seen then false
  else
    match ty with
    | Parameter _ -> true
    | Named _ when Option.is_some (buffer_elements context ty) -> true
    | Types.Named { path; arguments } when builtin ty = None -> (
        potential_clause context ty <> None
        ||
        match Query.demand context.database Interface.Environment.interface path with
        | Some (Interface.Environment.Type_interface interface) ->
            let substitution =
              try
                List.combine
                  (List.map
                     (fun (generic : Types.generic) -> generic.generic)
                     interface.type_generics)
                  arguments
              with Invalid_argument _ -> []
            in
            let fields =
              match interface.shape with
              | Record fields -> fields
              | Sum variants ->
                  List.concat_map
                    (fun (variant : Types.variant) -> Option.value variant.fields ~default:[])
                    variants
              | Todo_type | Builtin_type _ | Error_shape _ -> []
            in
            List.exists
              (fun (field : Types.field) ->
                has_potential context ~seen:(ty :: seen)
                  (Types.substitute substitution field.field_type))
              fields
        | _ -> false)
    | Types.Named { arguments; _ } ->
        if
          List.exists
            (function
              | Types.Type element -> has_potential context ~seen:(ty :: seen) element | _ -> false)
            arguments
        then raise (Foreign_unsupported "the potential of a collection's elements")
        else false
    | _ -> false

(* The potential a value holds: a function of it in the logic, at least
   zero for a valid value, as each type with a potential shows, and its
   type's own potential plus its parts', unfolded once for each value it is
   asked of. *)
and potential context frame ?(seen = []) (ty : Types.ty) term =
  if not (has_potential context ty) then Costs.zero
  else begin
    let held = held_symbol context ty term in
    if (not (List.mem held context.potentials)) && not (Logic.mentions frame.bound term) then begin
      context.potentials <- held :: context.potentials;
      fact context frame
        Logic.(validity context frame ~assuming:true ty term ==> Operation ("<=", [ int 0; held ]));
      match (potential_clause context ty, constructors context ty) with
      (* A type with visible fields holds its fields' potential; one with
         opaque fields, such as a [List] outside its package, is read as the
         buffer its model says it is. *)
      | None, None when Option.is_some (buffer_elements context ty) -> (
          (* A buffer's potential is its slack for growing, as a
             doubling array saves it: twice its length less its capacity,
             and never below zero, so at most two units for each element;
             and its elements' potentials. A view cannot grow, so it saves
             nothing of its own. *)
          match buffer_elements context ty with
          | Some (element, model) ->
              let sequence = model term in
              let slack = buffer_slack context ty term in
              let length = sequence_length context element sequence in
              fact context frame
                Logic.(
                  Operation ("<=", [ int 0; slack ])
                  &&& Operation ("<=", [ slack; Operation ("*", [ int 2; length ]) ]));
              (match ty with
              | Types.Named { path; _ } when Intrinsic.builtin_of_path path = Some Storage ->
                  let saved =
                    Logic.Operation
                      ( "-",
                        [
                          Logic.Operation ("*", [ Logic.int 2; length ]);
                          buffer_capacity context element term;
                        ] )
                  in
                  fact context frame
                    (Logic.equal slack
                       (Logic.ite
                          (Logic.Operation (">=", [ saved; Logic.int 0 ]))
                          saved (Logic.int 0)))
              | Types.Named { path; _ }
                when Intrinsic.builtin_of_path path = Some View
                     || Intrinsic.builtin_of_path path = Some Array ->
                  fact context frame (Logic.equal slack (Logic.int 0))
              | _ -> ());
              let elements =
                if has_potential context element then
                  sequence_sum context element sequence (potential_measure context element)
                else Costs.zero
              in
              fact context frame (Logic.equal held (Costs.plus slack elements))
          | None -> ())
      | clause, Some shape -> (
          try
            (* Without a clause, a type holds nothing of its own. *)
            let own =
              match clause with
              | Some (source, written) ->
                  snd
                    (specification_value context
                       (type_frame context frame source ty ~self:(Some term))
                       written)
              | None -> Costs.zero
            in
            let parts = parts_potential context frame ~seen ty term in
            let parts =
              match shape with
              | [ (None, fields) ] -> parts (None, fields)
              | variants -> (
                  match List.rev variants with
                  | last :: earlier ->
                      List.fold_left
                        (fun otherwise ((variant, _) as one) ->
                          Logic.ite
                            (Logic.Is (constructor_name ty variant, term))
                            (parts one) otherwise)
                        (parts last) earlier
                  | [] -> Costs.zero)
            in
            fact context frame (Logic.equal held (Costs.plus own parts))
          with Unsupported _ | Foreign_unsupported _ -> ())
      | _ -> ()
    end;
    (* A record that holds no potential of its own holds its parts' potential,
       which is the same term as theirs wherever they change. *)
    match (potential_clause context ty, constructors context ty) with
    | None, Some [ (None, fields) ] when Option.is_none (buffer_elements context ty) -> (
        try parts_potential context frame ~seen ty term (None, fields)
        with Unsupported _ | Foreign_unsupported _ -> held)
    | _ -> held
  end

(* The potential a value's parts hold, for one variant's fields: each
   unfolded in turn, except a part of a type already being unfolded, which
   would unfold forever. *)
and parts_potential context frame ~seen ty term (variant, fields) =
  List.fold_left
    (fun total (field, field_type) ->
      if has_potential context field_type then
        let part = selected context ty variant field term in
        Costs.plus total
          (if List.exists (Types.equal field_type) (ty :: seen) then
             held_symbol context field_type part
           else potential context frame ~seen:(ty :: seen) field_type part)
      else total)
    Costs.zero fields

(* A bound on [time(Types.method)] for a known type: a copy of a [Plain] value
   that holds no potential takes one step, and the method of an [impl] whose
   time clause is a constant [O(k)] takes at most [k] counted as a call is,
   where it makes no potential, since nothing it mutates or returns can
   hold any. *)
let method_time_bound context (method_ : Path.t) self_type =
  let holds ty = try has_potential context ty with Foreign_unsupported _ -> true in
  match method_ with
  | Method { owner = trait; name; receiver } -> (
      if Path.equal trait Interface.Impls.copyable_path then
        if
          Interface.Impls.plain context.database ~bounds:(current_bounds context) self_type
          && not (holds self_type)
        then Some Z.one
        else None
      else
        let reference : Types.trait_reference = { trait; trait_arguments = []; associated = [] } in
        match concrete_impl context reference self_type with
        | Some (impl, arguments) -> (
            let path = Path.Method { owner = impl; name; receiver } in
            let makes_no_potential =
              match Interface.Impls.signature context.database path with
              | Some (signature : Types.signature) -> (
                  List.for_all
                    (fun (parameter : Types.parameter_info) ->
                      parameter.mode <> Types.Mut || not (holds parameter.type_))
                    signature.parameters
                  && (match signature.receiver with Some (Mut, ty) -> not (holds ty) | _ -> true)
                  && match signature.output with Returns ty -> not (holds ty) | _ -> false)
              | None -> false
            in
            match
              method_contract ?reading_package:(reading_package context) context.database reference
                name receiver
                (Impl { impl; arguments })
            with
            | Some contract when makes_no_potential ->
                List.find_map
                  (fun (part : part) ->
                    List.find_map
                      (fun (cost : Mir.cost) ->
                        match cost with
                        | { resource = Time; amortized = false; bound = Order_of amount; _ } ->
                            literal amount
                        | _ -> None)
                      part.costs)
                  contract.parts
            | _ -> None)
        | None -> None)
  | _ -> None

let trait_method_time context frame (method_ : Path.t) self_type =
  let symbol = Symbol.Method_time { method_; self_type = type_key self_type } in
  declare context (Logic.Constant (symbol, Logic.Int));
  fact context frame (Logic.Operation ("<=", [ Logic.int 1; Logic.Symbol symbol ]));
  (match method_time_bound context method_ self_type with
  | Some limit ->
      fact context frame
        (Logic.Operation ("<=", [ Logic.Symbol symbol; Logic.Integer (Z.max limit Z.one) ]))
  | None -> ());
  Logic.Symbol symbol

(* [time(Types.method)]: the longest any one call of a trait's method on a type
   takes in this run, a constant of the run, at least one step. It is one
   symbol for each method and type, so a callee's bound and its caller's
   are about the same term. *)
let method_time context frame (callee : Invocation.callee) =
  match callee with
  | Trait_method { trait; name; receiver; self_type; _ } ->
      trait_method_time context frame
        (Path.Method { owner = trait.trait; name; receiver })
        (substituted context frame self_type)
  | _ -> raise (Foreign_unsupported "the time of a function that is not a trait's method")
