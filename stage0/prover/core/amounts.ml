open Core
open State
open Facts
open Contracts
open Validity
open Operations
open Models
open Lambdas
open Intrinsics

let definition_value context frame (definition : Mir.t) =
  match
    body_run context frame ~lambdas:definition.lambdas definition.body
      ~type_:(returned_type context frame definition.body)
  with
  | Some read -> read
  | None -> raise (Foreign_unsupported "a definition that never returns")

let body_over context frame bound (definition : Mir.t) bind =
  let mark = context.fresh in
  let saved_counters = context.counters in
  context.counters <- [];
  Fun.protect
    ~finally:(fun () -> context.counters <- saved_counters)
    (fun () ->
      try
        let inside =
          bind
            {
              frame with
              bound = List.map fst bound @ frame.bound;
              makes_obligations = false;
              result = None;
            }
        in
        let _, defined = definition_value context inside definition in
        if mentions_fresh_after context mark defined then None else Some defined
      with Unsupported _ | Foreign_unsupported _ -> None)

let code_value context frame (code : Mir.t) ~type_ =
  match body_run context frame ~lambdas:code.lambdas code.body ~type_ with
  | Some returned -> returned
  | None -> raise (Foreign_unsupported "code that returns no value")

let empty_parts context frame element =
  let parts = fresh context frame "parts" (sort_of context (sequence_type element)) in
  assume context frame (Logic.equal (sequence_length context element parts) (Logic.int 0));
  parts

let holds_specification (formula : Mir.formula) is_one =
  let holds = ref false in
  let visit (statement : Mir.statement) =
    match statement.kind with
    | Assign { value = Specification value; _ } when is_one value -> holds := true
    | _ -> ()
  in
  Mir.iter_formula visit formula;
  !holds

let mentions_result (clause : Mir.formula) =
  holds_specification clause (function Result -> true | _ -> false)

let mentions_history (clause : Mir.formula) =
  holds_specification clause (function Yielded -> true | _ -> false)

let assume_typed context frame term =
  match innermost_axiom context frame term with
  | Some axiom -> axiom.hypotheses <- Logic.( ==> ) frame.condition term :: axiom.hypotheses
  | None -> assume context frame term

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

let covers ~(clause : Costs.target) ~(counter : Costs.target) =
  match (clause, counter) with
  | Capability path, Capability_method (owner, _) -> Path.equal path owner
  | Through left, Through right -> left = right
  | Capability left, Capability right -> Path.equal left right
  | Capability_method (left, left_method), Capability_method (right, right_method) ->
      Path.equal left right && left_method = right_method
  | _ -> false

let same_resource (cost : Mir.cost) ~locals (counter : Costs.counter) =
  match (cost.resource, counter.resource) with
  | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
  | Calls _, Calls counted -> (
      match resource_of cost ~locals with
      | Some (Calls target) -> covers ~clause:target ~counter:counted
      | _ -> false)
  | _ -> false

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

let growth change =
  try Costs.at_least_zero (change ()) with Unsupported _ | Foreign_unsupported _ -> Costs.zero

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

let spent_where condition amount =
  match condition with
  | Logic.Boolean true -> amount
  | Logic.Boolean false -> Costs.zero
  | condition -> Logic.ite condition amount Costs.zero

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

let generic_argument context frame (operation : Intrinsic.operation) type_arguments name =
  let generics = (Intrinsic_signatures.signature operation).generics in
  List.find_map
    (fun ((generic : Types.generic), argument) ->
      match argument with
      | Types.Value value when generic.generic.name = name -> Some (value_term context frame value)
      | _ -> None)
    (try List.combine generics type_arguments with Invalid_argument _ -> [])

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

let buffer_elements context (ty : Types.ty) =
  let key = type_key ty in
  match Hashtbl.find_opt context.buffers key with
  | Some elements -> elements
  | None ->
      let elements = find_buffer_elements context ty in
      Hashtbl.replace context.buffers key elements;
      elements

let buffer_slack context (ty : Types.ty) term =
  let symbol = Symbol.Slack (type_key ty) in
  declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

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

and potential context frame ?(seen = []) (ty : Types.ty) term =
  if not (has_potential context ty) then Costs.zero
  else begin
    let held = held_symbol context ty term in
    if (not (List.mem held context.potentials)) && not (Logic.mentions frame.bound term) then begin
      context.potentials <- held :: context.potentials;
      fact context frame
        Logic.(validity context frame ~assuming:true ty term ==> Operation ("<=", [ int 0; held ]));
      match (potential_clause context ty, constructors context ty) with
      | None, None when Option.is_some (buffer_elements context ty) -> (
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
    match (potential_clause context ty, constructors context ty) with
    | None, Some [ (None, fields) ] when Option.is_none (buffer_elements context ty) -> (
        try parts_potential context frame ~seen ty term (None, fields)
        with Unsupported _ | Foreign_unsupported _ -> held)
    | _ -> held
  end

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

let method_time context frame (callee : Invocation.callee) =
  match callee with
  | Trait_method { trait; name; receiver; self_type; _ } ->
      trait_method_time context frame
        (Path.Method { owner = trait.trait; name; receiver })
        (substituted context frame self_type)
  | _ -> raise (Foreign_unsupported "the time of a function that is not a trait's method")
