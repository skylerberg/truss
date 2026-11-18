let apply_function context (function_type : Types.function_type) callee arguments =
  let inputs = List.map (fun (_, input) -> Facts.declare_sort context input) function_type.inputs in
  let output = Facts.declare_sort context function_type.output in
  let value_sort = Facts.declare_sort context (Types.Function function_type) in
  let symbol = Logic.Symbol.Apply ((value_sort :: inputs) @ [ output ]) in
  Facts.declare context (Logic.Function (symbol, value_sort :: inputs, output));
  Logic.Apply (symbol, callee :: arguments)

let add_lambda_facts (context : State.context) (frame : State.frame) ~capture_free
    (function_type : Types.function_type) term ~called ~arguments ~start_fresh ~end_fresh
    ~start_declarations ~premises ~shown ~ended =
  let declared_here =
    List.take (List.length context.declarations - start_declarations) context.declarations
  in
  let captures_fresh = function
    | Logic.Symbol.Lambda _ as name when not (Tables.Symbol_table.mem context.fresh_order name) -> (
        match Tables.Symbol_table.find_opt context.lambda_definitions name with
        | Some defined -> Facts.mentions_fresh_after context start_fresh defined
        | None -> false)
    | _ -> false
  in
  begin
    let parameters =
      List.mapi
        (fun index (_, input) ->
          ( Facts.make_variable "lambda.argument" ~numbers:[ index ],
            Facts.declare_sort context input ))
        function_type.inputs
    in
    let variables = List.map (fun (name, _) -> Logic.Symbol name) parameters in
    let renamed = Tables.Symbol_table.create 16 in
    (match called with
    | Logic.Symbol name -> Tables.Symbol_table.replace renamed name (Logic.Boolean true)
    | _ -> ());
    List.iter2
      (fun argument variable ->
        match argument with
        | Logic.Symbol name -> Tables.Symbol_table.replace renamed name variable
        | _ -> ())
      arguments variables;
    let functions = Tables.Symbol_table.create 8 in
    List.iter
      (function
        | Logic.Constant (name, sort) when not (Tables.Symbol_table.mem renamed name) ->
            let is_fresh_in_body =
              match Tables.Symbol_table.find_opt context.fresh_order name with
              | Some order -> order > start_fresh && order <= end_fresh
              | None -> captures_fresh name
            in
            if is_fresh_in_body then begin
              let lifted = Logic.Symbol.Lifted name in
              Facts.declare context (Logic.Function (lifted, List.map snd parameters, sort));
              Tables.Symbol_table.replace renamed name (Logic.Apply (lifted, variables))
            end
        | Logic.Function (name, inputs, sort) when frame.binders <> [] -> (
            match Tables.Symbol_table.find_opt context.fresh_order name with
            | Some order when order > start_fresh && order <= end_fresh ->
                let lifted = Logic.Symbol.Lifted name in
                Facts.declare context
                  (Logic.Function (lifted, inputs @ List.map snd parameters, sort));
                Tables.Symbol_table.replace functions name lifted
            | _ -> ())
        | _ -> ())
      declared_here;
    let rec lift = function
      | Logic.Symbol name as symbol ->
          Option.value (Tables.Symbol_table.find_opt renamed name) ~default:symbol
      | (Logic.Integer _ | Logic.Boolean _ | Logic.Bits _) as term -> term
      | Logic.Apply (name, _)
        when match called with Logic.Apply (called_name, _) -> called_name = name | _ -> false ->
          Logic.Boolean true
      | Logic.Apply (name, arguments) when Tables.Symbol_table.mem functions name ->
          Logic.Apply (Tables.Symbol_table.find functions name, List.map lift arguments @ variables)
      | (Logic.Apply _ | Logic.Operation _ | Logic.Is _) as term -> Logic.map_arguments lift term
      | Logic.Forall (bound, trigger, body) -> Logic.Forall (bound, List.map lift trigger, lift body)
      | Logic.Exists (bound, body) -> Logic.Exists (bound, lift body)
    in
    let premise = lift (Logic.conjunction premises) in
    let applied_here = apply_function context function_type term variables in
    let statements =
      List.map lift shown
      @ List.filter_map
          (fun ((exit_ : State.frame), value) ->
            Option.map
              (fun value ->
                Logic.( ==> ) (lift exit_.condition) (Logic.equal applied_here (lift value)))
              value)
          ended
    in
    List.iter
      (fun statement ->
        let stated = Logic.forall (parameters, Logic.( ==> ) premise statement) in
        if frame.bound = [] || capture_free then Facts.add_fact context stated
        else
          match Facts.close_over_binders frame stated with
          | Some closed -> Facts.add_fact context closed
          | None -> ())
      statements
  end

let is_in_the_logic (function_type : Types.function_type) =
  function_type.uses = Types.no_capabilities
  && List.for_all (fun (mode, _) -> mode <> Types.Mut) function_type.inputs

let make_parameter_symbols context (frame : State.frame) (function_type : Types.function_type) =
  let depth = List.length frame.bound in
  List.mapi
    (fun index (_, input) ->
      ( Logic.Symbol.Variable { label = "parameter"; numbers = [ depth; index ] },
        Facts.declare_sort context (Facts.substitute_type context frame input) ))
    function_type.inputs

let remove_temporaries locals =
  Locals.filter
    (fun key _ -> match key with Locals.Mir_local _ -> false | Core_local _ -> true)
    locals

let run_lambda_body ?(enter = Fun.id) (context : State.context) (frame : State.frame)
    ~(lambdas : Mir.body array) (body : Mir.body) ~type_ =
  let saved_returns = context.returns in
  context.returns <- [];
  Fun.protect
    ~finally:(fun () -> context.returns <- saved_returns)
    (fun () ->
      let inside =
        enter { frame with locals = remove_temporaries frame.locals; panic = Undeclarable }
      in
      Facts.run_in_source context frame.source (fun () -> context.run_body inside ~lambdas body);
      match Facts.join context ~value_type:type_ (List.rev context.returns) with
      | Some (returned, Some term) -> Some ({ frame with spent = returned.spent }, term)
      | Some (_, None) | None -> None)

let compute_returned_type context frame (body : Mir.body) =
  let rec find_returned_type (block : Mir.block) =
    List.find_map
      (fun (statement : Mir.statement) ->
        match statement.kind with
        | Jump (Return (Some value)) ->
            Some (Facts.substitute_type context frame (Mir.extract_operand_type value))
        | _ -> List.find_map find_returned_type (Mir.list_nested_blocks statement))
      block.statements
  in
  Option.value ~default:Types.unit (find_returned_type body.code)

let list_captured_locals (written : State.lambda_code) =
  List.filter_map
    (fun capture ->
      match written.code.locals.(capture).kind with
      | Source { local; _ } -> Some local
      | Temporary | Lent _ -> None)
    written.code.captures

let canonicalize_binders term =
  let count = ref 0 in
  let rec walk renamed = function
    | Logic.Symbol name -> (
        match List.assoc_opt name renamed with
        | Some other -> Logic.Symbol other
        | None -> Logic.Symbol name)
    | ( Logic.Integer _ | Logic.Boolean _ | Logic.Bits _ | Logic.Apply _ | Logic.Operation _
      | Logic.Is _ ) as term ->
        Logic.map_arguments (walk renamed) term
    | Logic.Forall (bound, trigger, body) ->
        let bound, renamed = rename renamed bound in
        Logic.Forall (bound, List.map (walk renamed) trigger, walk renamed body)
    | Logic.Exists (bound, body) ->
        let bound, renamed = rename renamed bound in
        Logic.Exists (bound, walk renamed body)
  and rename renamed bound =
    List.fold_right
      (fun (name, sort) (bound, renamed) ->
        incr count;
        let other = Logic.Symbol.Variable { label = "binder"; numbers = [ !count ] } in
        ((other, sort) :: bound, (name, other) :: renamed))
      bound ([], renamed)
  in
  walk [] term

let find_lambda_definition context frame (function_type : Types.function_type)
    (written : State.lambda_code) =
  match written.code.is_functional with
  | true when is_in_the_logic function_type -> (
      let bound = make_parameter_symbols context frame function_type in
      let defined =
        let mark = context.fresh in
        let saved_counters = context.counters in
        context.counters <- [];
        Fun.protect
          ~finally:(fun () -> context.counters <- saved_counters)
          (fun () ->
            try
              let enter inside =
                List.fold_left2
                  (fun inside parameter (name, _) ->
                    let info = written.code.locals.(parameter) in
                    Facts.bind inside
                      (Locals.make_key written.code.locals parameter)
                      (Facts.substitute_type context inside info.type_)
                      (Logic.Symbol name))
                  inside written.code.parameters bound
              in
              match
                run_lambda_body ~enter context
                  {
                    frame with
                    bound = List.map fst bound @ frame.bound;
                    makes_obligations = false;
                    result = None;
                  }
                  ~lambdas:written.lambdas written.code
                  ~type_:(compute_returned_type context frame written.code)
              with
              | Some (_, defined) when not (Facts.mentions_fresh_after context mark defined) ->
                  Some defined
              | Some _ | None -> None
            with Facts.Unsupported _ -> None)
      in
      let quantified = List.map (fun (name, _, _) -> name) frame.binders in
      let enclosing_parameters =
        List.filter (fun name -> not (List.mem name quantified)) frame.bound
      in
      match defined with
      | Some defined when Logic.mentions enclosing_parameters defined -> None
      | Some defined ->
          let defined = canonicalize_binders defined in
          let named_by_position =
            List.fold_left
              (fun term (index, (name, _)) ->
                Logic.replace ~from:(Logic.Symbol name)
                  ~into:(Logic.Symbol (Facts.make_variable "parameter" ~numbers:[ index ]))
                  term)
              defined
              (List.mapi (fun index parameter -> (index, parameter)) bound)
          in
          let symbol =
            Logic.Symbol.Lambda { sorts = List.map snd bound; definition = named_by_position }
          in
          let sort = Facts.declare_sort context (Types.Function function_type) in
          let term =
            if Logic.mentions frame.bound defined then
              Facts.declare_value_symbol context frame symbol sort
            else Facts.declare_value_symbol context { frame with binders = [] } symbol sort
          in
          let application =
            apply_function context function_type term
              (List.map (fun (name, _) -> Logic.Symbol name) bound)
          in
          Tables.Symbol_table.replace context.lambda_definitions symbol defined;
          Facts.add_frame_fact context frame (Logic.forall (bound, Logic.equal application defined));
          (match written.code.value_type with
          | Some value_type -> (
              match
                Facts.make_in_range (Facts.substitute_type context frame value_type) application
              with
              | Logic.Boolean true -> ()
              | range ->
                  let arguments_in_range =
                    Logic.conjunction
                      (List.map2
                         (fun (name, _) (_, input) ->
                           Facts.make_in_range
                             (Facts.substitute_type context frame input)
                             (Logic.Symbol name))
                         bound function_type.inputs)
                  in
                  Facts.add_frame_fact context frame
                    (Logic.forall (bound, Logic.( ==> ) arguments_in_range range)))
          | None -> ());
          Some term
      | _ -> None)
  | _ -> None

let check_valid context frame location ty term ~deep ~when_ =
  match Validity.make_validity context frame ~assuming:false ~deep ty term with
  | Logic.Boolean true -> ()
  | valid ->
      Facts.oblige context frame Invariant location
        [ Text (Printf.sprintf "The invariant of `%s` may not hold %s." (Types.show ty) when_) ]
        valid

let classify_counting (cost : Mir.cost) : Costs.counting =
  match cost.bound with Order_of _ | Finite -> Units | At_most _ -> At_most | Exactly _ -> Exactly

let list_loop_counters locals (body : Mir.body) =
  let counters = ref [] in
  let note (loop : Mir.loop) =
    List.iter
      (function
        | Mir.Cost cost -> (
            match Contracts.find_resource cost ~locals with
            | Some resource ->
                counters :=
                  { Costs.resource; counting = classify_counting cost; amortized = false }
                  :: !counters
            | None -> Facts.raise_unsupported Whole_definition "this `calls` target")
        | Invariant _ | Decreases _ -> ())
      loop.clauses
  in
  let rec visit (block : Mir.block) =
    List.iter
      (fun (statement : Mir.statement) ->
        (match statement.kind with
        | While { loop; _ } | For { loop; _ } -> note loop
        | Basic _ | Choose _ | Assert_by_bit_vector _ | Fork _ | Resume _ | Yield _ | Jump _ -> ());
        List.iter visit (Mir.list_nested_blocks statement))
      block.statements
  in
  visit body.code;
  List.rev !counters

let list_facts_since (context : State.context) count =
  let rec take count list =
    if count <= 0 then []
    else match list with [] -> [] | item :: rest -> item :: take (count - 1) rest
  in
  take (List.length context.facts - count) context.facts

let read_lambda ?(capture_free = false) context (frame : State.frame) ~(site : Invocation.site)
    (written : State.lambda_code) ~list_facts =
  let location = Facts.locate context frame.source site.origin in
  let ty = Facts.substitute_type context frame site.type_ in
  let function_type =
    match ty with
    | Types.Function function_type -> function_type
    | _ -> Facts.raise_bug "a lambda of type %s" (Types.show ty)
  in
  if List.length written.code.parameters <> List.length function_type.inputs then
    Facts.raise_bug "a lambda whose parameters do not match %s" (Types.show ty);
  let called = Facts.declare_fresh context frame "called" Logic.Bool in
  let inside = { (Facts.restrict frame called) with result = None } in
  let start_fresh = context.fresh
  and start_facts = List.length context.facts
  and start_declarations = List.length context.declarations in
  let arguments =
    List.map
      (fun (_, input) ->
        let input = Facts.substitute_type context frame input in
        let argument = Facts.arrive context inside "argument" input in
        Validity.assume_valid context inside input argument;
        argument)
      function_type.inputs
  in
  List.iter (Facts.assume context inside) (list_facts arguments);
  let promised =
    List.filter_map
      (fun (cost : Types.cost) ->
        let counting : Costs.counting option =
          match cost.bound with
          | Order_of -> Some Units
          | No_more_than (Some _) -> Some At_most
          | Exactly_cost (Some _) -> Some Exactly
          | No_more_than None | Exactly_cost None -> None
        in
        let resource : Costs.resource option =
          match cost.resource with Metric metric -> Some (Metric metric) | Calls _ -> None
        in
        match (resource, counting) with
        | Some resource, Some counting ->
            let counter = { Costs.resource; counting; amortized = cost.amortized } in
            Some (counter, cost.bound)
        | _ -> None)
      function_type.costs
  in
  let operand_counters =
    List.filter_map
      (fun metric ->
        let counter = Costs.make_operand_counter metric in
        let is_counted =
          List.exists
            (fun (enclosing : Costs.counter) -> enclosing.resource = counter.resource)
            context.counters
        in
        if is_counted && Option.is_none (Costs.find_stated_operand function_type.costs metric) then
          Some (metric, counter)
        else None)
      Metric.all
  in
  let saved_counters = context.counters in
  context.counters <-
    Contracts.deduplicate_counters
      (List.map snd operand_counters @ List.map fst promised
      @ list_loop_counters inside.locals written.code);
  let inside =
    { inside with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
  in
  let mark = context.fresh and facts_mark = List.length context.facts in
  let premises =
    List.drop (List.length context.facts - facts_mark) (list_facts_since context start_facts)
  in
  let ended = ref [] in
  let saved_returns = context.returns and saved_terminates = context.terminates in
  context.returns <- [];
  context.terminates <- Types.terminates function_type.uses;
  let pending =
    Fun.protect
      ~finally:(fun () ->
        context.returns <- saved_returns;
        context.terminates <- saved_terminates;
        context.counters <- saved_counters)
      (fun () ->
        let finished =
          let inside =
            { inside with locals = remove_temporaries inside.locals; panic = Undeclarable }
          in
          let inside =
            List.fold_left2
              (fun inside parameter argument ->
                let info = written.code.locals.(parameter) in
                Facts.bind inside
                  (Locals.make_key written.code.locals parameter)
                  (Facts.substitute_type context inside info.type_)
                  argument)
              inside written.code.parameters arguments
          in
          context.run_body inside ~lambdas:written.lambdas written.code;
          None
        in
        let exits =
          (match finished with Some (frame, _) -> [ frame ] | None -> [])
          @ List.map fst context.returns
        in
        ended :=
          (match finished with Some (frame, value) -> [ (frame, Some value) ] | None -> [])
          @ context.returns;
        List.iter
          (fun ((exit_ : State.frame), returned) ->
            Option.iter
              (fun term ->
                check_valid context exit_ location
                  (Facts.substitute_type context frame function_type.output)
                  term ~deep:true ~when_:"for the value this lambda returns")
              returned;
            List.iter2
              (fun parameter (mode, input) ->
                match (mode, written.code.locals.(parameter).kind) with
                | Types.Mut, Source { local; _ } -> (
                    match Locals.find_opt (Core_local local) exit_.locals with
                    | Some term ->
                        check_valid context exit_ location
                          (Facts.substitute_type context frame input)
                          term ~deep:true ~when_:"for a `mut` parameter when this lambda ends"
                    | None -> ())
                | _ -> ())
              written.code.parameters function_type.inputs)
          !ended;
        let compute_spent (exit_ : State.frame) counter =
          match List.assoc_opt counter exit_.spent with Some term -> term | None -> Costs.zero
        in
        List.iter
          (fun (exit_ : State.frame) ->
            List.iter
              (fun (counter, (bound : Types.cost_bound)) ->
                let spent = compute_spent exit_ counter in
                let goal =
                  match bound with
                  | Order_of -> Costs.at_most spent (Costs.bound (Logic.int 1))
                  | No_more_than (Some limit) -> Costs.at_most spent (Logic.Integer limit)
                  | Exactly_cost (Some limit) -> Logic.equal spent (Logic.Integer limit)
                  | _ -> Logic.Boolean true
                in
                let difference, verb =
                  match counter.counting with
                  | Units | At_most -> ("more than", "allows")
                  | Exactly -> ("more or less than", "states")
                in
                Facts.oblige context exit_ Cost location
                  [
                    Text
                      (Printf.sprintf "This lambda may spend %s its type, `%s`, %s." difference
                         (Types.show ty) verb);
                  ]
                  goal)
              promised)
          exits;
        let facts =
          list_facts_since context facts_mark
          @ List.map (fun (exit_ : State.frame) -> exit_.condition) exits
        in
        List.filter_map
          (fun ((metric : Metric.t), counter) ->
            let spent = List.map (fun exit_ -> compute_spent exit_ counter) exits in
            let most =
              match spent with
              | [] -> Costs.zero
              | first :: rest -> List.fold_left Costs.larger first rest
            in
            Option.map
              (fun bound ->
                ( metric,
                  ( bound,
                    List.filter_map
                      (fun ((exit_ : State.frame), spent) ->
                        Facts.make_closed_obligation context exit_ Cost location
                          [
                            Text
                              (Printf.sprintf
                                 "The prover cannot show that a call of this lambda %s than the \
                                  bound it found for every call, which a cost here relies on."
                                 (match metric with
                                 | Time -> "takes no more time"
                                 | Allocations -> "makes no more allocations"
                                 | Allocated_bytes -> "allocates no more bytes"));
                          ]
                          (Costs.at_most spent bound))
                      (List.combine exits spent) ) ))
              (Costs.find_cost_bound ~varies:(Facts.mentions_fresh_after context mark) ~facts most))
          operand_counters)
  in
  let end_fresh = context.fresh in
  let term =
    match find_lambda_definition context frame function_type written with
    | Some term -> term
    | None ->
        let term = Facts.arrive context frame "lambda" ty in
        if is_in_the_logic function_type then
          add_lambda_facts context frame ~capture_free function_type term ~called ~arguments
            ~start_fresh ~end_fresh ~start_declarations ~premises
            ~shown:(list_facts_since context facts_mark)
            ~ended:!ended;
        term
  in
  context.lambda_captures <- (term, list_captured_locals written) :: context.lambda_captures;
  context.lambda_costs <-
    List.map (fun (metric, pending_cost) -> ((term, metric), pending_cost)) pending
    @ context.lambda_costs;
  (frame, term)

let translate_lambda context (frame : State.frame) ~(site : Invocation.site)
    (written : State.lambda_code) ~list_facts =
  let find_captured (local : Core.local) =
    match local with Self -> frame.self | local -> Locals.find_opt (Core_local local) frame.locals
  in
  if
    frame.bound <> []
    && List.for_all
         (fun capture ->
           match find_captured capture with
           | Some term -> not (Logic.mentions frame.bound term)
           | None -> false)
         (list_captured_locals written)
  then
    let _, term =
      read_lambda ~capture_free:true context
        { frame with binders = []; condition = Logic.Boolean true }
        ~site written ~list_facts
    in
    (frame, term)
  else read_lambda context frame ~site written ~list_facts

let make_passed_values context frame (invocation : Invocation.t)
    (arguments : State.call_argument list) =
  let known =
    List.filter_map
      (function
        | State.Value_argument (passed : State.passed) -> Some (passed.position, passed.term)
        | Lambda_argument _ -> None)
      arguments
  in
  List.map
    (function
      | State.Value_argument passed -> passed
      | Lambda_argument { position; mode; site; lambda = written } ->
          let _, term =
            translate_lambda context frame ~site written
              ~list_facts:(Validity.list_callback_facts context frame invocation position known)
          in
          {
            position;
            mode;
            shape = Other;
            origin = Some site.origin;
            passed_place = None;
            type_ = Facts.substitute_type context frame site.type_;
            term;
          })
    arguments
