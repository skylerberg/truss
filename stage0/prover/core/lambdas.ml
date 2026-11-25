let apply_function context (function_type : Types.function_type) callee arguments =
  let inputs = List.map (fun (_, input) -> Facts.declare_sort context input) function_type.inputs in
  let output = Facts.declare_sort context function_type.output in
  let value_sort = Facts.declare_sort context (Types.Function function_type) in
  let symbol = Logic.Symbol.Apply ((value_sort :: inputs) @ [ output ]) in
  Facts.declare context (Logic.Function (symbol, value_sort :: inputs, output));
  Logic.Apply (symbol, callee :: arguments)

let returns_value (function_type : Types.function_type) =
  not (Types.equal function_type.output Types.unit)

let make_callback_ensures context (function_type : Types.function_type) callee ~entries ~exits
    ~result =
  let sorts =
    Facts.declare_sort context (Types.Function function_type)
    :: List.concat_map
         (fun ((mode : Language.Mode.t), input) ->
           let sort = Facts.declare_sort context input in
           match mode with Mut -> [ sort; sort ] | Read | Own -> [ sort ])
         function_type.inputs
    @
    if returns_value function_type then [ Facts.declare_sort context function_type.output ] else []
  in
  let arguments =
    List.concat
      (List.map2
         (fun ((mode : Language.Mode.t), _) (entry, exit_) ->
           match mode with Mut -> [ entry; exit_ ] | Read | Own -> [ entry ])
         function_type.inputs (List.combine entries exits))
    @ if returns_value function_type then [ result ] else []
  in
  let symbol = Logic.Symbol.Callback_ensures sorts in
  Facts.declare context (Logic.Function (symbol, sorts, Logic.Bool));
  Logic.Apply (symbol, callee :: arguments)

let apply_callback_ensures context (function_type : Types.function_type) values =
  let rec split inputs arguments ~entries ~exits =
    match (inputs, arguments) with
    | [], rest -> (List.rev entries, List.rev exits, rest)
    | (Language.Mode.Mut, _) :: inputs, entry :: exit_ :: rest ->
        split inputs rest ~entries:(entry :: entries) ~exits:(exit_ :: exits)
    | ((Language.Mode.Read | Own), _) :: inputs, value :: rest ->
        split inputs rest ~entries:(value :: entries) ~exits:(value :: exits)
    | _ :: _, _ ->
        Facts.raise_bug "`.ensures` with fewer arguments than its function type has inputs"
  in
  match values with
  | callee :: arguments -> (
      let entries, exits, rest = split function_type.inputs arguments ~entries:[] ~exits:[] in
      match rest with
      | [ result ] -> make_callback_ensures context function_type callee ~entries ~exits ~result
      | [] when not (returns_value function_type) ->
          make_callback_ensures context function_type callee ~entries ~exits
            ~result:(Logic.Apply (Logic.Symbol.Unit, []))
      | _ -> Facts.raise_bug "`.ensures` with arguments that do not match its function type")
  | [] -> Facts.raise_bug "`.ensures` without the function it describes"

let make_lifting (context : State.context) (frame : State.frame) ~called ~arguments ~start_fresh
    ~end_fresh ~start_declarations parameters =
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
  let variables = List.map (fun (name, _) -> Logic.Symbol name) parameters in
  let renamed = Tables.Symbol_table.create 16 in
  (match called with
  | Logic.Symbol name -> Tables.Symbol_table.replace renamed name (Logic.Boolean true)
  | _ -> ());
  List.iteri
    (fun index argument ->
      match argument with
      | Logic.Symbol name -> Tables.Symbol_table.replace renamed name (List.nth variables index)
      | _ -> ())
    arguments;
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
  lift

let add_quantified_fact (context : State.context) (frame : State.frame) ~capture_free stated =
  if frame.bound = [] || capture_free then Facts.add_fact context stated
  else
    match Facts.close_over_binders frame stated with
    | Some closed -> Facts.add_fact context closed
    | None -> ()

let make_input_variables context ~start_fresh (function_type : Types.function_type) =
  List.mapi
    (fun index (_, input) ->
      ( Facts.make_variable "lambda.argument" ~numbers:[ start_fresh; index ],
        Facts.declare_sort context input ))
    function_type.inputs

let add_lambda_facts (context : State.context) (frame : State.frame) ~capture_free
    (function_type : Types.function_type) term ~called ~arguments ~start_fresh ~end_fresh
    ~start_declarations ~premises ~shown ~ended =
  let parameters = make_input_variables context ~start_fresh function_type in
  let lift =
    make_lifting context frame ~called ~arguments ~start_fresh ~end_fresh ~start_declarations
      parameters
  in
  let premise = lift (Logic.conjunction premises) in
  let applied_here =
    apply_function context function_type term
      (List.map (fun (name, _) -> Logic.Symbol name) parameters)
  in
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
      add_quantified_fact context frame ~capture_free
        (Logic.forall (parameters, Logic.( ==> ) premise statement)))
    statements

let add_lambda_relation (context : State.context) (frame : State.frame) ~capture_free
    (function_type : Types.function_type) term ~called ~arguments ~start_fresh ~end_fresh
    ~start_declarations ~premises ~shown ~ended ~read_exits =
  let inputs = make_input_variables context ~start_fresh function_type in
  let changed =
    List.filter_map
      (fun (index, ((mode : Language.Mode.t), input)) ->
        match mode with
        | Mut ->
            Some
              ( index,
                ( Facts.make_variable "lambda.changed" ~numbers:[ start_fresh; index ],
                  Facts.declare_sort context input ) )
        | Read | Own -> None)
      (List.mapi (fun index input -> (index, input)) function_type.inputs)
  in
  let returned =
    if returns_value function_type then
      [
        ( Facts.make_variable "lambda.result" ~numbers:[ start_fresh ],
          Facts.declare_sort context function_type.output );
      ]
    else []
  in
  let parameters = inputs @ List.map snd changed @ returned in
  let lift =
    make_lifting context frame ~called ~arguments ~start_fresh ~end_fresh ~start_declarations
      parameters
  in
  let entries = List.map (fun (name, _) -> Logic.Symbol name) inputs in
  let exits =
    List.mapi
      (fun index entry ->
        match List.assoc_opt index changed with
        | Some (name, _) -> Logic.Symbol name
        | None -> entry)
      entries
  in
  let result =
    match returned with
    | [ (name, _) ] -> Logic.Symbol name
    | _ -> Logic.Apply (Logic.Symbol.Unit, [])
  in
  let holds = make_callback_ensures context function_type term ~entries ~exits ~result in
  let premise = lift (Logic.conjunction premises) in
  let exited =
    List.map
      (fun ((exit_ : State.frame), value) ->
        let finals = read_exits exit_ in
        let changed_values =
          List.filter_map
            (fun (index, (name, _)) ->
              Option.map
                (fun final -> Logic.equal (Logic.Symbol name) (lift final))
                (List.assoc_opt index finals))
            changed
        in
        let result_value =
          match (returned, value) with
          | [ (name, _) ], Some value -> [ Logic.equal (Logic.Symbol name) (lift value) ]
          | _ -> []
        in
        Logic.( ==> ) (lift exit_.condition) (Logic.conjunction (changed_values @ result_value)))
      ended
  in
  let statements =
    List.map lift shown @ exited
    @ [
        Logic.disjunction (List.map (fun ((exit_ : State.frame), _) -> lift exit_.condition) ended);
      ]
  in
  List.iter
    (fun statement ->
      add_quantified_fact context frame ~capture_free
        (Logic.forall ~trigger:[ holds ]
           (parameters, Logic.( ==> ) holds (Logic.( ==> ) premise statement))))
    statements

let add_logic_relation (context : State.context) (frame : State.frame) ~capture_free
    (function_type : Types.function_type) term =
  if returns_value function_type then begin
    let inputs =
      List.mapi
        (fun index (_, input) ->
          ( Facts.make_variable "relation.argument" ~numbers:[ index ],
            Facts.declare_sort context input ))
        function_type.inputs
    in
    let returned = Facts.make_variable "relation.result" ~numbers:[] in
    let entries = List.map (fun (name, _) -> Logic.Symbol name) inputs in
    let holds =
      make_callback_ensures context function_type term ~entries ~exits:entries
        ~result:(Logic.Symbol returned)
    in
    add_quantified_fact context frame ~capture_free
      (Logic.forall ~trigger:[ holds ]
         ( inputs @ [ (returned, Facts.declare_sort context function_type.output) ],
           Logic.equal holds
             (Logic.equal (Logic.Symbol returned)
                (apply_function context function_type term entries)) ))
  end

let is_in_the_logic (function_type : Types.function_type) =
  function_type.uses = Types.no_capabilities
  && List.for_all (fun (mode, _) -> mode <> Language.Mode.Mut) function_type.inputs

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
  let saved_returns = context.returns
  and saved_panics = context.panics
  and saved_can_declare_panic = context.can_declare_panic in
  context.returns <- [];
  context.panics <- false;
  context.can_declare_panic <- false;
  Fun.protect
    ~finally:(fun () ->
      context.returns <- saved_returns;
      context.panics <- saved_panics;
      context.can_declare_panic <- saved_can_declare_panic)
    (fun () ->
      let inside = enter { frame with locals = remove_temporaries frame.locals } in
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
              | range -> (
                  let find_argument_in_range (name, _) (_, input) =
                    Validity.find_parts_in_range context
                      (Facts.substitute_type context frame input)
                      (Logic.Symbol name)
                  in
                  match List.map2 find_argument_in_range bound function_type.inputs with
                  | arguments when List.for_all Option.is_some arguments ->
                      Facts.add_frame_fact context frame
                        (Logic.forall
                           ( bound,
                             Logic.( ==> )
                               (Logic.conjunction (List.filter_map Fun.id arguments))
                               range ))
                  | _ -> ()))
          | None -> ());
          Some term
      | _ -> None)
  | _ -> None

let check_valid context frame location ty term ~deep ~moment =
  match Validity.make_validity context frame ~assuming:false ~deep ty term with
  | Logic.Boolean true -> ()
  | valid -> Facts.oblige context frame location (Invariant_may_fail { type_ = ty; moment }) valid

let classify_counting (cost : Mir.cost) : Costs.counting =
  match cost.bound with Order_of _ -> Units | At_most _ -> At_most | Exactly _ -> Exactly

let list_loop_counters context locals (body : Mir.body) =
  let counters = ref [] in
  let note (loop : Mir.loop) =
    List.iter
      (function
        | Mir.Cost cost -> (
            match
              Conditions.find_obligation_condition
                (Conditions.decide context ~substitution:Types.no_substitution cost.holds_when)
            with
            | None -> ()
            | Some condition -> (
                match Contracts.find_resource cost ~locals with
                | Some resource ->
                    counters :=
                      ( {
                          Costs.resource;
                          counting = classify_counting cost;
                          amortized = false;
                          counts_potential = true;
                        },
                        condition )
                      :: !counters
                | None -> Facts.raise_unsupported Whole_definition Calls_target))
        | Invariant _ | Decreases _ -> ())
      loop.clauses
  in
  let rec visit (block : Mir.block) =
    List.iter
      (fun (statement : Mir.statement) ->
        (match statement.kind with
        | While { loop; _ } | For { loop; _ } -> note loop
        | Basic _ | Choose _ | Assert_by_bit_vector _ | Fork _ | Provide _ | Resume _ | Yield _
        | Jump _ ->
            ());
        List.iter visit (Mir.list_nested_blocks statement))
      block.statements
  in
  visit body.code;
  List.rev !counters

let list_checking_counters (context : State.context) counter =
  if context.checks_without_potential then Costs.list_checking_counters counter else [ counter ]

let assign_counters (context : State.context) (sources : (Costs.counter * Types.condition) list) =
  let counters = Contracts.deduplicate_counters (List.map fst sources) in
  context.counters <- counters;
  context.conditional_counters <-
    List.filter (fun counter -> not (List.mem (counter, []) sources)) counters

let list_facts_since (context : State.context) count =
  let rec take count list =
    if count <= 0 then []
    else match list with [] -> [] | item :: rest -> item :: take (count - 1) rest
  in
  take (List.length context.facts - count) context.facts

let read_lambda ?(capture_free = false) context (frame : State.frame) ~(site : Invocation.site)
    (written : State.lambda_code) ~list_facts ~list_promises =
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
        let counting : Costs.counting =
          match cost.bound with
          | Order_of -> Units
          | No_more_than _ -> At_most
          | Exactly_cost _ -> Exactly
        in
        match cost.resource with
        | Metric metric ->
            let counter =
              {
                Costs.resource = Metric metric;
                counting;
                amortized = cost.amortized;
                counts_potential = true;
              }
            in
            Some (counter, cost.bound)
        | Calls _ -> None)
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
      Language.Metric.all
  in
  let saved_counters = context.counters
  and saved_conditional_counters = context.conditional_counters in
  assign_counters context
    (List.concat_map
       (fun (_, (counter : Costs.counter)) ->
         let is_conditional =
           List.for_all
             (fun (enclosing : Costs.counter) ->
               enclosing.resource <> counter.resource
               || List.mem enclosing context.conditional_counters)
             context.counters
         in
         List.map
           (fun checking -> (checking, if is_conditional then context.condition else []))
           (list_checking_counters context counter))
       operand_counters
    @ List.concat_map
        (fun (counter, _) ->
          List.map (fun checking -> (checking, [])) (list_checking_counters context counter))
        promised
    @ list_loop_counters context inside.locals written.code);
  let inside =
    { inside with spent = List.map (fun counter -> (counter, Costs.zero)) context.counters }
  in
  let read_exits (exit_ : State.frame) =
    List.filter_map
      (fun (index, (parameter, ((mode : Language.Mode.t), _))) ->
        match (mode, written.code.locals.(parameter).kind) with
        | Mut, Source { local; _ } ->
            Option.map (fun term -> (index, term)) (Locals.find_opt (Core_local local) exit_.locals)
        | _ -> None)
      (List.mapi
         (fun index pair -> (index, pair))
         (List.combine written.code.parameters function_type.inputs))
  in
  let mark = context.fresh and facts_mark = List.length context.facts in
  let premises =
    List.drop (List.length context.facts - facts_mark) (list_facts_since context start_facts)
  in
  let ended = ref [] in
  let saved_returns = context.returns
  and saved_terminates = context.terminates
  and saved_panics = context.panics
  and saved_can_declare_panic = context.can_declare_panic in
  context.returns <- [];
  context.terminates <- Types.terminates function_type.uses;
  context.can_declare_panic <- false;
  context.panics <-
    Conditions.may_panic context.lookups ~current:context.current ~condition:context.condition
      function_type.uses;
  let pending =
    Fun.protect
      ~finally:(fun () ->
        context.returns <- saved_returns;
        context.terminates <- saved_terminates;
        context.panics <- saved_panics;
        context.can_declare_panic <- saved_can_declare_panic;
        context.counters <- saved_counters;
        context.conditional_counters <- saved_conditional_counters)
      (fun () ->
        let finished =
          let inside = { inside with locals = remove_temporaries inside.locals } in
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
                  term ~deep:true ~moment:Lambda_result)
              returned;
            List.iter2
              (fun parameter (mode, input) ->
                match (mode, written.code.locals.(parameter).kind) with
                | Language.Mode.Mut, Source { local; _ } -> (
                    match Locals.find_opt (Core_local local) exit_.locals with
                    | Some term ->
                        check_valid context exit_ location
                          (Facts.substitute_type context frame input)
                          term ~deep:true ~moment:Lambda_mut_parameter
                    | None -> ())
                | _ -> ())
              written.code.parameters function_type.inputs)
          !ended;
        List.iter
          (fun ((exit_ : State.frame), returned) ->
            let finals = read_exits exit_ in
            let exits =
              List.mapi
                (fun index argument -> Option.value (List.assoc_opt index finals) ~default:argument)
                arguments
            in
            let result =
              match returned with
              | Some result -> Some result
              | None when not (returns_value function_type) ->
                  Some (Logic.Apply (Logic.Symbol.Unit, []))
              | None -> None
            in
            Option.iter
              (fun result ->
                List.iter
                  (fun (quoted, promise) ->
                    Facts.oblige context exit_ location
                      (Lambda_promise { promise = quoted })
                      promise)
                  (list_promises ~entries:arguments ~exits ~result))
              result)
          !ended;
        let compute_spent (exit_ : State.frame) counter =
          match List.assoc_opt counter exit_.spent with Some term -> term | None -> Costs.zero
        in
        List.iter
          (fun (exit_ : State.frame) ->
            List.iter
              (fun ((counter : Costs.counter), (bound : Types.cost_bound)) ->
                let is_within spent =
                  match bound with
                  | Order_of -> Logic.less_equal spent (Costs.bound (Logic.int 1))
                  | No_more_than limit -> Logic.less_equal spent (Logic.Integer limit)
                  | Exactly_cost limit -> Logic.equal spent (Logic.Integer limit)
                in
                List.iter
                  (fun checking ->
                    Facts.oblige context exit_ location
                      (Lambda_cost
                         {
                           counting =
                             (match counter.counting with
                             | Units | At_most -> Upper_bound
                             | Exactly -> Exact);
                           type_ = ty;
                         })
                      (is_within (compute_spent exit_ checking)))
                  (list_checking_counters context counter))
              promised)
          exits;
        let facts =
          list_facts_since context facts_mark
          @ List.map (fun (exit_ : State.frame) -> exit_.condition) exits
        in
        List.filter_map
          (fun ((metric : Language.Metric.t), counter) ->
            let list_spent exit_ =
              List.map (compute_spent exit_) (list_checking_counters context counter)
            in
            let most =
              match List.concat_map list_spent exits with
              | [] -> Costs.zero
              | first :: rest -> List.fold_left Costs.larger first rest
            in
            Option.map
              (fun bound ->
                ( metric,
                  ( bound,
                    List.concat_map
                      (fun (exit_ : State.frame) ->
                        List.filter_map
                          (fun spent ->
                            Facts.make_closed_obligation context exit_ location
                              (Lambda_call_above_bound { metric })
                              (Logic.less_equal spent bound))
                          (list_spent exit_))
                      exits ) ))
              (Costs.find_cost_bound ~varies:(Facts.mentions_fresh_after context mark) ~facts most))
          operand_counters)
  in
  let end_fresh = context.fresh in
  let shown = list_facts_since context facts_mark in
  let term =
    match find_lambda_definition context frame function_type written with
    | Some term -> term
    | None ->
        let term = Facts.arrive context frame "lambda" ty in
        if is_in_the_logic function_type then
          add_lambda_facts context frame ~capture_free function_type term ~called ~arguments
            ~start_fresh ~end_fresh ~start_declarations ~premises ~shown ~ended:!ended;
        term
  in
  if is_in_the_logic function_type then
    add_logic_relation context frame ~capture_free function_type term
  else
    add_lambda_relation context frame ~capture_free function_type term ~called ~arguments
      ~start_fresh ~end_fresh ~start_declarations ~premises ~shown ~ended:!ended ~read_exits;
  context.lambda_captures <- (term, list_captured_locals written) :: context.lambda_captures;
  context.lambda_costs <-
    List.map (fun (metric, pending_cost) -> ((term, metric), pending_cost)) pending
    @ context.lambda_costs;
  (frame, term)

let translate_lambda context (frame : State.frame) ~(site : Invocation.site)
    (written : State.lambda_code) ~list_facts ~list_promises =
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
        ~site written ~list_facts ~list_promises
    in
    (frame, term)
  else read_lambda context frame ~site written ~list_facts ~list_promises

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
              ~list_promises:
                (Validity.list_callback_promises context frame invocation position known)
          in
          {
            position;
            mode;
            shape = Lambda;
            origin = Some site.origin;
            passed_place = None;
            type_ = Facts.substitute_type context frame site.type_;
            declared_type = Facts.substitute_declared_type context frame site.type_;
            term;
          })
    arguments
