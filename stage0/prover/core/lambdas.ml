let make_lifting (context : State.context) (frame : State.frame) ~called ~arguments ~start_fresh
    ~end_fresh ~start_declarations parameters =
  let declared_here = Query.list_declarations_since context.query ~count:start_declarations in
  let captures_fresh = function
    | Logic.Symbol.Lambda _ as name when Option.is_none (Query.find_fresh_order context.query name)
      -> (
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
            match Query.find_fresh_order context.query name with
            | Some order -> order > start_fresh && order <= end_fresh
            | None -> captures_fresh name
          in
          if is_fresh_in_body then begin
            let lifted = Logic.Symbol.Lifted name in
            Facts.declare context (Logic.Function (lifted, List.map snd parameters, sort));
            Tables.Symbol_table.replace renamed name (Logic.Apply (lifted, variables))
          end
      | Logic.Function (name, inputs, sort) when frame.binders <> [] -> (
          match Query.find_fresh_order context.query name with
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

let add_lambda_facts (context : State.context) (frame : State.frame) ~capture_free
    (function_type : Types.function_type) term ~called ~arguments ~start_fresh ~end_fresh
    ~start_declarations ~premises ~shown ~ended =
  let parameters =
    Callbacks.make_input_variables context function_type ~label:"lambda" ~numbers:[ start_fresh ]
  in
  let lift =
    make_lifting context frame ~called ~arguments ~start_fresh ~end_fresh ~start_declarations
      parameters
  in
  let premise = lift (Logic.conjunction premises) in
  let applied_here =
    Callbacks.apply_function context function_type term
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
  let ({ inputs; changed; returned; entries; exits; result } : Callbacks.relation_variables) =
    Callbacks.make_relation_variables context function_type ~label:"lambda" ~numbers:[ start_fresh ]
  in
  let parameters = inputs @ List.map snd changed @ returned in
  let lift =
    make_lifting context frame ~called ~arguments ~start_fresh ~end_fresh ~start_declarations
      parameters
  in
  let holds = Callbacks.make_callback_ensures context function_type term ~entries ~exits ~result in
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
  if Callbacks.returns_value function_type then begin
    let ({ inputs; returned; entries; result; _ } : Callbacks.relation_variables) =
      Callbacks.make_relation_variables context function_type ~label:"relation" ~numbers:[]
    in
    let holds =
      Callbacks.make_callback_ensures context function_type term ~entries ~exits:entries ~result
    in
    add_quantified_fact context frame ~capture_free
      (Logic.forall ~trigger:[ holds ]
         ( inputs @ returned,
           Logic.equal holds
             (Logic.equal result (Callbacks.apply_function context function_type term entries)) ))
  end

let make_parameter_symbols context (frame : State.frame) (function_type : Types.function_type) =
  let depth = List.length frame.bound in
  List.mapi
    (fun index (_, input) ->
      ( Logic.Symbol.Variable { label = "parameter"; numbers = [ depth; index ] },
        Encoding.declare_sort context (Encoding.substitute_type context frame input) ))
    function_type.inputs

let remove_temporaries locals =
  Locals.filter
    (fun key _ -> match key with Locals.Mir_local _ -> false | Core_local _ -> true)
    locals

let run_lambda_body ?(enter = Fun.id) (context : State.context) (frame : State.frame)
    ~(lambdas : Mir.body array) (body : Mir.body) ~type_ =
  let saved_returns = context.returns in
  context.returns <- [];
  Obligations.run_with_panics context ~panics:false @@ fun () ->
  Fun.protect
    ~finally:(fun () -> context.returns <- saved_returns)
    (fun () ->
      let inside = enter { frame with locals = remove_temporaries frame.locals } in
      Facts.run_in_source context frame.source (fun () -> context.run_body inside ~lambdas body);
      match
        Joins.join context ~value_type:type_
          (List.rev_map
             (fun (exit_ : State.function_exit) -> (exit_.frame, exit_.returned))
             context.returns)
      with
      | Some (returned, Some term) -> Some ({ frame with spent = returned.spent }, term)
      | Some (_, None) | None -> None)

let run_code context frame (code : Mir.t) ~type_ =
  match run_lambda_body context frame ~lambdas:code.lambdas code.body ~type_ with
  | Some returned -> returned
  | None -> (frame, Encoding.arrive context frame "unfinished" type_)

let compute_returned_type context frame (body : Mir.body) =
  let rec find_returned_type (block : Mir.block) =
    List.find_map
      (fun (statement : Mir.statement) ->
        match statement.kind with
        | Jump (Return (Some value)) ->
            Some (Encoding.substitute_type context frame (Mir.extract_operand_type value))
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
  | true when Callbacks.is_in_the_logic function_type -> (
      let bound = make_parameter_symbols context frame function_type in
      let defined =
        let mark = Query.count_fresh context.query in
        Counters.run_without_counters context (fun () ->
            try
              let enter inside =
                List.fold_left2
                  (fun inside parameter (name, _) ->
                    let info = written.code.locals.(parameter) in
                    Facts.bind inside
                      (Locals.make_key written.code.locals parameter)
                      (Encoding.substitute_type context inside info.type_)
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
          let sort = Encoding.declare_sort context (Types.Function function_type) in
          let term =
            if Logic.mentions frame.bound defined then
              Facts.declare_value_symbol context frame symbol sort
            else Facts.declare_value_symbol context { frame with binders = [] } symbol sort
          in
          let application =
            Callbacks.apply_function context function_type term
              (List.map (fun (name, _) -> Logic.Symbol name) bound)
          in
          Tables.Symbol_table.replace context.lambda_definitions symbol defined;
          Facts.add_frame_fact context frame (Logic.forall (bound, Logic.equal application defined));
          (match written.code.value_type with
          | Some value_type -> (
              match
                Encoding.make_in_range
                  (Encoding.substitute_type context frame value_type)
                  application
              with
              | Logic.Boolean true -> ()
              | range -> (
                  let find_argument_in_range (name, _) (_, input) =
                    Validity.find_parts_in_range context
                      (Encoding.substitute_type context frame input)
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

let read_lambda ?(capture_free = false) context (frame : State.frame) ~(site : Invocation.site)
    (written : State.lambda_code) ~list_facts ~list_promises =
  let location = Facts.locate context frame.source site.origin in
  let ty = Encoding.substitute_type context frame site.type_ in
  let function_type =
    match ty with
    | Types.Function function_type -> function_type
    | _ -> Facts.raise_bug "a lambda of type %s" (Types.show ty)
  in
  if List.length written.code.parameters <> List.length function_type.inputs then
    Facts.raise_bug "a lambda whose parameters do not match %s" (Types.show ty);
  let called = Facts.declare_fresh context frame "called" Logic.Bool in
  let inside = { (Facts.restrict frame called) with result = None } in
  let start_fresh = Query.count_fresh context.query
  and start_facts = Query.count_facts context.query
  and start_declarations = Query.count_declarations context.query in
  let arguments =
    List.map
      (fun (_, input) ->
        let input = Encoding.substitute_type context frame input in
        let argument = Encoding.arrive context inside "argument" input in
        Validity.assume_valid context inside input argument;
        argument)
      function_type.inputs
  in
  List.iter (Facts.assume context inside) (list_facts arguments);
  let counters, inside = Counters.enter_lambda context inside function_type written.code in
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
  let mark = Query.count_fresh context.query and facts_mark = Query.count_facts context.query in
  let premises =
    List.drop
      (Query.count_facts context.query - facts_mark)
      (Query.list_facts_since context.query ~count:start_facts)
  in
  let ended = ref [] in
  let saved_returns = context.returns in
  context.returns <- [];
  let inferred_bounds =
    Obligations.run_with_panics context
      ~panics:
        (Conditions.may_panic context.lookups ~current:context.current ~condition:context.condition
           function_type.uses)
    @@ fun () ->
    Termination.run_in_lambda context function_type @@ fun () ->
    Fun.protect
      ~finally:(fun () ->
        context.returns <- saved_returns;
        Counters.leave_lambda context counters)
      (fun () ->
        let inside = { inside with locals = remove_temporaries inside.locals } in
        let inside =
          List.fold_left2
            (fun inside parameter argument ->
              let info = written.code.locals.(parameter) in
              Facts.bind inside
                (Locals.make_key written.code.locals parameter)
                (Encoding.substitute_type context inside info.type_)
                argument)
            inside written.code.parameters arguments
        in
        context.run_body inside ~lambdas:written.lambdas written.code;
        let exits = List.map (fun (exit_ : State.function_exit) -> exit_.frame) context.returns in
        ended :=
          List.map
            (fun (exit_ : State.function_exit) -> (exit_.frame, exit_.returned))
            context.returns;
        List.iter
          (fun ((exit_ : State.frame), returned) ->
            Option.iter
              (fun term ->
                Validity.check_valid context exit_ location
                  (Encoding.substitute_type context frame function_type.output)
                  term ~deep:true ~moment:Lambda_result)
              returned;
            List.iter2
              (fun parameter (mode, input) ->
                match (mode, written.code.locals.(parameter).kind) with
                | Language.Mode.Mut, Source { local; _ } -> (
                    match Locals.find_opt (Core_local local) exit_.locals with
                    | Some term ->
                        Validity.check_valid context exit_ location
                          (Encoding.substitute_type context frame input)
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
              | None when not (Callbacks.returns_value function_type) ->
                  Some (Logic.Apply (Logic.Symbol.Unit, []))
              | None -> None
            in
            Option.iter
              (fun result ->
                List.iter
                  (fun (quoted, promise) ->
                    Obligations.oblige context exit_ location
                      (Lambda_promise { promise = quoted })
                      promise)
                  (list_promises ~entries:arguments ~exits ~result))
              result)
          !ended;
        Counters.check_lambda_exits context counters exits location ~type_:ty ~fresh_mark:mark
          ~facts_mark)
  in
  let end_fresh = Query.count_fresh context.query in
  let shown = Query.list_facts_since context.query ~count:facts_mark in
  let term =
    match find_lambda_definition context frame function_type written with
    | Some term -> term
    | None ->
        let term = Encoding.arrive context frame "lambda" ty in
        if Callbacks.is_in_the_logic function_type then
          add_lambda_facts context frame ~capture_free function_type term ~called ~arguments
            ~start_fresh ~end_fresh ~start_declarations ~premises ~shown ~ended:!ended;
        term
  in
  if Callbacks.is_in_the_logic function_type then
    add_logic_relation context frame ~capture_free function_type term
  else
    add_lambda_relation context frame ~capture_free function_type term ~called ~arguments
      ~start_fresh ~end_fresh ~start_declarations ~premises ~shown ~ended:!ended ~read_exits;
  Counters.note_lambda context counters term ~captures:(list_captured_locals written)
    ~bounds:inferred_bounds;
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
              ~list_facts:(Callbacks.list_callback_facts context frame invocation position known)
              ~list_promises:
                (Callbacks.list_callback_promises context frame invocation position known)
          in
          {
            position;
            mode;
            shape = Lambda;
            origin = Some site.origin;
            passed_place = None;
            is_step_self = false;
            type_ = Encoding.substitute_type context frame site.type_;
            declared_type = Encoding.substitute_declared_type context frame site.type_;
            term;
          })
    arguments
