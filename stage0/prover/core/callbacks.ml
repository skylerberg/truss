let make_state () : State.callback_state = { own = []; is_reading = false }
let declare_own (context : State.context) own = context.callbacks.own <- own
let is_reading (context : State.context) = context.callbacks.is_reading

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

let is_in_the_logic (function_type : Types.function_type) =
  function_type.uses = Types.no_capabilities
  && List.for_all (fun (mode, _) -> mode <> Language.Mode.Mut) function_type.inputs

let declare_callback_arguments context frame inputs =
  List.map
    (fun (_, input) ->
      let input = Facts.substitute_type context frame input in
      let term = Facts.arrive context frame "argument" input in
      Validity.assume_valid context frame input term;
      term)
    inputs

let make_callback_contract_frame (frame : State.frame) inputs arguments =
  let locals =
    List.fold_left2
      (fun locals input term -> Locals.add (Core_local input) term locals)
      frame.old_locals inputs arguments
  in
  { frame with locals; self = frame.old_self; makes_obligations = false }

let make_callback_ensures_frame (frame : State.frame) inputs ~entries ~exits ~result =
  let bind terms =
    List.fold_left2
      (fun locals input term -> Locals.add (Core_local input) term locals)
      frame.old_locals inputs terms
  in
  {
    frame with
    locals = bind exits;
    old_locals = bind entries;
    self = frame.old_self;
    result = Some result;
    makes_obligations = false;
  }

let find_own_callback (context : State.context) local =
  List.find_map
    (fun (parameter, name, callback) -> if parameter = local then Some (name, callback) else None)
    context.callbacks.own

let check_callback_contract context frame location ~name inputs requires arguments ~promised ~reason
    =
  let inside = make_callback_contract_frame frame inputs arguments in
  List.iter
    (fun (clause : Mir.formula) ->
      Facts.oblige context (Facts.restrict frame promised) location
        (Callback_requirement { name; reason; clause = Facts.quote frame.source clause.origin })
        (snd (Validity.read_specification context inside clause)))
    requires

let check_escaping_callback context frame local =
  match
    (find_own_callback context local, Facts.find_local_type context frame (Core_local local))
  with
  | ( Some (name, ({ inputs; requires = _ :: _ as requires; _ } : Mir.callback)),
      Some (Types.Function function_type) )
    when List.length inputs = List.length function_type.inputs ->
      let arguments = declare_callback_arguments context frame function_type.inputs in
      check_callback_contract context frame
        (Facts.locate context frame.source (List.hd requires).origin)
        ~name inputs requires arguments ~promised:(Logic.Boolean true)
        ~reason:Used_as_unpromising_value
  | _ -> ()

let run_reading_callback : 'a. _ -> (unit -> 'a) -> 'a =
 fun (context : State.context) read ->
  let saved = context.callbacks.is_reading in
  context.callbacks.is_reading <- true;
  Fun.protect ~finally:(fun () -> context.callbacks.is_reading <- saved) read

let make_callee_substitution (frame : State.frame) (signature : Types.signature) instantiation =
  Types.make_signature_substitution signature
    (Types.substitute_instantiation frame.substitution instantiation)

let find_callee_declaration (context : State.context) frame (invocation : Invocation.t) =
  let read path = Contracts.read_signature context path in
  match invocation.callee with
  | Function { path; instantiation } ->
      Option.map
        (fun signature -> (path, signature, make_callee_substitution frame signature instantiation))
        (read path)
  | Trait_method { trait; name; receiver; self_type; instantiation; _ } ->
      let path = Path.Method { owner = trait.trait; name; receiver } in
      Option.map
        (fun signature ->
          let trait =
            {
              trait with
              trait_arguments =
                List.map (Types.substitute_argument_erased frame.substitution) trait.trait_arguments;
            }
          in
          ( path,
            signature,
            Types.combine_substitutions
              (Contracts.make_trait_substitution context.lookups trait
                 (Facts.substitute_type context frame self_type))
              (make_callee_substitution frame signature instantiation) ))
        (read path)
  | Capability_method _ | Intrinsic _ | Indirect _ -> None

let read_callee_callback (context : State.context) frame (invocation : Invocation.t) position known
    read =
  match find_callee_declaration context frame invocation with
  | Some (path, _, substitution) -> (
      match Contracts.find_callee_clauses context path with
      | Some clauses -> (
          match List.assoc_opt position clauses.callbacks with
          | Some callback ->
              read clauses.callee
                (Contracts.bind_arguments frame clauses ~arguments:known ~substitution)
                callback
          | None -> [])
      | None -> [])
  | None -> []

let list_callback_facts context frame invocation position known arguments =
  read_callee_callback context frame invocation position known
    (fun _ inside ({ inputs; requires; _ } : Mir.callback) ->
      if List.length inputs <> List.length arguments then []
      else
        let inside = make_callback_contract_frame inside inputs arguments in
        List.map (fun clause -> snd (Validity.read_specification context inside clause)) requires)

let list_callback_promises context frame invocation position known ~entries ~exits ~result =
  read_callee_callback context frame invocation position known
    (fun callee inside ({ inputs; ensures; _ } : Mir.callback) ->
      if List.length inputs <> List.length entries then []
      else
        let inside = make_callback_ensures_frame inside inputs ~entries ~exits ~result in
        List.map
          (fun (clause : Mir.formula) ->
            ( Facts.quote callee clause.origin,
              snd (Validity.read_specification context inside clause) ))
          ensures)

let assume_own_callback_ensures context frame local ~entries ~exits ~result =
  match find_own_callback context local with
  | Some (_, ({ inputs; ensures; _ } : Mir.callback)) when List.length inputs = List.length entries
    ->
      let inside = make_callback_ensures_frame frame inputs ~entries ~exits ~result in
      List.iter
        (fun clause ->
          Facts.assume context frame (snd (Validity.read_specification context inside clause)))
        ensures
  | _ -> ()

let declare_callback_results context frame (function_type : Types.function_type) entries =
  let exits =
    List.map2
      (fun ((mode : Language.Mode.t), input) entry ->
        match mode with
        | Mut ->
            let input = Facts.substitute_type context frame input in
            let exit_ = Facts.arrive context frame "changed" input in
            Validity.assume_valid context frame input exit_;
            exit_
        | Read | Own -> entry)
      function_type.inputs entries
  in
  let output = Facts.substitute_type context frame function_type.output in
  let result = Facts.arrive context frame "result" output in
  Validity.assume_valid context frame output result;
  (exits, result)

let find_parameter_type (context : State.context) frame (invocation : Invocation.t) index =
  Option.bind (find_callee_declaration context frame invocation)
    (fun (_, (signature : Types.signature), substitution) ->
      let types =
        (match signature.receiver with Some (_, ty) -> [ ty ] | None -> [])
        @ List.map (fun (info : Types.parameter_info) -> info.type_) signature.parameters
      in
      Option.map (Types.substitute_erased substitution) (List.nth_opt types index))

let has_callback_promises context frame invocation position =
  read_callee_callback context frame invocation position []
    (fun _ _ ({ ensures; _ } : Mir.callback) -> ensures)
  <> []

let check_callback_promises context frame ~location (invocation : Invocation.t)
    (passed : State.passed) ~unpromised ~assume values =
  match find_parameter_type context frame invocation passed.position with
  | Some (Types.Function expected)
    when has_callback_promises context frame invocation passed.position ->
      let entries = declare_callback_arguments context frame expected.inputs in
      let known = List.map (fun (passed : State.passed) -> (passed.position, passed.term)) values in
      let exits, result = declare_callback_results context frame expected entries in
      let at_call =
        Facts.restrict frame
          (Logic.conjunction
             (list_callback_facts context frame invocation passed.position known entries))
      in
      assume at_call expected ~entries ~exits ~result;
      List.iter
        (fun (quoted, promise) ->
          Facts.oblige context at_call location
            (Callback_promise { promise = quoted; unpromised })
            promise)
        (list_callback_promises context frame invocation passed.position known ~entries ~exits
           ~result)
  | _ -> ()

let assume_nothing _ _ ~entries:_ ~exits:_ ~result:_ = ()

let check_forwarded_callback context frame (site : Invocation.site) (invocation : Invocation.t)
    (passed : State.passed) local values =
  (match find_own_callback context local with
  | Some (name, ({ inputs; requires = _ :: _ as requires; _ } : Mir.callback)) -> (
      match find_parameter_type context frame invocation passed.position with
      | Some (Types.Function expected) when List.length expected.inputs = List.length inputs ->
          let arguments = declare_callback_arguments context frame expected.inputs in
          let known =
            List.map (fun (passed : State.passed) -> (passed.position, passed.term)) values
          in
          check_callback_contract context frame
            (Facts.locate context frame.source site.origin)
            ~name inputs requires arguments
            ~promised:
              (Logic.conjunction
                 (list_callback_facts context frame invocation passed.position known arguments))
            ~reason:Passed_for_unpromising_parameter
      | _ -> check_escaping_callback context frame local)
  | _ -> ());
  let location = Facts.locate context frame.source site.origin in
  match find_own_callback context local with
  | Some (name, _) ->
      check_callback_promises context frame ~location invocation passed
        ~unpromised:(Type_may_not_promise name)
        ~assume:(fun at_call _ -> assume_own_callback_ensures context at_call local)
        values
  | None ->
      check_callback_promises context frame ~location invocation passed
        ~unpromised:
          (match local with
          | Declared { name; _ } -> Type_promises_nothing name
          | Self | Trait_parameter _ | Synthetic _ -> Nothing_promises)
        ~assume:assume_nothing values

let check_callback_requires context frame (site : Invocation.site) through
    (values : State.passed list) =
  match through with
  | Some (_, _, Invocation.Forwarded local) -> (
      match find_own_callback context local with
      | Some (name, { inputs; requires; _ }) when List.length inputs = List.length values ->
          let inside =
            make_callback_contract_frame frame inputs
              (List.map (fun (passed : State.passed) -> passed.term) values)
          in
          List.iter
            (fun (clause : Mir.formula) ->
              Facts.oblige context frame
                (Facts.locate context frame.source site.origin)
                (Callback_precondition
                   {
                     clause = Facts.quote frame.source clause.origin;
                     call = { at = Facts.locate context frame.source site.origin; callee = None };
                     name;
                   })
                (snd (Validity.read_specification context inside clause)))
            requires
      | _ -> ())
  | _ -> ()

let read_named_requires context (frame : State.frame) (clauses : State.clauses) ~entries =
  let inside =
    Contracts.bind_arguments frame clauses
      ~arguments:(List.mapi (fun index entry -> (index, entry)) entries)
      ~substitution:Types.no_substitution
  in
  List.filter_map
    (fun (requirement : Mir.formula) ->
      if Conditions.holds_here context requirement.holds_when then
        Some (snd (Validity.read_specification context inside requirement))
      else None)
    (Facts.list_clauses clauses.requires)

let read_named_ensures context (frame : State.frame) (clauses : State.clauses)
    (expected : Types.function_type) ~entries ~exits ~result =
  let inside =
    Contracts.bind_arguments frame clauses
      ~arguments:(List.mapi (fun index entry -> (index, entry)) entries)
      ~substitution:Types.no_substitution
  in
  let inside =
    List.fold_left2
      (fun (inside : State.frame) (parameter : Mir.parameter) (((mode : Language.Mode.t), _), exit_)
         ->
        match (mode, parameter.local) with
        | Mut, Self -> { inside with self = Some exit_ }
        | Mut, local -> { inside with locals = Locals.add (Core_local local) exit_ inside.locals }
        | (Read | Own), _ -> inside)
      { inside with result = Some result }
      clauses.parameters
      (List.combine expected.inputs exits)
  in
  List.filter_map
    (fun (clause : Mir.formula) ->
      match
        Conditions.find_obligation_condition
          (Conditions.decide context ~substitution:Types.no_substitution clause.holds_when)
      with
      | Some _ -> Some (snd (Validity.read_specification context inside clause))
      | None -> None)
    clauses.ensures

let add_named_relation context frame (expected : Types.function_type) callee_term
    (clauses : State.clauses) =
  let variable label index input =
    (Facts.make_variable label ~numbers:[ index ], Facts.declare_sort context input)
  in
  let inputs =
    List.mapi (fun index (_, input) -> variable "named.argument" index input) expected.inputs
  in
  let changed =
    List.mapi
      (fun index ((mode : Language.Mode.t), input) ->
        match mode with Mut -> Some (variable "named.changed" index input) | Read | Own -> None)
      expected.inputs
  in
  let returned = variable "named.result" 0 expected.output in
  let entries = List.map (fun (name, _) -> Logic.Symbol name) inputs in
  let exits =
    List.map2
      (fun entry changed ->
        match changed with Some (name, _) -> Logic.Symbol name | None -> entry)
      entries changed
  in
  let result = Logic.Symbol (fst returned) in
  let parameters = inputs @ List.filter_map Fun.id changed @ [ returned ] in
  let holds = make_callback_ensures context expected callee_term ~entries ~exits ~result in
  if is_in_the_logic expected then
    Facts.add_frame_fact context frame
      (Logic.forall ~trigger:[ holds ]
         ( parameters,
           Logic.equal holds
             (Logic.equal result (apply_function context expected callee_term entries)) ));
  let mark = Query.count_fresh context.State.query in
  let bound = List.map fst parameters in
  let is_inside_the_relation fact =
    Logic.mentions bound fact || Facts.mentions_fresh_after context mark fact
  in
  let premise, read =
    Query.run_dropping_facts context.query ~drop:is_inside_the_relation (fun () ->
        let premise =
          Logic.conjunction
            (List.map2
               (fun (_, input) entry ->
                 Logic.( &&& ) (Facts.make_in_range input entry)
                   (Validity.make_validity context frame ~assuming:true input entry))
               expected.inputs entries
            @ read_named_requires context frame clauses ~entries)
        in
        (premise, read_named_ensures context frame clauses expected ~entries ~exits ~result))
  in
  match read with
  | [] -> ()
  | ensures when List.exists (Facts.mentions_fresh_after context mark) (premise :: ensures) -> ()
  | ensures ->
      Facts.add_frame_fact context frame
        (Logic.forall ~trigger:[ holds ]
           (parameters, Logic.( ==> ) holds (Logic.( ==> ) premise (Logic.conjunction ensures))))

let check_named_callback context (frame : State.frame) (invocation : Invocation.t)
    (passed : State.passed) ~origin path (contract : State.contract) (values : State.passed list) =
  let location = Facts.locate context frame.source origin in
  let callee_clauses = contract.callee_clauses in
  match find_parameter_type context frame invocation passed.position with
  | Some (Types.Function expected) ->
      let inputs = declare_callback_arguments context frame expected.inputs in
      let known = List.map (fun (passed : State.passed) -> (passed.position, passed.term)) values in
      let promised =
        Logic.conjunction
          (list_callback_facts context frame invocation passed.position known inputs)
      in
      let at_call = Facts.restrict frame promised in
      if List.length callee_clauses.parameters = List.length inputs then (
        let inside =
          Contracts.bind_arguments frame callee_clauses
            ~arguments:(List.mapi (fun index input -> (index, input)) inputs)
            ~substitution:Types.no_substitution
        in
        List.iter
          (fun (requirement : Mir.formula) ->
            Facts.oblige context at_call location
              (Parameter_contract
                 { path; clause = Facts.quote callee_clauses.callee requirement.origin })
              (snd (Validity.read_specification context inside requirement)))
          (Facts.list_clauses callee_clauses.requires);
        if List.length callee_clauses.parameters = List.length expected.inputs then begin
          add_named_relation context frame expected passed.term callee_clauses;
          check_callback_promises context frame ~location invocation passed
            ~unpromised:(Ensures_may_not_promise path)
            ~assume:(fun at_call expected ~entries ~exits ~result ->
              List.iter (Facts.assume context at_call)
                (read_named_ensures context at_call callee_clauses expected ~entries ~exits ~result))
            values
        end)
  | _ ->
      if callee_clauses.requires <> [] then
        Facts.raise_unsupported location Unreadable_parameter_type
