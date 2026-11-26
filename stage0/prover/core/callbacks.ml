let make_state () : State.callback_state = { known = []; is_reading = false }

let note_known (context : State.context) term function_type known =
  if not (List.mem_assoc term context.callbacks.known) then
    context.callbacks.known <- (term, (function_type, known)) :: context.callbacks.known

let find_known (context : State.context) term =
  Option.map snd (List.assoc_opt term context.callbacks.known)

let declare_own context (frame : State.frame) own =
  List.iter
    (fun (local, name, callback) ->
      match
        ( Locals.find_opt (Core_local local) frame.locals,
          Encoding.find_local_type context frame (Core_local local) )
      with
      | Some term, Some (Types.Function function_type) ->
          note_known context term function_type (Own { name; callback })
      | _ -> Facts.raise_bug "the callback parameter `%s` is not a function bound at entry" name)
    own

let apply_function context (function_type : Types.function_type) callee arguments =
  let inputs =
    List.map (fun (_, input) -> Encoding.declare_sort context input) function_type.inputs
  in
  let output = Encoding.declare_sort context function_type.output in
  let value_sort = Encoding.declare_sort context (Types.Function function_type) in
  let symbol = Logic.Symbol.Apply ((value_sort :: inputs) @ [ output ]) in
  Facts.declare context (Logic.Function (symbol, value_sort :: inputs, output));
  Logic.Apply (symbol, callee :: arguments)

let returns_value (function_type : Types.function_type) =
  not (Types.equal function_type.output Types.unit)

let make_input_variables context (function_type : Types.function_type) ~label ~numbers =
  List.mapi
    (fun index (_, input) ->
      ( Facts.make_variable (label ^ ".argument") ~numbers:(numbers @ [ index ]),
        Encoding.declare_sort context input ))
    function_type.inputs

type relation_variables = {
  inputs : (Logic.symbol * Logic.sort) list;
  changed : (int * (Logic.symbol * Logic.sort)) list;
  returned : (Logic.symbol * Logic.sort) list;
  entries : Logic.term list;
  exits : Logic.term list;
  result : Logic.term;
}

let make_relation_variables context (function_type : Types.function_type) ~label ~numbers =
  let inputs = make_input_variables context function_type ~label ~numbers in
  let changed =
    List.filter_map
      (fun (index, ((mode : Language.Mode.t), input)) ->
        match mode with
        | Mut ->
            Some
              ( index,
                ( Facts.make_variable (label ^ ".changed") ~numbers:(numbers @ [ index ]),
                  Encoding.declare_sort context input ) )
        | Read | Own -> None)
      (List.mapi (fun index input -> (index, input)) function_type.inputs)
  in
  let returned =
    if returns_value function_type then
      [
        ( Facts.make_variable (label ^ ".result") ~numbers,
          Encoding.declare_sort context function_type.output );
      ]
    else []
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
  { inputs; changed; returned; entries; exits; result }

let make_callback_ensures context (function_type : Types.function_type) callee ~entries ~exits
    ~result =
  let sorts =
    Encoding.declare_sort context (Types.Function function_type)
    :: List.concat_map
         (fun ((mode : Language.Mode.t), input) ->
           let sort = Encoding.declare_sort context input in
           match mode with Mut -> [ sort; sort ] | Read | Own -> [ sort ])
         function_type.inputs
    @
    if returns_value function_type then [ Encoding.declare_sort context function_type.output ]
    else []
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

let declare_arguments context frame inputs =
  List.map
    (fun (_, input) ->
      let input = Encoding.substitute_type context frame input in
      let term = Encoding.arrive context frame "argument" input in
      Validity.assume_valid context frame input term;
      term)
    inputs

let declare_results context frame (function_type : Types.function_type) entries =
  let exits =
    List.map2
      (fun ((mode : Language.Mode.t), input) entry ->
        match mode with
        | Mut ->
            let input = Encoding.substitute_type context frame input in
            let exit_ = Encoding.arrive context frame "changed" input in
            Validity.assume_valid context frame input exit_;
            exit_
        | Read | Own -> entry)
      function_type.inputs entries
  in
  let output = Encoding.substitute_type context frame function_type.output in
  let result = Encoding.arrive context frame "result" output in
  Validity.assume_valid context frame output result;
  (exits, result)

let run_reading_callback : 'a. _ -> (unit -> 'a) -> 'a =
 fun (context : State.context) read ->
  let saved = context.callbacks.is_reading in
  context.callbacks.is_reading <- true;
  Fun.protect ~finally:(fun () -> context.callbacks.is_reading <- saved) read

type parameter_contract = (State.source * State.frame * Mir.callback) option

let bind_inputs (frame : State.frame) inputs terms =
  List.fold_left2
    (fun locals input term -> Locals.add (Core_local input) term locals)
    frame.old_locals inputs terms

let read_clauses context (source : State.source) inside clauses =
  List.map
    (fun (clause : Mir.formula) ->
      (Facts.quote source clause.origin, snd (Validity.read_specification context inside clause)))
    clauses

let read_requires context (stated : parameter_contract) arguments =
  match stated with
  | Some (source, inside, { inputs; requires; _ }) ->
      read_clauses context source
        {
          inside with
          locals = bind_inputs inside inputs arguments;
          self = inside.old_self;
          makes_obligations = false;
        }
        requires
  | None -> []

let read_ensures context (stated : parameter_contract) ~entries ~exits ~result =
  match stated with
  | Some (source, inside, { inputs; ensures; _ }) ->
      read_clauses context source
        {
          inside with
          locals = bind_inputs inside inputs exits;
          old_locals = bind_inputs inside inputs entries;
          self = inside.old_self;
          result = Some result;
          makes_obligations = false;
        }
        ensures
  | None -> []

let find_named context frame path instantiation : State.known_function option =
  let callee =
    Callee.resolve context frame
      (Core.Function { path; instantiation })
      ~lends:None ~uses:Types.no_capabilities
  in
  match callee.target with
  | Definition { contract = Some contract; substitution_of; type_arguments; _ } ->
      Some
        (Named
           { path; contract; substitution_of; type_arguments; group_member = callee.group_member })
  | Definition { contract = None; _ } | Function_value | Intrinsic _ -> None

let number terms = List.mapi (fun position term -> (position, term)) terms

let read_holding context (clauses : State.clauses) ~substitution inside formulas =
  read_clauses context clauses.callee inside
    (List.filter
       (fun (clause : Mir.formula) -> Conditions.holds_here context ~substitution clause.holds_when)
       formulas)

let list_requires context (frame : State.frame) (known : State.known_function) arguments =
  match known with
  | Named { substitution_of; contract; _ } ->
      let clauses = Contracts.select_precondition_clauses contract in
      let substitution = substitution_of clauses in
      read_holding context clauses ~substitution
        (Contracts.make_entry_frame frame clauses ~arguments:(number arguments) ~substitution)
        (Facts.list_clauses clauses.requires)
  | Own { callback; _ } -> read_requires context (Some (frame.source, frame, callback)) arguments

let list_ensures context (frame : State.frame) (known : State.known_function) ~entries ~exits
    ~result =
  List.map snd
    (match known with
    | Named { substitution_of; contract; _ } ->
        let clauses = contract.callee_clauses in
        let substitution = substitution_of clauses in
        read_holding context clauses ~substitution
          (Contracts.make_exit_frame frame clauses ~entries:(number entries) ~exits:(number exits)
             ~result:(Some result) ~substitution)
          clauses.ensures
    | Own { callback; _ } ->
        read_ensures context (Some (frame.source, frame, callback)) ~entries ~exits ~result)

let has_requires : State.known_function -> bool = function
  | Named { contract; _ } -> (Contracts.select_precondition_clauses contract).requires <> []
  | Own { callback; _ } -> callback.requires <> []

type use = Called | Not_called of Catalog.Prover.function_use

let check_requires context frame location (known : State.known_function) ~use arguments =
  let describe clause : Catalog.Prover.obligation =
    match (use, known) with
    | Called, Named { path; _ } ->
        Precondition_may_fail { clause; call = { at = location; callee = Some path } }
    | Called, Own { name; _ } ->
        Callback_precondition { clause; call = { at = location; callee = None }; name }
    | Not_called use, Named { path; _ } ->
        Function_requirement { function_ = Named_function path; use; clause }
    | Not_called use, Own { name; _ } ->
        Function_requirement { function_ = Callback_parameter name; use; clause }
  in
  List.iter
    (fun (clause, term) -> Obligations.oblige context frame location (describe clause) term)
    (list_requires context frame known arguments)

let check_escaping context frame location known (function_type : Types.function_type) =
  if has_requires known then
    check_requires context frame location known
      ~use:(Not_called (Used_as_value (Types.Function function_type)))
      (declare_arguments context frame function_type.inputs)

let check_read (context : State.context) (frame : State.frame) term =
  if frame.makes_obligations && not context.callbacks.is_reading then
    match List.assoc_opt term context.callbacks.known with
    | Some (function_type, (Own { callback = { requires = first :: _; _ }; _ } as known)) ->
        check_escaping context frame
          (Facts.locate context frame.source first.origin)
          known function_type
    | Some (_, (Own _ | Named _)) | None -> ()

let check_passed context (frame : State.frame) ~at (callee : Callee.t) (passed : State.passed)
    ~arguments =
  let known = find_known context passed.term in
  let location = Facts.locate context frame.source (Option.value passed.origin ~default:at) in
  match (Callee.find_parameter_type context callee passed.position, passed.type_) with
  | Some (Types.Function expected), _ ->
      let stated = Callee.find_callback context frame callee passed.position ~known:arguments in
      let promises =
        match stated with Some (_, _, { ensures = _ :: _; _ }) -> true | Some _ | None -> false
      in
      if promises || Option.fold ~none:false ~some:has_requires known then begin
        let entries = declare_arguments context frame expected.inputs in
        let at_call =
          Facts.restrict frame
            (Logic.conjunction (List.map snd (read_requires context stated entries)))
        in
        Option.iter
          (fun known ->
            check_requires context at_call location known ~use:(Not_called Passed_for_parameter)
              entries)
          known;
        if promises then begin
          let exits, result = declare_results context frame expected entries in
          Option.iter
            (fun known ->
              List.iter (Facts.assume context at_call)
                (list_ensures context at_call known ~entries ~exits ~result))
            known;
          let unpromised : Catalog.Prover.unpromised =
            match known with
            | Some (Named { path; _ }) -> Ensures_may_not_promise path
            | Some (Own { name; _ }) -> Type_may_not_promise name
            | None -> Nothing_promises
          in
          List.iter
            (fun (promise, term) ->
              Obligations.oblige context at_call location
                (Callback_promise { promise; unpromised })
                term)
            (read_ensures context stated ~entries ~exits ~result)
        end
      end
  | _, Types.Function passed_type ->
      Option.iter (fun known -> check_escaping context frame location known passed_type) known
  | _, _ -> ()

let check_called context (frame : State.frame) (site : Invocation.site) called arguments =
  Option.iter
    (fun known ->
      check_requires context frame
        (Facts.locate context frame.source site.origin)
        known ~use:Called arguments)
    (find_known context called)

let assume_returned context frame (function_type : Types.function_type) called ~entries ~exits
    ~result =
  Facts.assume context frame
    (make_callback_ensures context function_type called ~entries ~exits ~result);
  Option.iter
    (fun known ->
      List.iter (Facts.assume context frame)
        (list_ensures context frame known ~entries ~exits ~result))
    (find_known context called)

let find_logic_link context (function_type : Types.function_type) term =
  if is_in_the_logic function_type && returns_value function_type then
    let { inputs; returned; entries; result; _ } =
      make_relation_variables context function_type ~label:"relation" ~numbers:[]
    in
    let holds = make_callback_ensures context function_type term ~entries ~exits:entries ~result in
    Some
      (Logic.forall ~trigger:[ holds ]
         ( inputs @ returned,
           Logic.equal holds
             (Logic.equal result (apply_function context function_type term entries)) ))
  else None

let state_relation context (frame : State.frame) (function_type : Types.function_type) term known =
  let { inputs; changed; returned; entries; exits; result } =
    make_relation_variables context function_type ~label:"named" ~numbers:[]
  in
  let parameters = inputs @ List.map snd changed @ returned in
  let holds = make_callback_ensures context function_type term ~entries ~exits ~result in
  let mark = Query.mark context.State.query in
  let bound = List.map fst parameters in
  let is_inside_the_relation fact =
    Logic.mentions bound fact || Facts.mentions_fresh_since context mark fact
  in
  let premise, ensures =
    Query.run_dropping_facts context.query ~drop:is_inside_the_relation (fun () ->
        ( Logic.conjunction
            (List.map2
               (fun (_, input) entry ->
                 Logic.( &&& )
                   (Encoding.make_in_range input entry)
                   (Validity.make_validity context frame ~assuming:true input entry))
               function_type.inputs entries
            @ List.map snd (list_requires context frame known entries)),
          list_ensures context frame known ~entries ~exits ~result ))
  in
  if
    ensures <> []
    && not (List.exists (Facts.mentions_fresh_since context mark) (premise :: ensures))
  then
    Facts.add_frame_fact context frame
      (Logic.forall ~trigger:[ holds ]
         (parameters, Logic.( ==> ) holds (Logic.( ==> ) premise (Logic.conjunction ensures))))

let state_definition context (frame : State.frame) (function_type : Types.function_type) term ~path
    ~contract ~substitution_of ~type_arguments ~group_member =
  let parameters =
    make_input_variables context function_type ~label:"parameter"
      ~numbers:[ List.length frame.bound ]
  in
  let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
  let sorts = List.map snd parameters in
  let symbol =
    Contract_axioms.declare_function context ~path ~type_arguments ~sorts
      ~result_type:function_type.output
  in
  let value = Logic.Apply (symbol, inputs) in
  Contract_axioms.state context frame
    { symbol; sorts; term = value; is_limited = false }
    contract ~substitution_of ~result_type:function_type.output ~group_member
    ~is_on_bound_values:true;
  Facts.add_frame_fact context frame
    (Logic.forall
       (parameters, Logic.equal (apply_function context function_type term inputs) value))

let read_named_function (context : State.context) (frame : State.frame) (site : Invocation.site)
    path instantiation ~is_argument =
  let location = Facts.locate context frame.source site.origin in
  let type_ = Encoding.substitute_type context frame site.type_ in
  match (find_named context frame path instantiation, type_) with
  | ( Some (Named { contract; substitution_of; type_arguments; group_member; _ } as known),
      Types.Function function_type ) ->
      if frame.makes_obligations && not is_argument then
        check_escaping context frame location known function_type;
      if
        frame.makes_obligations
        && Types.states_no_allocation function_type.costs
        && context.lookups.may_abort path
      then
        Obligations.oblige context frame location
          (May_not_return_under_no_allocation (Named_function path)) (Logic.Boolean false);
      let symbol = Logic.Symbol.Function_value { callee = path; type_arguments } in
      Facts.declare context (Logic.Constant (symbol, Encoding.declare_sort context type_));
      let term = Logic.Symbol symbol in
      note_known context term function_type known;
      Facts.run_once context (Value_of symbol) (fun () ->
          if is_in_the_logic function_type && contract.is_logic_function then
            state_definition context frame function_type term ~path ~contract ~substitution_of
              ~type_arguments ~group_member;
          Option.iter
            (Facts.add_frame_fact context frame)
            (find_logic_link context function_type term);
          state_relation context frame function_type term known);
      term
  | _ -> Facts.raise_unsupported location Unreadable_function_value
