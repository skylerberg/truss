type state = { mutable named : (Logic.term * (Types.function_type * State.known_function)) list }

let state = Private_state.make_key (fun () -> { named = [] })

let note_named (query : Query.t) term function_type known =
  let state = Query.read_state query state in
  if not (List.mem_assoc term state.named) then
    state.named <- (term, (function_type, known)) :: state.named

let find_typed (frame : State.frame) term =
  match List.assoc_opt term frame.callbacks with
  | Some _ as own -> own
  | None -> List.assoc_opt term (Query.read_state frame.query state).named

let find_known (frame : State.frame) term = Option.map snd (find_typed frame term)

let bind_own (frame : State.frame) own =
  List.fold_left
    (fun (frame : State.frame) (local, name, callback) ->
      match
        ( Locals.find_opt (Core_local local) frame.locals,
          Encoding.find_local_type frame (Core_local local) )
      with
      | Some term, Some (Types.Function function_type) ->
          {
            frame with
            callbacks = (term, (function_type, State.Own { name; callback })) :: frame.callbacks;
          }
      | _ -> Facts.raise_bug "the callback parameter `%s` is not a function bound at entry" name)
    frame own

let apply_function (function_type : Types.function_type) callee arguments =
  let inputs = List.map (fun (_, input) -> Encoding.sort_of input) function_type.inputs in
  let output = Encoding.sort_of function_type.output in
  let value_sort = Encoding.sort_of (Types.Function function_type) in
  let symbol = Logic.Symbol.Apply ((value_sort :: inputs) @ [ output ]) in
  Logic.Apply (symbol, callee :: arguments)

let returns_value (function_type : Types.function_type) =
  not (Types.equal function_type.output Types.unit)

let make_input_variables (function_type : Types.function_type) ~label ~numbers =
  List.mapi
    (fun index (_, input) ->
      ( Query.make_variable (label ^ ".argument") ~numbers:(numbers @ [ index ]),
        Encoding.sort_of input ))
    function_type.inputs

type relation_variables = {
  inputs : (Logic.symbol * Logic.sort) list;
  changed : (int * (Logic.symbol * Logic.sort)) list;
  returned : (Logic.symbol * Logic.sort) list;
  entries : Logic.term list;
  exits : Logic.term list;
  result : Logic.term;
}

let make_relation_variables (function_type : Types.function_type) ~label ~numbers =
  let inputs = make_input_variables function_type ~label ~numbers in
  let changed =
    List.filter_map
      (fun (index, ((mode : Language.Mode.t), input)) ->
        match mode with
        | Mut ->
            Some
              ( index,
                ( Query.make_variable (label ^ ".changed") ~numbers:(numbers @ [ index ]),
                  Encoding.sort_of input ) )
        | Read | Own -> None)
      (List.mapi (fun index input -> (index, input)) function_type.inputs)
  in
  let returned =
    if returns_value function_type then
      [ (Query.make_variable (label ^ ".result") ~numbers, Encoding.sort_of function_type.output) ]
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

let make_callback_ensures (function_type : Types.function_type) callee ~entries ~exits ~result =
  let sorts =
    Encoding.sort_of (Types.Function function_type)
    :: List.concat_map
         (fun ((mode : Language.Mode.t), input) ->
           let sort = Encoding.sort_of input in
           match mode with Mut -> [ sort; sort ] | Read | Own -> [ sort ])
         function_type.inputs
    @ if returns_value function_type then [ Encoding.sort_of function_type.output ] else []
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
  Logic.Apply (symbol, callee :: arguments)

let apply_callback_ensures (function_type : Types.function_type) values =
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
      | [ result ] -> make_callback_ensures function_type callee ~entries ~exits ~result
      | [] when not (returns_value function_type) ->
          make_callback_ensures function_type callee ~entries ~exits
            ~result:(Logic.Apply (Logic.Symbol.Unit, []))
      | _ -> Facts.raise_bug "`.ensures` with arguments that do not match its function type")
  | [] -> Facts.raise_bug "`.ensures` without the function it describes"

let is_in_the_logic (function_type : Types.function_type) =
  function_type.uses = Types.no_capabilities
  && List.for_all (fun (mode, _) -> mode <> Language.Mode.Mut) function_type.inputs

let declare_arguments (frame : State.frame) inputs =
  List.map
    (fun (_, input) ->
      let input = Encoding.substitute_type frame input in
      let term = Encoding.arrive frame "argument" input in
      Validity.assume_valid frame input term;
      term)
    inputs

let declare_results (frame : State.frame) (function_type : Types.function_type) entries =
  let exits =
    List.map2
      (fun ((mode : Language.Mode.t), input) entry ->
        match mode with
        | Mut ->
            let input = Encoding.substitute_type frame input in
            let exit_ = Encoding.arrive frame "changed" input in
            Validity.assume_valid frame input exit_;
            exit_
        | Read | Own -> entry)
      function_type.inputs entries
  in
  let output = Encoding.substitute_type frame function_type.output in
  let result = Encoding.arrive frame "result" output in
  Validity.assume_valid frame output result;
  (exits, result)

type parameter_contract = (State.source * State.frame * Mir.callback) option

let bind_inputs (frame : State.frame) inputs terms =
  List.fold_left2
    (fun locals input term -> Locals.add (Core_local input) term locals)
    frame.old_locals inputs terms

let read_clauses (source : State.source) inside clauses =
  List.map
    (fun (clause : Mir.formula) ->
      (Facts.quote source clause.origin, snd (Validity.read_specification inside clause)))
    clauses

let read_requires (stated : parameter_contract) arguments =
  match stated with
  | Some (source, inside, { inputs; requires; _ }) ->
      read_clauses source
        {
          inside with
          locals = bind_inputs inside inputs arguments;
          self = inside.old_self;
          makes_obligations = false;
        }
        requires
  | None -> []

let read_ensures (stated : parameter_contract) ~entries ~exits ~result =
  match stated with
  | Some (source, inside, { inputs; ensures; _ }) ->
      read_clauses source
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

let find_named (frame : State.frame) path instantiation : State.known_function option =
  let callee =
    Callee.resolve frame
      (Core.Function { path; instantiation })
      ~lends:None ~uses:Types.no_capabilities
  in
  match callee.target with
  | Definition ({ contract = Some contract; substitution_of; type_arguments; _ } as definition) ->
      Some
        (Named
           {
             path;
             contract;
             substitution_of;
             type_arguments;
             group_member = callee.group_member;
             may_abort = Callee.may_abort frame.environment definition;
           })
  | Definition { contract = None; _ } | Function_value | Intrinsic _ -> None

let number terms = List.mapi (fun position term -> (position, term)) terms

let read_holding (environment : State.environment) (query : Query.t) (clauses : State.clauses)
    ~substitution inside formulas =
  read_clauses clauses.callee inside
    (List.filter
       (fun (clause : Mir.formula) ->
         Conditions.holds_here environment query ~substitution clause.holds_when)
       formulas)

let list_requires (frame : State.frame) (known : State.known_function) arguments =
  match known with
  | Named { substitution_of; contract; _ } ->
      let clauses = Contracts.select_precondition_clauses contract in
      let substitution = substitution_of clauses in
      read_holding frame.environment frame.query clauses ~substitution
        (Contracts.make_entry_frame frame clauses ~arguments:(number arguments) ~substitution)
        (Facts.list_clauses clauses.requires)
  | Own { callback; _ } -> read_requires (Some (frame.source, frame, callback)) arguments

let list_ensures (frame : State.frame) (known : State.known_function) ~entries ~exits ~result =
  match known with
  | Named { substitution_of; contract; _ } ->
      let clauses = contract.callee_clauses in
      let substitution = substitution_of clauses in
      read_holding frame.environment frame.query clauses ~substitution
        (Contracts.make_exit_frame frame clauses ~entries:(number entries) ~exits:(number exits)
           ~result:(Some result) ~substitution)
        clauses.ensures
  | Own { callback; _ } ->
      read_ensures (Some (frame.source, frame, callback)) ~entries ~exits ~result

let specify_parameter (stated : parameter_contract) : Specification.t =
  {
    list_requires = read_requires stated;
    list_ensures = read_ensures stated;
    has_ensures =
      (match stated with Some (_, _, { ensures = _ :: _; _ }) -> true | Some _ | None -> false);
  }

let specify_known (known : State.known_function) (frame : State.frame) : Specification.t =
  {
    list_requires = list_requires frame known;
    list_ensures = list_ensures frame known;
    has_ensures = true;
  }

let has_requires : State.known_function -> bool = function
  | Named { contract; _ } -> (Contracts.select_precondition_clauses contract).requires <> []
  | Own { callback; _ } -> callback.requires <> []

type use = Called | Not_called of Catalog.Prover.function_use

let describe_requirement location (known : State.known_function) ~use clause :
    Catalog.Prover.obligation =
  match (use, known) with
  | Called, Named { path; _ } ->
      Precondition_may_fail { clause; call = { at = location; callee = Some path } }
  | Called, Own { name; _ } ->
      Callback_precondition { clause; call = { at = location; callee = None }; name }
  | Not_called use, Named { path; _ } ->
      Function_requirement { function_ = Named_function path; use; clause }
  | Not_called use, Own { name; _ } ->
      Function_requirement { function_ = Callback_parameter name; use; clause }

let check_requires (frame : State.frame) location (known : State.known_function) ~use arguments =
  Specification.oblige_requires frame location (specify_known known frame) arguments
    ~describe:(describe_requirement location known ~use)

let check_escaping (frame : State.frame) location known (function_type : Types.function_type) =
  if has_requires known then
    let _, supposed = Facts.suppose frame "called" in
    check_requires supposed location known
      ~use:(Not_called (Used_as_value (Types.Function function_type)))
      (declare_arguments supposed function_type.inputs)

let check_read (frame : State.frame) term =
  if frame.makes_obligations && not frame.is_reading_callback then
    match find_typed frame term with
    | Some (function_type, (Own { callback = { requires = first :: _; _ }; _ } as known)) ->
        check_escaping frame (Facts.locate frame first.origin) known function_type
    | Some (_, (Own _ | Named _)) | None -> ()

let check_passed (frame : State.frame) ~at (callee : Callee.t) (passed : State.passed) ~arguments =
  let known = find_known frame passed.term in
  let location = Facts.locate frame (Option.value passed.origin ~default:at) in
  match (Callee.find_parameter_type frame.environment callee passed.position, passed.type_) with
  | Some (Types.Function expected), _ ->
      let stated =
        specify_parameter (Callee.find_callback frame callee passed.position ~known:arguments)
      in
      if stated.has_ensures || Option.fold ~none:false ~some:has_requires known then begin
        let _, supposed = Facts.suppose frame "called" in
        let unpromised : Catalog.Prover.unpromised =
          match known with
          | Some (Named { path; _ }) -> Ensures_may_not_promise path
          | Some (Own { name; _ }) -> Type_may_not_promise name
          | None -> Nothing_promises
        in
        let entries = declare_arguments supposed expected.inputs in
        Specification.refine supposed location
          ~by:
            (Option.map
               (fun known ->
                 ( specify_known known,
                   describe_requirement location known ~use:(Not_called Passed_for_parameter) ))
               known)
          stated entries
          ~havoc:(fun () -> declare_results supposed expected entries)
          ~describe_ensures:(fun promise -> Callback_promise { promise; unpromised })
      end
  | _, Types.Function passed_type ->
      Option.iter (fun known -> check_escaping frame location known passed_type) known
  | _, _ -> ()

let check_called (frame : State.frame) (site : Invocation.site) called arguments =
  Option.iter
    (fun known -> check_requires frame (Facts.locate frame site.origin) known ~use:Called arguments)
    (find_known frame called)

let list_called_requires (frame : State.frame) called arguments =
  match find_known frame called with
  | Some known -> List.map snd (list_requires frame known arguments)
  | None -> []

let assume_returned (frame : State.frame) (function_type : Types.function_type) called ~entries
    ~exits ~result =
  Facts.assume frame (make_callback_ensures function_type called ~entries ~exits ~result);
  Option.iter
    (fun known ->
      Specification.assume_ensures frame (specify_known known frame) ~entries ~exits ~result)
    (find_known frame called)

let find_logic_link (function_type : Types.function_type) term =
  if is_in_the_logic function_type && returns_value function_type then
    let { inputs; returned; entries; result; _ } =
      make_relation_variables function_type ~label:"relation" ~numbers:[]
    in
    let holds = make_callback_ensures function_type term ~entries ~exits:entries ~result in
    Some
      (Logic.forall ~trigger:[ holds ]
         ( inputs @ returned,
           Logic.equal holds (Logic.equal result (apply_function function_type term entries)) ))
  else None

let state_relation (frame : State.frame) (function_type : Types.function_type) term known ~proven_by
    =
  let { inputs; changed; returned; entries; exits; result } =
    make_relation_variables function_type ~label:"named" ~numbers:[]
  in
  let parameters = inputs @ List.map snd changed @ returned in
  let holds = make_callback_ensures function_type term ~entries ~exits ~result in
  let mark = Query.mark frame.query in
  let bound = List.map fst parameters in
  let is_inside_the_relation fact =
    Logic.mentions bound fact || Query.mentions_fresh_since frame.query mark fact
  in
  let premise, ensures =
    Query.run_dropping_facts frame.query ~drop:is_inside_the_relation (fun () ->
        ( Logic.conjunction
            (List.map2
               (fun (_, input) entry ->
                 Logic.( &&& )
                   (Encoding.make_in_range input entry)
                   (Validity.make_validity frame ~assuming:true input entry))
               function_type.inputs entries
            @ List.map snd (list_requires frame known entries)),
          List.map snd (list_ensures frame known ~entries ~exits ~result) ))
  in
  if
    ensures <> []
    && not (List.exists (Query.mentions_fresh_since frame.query mark) (premise :: ensures))
  then
    Facts.add_theorem frame ~because:(Proven_by proven_by)
      (Logic.forall ~trigger:[ holds ]
         (parameters, Logic.( ==> ) holds (Logic.( ==> ) premise (Logic.conjunction ensures))))

let state_definition (frame : State.frame) (function_type : Types.function_type) term ~path
    ~contract ~substitution_of ~type_arguments ~group_member =
  let parameters =
    make_input_variables function_type ~label:"parameter" ~numbers:[ List.length frame.bound ]
  in
  let inputs = List.map (fun (name, _) -> Logic.Symbol name) parameters in
  let sorts = List.map snd parameters in
  let symbol =
    Contract_axioms.declare_function frame.query ~path ~type_arguments ~sorts
      ~result_type:function_type.output
  in
  let value = Logic.Apply (symbol, inputs) in
  Contract_axioms.state frame
    { symbol; sorts; term = value; is_limited = false }
    contract ~substitution_of ~result_type:function_type.output ~group_member
    ~is_on_bound_values:true;
  Facts.add_theorem frame ~because:(Defines term)
    (Logic.forall (parameters, Logic.equal (apply_function function_type term inputs) value))

let read_named_function (frame : State.frame) (site : Invocation.site) path instantiation
    ~is_argument =
  let location = Facts.locate frame site.origin in
  let type_ = Encoding.substitute_type frame site.type_ in
  match (find_named frame path instantiation, type_) with
  | ( Some (Named { contract; substitution_of; type_arguments; group_member; may_abort; _ } as known),
      Types.Function function_type ) ->
      if frame.makes_obligations && not is_argument then
        check_escaping frame location known function_type;
      if frame.makes_obligations && Types.states_no_allocation function_type.costs && may_abort then
        Obligations.oblige frame location (May_not_return_under_no_allocation (Named_function path))
          (Logic.Boolean false);
      let symbol = Logic.Symbol.Function_value { callee = path; type_arguments } in
      Query.declare frame.query (Logic.Constant (symbol, Encoding.sort_of type_));
      let term = Logic.Symbol symbol in
      note_named frame.query term function_type known;
      Query.run_once frame.query (Value_of symbol) (fun () ->
          if not may_abort then begin
            if is_in_the_logic function_type && contract.is_logic_function then
              state_definition frame function_type term ~path ~contract ~substitution_of
                ~type_arguments ~group_member;
            Option.iter
              (Facts.add_theorem frame ~because:Lemma)
              (find_logic_link function_type term)
          end;
          state_relation frame function_type term known ~proven_by:path);
      term
  | _ -> Facts.raise_unsupported location Unreadable_function_value
