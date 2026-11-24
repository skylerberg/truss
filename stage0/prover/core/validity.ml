let find_selected_place (context : State.context) selection =
  let shift offset : State.place_value -> State.place_value = function
    | One index -> One (Costs.plus offset index)
    | Run (start, stop) -> Run (Costs.plus offset start, Costs.plus offset stop)
  in
  let rec find_from offset = function
    | [] -> Facts.raise_bug "a selection of no range or element"
    | [ innermost ] ->
        Option.map
          (fun (noted : State.noted_place) -> shift offset noted.value)
          (List.assoc_opt innermost context.indexes)
    | range :: inner -> (
        match List.assoc_opt range context.indexes with
        | Some { value = Run (start, _); _ } -> find_from (Costs.plus offset start) inner
        | Some { value = One _; _ } -> Facts.raise_bug "a selection that selects inside an element"
        | None -> None)
  in
  find_from (Logic.int 0) selection

let read_innermost selection =
  match List.rev selection with
  | innermost :: _ -> innermost
  | [] -> Facts.raise_bug "a selection of no range or element"

let note_place (context : State.context) (frame : State.frame) ~node ~origin value =
  let mentions (first, second) = List.mem node first || List.mem node second in
  if Facts.is_home context frame.source && List.exists mentions context.disjoint then begin
    context.indexes <- (node, { State.origin; value }) :: context.indexes;
    let quote selection =
      Facts.quote frame.source (List.assoc (read_innermost selection) context.indexes).origin
    in
    let outside index start stop = Logic.(less index start ||| less_equal stop index) in
    List.iter
      (fun (first, second) ->
        if read_innermost first = node || read_innermost second = node then
          match (find_selected_place context first, find_selected_place context second) with
          | Some left, Some right ->
              let apart =
                match (left, right) with
                | One left, One right -> Logic.not_ (Logic.equal left right)
                | One index, Run (start, stop) | Run (start, stop), One index ->
                    outside index start stop
                | Run (start, stop), Run (other_start, other_stop) ->
                    Logic.disjunction
                      [
                        Logic.less_equal stop other_start;
                        Logic.less_equal other_stop start;
                        Logic.less_equal stop start;
                        Logic.less_equal other_stop other_start;
                      ]
              in
              Facts.oblige context frame
                (Facts.locate context frame.source origin)
                (May_alias { first = quote first; second = quote second })
                apart
          | _ -> ())
      context.disjoint
  end

let run_without_costs : 'a. _ -> (unit -> 'a) -> 'a =
 fun (context : State.context) read ->
  let saved = context.counters in
  context.counters <- [];
  Fun.protect ~finally:(fun () -> context.counters <- saved) read

let run_as_specification (context : State.context) read =
  let panics = context.panics in
  context.panics <- false;
  Fun.protect
    ~finally:(fun () -> context.panics <- panics)
    (fun () -> run_without_costs context read)

let read_specification (context : State.context) frame (formula : Mir.formula) =
  run_as_specification context (fun () -> context.read_formula frame formula ~arguments:[])

let select_field context ty variant field term =
  match (term, Facts.find_constructors context ty) with
  | Logic.Apply (name, arguments), Some shape when name = Facts.make_constructor_symbol ty variant
    -> (
      let fields = Option.value (List.assoc_opt variant shape) ~default:[] in
      match List.find_index (fun (named, _) -> named = field) fields with
      | Some index when index < List.length arguments -> List.nth arguments index
      | _ -> Logic.Apply (Facts.make_selector_symbol ty variant field, [ term ]))
  | _ -> Logic.Apply (Facts.make_selector_symbol ty variant field, [ term ])

let replace_field context ty variant field whole new_value =
  match Option.bind (Facts.find_constructors context ty) (List.assoc_opt variant) with
  | Some fields ->
      Logic.Apply
        ( Facts.make_constructor_symbol ty variant,
          List.map
            (fun (name, _) ->
              if name = field then new_value else select_field context ty variant name whole)
            fields )
  | None -> Facts.raise_unsupported Whole_definition (Fields_of ty)

let find_record_field_type context ty field =
  match Facts.find_constructors context ty with
  | Some [ (None, fields) ] -> List.assoc_opt field fields
  | Some _ | None -> None

let rec find_part context ty term = function
  | [] -> Some (ty, term)
  | field :: fields ->
      Option.bind (find_record_field_type context ty field) (fun field_type ->
          find_part context field_type (select_field context ty None field term) fields)

let rec replace_part context ty whole fields make_part =
  match fields with
  | [] -> Some (make_part ty)
  | field :: fields ->
      Option.bind (find_record_field_type context ty field) (fun field_type ->
          Option.map
            (replace_field context ty None field whole)
            (replace_part context field_type
               (select_field context ty None field whole)
               fields make_part))

let make_type_frame context frame source (ty : Types.ty) ~self =
  let substitution =
    match Facts.find_visible_type context ty with
    | Some (_, substitution) -> substitution
    | None -> Types.no_substitution
  in
  {
    frame with
    State.source;
    locals = Locals.empty;
    types = Locals.empty;
    old_locals = Locals.empty;
    self;
    old_self = self;
    self_type = Some ty;
    result = None;
    makes_obligations = false;
    substitution;
  }

let find_type_declaration (context : State.context) (ty : Types.ty) =
  match ty with
  | Types.Named { path; _ } -> (
      match Tables.Path_table.find_opt context.type_clauses path with
      | Some declaration -> declaration
      | None ->
          let declaration =
            if Resolve.Names.find_kind context.lookups.interface.names path = Some Type then
              Option.map
                (fun (source, _, _) ->
                  ( source,
                    lazy
                      (Option.map
                         (fun ({ form; _ } : Mir.type_clauses Mir.sourced) -> form)
                         (Mir.read_type_clauses context.lookups.mir path)) ))
                (Contracts.find_source context.lookups path)
            else None
          in
          Tables.Path_table.replace context.type_clauses path declaration;
          declaration)
  | _ -> None

let find_type_source context ty = Option.map fst (find_type_declaration context ty)

let find_type_clauses context ty =
  Option.bind (find_type_declaration context ty) (fun (source, clauses) ->
      Option.map (fun clauses -> (source, clauses)) (Lazy.force clauses))

let list_invariants (clauses : Mir.loop_clause list) =
  List.filter_map (function Mir.Invariant value -> Some value | _ -> None) clauses

let find_invariants context (ty : Types.ty) =
  match find_type_clauses context ty with
  | Some (source, { invariants = _ :: _ as invariants; _ }) ->
      Some (source, List.map (fun (invariant : Mir.requirement) -> invariant.clause) invariants)
  | _ -> None

let find_module (context : State.context) path =
  Option.map
    (fun (key : Resolve.Names.key) -> key.module_)
    (context.lookups.interface.names.find_key path)

let is_private_to_another_module (context : State.context) ~current path =
  match context.lookups.interface.names.find_key path with
  | Some key ->
      (context.lookups.interface.names.read_declaration key).visibility = Resolve.Names.Private
      && Some key.module_ <> current
  | None -> false

let names_private_definition context ~current (clause : Mir.formula) =
  let is_hidden = ref false in
  Mir.iter_formula
    (fun statement ->
      List.iter
        (fun (edge : Mir.Call_edges.edge) ->
          let paths = match edge with Calls path -> [ path ] | Supplies { code; _ } -> code in
          if List.exists (is_private_to_another_module context ~current) paths then
            is_hidden := true)
        (Mir.Call_edges.list_statement_edges context.lookups.interface Types.no_substitution
           statement))
    clause;
  !is_hidden

let apply_opaque_validity context ty term =
  let symbol = Logic.Symbol.Valid ty in
  Facts.declare context (Logic.Function (symbol, [ Facts.declare_sort context ty ], Logic.Bool));
  Logic.Apply (symbol, [ term ])

let rec make_validity (context : State.context) frame ~assuming ?(deep = true)
    ?(includes_invariants = true) ?(seen = []) ty term =
  if List.exists (Types.equal ty) seen || List.exists (Types.equal ty) context.validating then
    Logic.Boolean true
  else
    let validating = context.validating in
    context.validating <- ty :: validating;
    Fun.protect ~finally:(fun () -> context.validating <- validating) @@ fun () ->
    let invariants_hold =
      match find_invariants context ty with
      | _ when not includes_invariants -> Logic.Boolean true
      | Some _ when Facts.find_constructors context ty = None ->
          apply_opaque_validity context ty term
      | Some (source, written) -> (
          let current = find_module context context.current in
          let hidden, shown = List.partition (names_private_definition context ~current) written in
          let inner = make_type_frame context frame source ty ~self:(Some term) in
          try
            Logic.conjunction
              ((if hidden = [] then [] else [ apply_opaque_validity context ty term ])
              @ List.map (fun invariant -> snd (read_specification context inner invariant)) shown)
          with Facts.Unsupported _ when assuming -> Logic.Boolean true)
      | None -> Logic.Boolean true
    in
    let fields =
      if not deep then Logic.Boolean true
      else
        match Facts.find_constructors context ty with
        | Some shape ->
            Logic.conjunction
              (List.concat_map
                 (fun (variant, fields) ->
                   List.map
                     (fun (field, field_type) ->
                       let part =
                         make_validity context frame ~assuming ~deep ~seen:(ty :: seen) field_type
                           (select_field context ty variant field term)
                       in
                       match (variant, part) with
                       | _, Logic.Boolean true -> part
                       | Some name_, _ ->
                           Logic.( ==> )
                             (Logic.Is (Facts.make_constructor_symbol ty (Some name_), term))
                             part
                       | None, _ -> part)
                     fields)
                 shape)
        | None -> Logic.Boolean true
    in
    Logic.( &&& ) invariants_hold fields

let rec find_parts_in_range context ?(seen = []) ty term =
  if List.exists (Types.equal ty) seen || Option.is_some (find_invariants context ty) then None
  else
    match Facts.find_constructors context ty with
    | Some shape ->
        let parts =
          List.concat_map
            (fun (variant, fields) ->
              List.map
                (fun (field, field_type) ->
                  Option.map
                    (fun part ->
                      match (variant, part) with
                      | _, Logic.Boolean true | None, _ -> part
                      | Some name_, _ ->
                          Logic.( ==> )
                            (Logic.Is (Facts.make_constructor_symbol ty (Some name_), term))
                            part)
                    (find_parts_in_range context ~seen:(ty :: seen) field_type
                       (select_field context ty variant field term)))
                fields)
            shape
        in
        if List.for_all Option.is_some parts then
          Some (Logic.conjunction (List.filter_map Fun.id parts))
        else None
    | None ->
        if
          Option.is_some (Facts.find_bounds ty)
          || Option.is_some (Facts.find_float_format ty)
          || Types.is_builtin Bool ty || Types.is_builtin Unit ty
        then Some (Facts.make_in_range ty term)
        else None

let assume_valid context frame ty term =
  Facts.assume context frame (make_validity context frame ~assuming:true ty term)

let declare_callback_arguments context frame inputs =
  List.map
    (fun (_, input) ->
      let input = Facts.substitute_type context frame input in
      let term = Facts.arrive context frame "argument" input in
      assume_valid context frame input term;
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
    context.callbacks

let check_callback_contract context frame location ~name inputs requires arguments ~promised ~reason
    =
  let inside = make_callback_contract_frame frame inputs arguments in
  List.iter
    (fun (clause : Mir.formula) ->
      Facts.oblige context (Facts.restrict frame promised) location
        (Callback_requirement { name; reason; clause = Facts.quote frame.source clause.origin })
        (snd (read_specification context inside clause)))
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
  let saved = context.reading_callback in
  context.reading_callback <- true;
  Fun.protect ~finally:(fun () -> context.reading_callback <- saved) read

let bind_arguments frame (clauses : State.clauses) ~arguments ~substitution =
  let locals, types, self =
    List.fold_left
      (fun (locals, types, self) (position, (parameter : Mir.parameter)) ->
        match (parameter.local, List.assoc_opt position arguments) with
        | Self, Some term -> (locals, types, Some (term, parameter.type_))
        | local, Some term ->
            ( Locals.add (Core_local local) term locals,
              Locals.add (Core_local local) parameter.type_ types,
              self )
        | _, None -> (locals, types, self))
      (Locals.empty, Locals.empty, None)
      (List.mapi (fun position parameter -> (position, parameter)) clauses.parameters)
  in
  {
    frame with
    State.source = clauses.callee;
    locals;
    types;
    old_locals = locals;
    self = Option.map fst self;
    old_self = Option.map fst self;
    self_type = Option.map (fun (_, ty) -> Types.substitute substitution ty) self;
    result = None;
    makes_obligations = false;
    substitution;
  }

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
                List.map (Types.substitute_argument frame.substitution) trait.trait_arguments;
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
                (bind_arguments frame clauses ~arguments:known ~substitution)
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
        List.map (fun clause -> snd (read_specification context inside clause)) requires)

let list_callback_promises context frame invocation position known ~entries ~exits ~result =
  read_callee_callback context frame invocation position known
    (fun callee inside ({ inputs; ensures; _ } : Mir.callback) ->
      if List.length inputs <> List.length entries then []
      else
        let inside = make_callback_ensures_frame inside inputs ~entries ~exits ~result in
        List.map
          (fun (clause : Mir.formula) ->
            (Facts.quote callee clause.origin, snd (read_specification context inside clause)))
          ensures)

let assume_own_callback_ensures context frame local ~entries ~exits ~result =
  match find_own_callback context local with
  | Some (_, ({ inputs; ensures; _ } : Mir.callback)) when List.length inputs = List.length entries
    ->
      let inside = make_callback_ensures_frame frame inputs ~entries ~exits ~result in
      List.iter
        (fun clause -> Facts.assume context frame (snd (read_specification context inside clause)))
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
            assume_valid context frame input exit_;
            exit_
        | Read | Own -> entry)
      function_type.inputs entries
  in
  let output = Facts.substitute_type context frame function_type.output in
  let result = Facts.arrive context frame "result" output in
  assume_valid context frame output result;
  (exits, result)

let find_parameter_type (context : State.context) frame (invocation : Invocation.t) index =
  Option.bind (find_callee_declaration context frame invocation)
    (fun (_, (signature : Types.signature), substitution) ->
      let types =
        (match signature.receiver with Some (_, ty) -> [ ty ] | None -> [])
        @ List.map (fun (info : Types.parameter_info) -> info.type_) signature.parameters
      in
      Option.map (Types.substitute substitution) (List.nth_opt types index))

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
