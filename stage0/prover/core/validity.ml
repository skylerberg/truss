let note_place (context : State.context) (frame : State.frame) origin place =
  if
    frame.source.key = Some context.home
    && List.exists (fun (first, second) -> first = origin || second = origin) context.disjoint
  then begin
    context.indexes <- (origin, place) :: context.indexes;
    let outside index start stop =
      Logic.(Operation ("<", [ index; start ]) ||| Operation ("<=", [ stop; index ]))
    in
    List.iter
      (fun (first, second) ->
        if first = origin || second = origin then
          match (List.assoc_opt first context.indexes, List.assoc_opt second context.indexes) with
          | Some left, Some right ->
              let apart =
                match (left, right) with
                | One left, One right -> Logic.not_ (Logic.equal left right)
                | One index, Run (start, stop) | Run (start, stop), One index ->
                    outside index start stop
                | Run (start, stop), Run (other_start, other_stop) ->
                    Logic.disjunction
                      [
                        Logic.Operation ("<=", [ stop; other_start ]);
                        Logic.Operation ("<=", [ other_stop; start ]);
                        Logic.Operation ("<=", [ stop; start ]);
                        Logic.Operation ("<=", [ other_stop; other_start ]);
                      ]
              in
              Facts.oblige context frame Disjoint
                (Facts.locate context frame.source origin)
                [
                  Text "`";
                  Facts.quote frame.source first;
                  Text "` and `";
                  Facts.quote frame.source second;
                  Text "` may reach the same elements, which are used together.";
                ]
                apart
          | _ -> ())
      context.disjoint
  end

let run_without_costs : 'a. _ -> (unit -> 'a) -> 'a =
 fun (context : State.context) read ->
  let saved = context.counters in
  context.counters <- [];
  Fun.protect ~finally:(fun () -> context.counters <- saved) read

let read_specification context frame (formula : Mir.formula) =
  run_without_costs context (fun () -> context.read_formula frame formula ~arguments:[])

let select_field context ty variant field term =
  match (term, Facts.find_constructors context ty) with
  | Logic.Apply (name, arguments), Some shape when name = Facts.make_constructor_symbol ty variant
    -> (
      let fields = Option.value (List.assoc_opt variant shape) ~default:[] in
      match List.find_index (fun (named, _) -> named = field) fields with
      | Some index when index < List.length arguments -> List.nth arguments index
      | _ -> Logic.Apply (Facts.make_selector_symbol ty variant field, [ term ]))
  | _ -> Logic.Apply (Facts.make_selector_symbol ty variant field, [ term ])

let make_type_frame context frame source (ty : Types.ty) ~self =
  let substitution =
    match Facts.find_visible_type context ty with Some (_, symbol) -> symbol | None -> []
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

let find_type_source (context : State.context) (ty : Types.ty) =
  match ty with
  | Types.Named { path; _ }
    when Resolve.Names.find_kind context.lookups.interface.names path = Some Type ->
      Option.map (fun (source, _, _) -> source) (Contracts.find_source context.lookups path)
  | _ -> None

let find_type_clauses context (ty : Types.ty) =
  match (ty, find_type_source context ty) with
  | Types.Named { path; _ }, Some source ->
      Option.map
        (fun ({ form; _ } : Mir.type_clauses Mir.sourced) -> (source, form))
        (Mir.read_type_clauses context.lookups.mir path)
  | _ -> None

let list_invariants (clauses : Mir.loop_clause list) =
  List.filter_map (function Mir.Invariant value -> Some value | _ -> None) clauses

let find_invariants context (ty : Types.ty) =
  match find_type_clauses context ty with
  | Some (source, { invariants = _ :: _ as invariants; _ }) ->
      Some (source, List.map (fun (invariant : Mir.requirement) -> invariant.clause) invariants)
  | _ -> None

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
          let symbol = Logic.Symbol.Valid ty in
          Facts.declare context
            (Logic.Function (symbol, [ Facts.declare_sort context ty ], Logic.Bool));
          Logic.Apply (symbol, [ term ])
      | Some (source, written) -> (
          let inner = make_type_frame context frame source ty ~self:(Some term) in
          try
            Logic.conjunction
              (List.map (fun invariant -> snd (read_specification context inner invariant)) written)
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

let find_own_callback (context : State.context) local =
  List.find_map
    (fun (parameter, name, callback) -> if parameter = local then Some (name, callback) else None)
    context.callbacks

let check_callback_contract context frame location ~name inputs requires arguments ~promised ~why =
  let inside = make_callback_contract_frame frame inputs arguments in
  List.iter
    (fun (clause : Mir.formula) ->
      Facts.oblige context (Facts.restrict frame promised) Requires location
        [
          Text (Printf.sprintf "`%s` %s, so its `" name why);
          Facts.quote frame.source clause.origin;
          Text "` may not hold.";
        ]
        (snd (read_specification context inside clause)))
    requires

let check_escaping_callback context frame local =
  match
    (find_own_callback context local, Facts.find_local_type context frame (Core_local local))
  with
  | ( Some (name, ({ inputs; requires = _ :: _ as requires } : Mir.callback)),
      Some (Types.Function function_type) )
    when List.length inputs = List.length function_type.inputs ->
      let arguments = declare_callback_arguments context frame function_type.inputs in
      check_callback_contract context frame
        (Facts.locate context frame.source (List.hd requires).origin)
        ~name inputs requires arguments ~promised:(Logic.Boolean true)
        ~why:"is used as a value whose type promises nothing of its arguments"
  | _ -> ()

let run_reading_callback : 'a. _ -> (unit -> 'a) -> 'a =
 fun (context : State.context) read ->
  let saved = context.reading_callback in
  context.reading_callback <- true;
  Fun.protect ~finally:(fun () -> context.reading_callback <- saved) read

let bind_part_arguments frame (part : State.part) ~arguments ~substitution =
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
      (List.mapi (fun position parameter -> (position, parameter)) part.parameters)
  in
  {
    frame with
    State.source = part.callee;
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

let make_callee_substitution (frame : State.frame) (signature : Types.signature) type_arguments =
  Types.make_substitution signature.generics
    (List.map (Types.substitute_argument frame.substitution) type_arguments)

let list_callback_facts (context : State.context) frame (invocation : Invocation.t) position known
    arguments =
  match invocation.callee with
  | Function { path; type_arguments } -> (
      match
        Option.bind (Contracts.find_source context.lookups path) (fun (callee, _, _) ->
            Contracts.find_part context.lookups path callee)
      with
      | Some part -> (
          match List.assoc_opt position part.callbacks with
          | Some { inputs; requires } when List.length inputs = List.length arguments ->
              let substitution =
                match Interface.Impls.read_signature context.lookups.interface path with
                | Some (signature : Types.signature) ->
                    make_callee_substitution frame signature type_arguments
                | None -> []
              in
              let inside = bind_part_arguments frame part ~arguments:known ~substitution in
              let inside =
                {
                  inside with
                  locals =
                    List.fold_left2
                      (fun locals local term -> Locals.add (Core_local local) term locals)
                      inside.locals inputs arguments;
                }
              in
              List.map (fun clause -> snd (read_specification context inside clause)) requires
          | _ -> [])
      | None -> [])
  | _ -> []

let find_parameter_type (context : State.context) frame (invocation : Invocation.t) index =
  match invocation.callee with
  | Function { path; type_arguments } -> (
      match Interface.Impls.read_signature context.lookups.interface path with
      | Some (signature : Types.signature) ->
          let types =
            (match signature.receiver with
              | Some ((Read | Mut | Own), ty) -> [ ty ]
              | Some (Static, _) | None -> [])
            @ List.map (fun (info : Types.parameter_info) -> info.type_) signature.parameters
          in
          Option.map
            (Types.substitute (make_callee_substitution frame signature type_arguments))
            (List.nth_opt types index)
      | None -> None)
  | _ -> None

let check_forwarded_callback context frame (site : Invocation.site) (invocation : Invocation.t)
    (passed : State.passed) local values =
  match find_own_callback context local with
  | Some (name, ({ inputs; requires = _ :: _ as requires } : Mir.callback)) -> (
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
            ~why:"is passed for a parameter that may not promise its `requires`"
      | _ -> check_escaping_callback context frame local)
  | _ -> ()
