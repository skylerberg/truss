let make_state () : State.validity_state =
  { type_clauses = Tables.Path_table.create 16; valid_values = Tables.Term_table.create 16 }

let list_valid_at (context : State.context) term =
  Option.value (Tables.Term_table.find_opt context.validity.valid_values term) ~default:[]

let is_known_valid (context : State.context) (frame : State.frame) ty term =
  List.exists
    (fun (valid_type, condition) ->
      Types.equal valid_type ty
      && (condition = Logic.Boolean true || Fact_list.encloses condition ~inner:frame.condition))
    (list_valid_at context term)

let note_valid (context : State.context) (frame : State.frame) ty term =
  if not (Logic.mentions frame.bound term || Logic.mentions frame.bound frame.condition) then
    Tables.Term_table.replace context.validity.valid_values term
      ((ty, frame.condition) :: list_valid_at context term)

let find_selected_place (context : State.context) selection =
  let shift offset : State.place_value -> State.place_value = function
    | One index -> One (Logic.add offset index)
    | Run (start, stop) -> Run (Logic.add offset start, Logic.add offset stop)
  in
  let rec find_from offset = function
    | [] -> Facts.raise_bug "a selection of no range or element"
    | [ innermost ] ->
        Option.map
          (fun (noted : State.noted_place) -> shift offset noted.value)
          (List.assoc_opt innermost context.indexes)
    | range :: inner -> (
        match List.assoc_opt range context.indexes with
        | Some { value = Run (start, _); _ } -> find_from (Logic.add offset start) inner
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
              Obligations.oblige context frame
                (Facts.locate context frame.source origin)
                (May_alias { first = quote first; second = quote second })
                apart
          | _ -> ())
      context.disjoint
  end

let run_as_specification (context : State.context) (frame : State.frame) read =
  Counters.run_without_counters context (fun () ->
      read (Obligations.set_panics frame ~panics:false))

let read_specification ?holds_when (context : State.context) (frame : State.frame)
    (formula : Mir.formula) =
  let after, term =
    run_as_specification context
      {
        frame with
        obligation_condition = Option.value holds_when ~default:frame.obligation_condition;
      }
      (fun specification -> context.read_formula specification formula ~arguments:[])
  in
  ( {
      after with
      panics = frame.panics;
      can_declare_panic = frame.can_declare_panic;
      obligation_condition = frame.obligation_condition;
    },
    term )

let check_defined context frame ~holds_when (formula : Mir.formula) =
  ignore (read_specification ~holds_when context frame formula)

let make_type_frame context frame source (ty : Types.ty) ~self =
  let substitution =
    match Encoding.find_visible_type context ty with
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
      match Tables.Path_table.find_opt context.validity.type_clauses path with
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
          Tables.Path_table.replace context.validity.type_clauses path declaration;
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

let apply_opaque_validity ty term =
  let symbol = Logic.Symbol.Valid ty in
  Logic.Apply (symbol, [ term ])

let rec make_validity (context : State.context) (frame : State.frame) ~assuming ?(deep = true)
    ?(includes_invariants = true) ?(includes_ranges = false) ?(seen = []) ty term =
  if List.exists (Types.equal ty) seen || List.exists (Types.equal ty) frame.validating then
    Logic.Boolean true
  else
    let frame = { frame with validating = ty :: frame.validating } in
    let invariants_hold =
      match find_invariants context ty with
      | _ when not includes_invariants -> Logic.Boolean true
      | Some _ when Encoding.find_constructors context ty = None -> Logic.Boolean true
      | Some (source, written) -> (
          let current = find_module context context.current in
          let hidden, shown = List.partition (names_private_definition context ~current) written in
          let inner = make_type_frame context frame source ty ~self:(Some term) in
          try
            Logic.conjunction
              ((if hidden = [] then [] else [ apply_opaque_validity ty term ])
              @ List.map (fun invariant -> snd (read_specification context inner invariant)) shown)
          with Facts.Unsupported _ when assuming -> Logic.Boolean true)
      | None -> Logic.Boolean true
    in
    let fields =
      if not deep then Logic.Boolean true
      else
        match Encoding.find_constructors context ty with
        | Some shape ->
            Logic.conjunction
              (List.concat_map
                 (fun (variant, fields) ->
                   List.map
                     (fun (field, field_type) ->
                       let part =
                         make_validity context frame ~assuming ~deep ~includes_ranges
                           ~seen:(ty :: seen) field_type
                           (Encoding.select_field context ty variant field term)
                       in
                       match (variant, part) with
                       | _, Logic.Boolean true -> part
                       | Some name_, _ ->
                           Logic.( ==> )
                             (Logic.Is (Encoding.make_constructor_symbol ty (Some name_), term))
                             part
                       | None, _ -> part)
                     fields)
                 shape)
        | None -> if includes_ranges then Encoding.make_in_range ty term else Logic.Boolean true
    in
    Logic.( &&& ) invariants_hold fields

let assume_valid ?(includes_invariants = true) context frame ty term =
  Facts.assume context frame
    (make_validity context frame ~assuming:true ~includes_invariants ty term);
  if includes_invariants then note_valid context frame ty term

let check_valid ?(includes_invariants = true) context (frame : State.frame) location ty term ~deep
    ~moment =
  if not (is_known_valid context frame ty term) then
    match make_validity context frame ~assuming:false ~deep ~includes_invariants ty term with
    | Logic.Boolean true -> ()
    | valid ->
        Obligations.oblige context frame location (Invariant_may_fail { type_ = ty; moment }) valid;
        if deep && includes_invariants && frame.makes_obligations then
          note_valid context frame ty term
