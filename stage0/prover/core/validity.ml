type place_value = One of Logic.term | Run of Logic.term * Logic.term
type noted_place = { origin : Core.origin; value : place_value }

type state = {
  valid_values : (Types.ty * Logic.term) list Tables.Term_table.t;
  mutable noted_places : (Core.id * noted_place) list;
}

let state =
  Private_state.make_key (fun () ->
      { valid_values = Tables.Term_table.create 16; noted_places = [] })

let type_declarations :
    (State.source * Mir.type_clauses option Lazy.t) option Tables.Path_table.t Private_state.key =
  Private_state.make_key (fun () -> Tables.Path_table.create 16)

let list_valid_at (query : Query.t) term =
  Option.value
    (Tables.Term_table.find_opt (Query.read_state query state).valid_values term)
    ~default:[]

let is_known_valid (frame : State.frame) ty term =
  List.exists
    (fun (valid_type, condition) ->
      Types.equal valid_type ty
      && (condition = Logic.Boolean true || Fact_list.encloses condition ~inner:frame.condition))
    (list_valid_at frame.query term)

let note_valid (frame : State.frame) ty term =
  if not (Logic.mentions frame.bound term || Logic.mentions frame.bound frame.condition) then
    Tables.Term_table.replace (Query.read_state frame.query state).valid_values term
      ((ty, frame.condition) :: list_valid_at frame.query term)

let find_selected_place (query : Query.t) selection =
  let noted_places = (Query.read_state query state).noted_places in
  let shift offset = function
    | One index -> One (Logic.add offset index)
    | Run (start, stop) -> Run (Logic.add offset start, Logic.add offset stop)
  in
  let rec find_from offset = function
    | [] -> Facts.raise_bug "a selection of no range or element"
    | [ innermost ] ->
        Option.map (fun noted -> shift offset noted.value) (List.assoc_opt innermost noted_places)
    | range :: inner -> (
        match List.assoc_opt range noted_places with
        | Some { value = Run (start, _); _ } -> find_from (Logic.add offset start) inner
        | Some { value = One _; _ } -> Facts.raise_bug "a selection that selects inside an element"
        | None -> None)
  in
  find_from (Logic.int 0) selection

let read_innermost selection =
  match List.rev selection with
  | innermost :: _ -> innermost
  | [] -> Facts.raise_bug "a selection of no range or element"

let note_place (frame : State.frame) ~node ~origin value =
  let mentions (first, second) = List.mem node first || List.mem node second in
  if Facts.is_home frame && List.exists mentions frame.environment.disjoint then begin
    let state = Query.read_state frame.query state in
    state.noted_places <- (node, { origin; value }) :: state.noted_places;
    let quote selection =
      Facts.quote frame.source (List.assoc (read_innermost selection) state.noted_places).origin
    in
    let outside index start stop = Logic.(less index start ||| less_equal stop index) in
    List.iter
      (fun (first, second) ->
        if read_innermost first = node || read_innermost second = node then
          match (find_selected_place frame.query first, find_selected_place frame.query second) with
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
              Obligations.oblige frame (Facts.locate frame origin)
                (May_alias { first = quote first; second = quote second })
                apart
          | _ -> ())
      frame.environment.disjoint
  end

let run_as_specification (frame : State.frame) read =
  let (after : State.frame), value =
    read (Counters.stop_counting (Obligations.set_panics frame ~panics:false))
  in
  ( {
      after with
      spent = frame.spent;
      conditional_counters = frame.conditional_counters;
      panics = frame.panics;
      can_declare_panic = frame.can_declare_panic;
    },
    value )

let read_specification ?holds_when (frame : State.frame) (formula : Mir.formula) =
  let after, term =
    run_as_specification
      {
        frame with
        obligation_condition = Option.value holds_when ~default:frame.obligation_condition;
      }
      (fun specification -> frame.environment.read_formula specification formula ~arguments:[])
  in
  ({ after with obligation_condition = frame.obligation_condition }, term)

let check_defined (frame : State.frame) ~holds_when (formula : Mir.formula) =
  ignore (read_specification ~holds_when frame formula)

let make_type_frame (frame : State.frame) source (ty : Types.ty) ~self =
  let substitution =
    match Encoding.find_visible_type frame.environment ty with
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

let find_type_declaration (environment : State.environment) (ty : Types.ty) =
  let type_declarations = Private_state.read environment.memos type_declarations in
  match ty with
  | Types.Named { path; _ } -> (
      match Tables.Path_table.find_opt type_declarations path with
      | Some declaration -> declaration
      | None ->
          let declaration =
            if Resolve.Names.find_kind environment.lookups.interface.names path = Some Type then
              Option.map
                (fun (source, _, _) ->
                  ( source,
                    lazy
                      (Option.map
                         (fun ({ form; _ } : Mir.type_clauses Mir.sourced) -> form)
                         (Mir.read_type_clauses environment.lookups.mir path)) ))
                (Contracts.find_source environment.lookups path)
            else None
          in
          Tables.Path_table.replace type_declarations path declaration;
          declaration)
  | _ -> None

let find_type_source (environment : State.environment) ty =
  Option.map fst (find_type_declaration environment ty)

let find_type_clauses (environment : State.environment) ty =
  Option.bind (find_type_declaration environment ty) (fun (source, clauses) ->
      Option.map (fun clauses -> (source, clauses)) (Lazy.force clauses))

let list_invariants (clauses : Mir.loop_clause list) =
  List.filter_map (function Mir.Invariant value -> Some value | _ -> None) clauses

let find_invariants (environment : State.environment) (ty : Types.ty) =
  match find_type_clauses environment ty with
  | Some (source, { invariants = _ :: _ as invariants; _ }) ->
      Some (source, List.map (fun (invariant : Mir.requirement) -> invariant.clause) invariants)
  | _ -> None

let find_module (environment : State.environment) path =
  Option.map
    (fun (key : Resolve.Names.key) -> key.module_)
    (environment.lookups.interface.names.find_key path)

let is_private_to_another_module (environment : State.environment) ~current path =
  match environment.lookups.interface.names.find_key path with
  | Some key ->
      (environment.lookups.interface.names.read_declaration key).visibility = Resolve.Names.Private
      && Some key.module_ <> current
  | None -> false

let names_private_definition (environment : State.environment) ~current (clause : Mir.formula) =
  let is_hidden = ref false in
  Mir.iter_formula
    (fun statement ->
      List.iter
        (fun (edge : Mir.Call_edges.edge) ->
          let paths = match edge with Calls path -> [ path ] | Supplies { code; _ } -> code in
          if List.exists (is_private_to_another_module environment ~current) paths then
            is_hidden := true)
        (Mir.Call_edges.list_statement_edges environment.lookups.interface Types.no_substitution
           statement))
    clause;
  !is_hidden

let apply_opaque_validity ty term =
  let symbol = Logic.Symbol.Valid ty in
  Logic.Apply (symbol, [ term ])

let rec make_validity (frame : State.frame) ~assuming ?(deep = true) ?(includes_invariants = true)
    ?(includes_ranges = false) ?(seen = []) ty term =
  if List.exists (Types.equal ty) seen || List.exists (Types.equal ty) frame.validating then
    Logic.Boolean true
  else
    let frame = { frame with validating = ty :: frame.validating } in
    let invariants_hold =
      match find_invariants frame.environment ty with
      | _ when not includes_invariants -> Logic.Boolean true
      | Some _ when Encoding.find_constructors frame.environment ty = None -> Logic.Boolean true
      | Some (source, written) -> (
          let current = find_module frame.environment frame.environment.current in
          let hidden, shown =
            List.partition (names_private_definition frame.environment ~current) written
          in
          let inner = make_type_frame frame source ty ~self:(Some term) in
          try
            Logic.conjunction
              ((if hidden = [] then [] else [ apply_opaque_validity ty term ])
              @ List.map (fun invariant -> snd (read_specification inner invariant)) shown)
          with Facts.Unsupported _ when assuming -> Logic.Boolean true)
      | None -> Logic.Boolean true
    in
    let fields =
      if not deep then Logic.Boolean true
      else
        match Encoding.find_constructors frame.environment ty with
        | Some shape ->
            Logic.conjunction
              (List.concat_map
                 (fun (variant, fields) ->
                   List.map
                     (fun (field, field_type) ->
                       let part =
                         make_validity frame ~assuming ~deep ~includes_ranges ~seen:(ty :: seen)
                           field_type
                           (Encoding.select_field frame.environment ty variant field term)
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

let assume_valid ?(includes_invariants = true) (frame : State.frame) ty term =
  Facts.assume frame (make_validity frame ~assuming:true ~includes_invariants ty term);
  if includes_invariants then note_valid frame ty term

let check_valid ?(includes_invariants = true) (frame : State.frame) location ty term ~deep ~moment =
  if not (is_known_valid frame ty term) then
    match make_validity frame ~assuming:false ~deep ~includes_invariants ty term with
    | Logic.Boolean true -> ()
    | valid ->
        Obligations.oblige frame location (Invariant_may_fail { type_ = ty; moment }) valid;
        if deep && includes_invariants && frame.makes_obligations then note_valid frame ty term
