type place_value = One of Logic.term | Run of Logic.term * Logic.term
type noted_place = { origin : Core.origin; value : place_value }

type state = {
  valid_values : (Types.ty * Logic.term) list Tables.Term_table.t;
  mutable noted_places : (Core.id * noted_place) list;
  has_predicate : bool Tables.Type_table.t;
}

let state =
  Private_state.make_key (fun () ->
      {
        valid_values = Tables.Term_table.create 16;
        noted_places = [];
        has_predicate = Tables.Type_table.create 16;
      })

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
          let paths = match edge with Calls path -> [ path ] | Passes { code; _ } -> code in
          if List.exists (is_private_to_another_module environment ~current) paths then
            is_hidden := true)
        (Mir.Call_edges.list_statement_edges environment.lookups.interface Types.no_substitution
           statement))
    clause;
  !is_hidden

let is_among (ty : Types.ty) types = List.exists (Types.equal ty) types

let list_parts (environment : State.environment) ty =
  Option.value (Encoding.find_constructors environment ty) ~default:[]

let rec reaches (environment : State.environment) ~target ~seen (ty : Types.ty) =
  Types.equal ty target
  || (not (is_among ty seen))
     && List.exists
          (fun (_, fields) ->
            List.exists
              (fun (_, field_type) -> reaches environment ~target ~seen:(ty :: seen) field_type)
              fields)
          (list_parts environment ty)

let is_recursive_part (environment : State.environment) ~whole field_type =
  reaches environment ~target:whole ~seen:[] field_type

let rec exists_in_parts (environment : State.environment) ~seen holds (ty : Types.ty) =
  match Encoding.find_constructors environment ty with
  | None -> false
  | Some shape ->
      holds ty
      || List.exists
           (fun (_, fields) ->
             List.exists
               (fun (_, field_type) ->
                 (not (is_among field_type (ty :: seen)))
                 && exists_in_parts environment ~seen:(ty :: seen) holds field_type)
               fields)
           shape

let has_invariants (environment : State.environment) ty =
  exists_in_parts environment ~seen:[]
    (fun part -> Option.is_some (find_invariants environment part))
    ty

let has_bounded_scalar (environment : State.environment) ty =
  exists_in_parts environment ~seen:[]
    (fun part ->
      List.exists
        (fun (_, fields) ->
          List.exists
            (fun (_, field_type) -> Option.is_some (Encoding.find_bounds field_type))
            fields)
        (list_parts environment part))
    ty

let is_recursive (environment : State.environment) ty =
  List.exists
    (fun (_, fields) ->
      List.exists (fun (_, field_type) -> is_recursive_part environment ~whole:ty field_type) fields)
    (list_parts environment ty)

let needs_predicate (environment : State.environment) ty =
  has_invariants environment ty || (is_recursive environment ty && has_bounded_scalar environment ty)

let read_invariants (frame : State.frame) ty term =
  match find_invariants frame.environment ty with
  | None -> Logic.Boolean true
  | Some (source, written) ->
      let current = find_module frame.environment frame.environment.current in
      let hidden, shown =
        List.partition (names_private_definition frame.environment ~current) written
      in
      let inner =
        make_type_frame
          { frame with validating = ty :: frame.validating }
          source ty ~self:(Some term)
      in
      Logic.conjunction
        ((if hidden = [] then [] else [ Logic.Apply (Logic.Symbol.Hidden_invariants ty, [ term ]) ])
        @ List.map (fun invariant -> snd (read_specification inner invariant)) shown)

let guard_variant ty variant term part =
  match (variant, part) with
  | _, Logic.Boolean true -> part
  | Some name, _ ->
      Logic.( ==> ) (Logic.Is (Encoding.make_constructor_symbol ty (Some name), term)) part
  | None, _ -> part

let map_parts (environment : State.environment) ty term make =
  let is_possible variant =
    match term with
    | Logic.Apply (Logic.Symbol.Constructor { type_; variant = built }, _) when Types.equal type_ ty
      ->
        built = variant
    | _ -> true
  in
  List.concat_map
    (fun (variant, fields) ->
      if not (is_possible variant) then []
      else
        List.map
          (fun (field, field_type) ->
            guard_variant ty variant term
              (make field_type (Encoding.select_field environment ty variant field term)))
          fields)
    (list_parts environment ty)

let rec is_built_in_place ty = function
  | Logic.Apply (Logic.Symbol.Constructor { type_; _ }, _) -> Types.equal type_ ty
  | Logic.Operation (Ite, [ _; chosen; other ]) ->
      is_built_in_place ty chosen || is_built_in_place ty other
  | _ -> false

let rec make_typed_validity (frame : State.frame) ~includes_ranges ty term =
  match (Encoding.find_constructors frame.environment ty, term) with
  | None, _ -> if includes_ranges then Encoding.make_in_range ty term else Logic.Boolean true
  | Some _, _ when is_among ty frame.validating -> Logic.Boolean true
  | Some _, Logic.Operation (Ite, [ condition; chosen; other ]) when is_built_in_place ty term -> (
      match
        ( make_typed_validity frame ~includes_ranges ty chosen,
          make_typed_validity frame ~includes_ranges ty other )
      with
      | Logic.Boolean true, Logic.Boolean true -> Logic.Boolean true
      | valid_chosen, valid_other -> Logic.ite condition valid_chosen valid_other)
  | Some _, Logic.Apply (Logic.Symbol.Constructor _, _)
    when is_built_in_place ty term && has_predicate frame ty -> (
      match read_invariants frame ty term with
      | invariants ->
          Logic.( &&& ) invariants
            (Logic.conjunction
               (map_parts frame.environment ty term (make_typed_validity frame ~includes_ranges)))
      | exception Facts.Unsupported _ -> Logic.Apply (Logic.Symbol.Valid ty, [ term ]))
  | Some _, _ when has_predicate frame ty -> Logic.Apply (Logic.Symbol.Valid ty, [ term ])
  | Some _, _ when includes_ranges ->
      Logic.conjunction
        (map_parts frame.environment ty term (make_typed_validity frame ~includes_ranges))
  | Some _, _ -> Logic.Boolean true

and has_predicate (frame : State.frame) ty =
  let predicates = (Query.read_state frame.query state).has_predicate in
  match Tables.Type_table.find_opt predicates ty with
  | Some has -> has
  | None ->
      let has = needs_predicate frame.environment ty in
      Tables.Type_table.replace predicates ty has;
      if has then state_predicate frame ty;
      has

and state_predicate (frame : State.frame) ty =
  let query = frame.query and environment = frame.environment in
  let symbol = Query.make_fresh_name query "valid" in
  let value = Logic.Symbol symbol in
  let sort = Encoding.sort_of ty in
  let holds term = Logic.Apply (Logic.Symbol.Valid ty, [ term ]) in
  let outside =
    {
      frame with
      bound = [ symbol ];
      binders = [];
      condition = Logic.Boolean true;
      makes_obligations = false;
      validating = ty :: frame.validating;
    }
  in
  let mark = Query.mark query in
  let invariants, facts =
    Query.run_in_scope query [ symbol ] (fun () ->
        match read_invariants outside ty value with
        | invariants when not (Query.mentions_fresh_since query mark invariants) -> Some invariants
        | _ -> None
        | exception Facts.Unsupported _ -> None)
  in
  let facts = List.filter (fun fact -> not (Query.mentions_fresh_since query mark fact)) facts in
  (match Logic.nest_under_conditions (Option.to_list invariants @ facts) with
  | Logic.Boolean true -> ()
  | consequences ->
      Query.add_theorem query ~because:Lemma
        (Logic.forall
           ~trigger:[ holds value ]
           ([ (symbol, sort) ], Logic.( ==> ) (holds value) consequences)));
  List.iter
    (fun (variant, fields) ->
      List.iter
        (fun (field, field_type) ->
          let selection = Encoding.select_field environment ty variant field value in
          if not (is_recursive_part environment ~whole:ty field_type) then
            match make_typed_validity outside ~includes_ranges:false field_type selection with
            | Logic.Boolean true -> ()
            | valid ->
                Query.add_theorem query ~because:Lemma
                  (Logic.forall
                     ~trigger:[ holds value; selection ]
                     ( [ (symbol, sort) ],
                       Logic.( ==> ) (holds value) (guard_variant ty variant value valid) )))
        fields;
      let parts =
        List.mapi
          (fun index (_, field_type) ->
            ( Logic.Symbol.Variable
                { label = "part"; numbers = [ Query.take_fresh_number query; index ] },
              Encoding.sort_of field_type ))
          fields
      in
      let constructed =
        Logic.Apply
          ( Encoding.make_constructor_symbol ty variant,
            List.map (fun (name, _) -> Logic.Symbol name) parts )
      in
      let list_part_validity ~includes_ranges =
        List.map2
          (fun (_, field_type) (name, _) ->
            make_typed_validity outside ~includes_ranges field_type (Logic.Symbol name))
          fields parts
      in
      let stated =
        match invariants with
        | Some invariants ->
            Logic.equal (holds constructed)
              (Logic.conjunction
                 (Logic.substitute [ (symbol, constructed) ] invariants
                 :: list_part_validity ~includes_ranges:true))
        | None ->
            Logic.( ==> ) (holds constructed)
              (Logic.conjunction (list_part_validity ~includes_ranges:false))
      in
      if stated <> Logic.Boolean true then
        Query.add_theorem query ~because:Lemma
          (match parts with
          | [] -> stated
          | _ -> Logic.forall ~trigger:[ holds constructed ] (parts, stated)))
    (list_parts environment ty)

let rec make_checked_validity (frame : State.frame) ~deep ~includes_invariants ty term =
  match (Encoding.find_constructors frame.environment ty, term) with
  | None, _ -> Logic.Boolean true
  | Some _, _ when is_among ty frame.validating -> Logic.Boolean true
  | Some _, Logic.Operation (Ite, [ condition; chosen; other ]) ->
      Logic.ite condition
        (make_checked_validity frame ~deep ~includes_invariants ty chosen)
        (make_checked_validity frame ~deep ~includes_invariants ty other)
  | Some _, _ ->
      let invariants =
        if includes_invariants then read_invariants frame ty term else Logic.Boolean true
      in
      let check_part field_type part =
        if
          is_recursive_part frame.environment ~whole:ty field_type
          || not (has_invariants frame.environment field_type)
        then Logic.Boolean true
        else if is_built_in_place field_type part then
          make_checked_validity frame ~deep ~includes_invariants:true field_type part
        else make_typed_validity frame ~includes_ranges:false field_type part
      in
      Logic.( &&& ) invariants
        (if deep then Logic.conjunction (map_parts frame.environment ty term check_part)
         else Logic.Boolean true)

let make_assumed_validity (frame : State.frame) ~includes_invariants ~includes_ranges ty term =
  if includes_invariants then make_typed_validity frame ~includes_ranges ty term
  else
    Logic.conjunction
      (map_parts frame.environment ty term (fun field_type part ->
           if is_recursive_part frame.environment ~whole:ty field_type then Logic.Boolean true
           else make_typed_validity frame ~includes_ranges:false field_type part))

let make_validity (frame : State.frame) ~assuming ?(deep = true) ?(includes_invariants = true)
    ?(includes_ranges = false) ty term =
  if assuming then make_assumed_validity frame ~includes_invariants ~includes_ranges ty term
  else make_checked_validity frame ~deep ~includes_invariants ty term

let assume_valid ?(includes_invariants = true) (frame : State.frame) ty term =
  Facts.assume frame (make_validity frame ~assuming:true ~includes_invariants ty term);
  if includes_invariants then note_valid frame ty term

let check_valid ?(includes_invariants = true) (frame : State.frame) location ty term ~deep ~moment =
  if frame.makes_obligations && not (is_known_valid frame ty term) then begin
    (match make_validity frame ~assuming:false ~deep ~includes_invariants ty term with
    | Logic.Boolean true -> ()
    | valid -> Obligations.oblige frame location (Invariant_may_fail { type_ = ty; moment }) valid);
    if deep && includes_invariants then begin
      Facts.assume frame (make_typed_validity frame ~includes_ranges:false ty term);
      note_valid frame ty term
    end
  end
